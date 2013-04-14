# This file contains code dealing specifically with converting Mercurial
# repositories to Git repositories. Code in this file is meant to be a generic
# library and should be usable outside the context of hg-git or an hg command.

import multiprocessing
import os
import Queue
import random
import stat
import time

from dulwich.objects import Blob
from dulwich.objects import S_IFGITLINK
from dulwich.objects import TreeEntry
from dulwich.objects import Tree
from dulwich.repo import Repo

from mercurial import error as hgerror
from mercurial.hg import repository
from mercurial.node import nullrev
from mercurial.ui import ui as hgui

from . import util

class TreeTracker(object):
    """Tracks Git tree objects across Mercurial revisions.

    The purpose of this class is to facilitate Git tree export that is more
    optimal than brute force. The tree calculation part of this class is
    essentially a reimplementation of dulwich.index.commit_tree. However, since
    our implementation reuses Tree instances and only recalculates SHA-1 when
    things change, we are much more efficient.

    Callers instantiate this class against a mercurial.localrepo instance. They
    then associate the tracker with a specific changeset by calling
    update_changeset(). That function emits Git objects that need to be
    exported to a Git repository. Callers then typically obtain the
    root_tree_sha and use that as part of assembling a Git commit.
    """

    def __init__(self, hg_repo, blob_cache=None):
        self._hg = hg_repo
        self._rev = nullrev
        self._dirs = {}
        self._blob_cache = blob_cache or {}

    @property
    def root_tree_sha(self):
        return self._dirs[''].id

    def update_changeset(self, ctx):
        """Set the tree to track a new Mercurial changeset.

        This is a generator of 2-tuples. The first item in each tuple is a
        dulwich object, either a Blob or a Tree. The second item is the
        corresponding Mercurial nodeid for the item, if any. Only blobs will
        have nodeids. Trees do not correspond to a specific nodeid, so it does
        not make sense to emit a nodeid for them.

        When exporting trees from Mercurial, callers typically write the
        returned dulwich object to the Git repo via the store's add_object().

        Some emitted objects may already exist in the Git repository.

        Emitted objects are those that have changed since the last call to
        update_changeset. If this is the first call to update_chanageset, all
        objects in the tree are emitted.
        """
        # In theory we should be able to look at changectx.files(). This is
        # *much* faster. However, it may not be accurate, especially with older
        # repositories, which may not record things like deleted files
        # explicitly in the manifest (which is where files() gets its data).
        # The only reliable way to get the full set of changes is by looking at
        # the full manifest. And, the easy way to compare two manifests is
        # localrepo.status().

        # The other members of status are only relevant when looking at the
        # working directory.
        modified, added, removed = self._hg.status(self._rev, ctx.rev())[0:3]

        # We track which directories/trees have modified in this update and we
        # only export those.
        dirty_trees = set()

        # We first process file removals so we can prune dead trees.
        for path in removed:
            d = os.path.dirname(path)
            tree = self._dirs.get(d, Tree())

            del tree[os.path.basename(path)]
            dirty_trees.add(d)

            if not len(tree):
                self._remove_tree(d)
                continue

            self._dirs[d] = tree

        # For every file that changed or was added, we need to calculate the
        # corresponding Git blob and its tree entry. We emit the blob
        # immediately and update trees to be aware of its presence.
        for path in set(modified) | set(added):
            # Handle special Mercurial paths.
            if path == '.hgsubstate':
                self._handle_subrepos(ctx, dirty_trees)
                continue

            if path == '.hgsub':
                continue

            d = os.path.dirname(path)
            tree = self._dirs.setdefault(d, Tree())
            dirty_trees.add(d)

            fctx = ctx[path]

            entry, blob = TreeTracker.tree_entry(fctx, self._blob_cache)
            if blob is not None:
                yield (blob, fctx.filenode())

            tree.add(*entry)
            self._dirs[d] = tree

        # Now that all the trees represent the current changeset, recalculate
        # the tree IDs and emit them. Note that we wait until now to calculate
        # tree SHA-1s. This is an important difference between us and
        # dulwich.index.commit_tree(), which builds new Tree instances for each
        # series of blobs.
        for obj in self._populate_tree_entries(dirty_trees):
            yield (obj, None)

        self._rev = ctx.rev()

    def _remove_tree(self, path):
        try:
            del self._dirs[path]
        except KeyError:
            return

        # Now we traverse up to the parent and delete any references.
        if path == '':
            return

        basename = os.path.basename(path)
        parent = os.path.dirname(path)
        while True:
            tree = self._dirs.get(parent, None)

            # No parent entry. Nothing to remove or update.
            if tree is None:
                return

            try:
                del tree[basename]
            except KeyError:
                return

            if len(tree):
                return

            # The parent tree is empty. Se, we can delete it.
            del self._dirs[parent]

            if parent == '':
                return

            basename = os.path.basename(parent)
            parent = os.path.dirname(parent)

    def _populate_tree_entries(self, dirty_trees):
        self._dirs.setdefault('', Tree())

        # Fill in missing directories.
        for path in self._dirs.keys():
            parent = os.path.dirname(path)

            while parent != '':
                parent_tree = self._dirs.get(parent, None)

                if parent_tree is not None:
                    break

                self._dirs[parent] = Tree()
                parent = os.path.dirname(parent)

        for dirty in list(dirty_trees):
            parent = os.path.dirname(dirty)

            while parent != '':
                if parent in dirty_trees:
                    break

                dirty_trees.add(parent)
                parent = os.path.dirname(parent)

        # The root tree is always dirty but doesn't always get updated.
        dirty_trees.add('')

        # We only need to recalculate and export dirty trees.
        for d in sorted(dirty_trees, key=len, reverse=True):
            # Only happens for deleted directories.
            try:
                tree = self._dirs[d]
            except KeyError:
                continue

            yield tree

            if d == '':
                continue

            parent_tree = self._dirs[os.path.dirname(d)]

            # Accessing the tree's ID is what triggers SHA-1 calculation and is
            # the expensive part (at least if the tree has been modified since
            # the last time we retrieved its ID). Also, assigning an entry to a
            # tree (even if it already exists) invalidates the existing tree
            # and incurs SHA-1 recalculation. So, it's in our interest to avoid
            # invalidating trees. Since we only update the entries of dirty
            # trees, this should hold true.
            parent_tree[os.path.basename(d)] = (stat.S_IFDIR, tree.id)

    def _handle_subrepos(self, ctx, dirty_trees):
        substate = util.parse_hgsubstate(ctx['.hgsubstate'].data().splitlines())
        sub = util.OrderedDict()

        if '.hgsub' in ctx:
            sub = util.parse_hgsub(ctx['.hgsub'].data().splitlines())

        for path, sha in substate.iteritems():
            # Ignore non-Git repositories keeping state in .hgsubstate.
            if path in sub and not sub[path].startswith('[git]'):
                continue

            d = os.path.dirname(path)
            dirty_trees.add(d)
            tree = self._dirs.setdefault(d, Tree())
            tree.add(os.path.basename(path), S_IFGITLINK, sha)

    @staticmethod
    def tree_entry(fctx, blob_cache):
        blob_id = blob_cache.get(fctx.filenode(), None)
        blob = None

        if blob_id is None:
            blob = Blob.from_string(fctx.data())
            blob_id = blob.id
            blob_cache[fctx.filenode()] = blob_id

        flags = fctx.flags()

        if 'l' in flags:
            mode = 0120000
        elif 'x' in flags:
            mode = 0100755
        else:
            mode = 0100644

        return (TreeEntry(os.path.basename(fctx.path()), mode, blob_id), blob)


class MercurialToGitConverter(object):
    def __init__(self, hg_repo, git_repo):
        self.hg = hg_repo
        self.git = git_repo

    def export_trees(self, changeids=None, auto_pack=True,
            auto_pack_interval=60, batch_size=100,
            worker_pool_size=multiprocessing.cpu_count(),
            on_blob=None, existing_objects=None):
        """Export Git trees for Mercurial changesets.

        The caller specifies a list of Mercurial changesets to export. These
        can be specified as numeric revisions or binary node IDs. This function
        spins up a pool of worker processes that exports the Git trees for
        these changesets. If no changesets are specified, all changesets are
        exported.

        This is a generator of 2-tuple of (node, tree_sha). Each node is
        emitted in the order from the changeids input. If a tree finishes
        export, the result is buffered until changesets before it from
        changeids is emitted. This does not impact the overall execution time.
        But, downstream consumers will appear to be starved.

        By default, a background process will automatically pack loose objects
        every 60 seconds. This prevents the number of loose objects in the Git
        repository from becoming too unwieldy. For "small" exports (that take
        less than auto_pack_interval seconds), automatic background packing
        will never kick in.

        To disable automatic background packing, just set auto_pack_interval to
        False.

        Work is distributed among a worker pool. By default, we spin up a
        worker for each processor in the machine.

        Work is distributed to each worker process in batches of adjacent
        changesets. Processing adjacent changesets (specifically changesets
        that are direct descendants of each other) is more efficient than
        jumping around to disconnected changesets. Therefore, the larger the
        batch size, the more efficient export will run. The risk with a large
        batch size is that at the end of the export, workers will become
        starved while 1 or a small number of workers has outstanding work. The
        default batch size is small enough to mitigate this risk while large
        enough to gain efficiency from adjacent changeset processing.
        """

        if changeids is None:
            changeids = [self.hg.lookup(n) for n in self.hg]

        # Each worker has a handle on a job queue, a result queue, and an
        # "should I continue to be alive" flag.
        job_queue = multiprocessing.Queue()
        result_queue = multiprocessing.Queue()
        alive = multiprocessing.Value('i', 1)

        packer = None
        if auto_pack:
            packer = multiprocessing.Process(
                target=MercurialToGitConverter._process_periodic_pack,
                name='packer',
                args=(self.git.path, auto_pack_interval, alive))

            packer.start()

        config = list(self.hg.ui.walkconfig())
        workers = []
        for i in range(worker_pool_size):
            worker = multiprocessing.Process(
                target=MercurialToGitConverter._process_tree_export,
                args=(config, self.hg.root, self.git.path, existing_objects,
                    job_queue, result_queue, alive))
            worker.start()

            workers.append(worker)

        # Try to balance out work across all workers when we have a small
        # number of changesets.
        if len(changeids) < batch_size * worker_pool_size:
            # If we have a really small number, just give them to one worker.
            if len(changeids) < worker_pool_size:
                batch_size = worker_pool_size
            else:
                batch_size = len(changeids) / worker_pool_size

        batches = [changeids[i:i+batch_size] for i in range(0, len(changeids),
            batch_size)]

        for batch in batches:
            job_queue.put(batch)

        # Holds the results we have yet to emit.
        pending = [rev for rev in changeids]

        # Buffers results as they are received.
        finished = {}

        try:
            while len(pending):
                # Emit results as soon as we can.
                if pending[0] in finished:
                    yield (pending[0], finished[pending[0]])
                    del finished[pending[0]]
                    pending.pop(0)
                    continue

                results = []
                wait = 0.25
                try:
                    # Grab as many results as possible.
                    while True:
                        results.append(result_queue.get(wait != 0, wait))
                        wait = 0
                except Queue.Empty:
                    pass

                for result_type, data in results:
                    if result_type == 'TREE':
                        finished[data[0]] = data[1]
                        continue

                    if result_type == 'BLOB':
                        if on_blob:
                            on_blob(data[0], data[1])

                        continue

                    raise Exception('Unknown result type: %s', result_type)

            alive.value = 0
        except Exception as e:
            alive.value = 0

            for worker in workers:
                worker.terminate()

            if packer is not None:
                packer.terminate()

            raise e
        finally:
            alive.value = 0

            for worker in workers:
                worker.join()

            # If packing started near the end of processing, this could take
            # a while. But, packing needs to be done sometime. And, aborting
            # would result in a temporary file in the object directory.
            if packer is not None:
                packer.join()

    @staticmethod
    def robust_add_object(git, obj):
        """Robustly add an object to a Git repository.

        There are race conditions between different processes when writing
        objects to a Git repo. The underlying problem is that dulwich is
        obtaining an exclusive lock every time it writes an object file.

        If theory, we should be able to ignore the error and rely on the lock
        owner to finish the write. Unfortunately, we can't just steam ahead
        because as part of writing Tree objects, dulwich verifies that all
        referenced objects in the Tree are present. So, this introduces another
        race condition that must be avoided.

        We work around this ugly mess by attempting writes into the Git repo
        until it works without locking issues. This results in redundant work
        when there is a contention issue, but that's unavoidable.

        There is also a bug in dulwich locking mechanism. Essentially, it
        doesn't do things atomically. It's not only possible for dulwich to
        raise when trying to obtain the exclusive lock on the lock file, but
        it can also fail when attempting to perform a rename as part of
        releasing the lock.

        When we encounter a locking issue, we sleep for a random amount of
        time and then try again. The sleep is here to reduce the possibility
        that the two processes will continuously trigger locking issues. It
        isn't perfect but it does get the job done.
        """
        failed = 0
        while True:
            try:
                git.object_store.add_object(obj)
                return
            except OSError as e:
                # Don't spin forever.
                failed += 1
                if failed >= 10:
                    raise e

                # 17 is for obtaining the exclusive lock. 2 is the bug on
                # releasing it.
                if e.errno in (2, 17):
                    ms = random.randint(100, 1000)
                    time.sleep(ms / 1000.0)
                    continue

                raise e

    @staticmethod
    def _process_periodic_pack(git_path, interval, alive):
        """Background process that performs periodic store packs."""
        git = Repo(git_path)

        next_pack = time.time() + interval

        while alive.value == 1:
            time.sleep(0.25)

            if time.time() < next_pack:
                continue

            try:
                git.object_store.pack_loose_objects()
            except KeyboardInterrupt:
                pass
            except Exception as e:
                import traceback
                traceback.print_exc()
                continue

            next_pack = time.time() + interval

    @staticmethod
    def _process_tree_export(ui_config, hg_path, git_path, existing_objects,
        jobs, results, alive):
        """Background process that performs tree export work."""

        git = Repo(git_path)

        ui = hgui()
        for section, name, value in ui_config:
            ui.setconfig(section, name, value)

        hg = repository(ui, hg_path)
        tracker = TreeTracker(hg, blob_cache=existing_objects)

        pending = []

        while alive.value == 1:
            if not len(pending):
                try:
                    pending.extend(jobs.get(True, 1))
                except Queue.Empty:
                    pass

                if not len(pending):
                    continue

            # Only do one job per loop so we detect !alive quicker.
            node = pending[0]
            ctx = hg.changectx(node)

            for obj, nodeid in tracker.update_changeset(ctx):
                MercurialToGitConverter.robust_add_object(git, obj)

                if nodeid is not None:
                    results.put(('BLOB', (nodeid, obj.id)))

            results.put(('TREE', (node, tracker.root_tree_sha)))

            pending.pop(0)

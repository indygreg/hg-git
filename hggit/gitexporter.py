# This file contains code for converting Mercurial repositories to Git
# repositories. It is written as a generic library, suitable for use in any
# context, including outside of a Mercurial command.

import gc
import logging
import multiprocessing
import Queue
import os
import random
import re
import signal
import stat
import time
import urllib

from itertools import chain
from itertools import repeat

from dulwich.objects import Blob
from dulwich.objects import Commit
from dulwich.objects import Tree
from dulwich.objects import TreeEntry
from dulwich.objects import parse_timezone
from dulwich.pack import apply_delta
from dulwich.repo import Repo

from mercurial.hg import repository
from mercurial.ui import ui as hgui
from mercurial import error as hgerror

# TODO handle encoding issues.

class TreeTracker(object):
    """Tracks incremental changes to Git trees.

    This class essentially models a Git "root" tree (a tree referenced by a
    commit). It also contains data from all sub-trees.

    The magic in this class is incremental change processing. You can feed it
    a changectx and it performs the minimal work necessary to update the tree
    for that changectx.

    This class exists to make Git exporting faster. It allows us to
    incrementally compute Git trees without having to exhaustively iterate
    files in a changeset.

    There are two main factors contributing to the performance wins.

    First, we avoid having to iterate the entire manifest when moving between
    revisions. This avoids having to compute the full manifest, iterating over
    it, and possibly grabbing raw content from Mercurial to compute hashes.

    The second big performance win is from caching Tree objects. Tree
    calculation is not cheap, at least in dulwich. By only constructing Tree
    objects from trees that have actually changed since the last time they were
    retrieved, we net a huge performance win.

    Crude benchmarking reveals that each optimization above results in about a
    4-5x improvement over the inefficient case. Together, they represent a
    16-20x speedup over the unoptimized case.
    """

    def __init__(self, repo):
        """Create a new tree tracker seeded with a specific changectx."""

        self.repo = repo
        self.rev = None
        self.node = None
        self.dirs = None
        self.tree_cache = None
        self.dirty_trees = None

    def update_revision(self, ctx, incremental=True):
        """Update the revision that we track.

        This is how you update the TreeTracker to point to a different commit.
        """
        rev = ctx.rev()
        node = ctx.node()

        if self.rev is None or not incremental:
            self._populate_full(ctx)
            return

        # We attempt to find nodes between the previously tracked revision and
        # the new one. If we find them, we walk that path and update state
        # incrementally. If there is no common path or if the path is long, we
        # just rebuild from scratch.

        # We could probably handle going backwards if we wanted to. For now,
        # we assume we always go forward.
        if rev < self.rev:
            self._populate_full(ctx)
            return

        between = self.repo.changelog.nodesbetween([self.node], [node])[0]

        # The distance is arbitrary.
        if not len(between) or len(between) > 25:
            self._populate_full(ctx)
            return

        # The first node is always the starting point, which we've already
        # processed.
        between.pop(0)

        for node in between:
            ctx2 = self.repo.changectx(node)

            # Merge commits are hard. We should ideally follow their nodes.
            # For now, we just bail and do a full population.
            if len(ctx2.parents()) > 1:
                self._populate_full(ctx)
                return

            self._populate_incremental(ctx2)

        self._finish_populating()

    def trees(self, incremental=True):
        """Obtain all the Git Tree instances we represent.

        This is a generator of 2-tuples of (Tree, path).

        The tuple with path == '' represents the root tree and is what is used
        for the commit object.

        The default behavior is to only retrieve trees that changed since we
        last obtained trees. Note that if you call this multiple times without
        updating the revision, no trees will be returned on subsequent calls.
        """

        trees = {}
        children = {}

        # Empty trees are special.
        if not len(self.dirs):
            yield (Tree(), '')
            return

        for tree_path in sorted(self.dirs.keys(), key=len, reverse=True):
            tree = self.tree_cache.get(tree_path, None)

            if tree is not None:
                if not incremental:
                    yield (tree, tree_path)

                continue

            tree = Tree()
            for entry in self.dirs[tree_path].values():
                tree.add(entry.path, entry.mode, entry.sha)

            for path, tree_id in children.get(tree_path, {}).iteritems():
                tree.add(path, stat.S_IFDIR, tree_id)

            # Empty trees can creep in since we don't traverse fully on
            # deletion. Ignore empty trees.
            if not len(tree):
                continue

            parent = os.path.dirname(tree_path)
            entry = children.get(parent, {})
            entry[os.path.basename(tree_path)] = tree.id
            children[parent] = entry

            yield (tree, tree_path)
            self.tree_cache[tree_path] = tree

    def _populate_full(self, ctx):
        self.dirs = {}
        self.tree_cache = {}
        self.dirty_trees = set()

        for path in ctx.manifest().keys():
            fctx = ctx[path]

            entry = TreeTracker.tree_entry(fctx)

            d = os.path.dirname(path)

            dir_entry = self.dirs.get(d, {})
            dir_entry[entry.path] = entry
            self.dirs[d] = dir_entry

        self.node = ctx.node()
        self.rev = ctx.rev()

        self._finish_populating()

    def _populate_incremental(self, ctx):
        for path in sorted(ctx.files(), key=len):
            d = os.path.dirname(path)
            self.dirty_trees.add(d)

            try:
                fctx = ctx[path]
            # If the file was deleted, remove record of it.
            except hgerror.LookupError:
                dir_entry = self.dirs.get(d, None)

                # Directory didn't exist before. This is weird, but OK.
                if dir_entry is None:
                    continue

                try:
                    del dir_entry[os.path.basename(path)]
                # Directory existed but it didn't have this file. That's
                # kinda weird, but it's possible on merges.
                except KeyError:
                    pass

                self.dirs[d] = dir_entry
                continue

            # It's possible the path used to be a directory. Blindly delete
            # any directories having the same name as this.
            try:
                del self.dirs[path]
            except KeyError:
                pass

            entry = TreeTracker.tree_entry(fctx)

            dir_entry = self.dirs.get(d, {})
            dir_entry[entry.path] = entry
            self.dirs[d] = dir_entry

        self.node = ctx.node()
        self.rev = ctx.rev()

    def _finish_populating(self):
        """Finished populating state.

        This is called whenever the revision of the tree is updated. For
        incremental updates, it should only be called once after the final
        revision has been applied.
        """

        # Look for missing parent directories and populate them.
        for d in self.dirs.keys():
            if d == '':
                continue

            parent = d

            while True:
                parent = os.path.dirname(parent)

                entry = self.dirs.get(parent, None)
                if entry is None:
                    self.dirs[parent] = {}

                if parent == '':
                    break

        # Ensure dirty trees dirty their ancestors.
        for path in [d for d in self.dirty_trees]:
            if path == '':
                continue

            parent = path

            while True:
                parent = os.path.dirname(parent)
                self.dirty_trees.add(parent)

                if parent == '':
                    break

        # Wipe out dirty trees from cache.
        for path in self.dirty_trees:
            try:
                del self.tree_cache[path]
            except KeyError:
                pass

    @staticmethod
    def tree_entry(fctx):
        blob = Blob.from_string(fctx.data())

        flags = fctx.flags()

        if 'l' in flags:
            mode = 0120000
        elif 'x' in flags:
            mode = 0100755
        else:
            mode = 0100644

        return TreeEntry(os.path.basename(fctx.path()), mode, blob.id)


class MercurialToGitConverter(object):
    """Provides functionality for converting Mercurial repos to Git repos.

    """

    RE_GIT_AUTHOR = re.compile('^(.*?) ?\<(.*?)(?:\>(.*))?$')
    RE_GIT_USERNAME_SANITIZE = re.compile('[<>\n]')

    def __init__(self, hg_repo, git_repo, author_map=None, id_map=None):
        """Create a new converter bound to specific repository instances."""

        self.hg = hg_repo
        self.git = git_repo

        self.logger = logging.getLogger(__name__)

        self.author_map = author_map or {}
        self.id_map = id_map or {}

    def export_changesets(self, cb=None, **kwargs):
        """Export Mercurial changesets to Git.

        This takes care of exporting blobs, trees, and commits to Git.

        If you are looking to export a repository to Git, this is one of the
        most important functions as it is what transfers the bulk of the data.
        """

        # We use export_trees() and its background workers to do as much work
        # in parallel as possible. We additionally have a background process
        # churning through commits. The reason we have a background process is
        # that commit processing can be expensive and we don't want to let this
        # block the tree workers from moving as fast as possible.

        job_queue = multiprocessing.Queue()
        result_queue = multiprocessing.Queue()
        active = multiprocessing.Value('i', 1)

        config = list(self.hg.ui.walkconfig())

        worker = multiprocessing.Process(
            target=MercurialToGitConverter._process_commits,
            name='commit-processor',
            args=(config, self.hg.root, self.git.path, self.author_map,
                self.id_map, job_queue, result_queue, active))
        worker.start()

        def process_results():
            results = []
            try:
                while True:
                    results.append(result_queue.get(False))
            except Queue.Empty:
                pass

            for action, data in results:
                if action == 'COMMIT':
                    finished_rev, finished_tree_id, finished_commit_id = data
                    ctx = self.hg.changectx(finished_rev)

                    self.id_map[ctx.hex()] = finished_commit_id

                    if cb:
                        cb(finished_rev, finished_tree_id, finished_commit_id)

                elif action == 'DONE':
                    return True

            return None

        # Pulling items off of result_queue is suboptimally implemented.
        # But, it's not a huge deal: it just delays the firing of the commit
        # callback.

        def on_tree(rev, tree_id):
            job_queue.put(('TREE', (rev, tree_id)))

            process_results()

        try:
            self.export_trees(cb=on_tree, **kwargs)

            job_queue.put(('TERMINATE', None))

            while process_results() is None:
                pass

            active.value = 0
        except:
            active.value = 0
            worker.terminate()
        finally:
            worker.join()

    def export_trees(self, changeids=None, incremental=True, cb=None,
            auto_pack=True, auto_pack_interval=60,
            worker_pool_size=multiprocessing.cpu_count(),
            major_chunk_size=200, reissue_chunk_size=3,
            reissue_pending_threshold=5, reissue_skip_initial=1):
        """Export Git trees from Mercurial changesets.

        This functions takes a set of Mercurial revisions IDs and exports the
        Git trees for them, including the underlying blobs.

        The default behavior is to export trees for every revision ID. To
        limit the set of revisions exported, pass an iterable of the raw 20
        byte revision IDs via the changeids argument.

        The default behavior is to intelligently process exports incrementally.
        This saves us from performing a lot of redundant processing and is much
        faster. It is typically what is wanted. However, if the repository is
        corrupted or missing data, you can perform a non-incremental export to
        hopefully repair it.

        Exporting can be easily parallelized: it's commit processing that needs
        to occur in a certain order. Therefore, this function makes use of
        background processes to perform the exporting work.

        By default, we also fire up a background process that periodically
        packs loose objects in the Git repository. This is extremely useful on
        large repositories, where large amounts of loose objects (tens of
        thousands) can cause things to slow down over time. If you do not want
        auto packing, it can be disabled.

        The logic for distributing work to the worker pool is somewhat
        complicated and worth explaining.

        The underlying tree export mechanism is most efficient when it exports
        neighboring changesets. That is changesets where one is an immediate
        descendent of the other. With this in mind, we distribute changesets to
        workers in chunks. Each chunk is linearly connected (or at least as
        close to linearly connected as we have available). This allows each
        chunk to be executed as efficiently as possible.

        A problem with a naive implementation of this chunking is that some
        chunks finish before others, sometimes significantly sooner. The
        outstanding chunks could delay downstream systems that depend on them.
        So, instead of blazing forward on a completely new chunk, we have a
        mechanism where we feed in outstanding chunks to idle workers who have
        already completed their work.

        As things are implemented, we start by splitting the changesets into
        large blocks of size major_chunk_size * worker_pool_size. Each large
        block is split into an equal size chunk of size major_chunk_size and
        passed to a worker.

        If a worker finishes its work, it announces that it is idle. If we have
        a significant amount of outstanding work, we reissue a small set of
        this work to the idle worker. This does result in some redundant work
        being performed. But, in cases where a particular worker is taking much
        longer than expected to do work, it saves time because other workers
        chip in.

        While exporting in the worker pool may occur in any order, results are
        emitted in the order they occur in changeids. This doesn't change the
        overall execution time of this function but it may delay certain
        results.
        """
        if changeids is None:
            changeids = [self.hg.lookup(n) for n in self.hg]

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
        announce_queues = []
        for i in range(worker_pool_size):
            announce = multiprocessing.Queue()

            worker = multiprocessing.Process(
                target=MercurialToGitConverter._process_tree_export,
                args=(config, self.hg.root, self.git.path, incremental,
                    job_queue, result_queue, announce, alive))
            worker.start()

            workers.append(worker)
            announce_queues.append(announce)

        batch_size = major_chunk_size * worker_pool_size

        batches = [changeids[i:i+batch_size] for i in range(0, len(changeids),
            batch_size)]

        def send_announcement(name, data):
            for announce in announce_queues:
                announce.put((name, data))

        try:
            for batch in batches:
                chunk_chain = chain(batch, repeat(None, major_chunk_size - 1))
                chunks = zip(*[chunk_chain] * major_chunk_size)

                for chunk in chunks:
                    job_queue.put([rev for rev in chunk if rev is not None])

                pending = [rev for rev in batch]
                finished = {}
                reissued = set()
                starved_count = 0

                while len(pending):
                    # If the first outstanding revision is available, process
                    # it immediately. We do this until we exhaust the
                    # immediately available set because we don't want to delay
                    # downstream consumers.
                    if pending[0] in finished:
                        self.logger.info('Finished tree for %s' % pending[0])
                        if cb:
                            cb(pending[0], finished[pending[0]])

                        pending.pop(0)
                        continue

                    # Gather all available results and decide what to do.
                    results = []
                    wait = 0.25
                    try:
                        while True:
                            # Only wait the first time around. This prevents
                            # a busy loop and avoids excess waiting.
                            results.append(result_queue.get(wait != 0, wait))
                            wait = 0
                    except Queue.Empty:
                        pass

                    have_tree = False
                    for result_type, data in results:
                        if result_type == 'STARVED':
                            starved_count += 1
                            self.logger.debug('Starved worker encountered.')
                        elif result_type == 'TREE':
                            self.logger.debug('Received tree for %s' % data[0])
                            finished[data[0]] = data[1]
                            have_tree = True

                            send_announcement('TREE_COMPLETE', data[0])
                        else:
                            raise Exception('Unknown type: %s' % result_type)

                    # A new tree may have unblocked the immediately pending
                    # item. This forces us to try processing that immediately.
                    # It also has the side-effect that we'll wait for items on
                    # the result queue again. This is acceptable.
                    if have_tree:
                        continue

                    # No starved workers, so there's nothing for us to do
                    # besides wait again.
                    if not starved_count:
                        continue

                    # If we're close to the end, don't bother reissuing.
                    if len(pending) < reissue_pending_threshold:
                        continue

                    # We have a starved worker. Let's try to get some work to
                    # it.
                    reissue_work = []
                    for i, rev in enumerate(pending):
                        # Ignore the first N items from pending.
                        if i < reissue_skip_initial:
                            continue

                        # If we have data already or have already reissued,
                        # don't reissue again.
                        if rev in finished or rev in reissued:
                            continue

                        reissue_work.append(rev)

                        if len(reissue_work) == reissue_chunk_size:
                            break

                    # If we couldn't find enough work to satisfy a reissue
                    # chunk, don't bother.
                    if len(reissue_work) < reissue_chunk_size:
                        continue

                    for rev in reissue_work:
                        reissued.add(rev)

                    self.logger.debug('Reissuing work')
                    job_queue.put(reissue_work)
                    starved_count -= 1

                # Finished this batch.

            # Done with all batches.
            alive.value = 0

        except Exception as e:
            alive.value = 0

            for worker in workers:
                worker.terminate()

            packer.terminate()

            raise e

        finally:
            alive.value = 0

            for worker in workers:
                worker.join()

            if packer is not None:
                packer.join()

    @staticmethod
    def get_git_author(ctx, author_map):
        """Obtain the Git author string for a changeset."""
        hg_author = ctx.user()

        author = author_map.get(hg_author, hg_author)

        # Check for git author pattern compliance.
        a = MercurialToGitConverter.RE_GIT_AUTHOR.match(author)

        get_valid = MercurialToGitConverter.get_valid_git_username_email

        if a:
            name = get_valid(a.group(1))
            email = get_valid(a.group(2))
            if a.group(3) != None and len(a.group(3)) != 0:
                name += ' ext:(' + urllib.quote(a.group(3)) + ')'
            author = get_valid(name) + ' <' + get_valid(email) + '>'
        elif '@' in author:
            author = get_valid(author) + ' <' + get_valid(author) + '>'
        else:
            author = get_valid(author) + ' <none@none>'

        if 'author' in ctx.extra():
            author = ''.join(apply_delta(author, ctx.extra()['author']))

        return author

    @staticmethod
    def get_valid_git_username_email(name):
        """Sanitize usernames and emails to fit git's restrictions.

        The following is taken from the man page of git's fast-import
        command:

            [...] Likewise LF means one (and only one) linefeed [...]

            committer
                The committer command indicates who made this commit,
                and when they made it.

                Here <name> is the person's display name (for example
                "Com M Itter") and <email> is the person's email address
                ("cm@example.com[1]"). LT and GT are the literal
                less-than (\x3c) and greater-than (\x3e) symbols. These
                are required to delimit the email address from the other
                fields in the line. Note that <name> and <email> are
                free-form and may contain any sequence of bytes, except
                LT, GT and LF. <name> is typically UTF-8 encoded.

        Accordingly, this function makes sure that there are none of the
        characters <, >, or \n in any string which will be used for
        a git username or email. Before this, it first removes left
        angle brackets and spaces from the beginning, and right angle
        brackets and spaces from the end, of this string, to convert
        such things as " <john@doe.com> " to "john@doe.com" for
        convenience.

        TESTS:

        >>> from gitexporter import MercurialToGitConverter as converter
        >>> g = converter.get_valid_git_username_email
        >>> g('John Doe')
        'John Doe'
        >>> g('john@doe.com')
        'john@doe.com'
        >>> g(' <john@doe.com> ')
        'john@doe.com'
        >>> g('    <random<\n<garbage\n>  > > ')
        'random???garbage?'
        >>> g('Typo in hgrc >but.hg-git@handles.it.gracefully>')
        'Typo in hgrc ?but.hg-git@handles.it.gracefully'
        """
        return MercurialToGitConverter.RE_GIT_USERNAME_SANITIZE.sub('?',
            name.lstrip('< ').rstrip('> '))

    @staticmethod
    def get_git_parents(ctx):
        def is_octopus_part(ctx):
            extra = ctx.extra().get('hg-git', None)
            return extra in ('octopus', 'octopus-done')

        parents = []
        if ctx.extra().get('hg-git', None) == 'octopus-done':
            # Implode octopus parents.
            part = ctx
            while is_octopus_part(part):
                p1, p2 = part.parents()
                assert not is_octopus_part(p1)
                parents.append(p1)
                part = p2
            parents.append(p2)
        else:
            parents = ctx.parents()

        return parents

    @staticmethod
    def get_git_message(ctx):
        """Converts the message from a changectx into a Git commit message."""
        extra = ctx.extra()

        message = ctx.description() + "\n"
        if 'message' in extra:
            message = ''.join(apply_delta(message, extra['message']))

        # HG EXTRA INFORMATION
        add_extras = False
        extra_message = ''
        if ctx.branch() != 'default':
            add_extras = True
            extra_message += 'branch : ' + ctx.branch() + '\n'

        renames = []
        for f in ctx.files():
            if f not in ctx.manifest():
                continue

            rename = ctx.filectx(f).renamed()
            if rename:
                renames.append((rename[0], f))

        if renames:
            add_extras = True
            for oldfile, newfile in renames:
                extra_message += "rename : " + oldfile + " => " + newfile + "\n"

        for key, value in extra.iteritems():
            if key in ('author', 'committer', 'encoding', 'message', 'branch', 'hg-git'):
                continue
            else:
                add_extras = True
                extra_message += 'extra : ' + key + ' : ' + urllib.quote(value) + '\n'

        if add_extras:
            message += '\n--HG--\n' + extra_message

        return message

    @staticmethod
    def export_commit_object(ctx, git, tree_sha, author_map, id_map):
        """Export a commit object for a specific changeset.

        This takes a changectx and a tree hash and writes out the Git commit
        object.

        The SHA-1 of the resulting commit object is returned.
        """
        extra = ctx.extra()

        commit = Commit()

        (time, timezone) = ctx.date()
        commit.author = MercurialToGitConverter.get_git_author(ctx, author_map)
        commit.author_time = int(time)
        commit.author_timezone = -timezone

        if 'committer' in extra:
            # Adjust timezone.
            name, timestamp, timezone = extra['committer'].rsplit(' ', 2)
            commit.committer = name
            commit.commit_time = timestamp

            # Work around a timezone format change.
            if int(timezone) % 60 != 0: #pragma: no cover
                timezone = parse_timezone(timezone)

                # Newer versions of Dulwich return a tuple here.
                if isinstance(timezone, tuple):
                    timezone, neg_utc = timezone
                    commit._commit_timezone_neg_utc = neg_utc

            else:
                timezone = -int(timezone)

            commit.commit_timezone = timezone
        else:
            commit.committer = commit.author
            commit.commit_time = commit.author_time
            commit.commit_timezone = commit.author_timezone

        commit.parents = []
        for parent in MercurialToGitConverter.get_git_parents(ctx):
            hg_sha = parent.hex()
            git_sha = id_map.get(hg_sha, None)

            if git_sha is not None:
                commit.parents.append(git_sha)

        commit.message = MercurialToGitConverter.get_git_message(ctx)

        if 'encoding' in extra:
            commit.encoding = extra['encoding']

        commit.tree = tree_sha
        MercurialToGitConverter.robust_add_object(git, commit)

        return commit.id

    @staticmethod
    def export_tree(ctx, git, tracker, incremental=True):
        """Export Git objects for a specific HG changeset.

        This takes an HG changecontext, a Git repo, a TreeTracker, a changeset
        revision ID (the raw value) and exports Git blobs and tree objects for
        that changeset.

        The incremental flag controls incremental exporting. If True (the
        default), this will only export blobs changed in this changeset and
        trees that have been changed since the last time the TreeTracker was
        updated.
        """
        blobs = MercurialToGitConverter.export_blobs_for_changeset(
            ctx, git, incremental)

        tracker.update_revision(ctx, incremental)

        root_id = None

        for tree, path in tracker.trees():
            MercurialToGitConverter.robust_add_object(git, tree)
            if path == '':
                root_id = tree.id

        return (root_id, blobs)

    @staticmethod
    def export_blobs_for_changeset(ctx, git, incremental=True):
        """Export Git blobs for a specific HG changeset.

        This takes an HG changeset context, a Git repo, a revision ID, and a
        flag saying whether to perform incremental export. If incremental is
        True (the default), only changed files will be exported.

        The return value is a mapping of filenames to the hex representation of
        the blob's SHA-1. If operating in incremental mode, only the changed
        filenames will be present in the mapping. If the file was deleted, it's
        SHA-1 will be None.
        """
        files = ctx.files() if incremental else ctx.manifest.keys()

        result = {}

        for filename in files:
            try:
                fctx = ctx[filename]

            # This happens if in incremental mode and the change was a
            # deletion. Obviously this means there is nothing to export.
            except hgerror.LookupError:
                assert incremental
                result[filename] = None
                continue

            blob = Blob.from_string(fctx.data())

            MercurialToGitConverter.robust_add_object(git, blob)
            result[filename] = blob.id

        return result

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
        while True:
            try:
                git.object_store.add_object(obj)
                return
            except OSError as e:
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

            git.object_store.pack_loose_objects()
            next_pack = time.time() + interval

    @staticmethod
    def _process_tree_export(ui_config, hg_path, git_path, incremental,
        jobs, results, announcements, alive):
        """Background process that performs tree exports."""
        git = Repo(git_path)

        ui = hgui()
        for section, name, value in ui_config:
            ui.setconfig(section, name, value)

        hg = repository(ui, hg_path)
        tracker = TreeTracker(hg)

        outstanding = []
        complained_starving = False
        finished = set()
        processed_count = 0

        while alive.value == 1:
            try:
                name, data = announcements.get(False)

                # If another worker finished a tree were have yet to compute
                # we no longer need to compute that tree, obviously.
                if name == 'TREE_COMPLETE':
                    finished.add(data)

                continue

            except Queue.Empty:
                pass

            if len(outstanding):
                node = outstanding[0]

                if node in finished:
                    outstanding.pop(0)
                    continue

                ctx = hg.changectx(node)

                root_id, blobs = MercurialToGitConverter.export_tree(ctx,
                    git, tracker, incremental)

                results.put(('TREE', (node, root_id)))
                outstanding.pop(0)

                processed_count += 1
                if processed_count % 500 == 0:
                    tracker = TreeTracker(hg)
                    gc.collect()

                continue

            try:
                outstanding.extend(jobs.get(True, 1))
                complained_starving = False
                continue
            except Queue.Empty:
                pass

            # We don't have any work. signal we are starved.
            if not complained_starving:
                results.put(('STARVED', None))
                complained_starving = True

    @staticmethod
    def _process_commits(ui_config, hg_path, git_path, author_map, id_map,
        jobs, results, active):

        git = Repo(git_path)

        ui = hgui()
        for section, name, value in ui_config:
            ui.setconfig(section, name, value)

        hg = repository(ui, hg_path)

        while active.value:
            action, data = jobs.get()

            if action == 'TERMINATE':
                results.put(('DONE', None))
                return

            if action != 'TREE':
                raise AssertionError('Unknown action: %s' % action)

            rev, tree_id = data
            ctx = hg.changectx(rev)

            state = ctx.extra().get('hg-git', None)
            if state == 'octopus':
                continue

            commit_id = MercurialToGitConverter.export_commit_object(ctx, git,
                tree_id, author_map, id_map)

            id_map[ctx.hex()] = commit_id

            results.put(('COMMIT', (rev, tree_id, commit_id)))

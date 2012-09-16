import os, math, multiprocessing, random, urllib, re, stat, time

from dulwich.errors import HangupException, GitProtocolError
from dulwich.index import commit_tree
from dulwich.objects import Blob, Commit, Tag, Tree, TreeEntry, parse_timezone
from dulwich.pack import create_delta, apply_delta
from dulwich.repo import Repo
from dulwich import client

try:
    from mercurial import bookmarks
    bookmarks.update
    from mercurial import commands
except ImportError:
    from hgext import bookmarks
try:
    from mercurial.error import RepoError
except ImportError:
    from mercurial.repo import RepoError

from mercurial.i18n import _
from mercurial.node import hex, bin, nullid
from mercurial import context, util as hgutil
from mercurial import error
from mercurial.hg import repository as hgrepository
from mercurial.ui import ui as hgui

import _ssh
import util
from overlay import overlayrepo

tree_tracker = None

def robust_add_object(git, obj):
    """Robustly add an object to a Git repository.

     There are race conditions between different processes when writing objects
     to a Git repo. The underlying problem is that dulwich is obtaining an
     exclusive lock every time it writes an object file.

     If theory, we should be able to ignore the error and rely on the lock
     owner to finish the write. Unfortunately, we can't just steam ahead
     because as part of writing Tree objects, dulwich verifies that all
     referenced objects in the Tree are present. So, this introduces another
     race condition that must be avoided.

     We work around this ugly mess by attempting writes into the Git repo until
     it works without locking issues. This results in redundant work when there
     is a contention issue, but that's unavoidable.

     There is also a bug in dulwich locking mechanism. Essentially, it doesn't
     do things atomically. It's not only possible for dulwich to raise when
     trying to obtain the exclusive lock on the lock file, but it can also fail
     when attempting to perform a rename as part of releasing the lock.

     When we encounter a locking issue, we sleep for a random amount of time
     and then try again. The sleep is here to reduce the possibility that the
     two processes will continuously trigger locking issues. It isn't perfect
     but it does get the job done.

     We could possibly work around this bug
    """
    while True:
        try:
            git.object_store.add_object(obj)
            return
        except OSError as e:
            # 17 is for obtaining the exclusive lock. 2 is the bug on releasing
            # it.
            if e.errno in (2, 17):
                ms = random.randint(100, 1000)
                time.sleep(ms / 1000.0)
                continue

            raise e

def process_git_export(config, hgpath, rev, gitdir, incremental=True):
    global tree_tracker

    git = Repo(gitdir)
    ui = hgui()

    for section, name, value in config:
        ui.setconfig(section, name, value)

    hg = hgrepository(ui, hgpath)

    if tree_tracker is None:
        tree_tracker = TreeTracker(hg)

    blobs = GitHandler.export_git_blobs_for_revision(hg, git, rev,
        incremental)
    tree_tracker.update_revision(rev, incremental)

    root_id = None

    for tree, tree_path in tree_tracker.trees():
        robust_add_object(git, tree)
        if tree_path == '':
            root_id = tree.id

    return (rev, root_id)

class GitProgress(object):
    """convert git server progress strings into mercurial progress"""
    def __init__(self, ui):
        self.ui = ui

        self.lasttopic = None
        self.msgbuf = ''

    def progress(self, msg):
        # 'Counting objects: 33640, done.\n'
        # 'Compressing objects:   0% (1/9955)   \r
        msgs = re.split('[\r\n]', self.msgbuf + msg)
        self.msgbuf = msgs.pop()

        for msg in msgs:
            td = msg.split(':', 1)
            data = td.pop()
            if not td:
                self.flush(data)
                continue
            topic = td[0]

            m = re.search('\((\d+)/(\d+)\)', data)
            if m:
                if self.lasttopic and self.lasttopic != topic:
                    self.flush()
                self.lasttopic = topic

                pos, total = map(int, m.group(1, 2))
                util.progress(self.ui, topic, pos, total=total)
            else:
                self.flush(msg)

    def flush(self, msg=None):
        if self.lasttopic:
            util.progress(self.ui, self.lasttopic, None)
        self.lasttopic = None
        if msg:
            self.ui.note(msg + '\n')


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

    def update_revision(self, rev, incremental=True):
        """Update the revision that we track.

        This is how you update the TreeTracker to point to a different commit.
        """
        ctx = self.repo.changectx(rev)

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

        # 100 is arbitrary.
        if not len(between) or len(between) > 100:
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
            except error.LookupError:
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


class GitHandler(object):
    mapfile = 'git-mapfile'
    tagsfile = 'git-tags'
    versionfile = 'git-state-version'

    def __init__(self, dest_repo, ui):
        self.repo = dest_repo
        self.ui = ui

        if ui.configbool('git', 'intree'):
            self.gitdir = self.repo.wjoin('.git')
        else:
            self.gitdir = self.repo.join('git')

        self.init_author_file()

        self.paths = ui.configitems('paths')

        self.branch_bookmark_suffix = ui.config('git', 'branch_bookmark_suffix')

        self.load_state()

    # make the git data directory
    def init_if_missing(self):
        if os.path.exists(self.gitdir):
            self.git = Repo(self.gitdir)
        else:
            os.mkdir(self.gitdir)
            self.git = Repo.init_bare(self.gitdir)

    def init_author_file(self):
        self.author_map = {}
        if self.ui.config('git', 'authors'):
            with open(self.repo.wjoin(
                self.ui.config('git', 'authors')
            )) as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue
                    from_, to = re.split(r'\s*=\s*', line, 2)
                    self.author_map[from_] = to

    ## FILE LOAD AND SAVE METHODS

    def map_set(self, gitsha, hgsha):
        self._map_git[gitsha] = hgsha
        self._map_hg[hgsha] = gitsha

    def map_hg_get(self, gitsha):
        return self._map_git.get(gitsha)

    def map_git_get(self, hgsha):
        return self._map_hg.get(hgsha)

    def load_state(self):
        """Load cached state from a previous run into the instance."""

        self._map_git = {}
        self._map_hg = {}
        self.tags = {}

        # If there is no Git repo, this invalidates assertions about what's
        # already stored in the repo. So, don't load any saved state.
        # Essentially, this clears all stored state.
        if not os.path.exists(self.gitdir):
            return

        # We didn't always have a version file. If it isn't present, we
        # assume version 1.
        version = None
        if os.path.exists(self.repo.join(self.versionfile)):
            version = self.repo.opener.read(self.versionfile)

            try:
                version = int(version)
            except ValueError:
                self.ui.status(_("version file corrupted: not an int\n"))
                version = 1
        else:
            version = 1

        # Load the map file.
        if os.path.exists(self.repo.join(self.mapfile)):
            for line in self.repo.opener(self.mapfile):
                gitsha, hgsha = line.strip().split(' ', 1)
                self._map_git[gitsha] = hgsha
                self._map_hg[hgsha] = gitsha

        # Load the tags file.
        if os.path.exists(self.repo.join(self.tagsfile)):
            for line in self.repo.opener(self.tagsfile):
                sha, name = line.strip().split(' ', 1)
                self.tags[name] = sha

        self._migrate_state(version)

    def save_state(self):
        map_file = self.repo.opener(self.mapfile, 'w', atomictemp=True)
        for hgsha, gitsha in sorted(self._map_hg.iteritems()):
            map_file.write("%s %s\n" % (gitsha, hgsha))
        # If this complains that NoneType is not callable, then
        # atomictempfile no longer has either of rename (pre-1.9) or
        # close (post-1.9)
        getattr(map_file, 'rename', getattr(map_file, 'close', None))()

        tags_file = self.repo.opener(self.tagsfile, 'w', atomictemp=True)
        for name, sha in sorted(self.tags.iteritems()):
            if not self.repo.tagtype(name) == 'global':
                tags_file.write("%s %s\n" % (sha, name))
        # If this complains that NoneType is not callable, then
        # atomictempfile no longer has either of rename (pre-1.9) or
        # close (post-1.9)
        getattr(tags_file, 'rename', getattr(tags_file, 'close', None))()

        version_file = self.repo.opener(self.versionfile, 'w', atomictemp=True)
        version_file.write('2')
        getattr(version_file, 'rename', getattr(version_file, 'close', None))()

    def _migrate_state(self, version):
        if version == 2:
            return

        assert version == 1

        self.init_if_missing()

        pruned_map = {}

        # In version 2, we stopped recording the mapping from HG file revision
        # nodes to Git blob SHAs because they aren't useful. The migration
        # involves pruning the old entries from the mapping.
        for blob_id, node in self._map_git.iteritems():
            try:
                blob = self.git.object_store[blob_id]

                if isinstance(blob, Blob):
                    continue

                pruned_map[blob_id] = node

            # We must have failed getting the object from the store. We
            # definitely don't want it to exist in the mapping if it isn't
            # available.
            except Exception:
                pass

        self._map_git = {}
        self._map_hg = {}
        for k, v in pruned_map.iteritems():
            self.map_set(k, v)

    ## END FILE LOAD AND SAVE METHODS

    ## COMMANDS METHODS

    def import_commits(self, remote_name):
        self.import_git_objects(remote_name)
        self.update_hg_bookmarks(self.git.get_refs())
        self.save_state()

    def fetch(self, remote, heads):
        self.export_commits()
        refs = self.fetch_pack(remote, heads)
        remote_name = self.remote_name(remote)

        oldrefs = self.git.get_refs()
        if refs:
            self.import_git_objects(remote_name, refs)
            self.import_tags(refs)
            self.update_hg_bookmarks(refs)
            if remote_name:
                self.update_remote_branches(remote_name, refs)
            elif not self.paths:
                # intial cloning
                self.update_remote_branches('default', refs)

                # "Activate" a tipmost bookmark.
                bms = getattr(self.repo['tip'], 'bookmarks',
                              lambda : None)()
                if bms:
                    bookmarks.setcurrent(self.repo, bms[0])

        def remoteref(ref):
            rn = remote_name or 'default'
            return 'refs/remotes/' + rn + ref[10:]

        modheads = [refs[k] for k in refs if k.startswith('refs/heads/')
                    and not k.endswith('^{}')
                    and refs[k] != oldrefs.get(remoteref(k))]

        if not modheads:
            self.ui.status(_("no changes found\n"))

        self.save_state()

        return len(modheads)

    def export_commits(self):
        try:
            self.export_git_objects()
            self.export_hg_tags()
            self.update_references()
        finally:
            self.save_state()

    def get_refs(self, remote):
        self.export_commits()
        client, path = self.get_transport_and_path(remote)
        old_refs = {}
        new_refs = {}
        def changed(refs):
            old_refs.update(refs)
            to_push = set(self.local_heads().values() + self.tags.values())
            new_refs.update(self.get_changed_refs(refs, to_push, True))
            # don't push anything
            return {}

        try:
            client.send_pack(path, changed, lambda have, want: [])

            changed_refs = [ref for ref, sha in new_refs.iteritems()
                            if sha != old_refs.get(ref)]
            new = [bin(self.map_hg_get(new_refs[ref])) for ref in changed_refs]
            old = {}
            for r in old_refs:
                old_ref = self.map_hg_get(old_refs[r])
                if old_ref:
                    old[bin(old_ref)] = 1

            return old, new
        except (HangupException, GitProtocolError), e:
            raise hgutil.Abort(_("git remote error: ") + str(e))

    def push(self, remote, revs, force):
        self.export_commits()
        old_refs, new_refs = self.upload_pack(remote, revs, force)
        remote_name = self.remote_name(remote)

        if remote_name and new_refs:
            for ref, new_sha in new_refs.iteritems():
                if new_sha != old_refs.get(ref):
                    self.ui.status("    %s::%s => GIT:%s\n" %
                                   (remote_name, ref, new_sha[0:8]))

            self.update_remote_branches(remote_name, new_refs)
        if old_refs == new_refs:
            self.ui.status(_("no changes found\n"))
            ret = None
        elif len(new_refs) > len(old_refs):
            ret = 1 + (len(new_refs) - len(old_refs))
        elif len(old_refs) > len(new_refs):
            ret = -1 - (len(new_refs) - len(old_refs))
        else:
            ret = 1
        return ret

    def clear(self):
        mapfile = self.repo.join(self.mapfile)
        if os.path.exists(self.gitdir):
            for root, dirs, files in os.walk(self.gitdir, topdown=False):
                for name in files:
                    os.remove(os.path.join(root, name))
                for name in dirs:
                    os.rmdir(os.path.join(root, name))
            os.rmdir(self.gitdir)
        if os.path.exists(mapfile):
            os.remove(mapfile)

    # incoming support
    def getremotechanges(self, remote, revs):
        self.export_commits()
        refs = self.fetch_pack(remote.path, revs)

        # refs contains all remote refs. Prune to only those requested.
        if revs:
            reqrefs = {}
            for rev in revs:
                for n in ('refs/heads/' + rev, 'refs/tags/' + rev):
                    if n in refs:
                        reqrefs[n] = refs[n]
        else:
            reqrefs = refs

        commits = [bin(c) for c in self.getnewgitcommits(reqrefs)[1]]

        b = overlayrepo(self, commits, refs)

        return (b, commits, lambda: None)

    ## CHANGESET CONVERSION METHODS

    def export_git_objects(self):
        self.init_if_missing()

        nodes = [self.repo.lookup(n) for n in self.repo]
        export = [node for node in nodes if hex(node) not in self._map_hg]
        total = len(export)
        if total:
            self.ui.status(_("exporting hg objects to git\n"))

        tracker = None

        i = 0
        for rev, tree_id in self.export_git_trees(export):
            i += 1
            ctx = self.repo.changectx(rev)
            state = ctx.extra().get('hg-git', None)
            if state == 'octopus':
                self.ui.debug("revision %d is a part of octopus"
                              "explosion\n" % ctx.rev())
                continue

            self.export_hg_commit(rev, tree_id)
            util.progress(self.ui, 'exporting', i, total=total)

        util.progress(self.ui, 'importing', None, total=total)

    def export_git_trees(self, changeids=None, incremental=True):
        """Export git trees for Mercurial nodes.

        This functions takes a set of Mercurial revisions IDs and exports the
        Git trees for them, including the underlying blobs.

        The default behavior is to export trees for every revision ID. To
        limit the set of revisions exported, pass an interable of the raw 20
        byte revision IDs via the changeids argument.

        The default behavior is to intelligently process exports incrementally.
        This saves us from performing a lot of redundant processing and is much
        faster. It is typically what is wanted. However, if the repository is
        corrupted or missing data, you can perform a full export to hopefully
        repair it.
        """
        changeids = changeids or [self.repo.lookup(n) for n in self.repo]

        oldenc = self.swap_out_encoding()

        config = list(self.ui.walkconfig())
        pool = multiprocessing.Pool()

        results = [pool.apply_async(process_git_export,
            [config, self.repo.root, rev, self.git.path, incremental])
            for rev in changeids]

        for result in results:
            rev, root_id = result.get()

            yield (rev, root_id)

        pool.close()
        pool.join()

    def export_git_blobs(self, changeids=None, incremental=True):
        """Export git blobs for Mercurial nodes.

        This function takes a set of Mercurial revision IDs and exports the
        Git blobs for them.

        The default behavior is to export blobs for every revision ID. To
        limit the set of revisions exported, pass an iterable of the raw 20
        byte revision IDs via the changeids argument.

        The default behavior is also to intelligently export only the
        changed files. The function assumes that if a file did not change
        then the blob has already been exported or will be exported via
        another revision. This is typically fine and it prevents us from
        doing redundant work.

        There is no harm to redundantly exporting git blobs aside from
        performance losses.
        """
        changeids = changeids or [self.repo.lookup(n) for n in self.repo]

        oldenc = self.swap_out_encoding()

        for rev in changeids:
            data = GitHandler.export_git_blobs_for_revision(self.repo,
                self.git, rev, incremental)

            yield (rev, data)

        self.swap_out_encoding(oldenc)

    @staticmethod
    def export_git_blobs_for_revision(hgrepo, gitrepo, rev, incremental=True):
        """Export Git blobs for a specific HG revision ID.

        This takes an HG repo, a Git repo, a revision ID, and a flag saying
        whether to perform incremental export. If incremental is True (the
        default), only changed files will be exported.

        The return value is a mapping of filenames to the hex representation
        of the blob's SHA-1. If operating in incremental mode, only the changed
        filenames will be present in the mapping. If the file was deleted, its
        SHA-1 will be None.
        """
        ctx = hgrepo.changectx(rev)

        files = ctx.files() if incremental else ctx.manifest.keys()

        result = {}

        for filename in files:
            try:
                fctx = ctx[filename]

            # This happens if in incremental mode and the change was a
            # deletion. Obviously this means there is nothing to export.
            except error.LookupError:
                assert incremental
                result[filename] = None
                continue

            blob = Blob.from_string(fctx.data())
            robust_add_object(gitrepo, blob)
            result[filename] = blob.id

        return result

    # convert this commit into git objects
    # go through the manifest, convert all blobs/trees we don't have
    # write the commit object (with metadata info)
    def export_hg_commit(self, rev, tree_sha):
        self.ui.note(_("converting revision %s\n") % hex(rev))

        oldenc = self.swap_out_encoding()

        ctx = self.repo.changectx(rev)
        extra = ctx.extra()

        commit = Commit()

        (time, timezone) = ctx.date()
        commit.author = self.get_git_author(ctx)
        commit.author_time = int(time)
        commit.author_timezone = -timezone

        if 'committer' in extra:
            # fixup timezone
            (name, timestamp, timezone) = extra['committer'].rsplit(' ', 2)
            commit.committer = name
            commit.commit_time = timestamp

            # work around a timezone format change
            if int(timezone) % 60 != 0: #pragma: no cover
                timezone = parse_timezone(timezone)
                # Newer versions of Dulwich return a tuple here
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
        for parent in self.get_git_parents(ctx):
            hgsha = hex(parent.node())
            git_sha = self.map_git_get(hgsha)
            if git_sha:
                commit.parents.append(git_sha)

        commit.message = self.get_git_message(ctx)

        if 'encoding' in extra:
            commit.encoding = extra['encoding']

        commit.tree = tree_sha

        self.git.object_store.add_object(commit)
        self.map_set(commit.id, ctx.hex())

        self.swap_out_encoding(oldenc)
        return commit.id

    def get_valid_git_username_email(self, name):
        r"""Sanitize usernames and emails to fit git's restrictions.

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

        >>> from mercurial.ui import ui
        >>> g = GitHandler('', ui()).get_valid_git_username_email
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
        return re.sub('[<>\n]', '?', name.lstrip('< ').rstrip('> '))

    def get_git_author(self, ctx):
        # hg authors might not have emails
        author = ctx.user()

        # see if a translation exists
        if author in self.author_map:
            author = self.author_map[author]

        # check for git author pattern compliance
        regex = re.compile('^(.*?) ?\<(.*?)(?:\>(.*))?$')
        a = regex.match(author)

        if a:
            name = self.get_valid_git_username_email(a.group(1))
            email = self.get_valid_git_username_email(a.group(2))
            if a.group(3) != None and len(a.group(3)) != 0:
                name += ' ext:(' + urllib.quote(a.group(3)) + ')'
            author = self.get_valid_git_username_email(name) + ' <' + self.get_valid_git_username_email(email) + '>'
        elif '@' in author:
            author = self.get_valid_git_username_email(author) + ' <' + self.get_valid_git_username_email(author) + '>'
        else:
            author = self.get_valid_git_username_email(author) + ' <none@none>'

        if 'author' in ctx.extra():
            author = "".join(apply_delta(author, ctx.extra()['author']))

        return author

    def get_git_parents(self, ctx):
        def is_octopus_part(ctx):
            return ctx.extra().get('hg-git', None) in ('octopus', 'octopus-done')

        parents = []
        if ctx.extra().get('hg-git', None) == 'octopus-done':
            # implode octopus parents
            part = ctx
            while is_octopus_part(part):
                (p1, p2) = part.parents()
                assert not is_octopus_part(p1)
                parents.append(p1)
                part = p2
            parents.append(p2)
        else:
            parents = ctx.parents()

        return parents

    def get_git_message(self, ctx):
        extra = ctx.extra()

        message = ctx.description() + "\n"
        if 'message' in extra:
            message = "".join(apply_delta(message, extra['message']))

        # HG EXTRA INFORMATION
        add_extras = False
        extra_message = ''
        if not ctx.branch() == 'default':
            add_extras = True
            extra_message += "branch : " + ctx.branch() + "\n"

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
                extra_message += "extra : " + key + " : " +  urllib.quote(value) + "\n"

        if add_extras:
            message += "\n--HG--\n" + extra_message

        return message

    def getnewgitcommits(self, refs=None):
        self.init_if_missing()

        # import heads and fetched tags as remote references
        todo = []
        done = set()
        convert_list = {}

        # get a list of all the head shas
        seenheads = set()
        if refs is None:
            refs = self.git.refs.as_dict()
        if refs:
            for sha in refs.itervalues():
                # refs contains all the refs in the server, not just the ones
                # we are pulling
                if sha in self.git.object_store:
                    obj = self.git.get_object(sha)
                    while isinstance(obj, Tag):
                        obj_type, sha = obj.object
                        obj = self.git.get_object(sha)
                    if isinstance (obj, Commit) and sha not in seenheads:
                        seenheads.add(sha)
                        todo.append(sha)

        # sort by commit date
        def commitdate(sha):
            obj = self.git.get_object(sha)
            return obj.commit_time-obj.commit_timezone

        todo.sort(key=commitdate, reverse=True)

        # traverse the heads getting a list of all the unique commits
        commits = []
        seen = set(todo)
        while todo:
            sha = todo[-1]
            if sha in done:
                todo.pop()
                continue
            assert isinstance(sha, str)
            obj = self.git.get_object(sha)
            assert isinstance(obj, Commit)
            for p in obj.parents:
                if p not in done:
                    todo.append(p)
                    break
            else:
                commits.append(sha)
                convert_list[sha] = obj
                done.add(sha)
                todo.pop()

        return convert_list, [commit for commit in commits if not commit in self._map_git]

    def import_git_objects(self, remote_name=None, refs=None):
        convert_list, commits = self.getnewgitcommits(refs)
        # import each of the commits, oldest first
        total = len(commits)
        if total:
            self.ui.status(_("importing git objects into hg\n"))

        for i, csha in enumerate(commits):
            util.progress(self.ui, 'importing', i, total=total, unit='commits')
            commit = convert_list[csha]
            self.import_git_commit(commit)
        util.progress(self.ui, 'importing', None, total=total, unit='commits')

        # Remove any dangling tag references.
        for name, rev in self.repo.tags().items():
            if not rev in self.repo:
                if hasattr(self, 'tagscache') and self.tagscache and \
                        'name' in self.tagscache:
                    # Mercurial 1.4 and earlier.
                    del self.repo.tagscache[name]
                elif hasattr(self, '_tags') and self._tags and \
                        'name' in self._tags:
                    # Mercurial 1.5 and later.
                    del self.repo._tags[name]
                if (hgutil.safehasattr(self.repo, '_tagtypes') and
                    self.repo._tagtypes and
                    name in self.repo._tagtypes):
                    # Mercurial 1.9 and earlier.
                    del self.repo._tagtypes[name]
                elif (hgutil.safehasattr(self.repo, 'tagscache') and
                      self.repo.tagscache and
                      hgutil.safehasattr(self.repo.tagscache, '_tagtypes') and
                      self.repo.tagscache._tagtypes and
                      name in self.repo.tagscache._tagtypes):
                    # Mercurial 2.0 and later.
                    del self.repo.tagscache._tagtypes[name]

    def import_git_commit(self, commit):
        self.ui.debug(_("importing: %s\n") % commit.id)

        (strip_message, hg_renames,
         hg_branch, extra) = self.extract_hg_metadata(commit.message)

        # get a list of the changed, added, removed files
        files = self.get_files_changed(commit)

        date = (commit.author_time, -commit.author_timezone)
        text = strip_message

        origtext = text
        try:
            text.decode('utf-8')
        except UnicodeDecodeError:
            text = self.decode_guess(text, commit.encoding)

        text = '\n'.join([l.rstrip() for l in text.splitlines()]).strip('\n')
        if text + '\n' != origtext:
            extra['message'] = create_delta(text +'\n', origtext)

        author = commit.author

        # convert extra data back to the end
        if ' ext:' in commit.author:
            regex = re.compile('^(.*?)\ ext:\((.*)\) <(.*)\>$')
            m = regex.match(commit.author)
            if m:
                name = m.group(1)
                ex = urllib.unquote(m.group(2))
                email = m.group(3)
                author = name + ' <' + email + '>' + ex

        if ' <none@none>' in commit.author:
            author = commit.author[:-12]

        try:
            author.decode('utf-8')
        except UnicodeDecodeError:
            origauthor = author
            author = self.decode_guess(author, commit.encoding)
            extra['author'] = create_delta(author, origauthor)

        oldenc = self.swap_out_encoding()

        def findconvergedfiles(p1, p2):
            # If any files have the same contents in both parents of a merge
            # (and are therefore not reported as changed by Git) but are at
            # different file revisions in Mercurial (because they arrived at
            # those contents in different ways), we need to include them in
            # the list of changed files so that Mercurial can join up their
            # filelog histories (same as if the merge was done in Mercurial to
            # begin with).
            if p2 == nullid:
                return []
            manifest1 = self.repo.changectx(p1).manifest()
            manifest2 = self.repo.changectx(p2).manifest()
            return [path for path, node1 in manifest1.iteritems()
                    if path not in files and manifest2.get(path, node1) != node1]

        def getfilectx(repo, memctx, f):
            info = files.get(f)
            if info != None:
                # it's a file reported as modified from Git
                delete, mode, sha = info
                if delete:
                    raise IOError

                data = self.git[sha].data
                copied_path = hg_renames.get(f)
                e = self.convert_git_int_mode(mode)
            else:
                # it's a converged file
                fc = context.filectx(self.repo, f, changeid=memctx.p1().rev())
                data = fc.data()
                e = fc.flags()
                copied_path = fc.renamed()

            return context.memfilectx(f, data, 'l' in e, 'x' in e, copied_path)

        gparents = map(self.map_hg_get, commit.parents)
        p1, p2 = (nullid, nullid)
        octopus = False

        if len(gparents) > 1:
            # merge, possibly octopus
            def commit_octopus(p1, p2):
                ctx = context.memctx(self.repo, (p1, p2), text,
                                     list(files) + findconvergedfiles(p1, p2),
                                     getfilectx, author, date, {'hg-git': 'octopus'})
                return hex(self.repo.commitctx(ctx))

            octopus = len(gparents) > 2
            p2 = gparents.pop()
            p1 = gparents.pop()
            while len(gparents) > 0:
                p2 = commit_octopus(p1, p2)
                p1 = gparents.pop()
        else:
            if gparents:
                p1 = gparents.pop()

        pa = None
        if not (p2 == nullid):
            node1 = self.repo.changectx(p1)
            node2 = self.repo.changectx(p2)
            pa = node1.ancestor(node2)

        # if named branch, add to extra
        if hg_branch:
            extra['branch'] = hg_branch

        # if committer is different than author, add it to extra
        if commit.author != commit.committer \
               or commit.author_time != commit.commit_time \
               or commit.author_timezone != commit.commit_timezone:
            extra['committer'] = "%s %d %d" % (
                commit.committer, commit.commit_time, -commit.commit_timezone)

        if commit.encoding:
            extra['encoding'] = commit.encoding

        if hg_branch:
            extra['branch'] = hg_branch

        if octopus:
            extra['hg-git'] ='octopus-done'

        # TODO use 'n in self.repo' when we require hg 1.5
        def repo_contains(n):
            try:
                return bool(self.repo.lookup(n))
            except error.RepoLookupError:
                return False

        if not (repo_contains(p1) and repo_contains(p2)):
            raise hgutil.Abort(_('you appear to have run strip - '
                                 'please run hg git-cleanup'))
        ctx = context.memctx(self.repo, (p1, p2), text,
                             list(files) + findconvergedfiles(p1, p2),
                             getfilectx, author, date, extra)

        node = self.repo.commitctx(ctx)

        self.swap_out_encoding(oldenc)

        # save changeset to mapping file
        cs = hex(node)
        self.map_set(commit.id, cs)

    ## PACK UPLOADING AND FETCHING

    def upload_pack(self, remote, revs, force):
        client, path = self.get_transport_and_path(remote)
        old_refs = {}
        def changed(refs):
            old_refs.update(refs)
            to_push = revs or set(self.local_heads().values() + self.tags.values())
            return self.get_changed_refs(refs, to_push, force)

        genpack = self.git.object_store.generate_pack_contents
        try:
            self.ui.status(_("creating and sending data\n"))
            new_refs = client.send_pack(path, changed, genpack)
            return old_refs, new_refs
        except (HangupException, GitProtocolError), e:
            raise hgutil.Abort(_("git remote error: ") + str(e))

    def get_changed_refs(self, refs, revs, force):
        new_refs = refs.copy()

        #The remote repo is empty and the local one doesn't have bookmarks/tags
        if refs.keys()[0] == 'capabilities^{}':
            del new_refs['capabilities^{}']
            if not self.local_heads():
                tip = hex(self.repo.lookup('tip'))
                try:
                    commands.bookmark(self.ui, self.repo, 'master', tip, force=True)
                except NameError:
                    bookmarks.bookmark(self.ui, self.repo, 'master', tip, force=True)
                bookmarks.setcurrent(self.repo, 'master')
                new_refs['refs/heads/master'] = self.map_git_get(tip)

        for rev in revs:
            ctx = self.repo[rev]
            if getattr(ctx, 'bookmarks', None):
                labels = lambda c: ctx.tags() + [
                                fltr for fltr, bm
                                in self._filter_for_bookmarks(ctx.bookmarks())
                            ]
            else:
                labels = lambda c: ctx.tags()
            prep = lambda itr: [i.replace(' ', '_') for i in itr]

            heads = [t for t in prep(labels(ctx)) if t in self.local_heads()]
            tags = [t for t in prep(labels(ctx)) if t in self.tags]

            if not (heads or tags):
                raise hgutil.Abort("revision %s cannot be pushed since"
                                   " it doesn't have a ref" % ctx)

            # Check if the tags the server is advertising are annotated tags,
            # by attempting to retrieve it from the our git repo, and building a
            # list of these tags.
            #
            # This is possible, even though (currently) annotated tags are
            # dereferenced and stored as lightweight ones, as the annotated tag
            # is still stored in the git repo.
            uptodate_annotated_tags = []
            for r in tags:
                ref = 'refs/tags/'+r
                # Check tag.
                if not ref in refs:
                    continue
                try:
                    # We're not using Repo.tag(), as it's deprecated.
                    tag = self.git.get_object(refs[ref])
                    if not isinstance(tag, Tag):
                        continue
                except KeyError:
                    continue

                # If we've reached here, the tag's good.
                uptodate_annotated_tags.append(ref)

            for r in heads + tags:
                if r in heads:
                    ref = 'refs/heads/'+r
                else:
                    ref = 'refs/tags/'+r

                if ref not in refs:
                    new_refs[ref] = self.map_git_get(ctx.hex())
                elif new_refs[ref] in self._map_git:
                    rctx = self.repo[self.map_hg_get(new_refs[ref])]
                    if rctx.ancestor(ctx) == rctx or force:
                        new_refs[ref] = self.map_git_get(ctx.hex())
                    else:
                        raise hgutil.Abort("pushing %s overwrites %s"
                                           % (ref, ctx))
                elif ref in uptodate_annotated_tags:
                    # we already have the annotated tag.
                    pass
                else:
                    raise hgutil.Abort("%s changed on the server, please pull "
                                       "and merge before pushing" % ref)

        return new_refs


    def fetch_pack(self, remote_name, heads):
        client, path = self.get_transport_and_path(remote_name)
        graphwalker = self.git.get_graph_walker()
        def determine_wants(refs):
            if heads:
                want = []
                # contains pairs of ('refs/(heads|tags|...)/foo', 'foo')
                # if ref is just '<foo>', then we get ('foo', 'foo')
                stripped_refs = [
                    (r, r[r.find('/', r.find('/')+1)+1:])
                        for r in refs]
                for h in heads:
                    r = [pair[0] for pair in stripped_refs if pair[1] == h]
                    if not r:
                        raise hgutil.Abort("ref %s not found on remote server" % h)
                    elif len(r) == 1:
                        want.append(refs[r[0]])
                    else:
                        raise hgutil.Abort("ambiguous reference %s: %r" % (h, r))
            else:
                want = [sha for ref, sha in refs.iteritems()
                        if not ref.endswith('^{}')
                        and ( ref.startswith('refs/heads/') or ref.startswith('refs/tags/') ) ]
            want = [x for x in want if x not in self.git]
            return want
        f, commit = self.git.object_store.add_pack()
        try:
            try:
                progress = GitProgress(self.ui)
                ret = client.fetch_pack(path, determine_wants, graphwalker,
                                        f.write, progress.progress)
                progress.flush()
                return ret
            except (HangupException, GitProtocolError), e:
                raise hgutil.Abort(_("git remote error: ") + str(e))
        finally:
            commit()

    ## REFERENCES HANDLING

    def update_references(self):
        heads = self.local_heads()

        # Create a local Git branch name for each
        # Mercurial bookmark.
        for key in heads:
            git_ref = self.map_git_get(heads[key])
            if git_ref:
                self.git.refs['refs/heads/' + key] = self.map_git_get(heads[key])

    def export_hg_tags(self):
        for tag, sha in self.repo.tags().iteritems():
            if self.repo.tagtype(tag) in ('global', 'git'):
                tag = tag.replace(' ', '_')
                self.git.refs['refs/tags/' + tag] = self.map_git_get(hex(sha))
                self.tags[tag] = hex(sha)

    def _filter_for_bookmarks(self, bms):
        if not self.branch_bookmark_suffix:
            return [(bm, bm) for bm in bms]
        else:
            def _filter_bm(bm):
                if bm.endswith(self.branch_bookmark_suffix):
                    return bm[0:-(len(self.branch_bookmark_suffix))]
                else:
                    return bm
            return [(_filter_bm(bm), bm) for bm in bms]

    def local_heads(self):
        try:
            if getattr(bookmarks, 'parse', None):
                bms = bookmarks.parse(self.repo)
            else:
                bms = self.repo._bookmarks
            return dict([(filtered_bm, hex(bms[bm])) for
                        filtered_bm, bm in self._filter_for_bookmarks(bms)])
        except AttributeError: #pragma: no cover
            return {}

    def import_tags(self, refs):
        keys = refs.keys()
        if not keys:
            return
        for k in keys[:]:
            ref_name = k
            parts = k.split('/')
            if parts[0] == 'refs' and parts[1] == 'tags':
                ref_name = "/".join([v for v in parts[2:]])
                # refs contains all the refs in the server, not just
                # the ones we are pulling
                if refs[k] not in self.git.object_store:
                    continue
                if ref_name[-3:] == '^{}':
                    ref_name = ref_name[:-3]
                if not ref_name in self.repo.tags():
                    obj = self.git.get_object(refs[k])
                    sha = None
                    if isinstance (obj, Commit): # lightweight
                        sha = self.map_hg_get(refs[k])
                        self.tags[ref_name] = sha
                    elif isinstance (obj, Tag): # annotated
                        (obj_type, obj_sha) = obj.object
                        obj = self.git.get_object(obj_sha)
                        if isinstance (obj, Commit):
                            sha = self.map_hg_get(obj_sha)
                            # TODO: better handling for annotated tags
                            self.tags[ref_name] = sha
        self.save_state()

    def update_hg_bookmarks(self, refs):
        try:
            oldbm = getattr(bookmarks, 'parse', None)
            if oldbm:
                bms = bookmarks.parse(self.repo)
            else:
                bms = self.repo._bookmarks

            heads = dict([(ref[11:],refs[ref]) for ref in refs
                          if ref.startswith('refs/heads/')])

            for head, sha in heads.iteritems():
                # refs contains all the refs in the server, not just
                # the ones we are pulling
                if sha not in self.git.object_store:
                    continue
                hgsha = bin(self.map_hg_get(sha))
                if not head in bms:
                    # new branch
                    bms[head] = hgsha
                else:
                    bm = self.repo[bms[head]]
                    if bm.ancestor(self.repo[hgsha]) == bm:
                        # fast forward
                        bms[head] = hgsha

            # if there's a branch bookmark suffix,
            # then add it on to all bookmark names
            # that would otherwise conflict with a branch
            # name
            if self.branch_bookmark_suffix:
                real_branch_names = self.repo.branchmap()
                bms = dict(
                    (
                        bm_name + self.branch_bookmark_suffix
                            if bm_name in real_branch_names
                        else bm_name,
                        bms[bm_name]
                    )
                    for bm_name in bms
                )
            if heads:
                if oldbm:
                    bookmarks.write(self.repo, bms)
                else:
                    self.repo._bookmarks = bms
                    bookmarks.write(self.repo)

        except AttributeError:
            self.ui.warn(_('creating bookmarks failed, do you have'
                         ' bookmarks enabled?\n'))

    def update_remote_branches(self, remote_name, refs):
        tagfile = self.repo.join(os.path.join('git-remote-refs'))
        tags = self.repo.gitrefs()
        # since we re-write all refs for this remote each time, prune
        # all entries matching this remote from our tags list now so
        # that we avoid any stale refs hanging around forever
        for t in list(tags):
            if t.startswith(remote_name + '/'):
                del tags[t]
        tags = dict((k, hex(v)) for k, v in tags.iteritems())
        store = self.git.object_store
        for ref_name, sha in refs.iteritems():
            if ref_name.startswith('refs/heads'):
                if sha not in store:
                    continue
                hgsha = self.map_hg_get(sha)
                head = ref_name[11:]
                tags['/'.join((remote_name, head))] = hgsha
                # TODO(durin42): what is this doing?
                new_ref = 'refs/remotes/%s/%s' % (remote_name, head)
                self.git.refs[new_ref] = sha
            elif (ref_name.startswith('refs/tags')
                  and not ref_name.endswith('^{}')):
                self.git.refs[ref_name] = sha

        tf = open(tagfile, 'wb')
        for tag, node in tags.iteritems():
            tf.write('%s %s\n' % (node, tag))
        tf.close()


    ## UTILITY FUNCTIONS

    def convert_git_int_mode(self, mode):
        # TODO: make these into constants
        convert = {
         0100644: '',
         0100755: 'x',
         0120000: 'l'}
        if mode in convert:
            return convert[mode]
        return ''

    def extract_hg_metadata(self, message):
        split = message.split("\n--HG--\n", 1)
        renames = {}
        extra = {}
        branch = False
        if len(split) == 2:
            message, meta = split
            lines = meta.split("\n")
            for line in lines:
                if line == '':
                    continue

                if ' : ' not in line:
                    break
                command, data = line.split(" : ", 1)

                if command == 'rename':
                    before, after = data.split(" => ", 1)
                    renames[after] = before
                if command == 'branch':
                    branch = data
                if command == 'extra':
                    before, after = data.split(" : ", 1)
                    extra[before] = urllib.unquote(after)
        return (message, renames, branch, extra)

    def get_file(self, commit, f):
        otree = self.git.tree(commit.tree)
        parts = f.split('/')
        for part in parts:
            (mode, sha) = otree[part]
            obj = self.git.get_object(sha)
            if isinstance (obj, Blob):
                return (mode, sha, obj._text)
            elif isinstance(obj, Tree):
                otree = obj

    def get_files_changed(self, commit):
        tree = commit.tree
        btree = None

        if commit.parents:
            btree = self.git[commit.parents[0]].tree

        changes = self.git.object_store.tree_changes(btree, tree)
        files = {}
        for (oldfile, newfile), (oldmode, newmode), (oldsha, newsha) in changes:
            # don't create new submodules
            if newmode == 0160000:
                if oldfile:
                    # become a regular delete
                    newfile, newmode = None, None
                else:
                    continue
            # so old submodules shoudn't exist
            if oldmode == 0160000:
                if newfile:
                    # become a regular add
                    oldfile, oldmode = None, None
                else:
                    continue

            if newfile is None:
                file = oldfile
                delete = True
            else:
                file = newfile
                delete = False

            files[file] = (delete, newmode, newsha)

        return files

    def remote_name(self, remote):
        names = [name for name, path in self.paths if path == remote]
        if names:
            return names[0]

    # Stolen from hgsubversion
    def swap_out_encoding(self, new_encoding='UTF-8'):
        try:
            from mercurial import encoding
            old = encoding.encoding
            encoding.encoding = new_encoding
        except ImportError:
            old = hgutil._encoding
            hgutil._encoding = new_encoding
        return old

    def decode_guess(self, string, encoding):
        # text is not valid utf-8, try to make sense of it
        if encoding:
            try:
                return string.decode(encoding).encode('utf-8')
            except UnicodeDecodeError:
                pass

        try:
            return string.decode('latin-1').encode('utf-8')
        except UnicodeDecodeError:
            return string.decode('ascii', 'replace').encode('utf-8')

    def get_transport_and_path(self, uri):
        # pass hg's ui.ssh config to dulwich
        if not issubclass(client.get_ssh_vendor, _ssh.SSHVendor):
            client.get_ssh_vendor = _ssh.generate_ssh_vendor(self.ui)

        # Test for git:// and git+ssh:// URI.
        #  Support several URL forms, including separating the
        #  host and path with either a / or : (sepr)
        git_pattern = re.compile(
            r'^(?P<scheme>git([+]ssh)?://)(?P<host>.*?)(:(?P<port>\d+))?'
            r'(?P<sepr>[:/])(?P<path>.*)$'
        )
        git_match = git_pattern.match(uri)
        if git_match:
            res = git_match.groupdict()
            transport = client.SSHGitClient if 'ssh' in res['scheme'] else client.TCPGitClient
            host, port, sepr, path = res['host'], res['port'], res['sepr'], res['path']
            if sepr == '/':
                path = '/' + path
            # strip trailing slash for heroku-style URLs
            # ssh+git://git@heroku.com:project.git/
            if sepr == ':' and path.endswith('.git/'):
                path = path.rstrip('/')
            if port:
                client.port = port

            return transport(host, thin_packs=False, port=port), path

        httpclient = getattr(client, 'HttpGitClient', None)

        if uri.startswith('git+http://') or uri.startswith('git+https://'):
            uri = uri[4:]

        if uri.startswith('http://') or uri.startswith('https://'):
            if not httpclient:
                raise RepoError('git via HTTP requires dulwich 0.8.1 or later')
            else:
                return client.HttpGitClient(uri, thin_packs=False), uri

        # if its not git or git+ssh, try a local url..
        return client.SubprocessGitClient(thin_packs=False), uri

# This file contains code dealing specifically with converting Mercurial
# repositories to Git repositories. Code in this file is meant to be a generic
# library and should be usable outside the context of hg-git or an hg command.

import os
import stat

from dulwich.objects import Blob
from dulwich.objects import S_IFGITLINK
from dulwich.objects import TreeEntry
from dulwich.objects import Tree

from mercurial import error as hgerror
from mercurial.node import nullrev

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

    def __init__(self, hg_repo):
        self._hg = hg_repo
        self._rev = nullrev
        self._dirs = {}
        self._blob_cache = {}

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

        for path in sorted(removed, key=len, reverse=True):
            d = os.path.dirname(path)
            tree = self._dirs.get(d, Tree())

            del tree[os.path.basename(path)]

            if not len(tree):
                self._remove_tree(d)
                continue

            self._dirs[d] = tree

        for path in sorted(set(modified) | set(added), key=len, reverse=True):
            if path == '.hgsubstate':
                self._handle_subrepos(ctx)
                continue

            if path == '.hgsub':
                continue

            d = os.path.dirname(path)
            tree = self._dirs.get(d, Tree())

            fctx = ctx[path]

            entry, blob = TreeTracker.tree_entry(fctx, self._blob_cache)
            if blob is not None:
                yield (blob, fctx.filenode())

            tree.add(*entry)
            self._dirs[d] = tree

        for obj in self._populate_tree_entries():
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

    def _populate_tree_entries(self):
        if '' not in self._dirs:
            self._dirs[''] = Tree()

        # Fill in missing directories.
        for path in self._dirs.keys():
            parent = os.path.dirname(path)

            while parent != '':
                parent_tree = self._dirs.get(parent, None)

                if parent_tree is not None:
                    break

                self._dirs[parent] = Tree()
                parent = os.path.dirname(parent)

        # TODO only emit trees that have been modified.
        for d in sorted(self._dirs.keys(), key=len, reverse=True):
            tree = self._dirs[d]
            yield tree

            if d == '':
                continue

            parent_tree = self._dirs[os.path.dirname(d)]
            parent_tree[os.path.basename(d)] = (stat.S_IFDIR, tree.id)

    def _handle_subrepos(self, ctx):
        substate = util.parse_hgsubstate(ctx['.hgsubstate'].data().splitlines())
        sub = util.OrderedDict()

        if '.hgsub' in ctx:
            sub = util.parse_hgsub(ctx['.hgsub'].data().splitlines())

        for path, sha in substate.iteritems():
            # Ignore non-Git repositories keeping state in .hgsubstate.
            if path in sub and not sub[path].startswith('[git]'):
                continue

            d = os.path.dirname(path)
            tree = self._dirs.get(d, Tree())
            tree.add(os.path.basename(path), S_IFGITLINK, sha)
            self._dirs[d] = tree

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


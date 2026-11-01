#!/usr/bin/env python3
"""Resolve source identities from the caller's Lake configuration and Git tree.

Compiled artifacts remain module-relative. Archive lookup is explicit, so the
reader ARCHITECTURE.md cannot accidentally replace the historical document.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile
import tomllib


def under(name, prefix):
    return name == prefix or name.startswith(prefix + '.')


class Layout:
    def __init__(self, root, revision=None):
        self.root = Path(root).resolve()
        self.revision = revision
        raw = self.read('lakefile.toml')
        config = tomllib.loads(raw.decode())
        self._declarations = config.get('lean_lib', [])
        if not isinstance(self._declarations, list):
            raise ValueError('lean_lib must be an array')
        self._prefixes = {}
        self._scopes = {}
        names = set()
        default = config.get('srcDir', '.')
        for lib in self._declarations:
            name = lib.get('name')
            if not isinstance(name, str) or not name or name in names:
                raise ValueError('missing or duplicate library name')
            names.add(name)
            src = lib.get('srcDir', '.')
            if not isinstance(default, str) or not isinstance(src, str):
                raise ValueError('srcDir must be a string')
            src = (PurePosixPath(default) / src).as_posix()
            p = PurePosixPath(src)
            if p.is_absolute() or '..' in p.parts or '\\' in src:
                raise ValueError('out-of-root srcDir: ' + src)
            src = p.as_posix()
            if not (self.root / src).resolve().is_relative_to(self.root):
                raise ValueError('out-of-root srcDir: ' + src)
            roots = lib.get('roots', [name])
            globs = lib.get('globs', [])
            for values in (roots, globs):
                if not isinstance(values, list) or not all(isinstance(v, str) for v in values):
                    raise ValueError('roots/globs must be string arrays')
            prefixes = set(roots) | {g[:-2] if g.endswith(('.*', '.+')) else g for g in globs}
            self._scopes[name] = (src, roots, globs, prefixes)
            for prefix in prefixes:
                if not re.fullmatch(r'\w+(?:\.\w+)*', prefix):
                    raise ValueError('malformed module prefix: ' + prefix)
                old = self._prefixes.setdefault(prefix, src)
                if old != src:
                    raise ValueError('conflicting mapping: ' + prefix)
        for a, src in self._prefixes.items():
            for b, other in self._prefixes.items():
                if under(a, b) and src != other:
                    raise ValueError('conflicting overlapping mapping: ' + a)
        self._tree = None
        if revision:
            self._tree = self.git('ls-tree', '-r', '--name-only', revision).decode().splitlines()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args])

    def read(self, path):
        if self.revision:
            return self.git('show', self.revision + ':' + str(path))
        return (self.root / path).read_bytes()

    def exists(self, path):
        if self._tree is not None:
            return str(path) in self._tree
        return (self.root / path).is_file()

    def declarations(self):
        return [dict(lib, srcDir=self._scopes[lib['name']][0])
                for lib in self._declarations]

    def _src(self, module):
        matches = [p for p in self._prefixes if under(module, p)]
        if not matches:
            raise ValueError('undeclared module: ' + module)
        return self._prefixes[max(matches, key=len)]

    def source_dir(self, module_prefix):
        return (PurePosixPath(self._src(module_prefix)) /
                module_prefix.replace('.', '/')).as_posix()

    def source_path(self, module):
        return self.source_dir(module) + '.lean'

    def module_of_source(self, path, *, undeclared=False):
        p = Path(path)
        if p.is_absolute():
            p = p.relative_to(self.root)
        text = p.as_posix()
        if '..' in p.parts or p.suffix.lower() != '.lean':
            raise ValueError('invalid Lean source path: ' + text)
        matches = set()
        for prefix, src in self._prefixes.items():
            base = PurePosixPath(src)
            try:
                rel = PurePosixPath(text).relative_to(base)
            except ValueError:
                continue
            module = rel.with_suffix('').as_posix().replace('/', '.')
            if under(module, prefix):
                matches.add(module)
        if len(matches) == 1:
            return matches.pop()
        if matches:
            raise ValueError('ambiguous inverse source path: ' + text)
        if undeclared:
            return p.with_suffix('').as_posix().replace('/', '.')
        raise ValueError('undeclared source path: ' + text)

    def logical_path(self, path):
        text = str(path).replace(os.sep, '/')
        for src in sorted(set(self._prefixes.values()), key=len, reverse=True):
            if src != '.' and text.startswith(src + '/'):
                rel = text[len(src) + 1:]
                module = rel.removesuffix('.lean').replace('/', '.')
                if any(under(module, p) for p, s in self._prefixes.items() if s == src):
                    return rel
        return text

    def physical_path(self, logical_path):
        text = self.logical_path(logical_path)
        pre = text.removesuffix('.lean').replace('/', '.')
        try:
            src = self._src(pre)
        except ValueError:
            return text
        return (PurePosixPath(src) / text).as_posix()

    def archive_doc_path(self, logical_doc):
        text = str(logical_doc)
        if text.startswith('docs/internal/'):
            text = 'docs/' + text[len('docs/internal/'):]
        if not text.startswith('docs/'):
            text = 'docs/' + text
        moved = 'docs/internal/' + text[5:]
        # Layout state, not basename existence, selects the archive.
        relocated = (any(p.startswith('docs/internal/') for p in self._tree)
                     if self._tree is not None else (self.root / 'docs/internal').is_dir())
        return moved if relocated else text

    def expand_checker_pattern(self, pattern):
        if pattern.startswith('docs/'):
            return self.archive_doc_path(pattern)
        return self.physical_path(pattern)

    def _files(self, directory):
        if self._tree is not None:
            return [p for p in self._tree if p.startswith(directory + '/') and
                    PurePosixPath(p).suffix.lower() == '.lean']
        out = []
        for dp, dirs, files in os.walk(self.root / directory, followlinks=True):
            dirs[:] = sorted(dirs)
            # Reject cycles but retain ordinary symlink source coverage.
            for d in list(dirs):
                target = (Path(dp) / d).resolve()
                if target in [Path(dp).resolve(), *Path(dp).resolve().parents]:
                    raise ValueError('source symlink cycle: ' + str(Path(dp) / d))
            for f in sorted(files):
                if Path(f).suffix.lower() == '.lean':
                    out.append((Path(dp) / f).relative_to(self.root).as_posix())
        return out

    def source_files(self, libraries=None):
        selected = list(self._scopes) if libraries is None else list(libraries)
        paths = set()
        for lib in selected:
            if lib in self._scopes:
                prefixes = self._scopes[lib][3]
            else:
                self._src(lib)  # explicit prefix scopes are allowed, undeclared ones fail
                prefixes = {lib}
            if not prefixes:
                continue  # Explicit roots=[] and globs=[] declares no source scope.
            found = set()
            for prefix in prefixes:
                facade = self.source_path(prefix)
                if self.exists(facade):
                    found.add(facade)
                found.update(self._files(self.source_dir(prefix)))
            if not found:
                raise ValueError('absent declared source scope: ' + lib)
            paths.update(found)
        providers = {}
        for path in sorted(paths):
            module = self.module_of_source(path)
            if module in providers and providers[module] != path:
                raise ValueError('duplicate physical module provider: ' + module)
            providers[module] = path
        return sorted(paths)

    def declared_module_files(self):
        out = set()
        for name, (_, roots, globs, _) in self._scopes.items():
            for path in self.source_files([name]):
                mod = self.module_of_source(path)
                if mod in roots or any(
                    under(mod, g[:-2]) and (g.endswith('.*') or mod != g[:-2])
                    if g.endswith(('.*', '.+')) else mod == g for g in globs):
                    out.add(path)
        return sorted(out)

    def check(self):
        for prefix, src in self._prefixes.items():
            if src == '.':
                continue
            flat = prefix.replace('.', '/')
            if self.exists(flat + '.lean') or self._files(flat):
                raise ValueError('source outside declared srcDir: ' + flat)
        files = self.source_files()
        for p in files:
            m = self.module_of_source(p)
            canonical = self.source_path(m)
            if canonical.lower() != p.lower():
                raise ValueError('source bijection failed: ' + p)
        return len(files)


def selftest():
    def must_fail(f):
        try:
            f()
        except (ValueError, tomllib.TOMLDecodeError):
            return
        raise AssertionError('expected layout rejection')
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        for nested in (False, True):
            root = base / ('nested' if nested else 'flat')
            root.mkdir()
            src = 'src' if nested else '.'
            (root / 'lakefile.toml').write_text(
                'srcDir = "' + src + '"\n'
                '[[lean_lib]]\nname = "A"\nglobs = ["A.*"]\n'
                '[[lean_lib]]\nname = "ATests"\nroots = []\nglobs = ["A.Tests.+"]\n'
                '[[lean_lib]]\nname = "ARun"\n'
                '[[lean_lib]]\nname = "Alias"\nroots = ["B"]\nglobs = ["B.+"]\n')
            for mod in ('A', 'A.Orphan', 'A.Tests.Axioms', 'ARun', 'B', 'B.Child'):
                p = root / src / (mod.replace('.', '/') + '.lean')
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text('module\n')
            layout = Layout(root)
            assert layout.check() == 6
            assert layout.declarations()[0]["srcDir"] == src
            assert layout.module_of_source(layout.source_path('ARun')) == 'ARun'
            assert len(layout.source_files(['ATests'])) == 1
            assert len(layout.declared_module_files()) == 6
            assert layout.logical_path(layout.source_path('A.Orphan')) == 'A/Orphan.lean'
            assert layout.physical_path('A/Orphan.lean') == layout.source_path('A.Orphan')
            if nested:
                (root / 'A.lean').write_text('module\n')
                must_fail(lambda: layout.check())
                (root / 'A.lean').unlink()
            must_fail(lambda: layout.source_path('AX'))
            must_fail(lambda: layout.source_files(['Missing']))
            assert layout.module_of_source('Fixture.lean', undeclared=True) == 'Fixture'
        (root/'lakefile.toml').write_text('[[lean_lib]]\nname="A"\nsrcDir="../bad"\n')
        must_fail(lambda: Layout(root))
        (root/'lakefile.toml').write_text(
            '[[lean_lib]]\nname="A"\nsrcDir="src"\n'
            '[[lean_lib]]\nname="ATests"\nsrcDir="other"\n'
            'roots=[]\nglobs=["A.Tests.+"]\n')
        must_fail(lambda: Layout(root))
        (root/'lakefile.toml').write_text('[[lean_lib]]\nname="A"\nsrcDir="src"\n')
        (root/'src/A/dup.lean').write_text('module\n')
        (root/'src/A/dup.LEAN').write_text('module\n')
        must_fail(lambda: Layout(root).check())
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / 'lakefile.toml').write_text(
            'srcDir="src"\n[[lean_lib]]\nname="A"\nsrcDir="nested"\nglobs=["A.*"]\n')
        for module in ('A', 'A.Child'):
            path = root / 'src/nested' / (module.replace('.', '/') + '.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('module\n')
        layout = Layout(root)
        assert layout.source_path('A') == 'src/nested/A.lean'
        assert layout.source_path('A.Child') == 'src/nested/A/Child.lean'
        assert layout.module_of_source('src/nested/A.lean') == 'A'
        assert layout.module_of_source('src/nested/A/Child.lean') == 'A.Child'
        assert layout.check() == 2
        (root / 'src/nested').rename(root / 'outside')
        (root / 'src/nested').symlink_to(root.parent, target_is_directory=True)
        must_fail(lambda: Layout(root))
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        def git(*args):
            return subprocess.check_output(['git', '-C', str(root), *args])
        git('init', '-q')
        (root / 'lakefile.toml').write_text('[[lean_lib]]\nname="A"\n')
        (root / 'A.lean').write_text('module\n')
        (root / 'docs').mkdir()
        (root / 'docs/ARCHITECTURE.md').write_text('archive\n')
        git('add', '.')
        git('-c', 'user.name=Layout', '-c', 'user.email=layout@example.invalid',
            'commit', '-qm', 'flat fixture')
        old = git('rev-parse', 'HEAD').decode().strip()
        (root / 'src').mkdir()
        (root / 'A.lean').rename(root / 'src/A.lean')
        (root / 'lakefile.toml').write_text('[[lean_lib]]\nname="A"\nsrcDir="src"\n')
        (root / 'docs/internal').mkdir()
        (root / 'docs/ARCHITECTURE.md').rename(root / 'docs/internal/ARCHITECTURE.md')
        (root / 'docs/ARCHITECTURE.md').write_text('reader\n')
        git('add', '.')
        git('-c', 'user.name=Layout', '-c', 'user.email=layout@example.invalid',
            'commit', '-qm', 'nested fixture')
        before, after = Layout(root, old), Layout(root, 'HEAD')
        assert before.source_path('A') == 'A.lean'
        assert after.source_path('A') == 'src/A.lean'
        assert before.source_files() == ['A.lean']
        assert after.source_files() == ['src/A.lean']
        doc = 'docs/ARCHITECTURE.md'
        assert before.archive_doc_path(doc) == doc
        assert after.archive_doc_path(doc) == 'docs/internal/ARCHITECTURE.md'
        assert before.read(before.archive_doc_path(doc)) == after.read(after.archive_doc_path(doc))
    print('source_layout selftest: PASS (flat/nested, overlap, roots/globs, rejection)')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--revision')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--nul', action='store_true')
    ap.add_argument('--lines', action='store_true')
    ap.add_argument('--undeclared', action='store_true')
    ap.add_argument('--exclude-source-dir', action='append', default=[])
    ap.add_argument('command', nargs='?', choices=('path', 'dir', 'module', 'files', 'modules',
                                                 'archive-doc', 'logical', 'physical'))
    ap.add_argument('values', nargs='*')
    a = ap.parse_args()
    if a.selftest:
        selftest()
        return
    layout = Layout(a.root, a.revision)
    if a.check:
        print(f'source_layout: PASS ({layout.check()} unique source files)')
        return
    if a.command in ('files', 'modules'):
        out = layout.source_files(a.values or None)
        out = [p for p in out if not any(
            PurePosixPath(p).is_relative_to(PurePosixPath(d))
            for d in a.exclude_source_dir)]
        if a.command == 'modules':
            out = sorted(layout.module_of_source(p) for p in out)
        if a.nul or a.lines:
            print(('\0' if a.nul else '\n').join(out), end='\0' if a.nul else '\n')
        else:
            print(json.dumps(out))
        return
    methods = {'path': layout.source_path, 'dir': layout.source_dir,
               'module': lambda p: layout.module_of_source(p, undeclared=a.undeclared),
               'archive-doc': layout.archive_doc_path, 'logical': layout.logical_path,
               'physical': layout.physical_path}
    if a.command not in methods or not a.values:
        ap.error('a command and input are required')
    for v in a.values:
        print(methods[a.command](v))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from None

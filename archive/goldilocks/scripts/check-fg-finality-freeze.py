#!/usr/bin/env python3
"""Archival since 2026-10-09 (user decision); the S0 freeze is retired.

Check the S0 frozen files of FG finality safety against their recorded history.

The S0 manifest (docs/FG-FINALITY-SAFETY-S0-hashes.json) pins 122 files at
88c616d1. docs/FG-FINALITY-SAFETY-S0-inherited.json records each later
change to one of them, with its exact commit, parent and byte hashes. The
record is history only: it grants no permission to edit a listed path.

Modes:
  --check                   the archive mode. It reads no Git history: each S0
                            path in the working tree has its S0 bytes, or,
                            for a recorded difference, the recorded main
                            bytes. It also checks the record and the two
                            manifest hashes. It runs on an archive.
  --history [--revision REV]  every S0 path at REV (default HEAD, with the
                            working tree) has its S0 bytes or its recorded
                            bytes; the record matches Git history; the open
                            package (tip null) adds no frozen-byte change.
                            Not a gate step: it reads old revisions.
  --packages                every package base/tip pair changes only its
                            recorded frozen paths.
  --base BASE --tip TIP     the range changes no frozen byte.
  --selftest                isolated byte and Git-history fixtures.
"""
import argparse
import hashlib
import json
from pathlib import Path
from source_layout import Layout
import subprocess
import sys
import tempfile

MANIFEST = 'docs/FG-FINALITY-SAFETY-S0-hashes.json'
STEP1 = 'docs/FG-FINALITY-SAFETY-S0-step1-hashes.json'
RECORD = 'docs/FG-FINALITY-SAFETY-S0-inherited.json'


class FreezeError(Exception):
    pass


def strict_json(text, what):
    def pairs(items):
        keys = [k for k, _ in items]
        if len(keys) != len(set(keys)):
            raise FreezeError(f'DUPLICATE JSON KEY in {what}')
        return dict(items)
    try:
        return json.loads(text, object_pairs_hook=pairs)
    except json.JSONDecodeError as exc:
        raise FreezeError(f'INVALID JSON in {what}: {exc}') from None


def sha(data):
    return hashlib.sha256(data).hexdigest()


class Repo:
    def __init__(self, root):
        self.root = Path(root)
        self._blobs = {}
        self._layouts = {}

    def git(self, *args, check=True):
        r = subprocess.run(['git', '-C', str(self.root), *args], capture_output=True)
        if check and r.returncode != 0:
            raise FreezeError(f'GIT FAILED: git {" ".join(args)}: '
                              + r.stderr.decode(errors='replace').strip())
        return r

    def commit(self, rev):
        r = self.git('rev-parse', '--verify', '--quiet', rev + '^{commit}', check=False)
        if r.returncode != 0:
            raise FreezeError(f'MISSING COMMIT {rev}')
        return r.stdout.decode().strip()

    def parents(self, rev):
        out = self.git('rev-list', '--parents', '-n', '1', rev).stdout.decode().split()
        return out[1:]

    def ancestor(self, a, b):
        return self.git('merge-base', '--is-ancestor', a, b, check=False).returncode == 0

    def physical(self, path, rev=None):
        if rev not in self._layouts:
            self._layouts[rev] = Layout(self.root, rev)
        layout = self._layouts[rev]
        return (layout.archive_doc_path(path) if path.startswith('docs/')
                else layout.physical_path(path))

    def blob(self, rev, path):
        key = (rev, path)
        if key not in self._blobs:
            r = self.git('show', f'{rev}:{self.physical(path, rev)}', check=False)
            self._blobs[key] = sha(r.stdout) if r.returncode == 0 else None
        return self._blobs[key]

    def worktree(self, path):
        p = self.root / self.physical(path)
        return sha(p.read_bytes()) if p.is_file() else None

    def touching(self, base, tip, path):
        out = self.git('rev-list', '--full-history', '--parents', f'{base}..{tip}', '--',
                       path).stdout.decode().split('\n')
        return [line.split() for line in out if line]


class Checker:
    def __init__(self, root, manifest=MANIFEST, step1=STEP1, record=RECORD):
        self.repo = Repo(root)
        self.root = Path(root)
        self.manifest_path, self.step1_path, self.record_path = [
            self.repo.physical(p) for p in (manifest, step1, record)]
        self.findings = []

    def fail(self, msg):
        self.findings.append(msg)

    def load_files(self):
        """The record and the manifests, from files only (no Git)."""
        rp = self.root / self.record_path
        if not rp.is_file():
            raise FreezeError(f'MISSING RECORD {self.record_path}')
        self.record = strict_json(rp.read_text(), self.record_path)
        mp = self.root / self.manifest_path
        if not mp.is_file():
            raise FreezeError(f'MISSING MANIFEST {self.manifest_path}')
        mbytes = mp.read_bytes()
        self.manifest = strict_json(mbytes.decode(), self.manifest_path)
        r = self.record
        for key in ('version', 's0_revision', 's0_manifest_sha256', 'comparison_revision',
                    'main_revision', 'differences', 'packages'):
            if key not in r:
                raise FreezeError(f'RECORD MISSING FIELD {key}')
        if r['version'] != 1:
            raise FreezeError('RECORD WRONG VERSION')
        if sha(mbytes) != r['s0_manifest_sha256']:
            raise FreezeError('S0 MANIFEST CHANGED: ' + self.manifest_path)
        if 's0_step1_manifest_sha256' in r:
            sp = self.root / self.step1_path
            if not sp.is_file() or sha(sp.read_bytes()) != r['s0_step1_manifest_sha256']:
                raise FreezeError('S0 STEP-1 MANIFEST CHANGED: ' + self.step1_path)
        self.diffs = {}
        for d in r['differences']:
            p = d.get('path')
            if p in self.diffs:
                raise FreezeError(f'DUPLICATE DIFFERENCE {p}')
            if p not in self.manifest:
                raise FreezeError(f'DIFFERENCE NOT IN S0 MANIFEST {p}')
            for key in ('s0_sha256', 'main_sha256'):
                if not isinstance(d.get(key), str) or len(d[key]) != 64:
                    raise FreezeError(f'DIFFERENCE MISSING {key} {p}')
            if d['s0_sha256'] != self.manifest[p]:
                raise FreezeError(f'S0 HASH MISMATCH {p}')
            self.diffs[p] = d

    def load(self):
        self.load_files()
        r = self.record
        self.s0 = self.repo.commit(r['s0_revision'])
        self.cmp = self.repo.commit(r['comparison_revision'])
        self.main = self.repo.commit(r['main_revision'])

    def check_bytes(self):
        """The archive mode: working-tree bytes only."""
        for p, v in self.manifest.items():
            want = self.diffs[p]['main_sha256'] if p in self.diffs else v
            got = self.repo.worktree(p)
            if got is None:
                self.fail(f'MISSING FILE {p} in working tree')
            elif got != want:
                self.fail(f'UNLISTED DIFFERENCE {p} in working tree')

    def check_history(self):
        """Each recorded change is an exact parent-to-commit byte change, and
        the record lists every such change between S0 and main."""
        for p, d in self.diffs.items():
            if d['s0_sha256'] != self.manifest[p]:
                self.fail(f'S0 HASH MISMATCH {p}')
            if self.repo.blob(self.s0, p) != self.manifest[p]:
                self.fail(f'S0 REVISION BYTES MISMATCH {p}')
            if self.repo.blob(self.cmp, p) != d['comparison_sha256']:
                self.fail(f'COMPARISON HASH MISMATCH {p}')
            if self.repo.blob(self.main, p) != d['main_sha256']:
                self.fail(f'MAIN HASH MISMATCH {p}')
            recorded = set()
            for c in d['changes']:
                try:
                    commit = self.repo.commit(c['commit'])
                except FreezeError as exc:
                    self.fail(f'{exc} ({p})')
                    continue
                recorded.add(commit)
                ps = self.repo.parents(commit)
                if c.get('parent') not in ps:
                    self.fail(f'WRONG PARENT {p} {commit[:8]}')
                    continue
                if not c.get('reason', '').strip():
                    self.fail(f'CHANGE WITHOUT REASON {p} {commit[:8]}')
                after = self.repo.blob(commit, p)
                if after != c['after_sha256']:
                    self.fail(f'AFTER HASH MISMATCH {p} {commit[:8]}')
                if self.repo.blob(c['parent'], p) != c['before_sha256']:
                    self.fail(f'BEFORE HASH MISMATCH {p} {commit[:8]}')
                if len(ps) > 1:
                    mp = c.get('merge_parents')
                    if c.get('kind') != 'merge-resolution' or mp is None or \
                            [x['parent'] for x in mp] != ps:
                        self.fail(f'MERGE PARENTS MISMATCH {p} {commit[:8]}')
                    else:
                        for x in mp:
                            if self.repo.blob(x['parent'], p) != x['before_sha256']:
                                self.fail(f'BEFORE HASH MISMATCH {p} {commit[:8]}')
                if any(self.repo.blob(q, p) == after for q in ps):
                    self.fail(f'NOT A BYTE CHANGE {p} {commit[:8]}')
                if not (self.repo.ancestor(self.s0, commit) and
                        self.repo.ancestor(commit, self.main)):
                    self.fail(f'WRONG ANCESTRY {p} {commit[:8]}')
            actual = set()
            for c, *ps in self.repo.touching(self.s0, self.main, p):
                after = self.repo.blob(c, p)
                if all(self.repo.blob(q, p) != after for q in ps):
                    actual.add(c)
            for c in sorted(actual - recorded):
                self.fail(f'UNRECORDED CHANGE {p} {c[:8]}')
            for c in sorted(recorded - actual):
                self.fail(f'RECORDED CHANGE OUTSIDE S0..MAIN {p} {c[:8]}')
        for p, v in self.manifest.items():
            if p not in self.diffs and self.repo.blob(self.main, p) != v:
                self.fail(f'UNLISTED DIFFERENCE AT MAIN {p}')

    def accepted(self, rev, p):
        d = self.diffs.get(p)
        if d is None:
            return {self.manifest[p]}
        if self.repo.ancestor(self.main, rev):
            return {d['main_sha256']}
        ok = {self.manifest[p]}
        for c in d['changes']:
            if self.repo.ancestor(c['commit'], rev):
                ok.add(c['after_sha256'])
        return ok

    def check_revision(self, rev, worktree):
        rev = self.repo.commit(rev)
        for p in self.manifest:
            ok = self.accepted(rev, p)
            got = self.repo.blob(rev, p)
            if got is None:
                self.fail(f'MISSING FILE {p} at {rev[:8]}')
            elif got not in ok:
                self.fail(f'UNLISTED DIFFERENCE {p} at {rev[:8]}')
            if worktree:
                w = self.repo.worktree(p)
                if w is None:
                    self.fail(f'MISSING FILE {p} in working tree')
                elif w != got:
                    self.fail(f'WORKING TREE DIFFERS {p}')
        return rev

    def frozen_changes(self, base, tip):
        return sorted(p for p in self.manifest
                      if self.repo.blob(base, p) != self.repo.blob(tip, p))

    def check_range(self, base, tip, allowed=(), inherited=()):
        base, tip = self.repo.commit(base), self.repo.commit(tip)
        if not self.repo.ancestor(base, tip):
            self.fail(f'WRONG ANCESTRY base {base[:8]} not below tip {tip[:8]}')
        changed = [p for p in self.frozen_changes(base, tip) if p not in inherited]
        allowed = dict(allowed)
        for p in changed:
            if p not in allowed:
                self.fail(f'FROZEN BYTE CHANGE {p} in {base[:8]}..{tip[:8]}')
        for p, commit in allowed.items():
            if p not in changed:
                self.fail(f'RECORDED PACKAGE CHANGE ABSENT {p} in {base[:8]}..{tip[:8]}')
                continue
            c = self.repo.commit(commit)
            if not (self.repo.ancestor(c, tip) and not self.repo.ancestor(c, base)):
                self.fail(f'WRONG ANCESTRY package change {p} {c[:8]}')
            if self.repo.blob(tip, p) != self.repo.blob(c, p):
                self.fail(f'PACKAGE TIP BYTES NOT THE RECORDED CHANGE {p}')
        return changed

    def check_packages(self, report=print):
        ids = set()
        for pk in self.record['packages']:
            i = pk.get('id')
            if i in ids:
                raise FreezeError(f'DUPLICATE PACKAGE {i}')
            ids.add(i)
            if pk.get('tip') is None:
                continue
            allowed = [(c['path'], c['commit']) for c in pk.get('recorded_changes', [])]
            changed = self.check_range(pk['base'], pk['tip'], allowed)
            for pc in pk.get('policy_commits', []):
                self.check_range(pc['base'], pc['tip'])
            line = f'{i}: {pk["base"][:8]}..{pk["tip"][:8]} frozen changes {len(changed)}'
            tip = self.repo.commit(pk['tip'])
            if self.repo.ancestor(self.cmp, tip):
                total = self.frozen_changes(self.cmp, tip)
                line += f'; since {self.cmp[:8]}: {len(total)} (main history ' \
                        f'{len(total) - len(changed)}, package {len(changed)})'
            report(line)

    def open_packages(self):
        return [pk for pk in self.record['packages'] if pk.get('tip') is None]

    def inherited_since(self, base, rev):
        """Recorded paths that a merge of a newer main brought into base..rev.
        check_revision already requires their bytes at rev to be the main bytes."""
        base = self.repo.commit(base)
        if self.repo.ancestor(self.main, base) or not self.repo.ancestor(self.main, rev):
            return []
        return [p for p, d in self.diffs.items() if self.repo.blob(rev, p) == d['main_sha256']]


def run_bytes_check(root, report=print):
    ch = Checker(root)
    ch.load_files()
    ch.check_bytes()
    if not ch.findings:
        report(f'fg-finality-freeze: PASS (bytes): {len(ch.manifest)} S0 paths, '
               f'{len(ch.diffs)} recorded differences at their main bytes')
    return ch.findings


def run_check(root, revision, report=print):
    ch = Checker(root)
    ch.load()
    ch.check_history()
    worktree = revision is None
    rev = ch.check_revision(revision or 'HEAD', worktree)
    for pk in ch.open_packages():
        ch.check_range(pk['base'], rev, inherited=ch.inherited_since(pk['base'], rev))
    if not ch.findings:
        report(f'fg-finality-freeze: PASS: {len(ch.manifest)} S0 paths at {rev[:8]}, '
               f'{len(ch.diffs)} recorded differences, '
               f'{sum(len(d["changes"]) for d in ch.diffs.values())} recorded changes')
    return ch.findings


# ---------------------------------------------------------------- selftest

def selftest():
    cases = 0

    def sh(root, *args):
        subprocess.run(['git', '-C', str(root), *args], check=True, capture_output=True)

    def commit(root, msg):
        sh(root, 'add', '-A')
        sh(root, '-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q',
           '--allow-empty', '-m', msg)
        return subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'],
                                       text=True).strip()

    def write(root, path, data):
        p = Path(root) / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(data)

    def fixture(tmp, change=True):
        root = Path(tmp)
        sh(root, 'init', '-q')
        write(root, 'lakefile.toml', 'name="archive-fixture"\n')
        write(root, 'a.lean', 'a0\n')
        write(root, 'b.lean', 'b0\n')
        man = {'a.lean': sha(b'a0\n'), 'b.lean': sha(b'b0\n')}
        write(root, MANIFEST, json.dumps(man, indent=2) + '\n')
        write(root, STEP1, '{}\n')
        s0 = commit(root, 's0')
        if change:
            write(root, 'a.lean', 'a1\n')
        c1 = commit(root, 'change a')
        write(root, 'other.txt', 'x\n')
        main = commit(root, 'main')
        rec = dict(version=1, s0_revision=s0,
                   s0_manifest_sha256=sha((root / MANIFEST).read_bytes()),
                   s0_step1_manifest_sha256=sha((root / STEP1).read_bytes()),
                   comparison_revision=main, main_revision=main,
                   differences=[dict(path='a.lean', s0_sha256=man['a.lean'],
                                     comparison_sha256=sha(b'a1\n'),
                                     main_sha256=sha(b'a1\n'),
                                     changes=[dict(commit=c1, parent=s0,
                                                   before_sha256=man['a.lean'],
                                                   after_sha256=sha(b'a1\n'),
                                                   reason='fixture change', kind='commit')])],
                   packages=[dict(id='P', base=main, tip=None, recorded_changes=[])])
        if not change:
            rec['differences'] = []
        write(root, RECORD, json.dumps(rec, indent=2) + '\n')
        tip = commit(root, 'record')
        return root, rec, dict(s0=s0, c1=c1, main=main, tip=tip)

    def expect(name, findings, want):
        nonlocal cases
        cases += 1
        text = '\n'.join(findings)
        if want is None:
            if findings:
                raise SystemExit(f'SELFTEST {name}: expected PASS, got:\n{text}')
        elif not any(want in f for f in findings):
            raise SystemExit(f'SELFTEST {name}: expected {want!r}, got:\n{text or "PASS"}')
        print(f'PASS {name}: ' + ('PASS' if want is None else want))

    def check(root):
        try:
            return run_check(root, None, report=lambda _: None)
        except FreezeError as exc:
            return [str(exc)]

    def rewrite_record(root, rec):
        write(root, RECORD, json.dumps(rec, indent=2) + '\n')
        commit(root, 'edit record')

    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        expect('one recorded inherited change', check(root), None)
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp, change=False)
        expect('unchanged bytes', check(root), None)
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        rec['differences'] = []
        rewrite_record(root, rec)
        expect('unlisted inherited difference', check(root), 'UNLISTED DIFFERENCE AT MAIN a.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        write(root, 'b.lean', 'b1\n')
        commit(root, 'unlisted')
        expect('unlisted byte change', check(root), 'UNLISTED DIFFERENCE b.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        write(root, 'a.lean', 'a2\n')
        commit(root, 'third hash')
        expect('recorded file with a third hash', check(root), 'UNLISTED DIFFERENCE a.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        rec['differences'][0]['changes'][0]['commit'] = '0' * 40
        rewrite_record(root, rec)
        expect('wrong commit', check(root), 'MISSING COMMIT')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        rec['differences'][0]['changes'][0]['parent'] = c['main']
        rewrite_record(root, rec)
        expect('wrong parent', check(root), 'WRONG PARENT a.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        (root / 'b.lean').unlink()
        commit(root, 'remove b')
        expect('missing file', check(root), 'MISSING FILE b.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        man = json.loads((root / MANIFEST).read_text())
        man['b.lean'] = sha(b'b1\n')
        write(root, MANIFEST, json.dumps(man, indent=2) + '\n')
        commit(root, 'regenerate manifest')
        expect('changed S0 manifest', check(root), 'S0 MANIFEST CHANGED')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        write(root, 'a.lean', 'a1-package\n')
        commit(root, 'package edits an inherited path')
        expect('package changes an inherited path', check(root), 'FROZEN BYTE CHANGE a.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        write(root, RECORD, (root / RECORD).read_text().replace(
            '"version": 1,', '"version": 1, "version": 1,', 1))
        commit(root, 'duplicate key')
        expect('duplicate JSON key', check(root), 'DUPLICATE JSON KEY')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        write(root, 'a.lean', 'dirty\n')
        expect('dirty working tree', check(root), 'WORKING TREE DIFFERS a.lean')
    with tempfile.TemporaryDirectory() as tmp:
        root, rec, c = fixture(tmp)
        write(root, 'a.lean', 'a3\n')
        c3 = commit(root, 'unrecorded change on main')
        rec['main_revision'] = rec['comparison_revision'] = c3
        rec['differences'][0]['main_sha256'] = rec['differences'][0]['comparison_sha256'] = \
            sha(b'a3\n')
        rec['packages'][0]['base'] = c3
        rewrite_record(root, rec)
        expect('unrecorded history change', check(root), 'UNRECORDED CHANGE a.lean')
    for edit in (False, True):
        with tempfile.TemporaryDirectory() as tmp:
            # Main advances with a recorded change of b.lean; the open package
            # merges it. A package edit of b.lean after that still fails.
            root, rec, c = fixture(tmp)
            write(root, 'b.lean', 'b1\n')
            c4 = commit(root, 'recorded change on a newer main')
            rec['main_revision'] = c4
            rec['differences'].append(dict(
                path='b.lean', s0_sha256=sha(b'b0\n'), comparison_sha256=sha(b'b0\n'),
                main_sha256=sha(b'b1\n'),
                changes=[dict(commit=c4, parent=c['tip'], before_sha256=sha(b'b0\n'),
                              after_sha256=sha(b'b1\n'), reason='fixture main change',
                              kind='commit')]))
            rewrite_record(root, rec)
            if edit:
                write(root, 'b.lean', 'b2\n')
                commit(root, 'package edits the newly inherited path')
                expect('package edits a newer inherited path', check(root),
                       'UNLISTED DIFFERENCE b.lean')
            else:
                expect('newer main change merged into the open package', check(root), None)
    import tarfile
    for label, edit, want in [('archive positive (no Git)', None, None),
                              ('archive byte change (no Git)', 'b.lean',
                               'UNLISTED DIFFERENCE b.lean in working tree'),
                              ('archive recorded file at an older hash (no Git)', 'a.lean',
                               'UNLISTED DIFFERENCE a.lean in working tree')]:
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as out:
            root, rec, c = fixture(tmp)
            data = subprocess.run(['git', '-C', str(root), 'archive', 'HEAD'], check=True,
                                  capture_output=True).stdout
            archive = Path(out) / 'tree.tar'
            archive.write_bytes(data)
            with tarfile.open(archive) as tar:
                tar.extractall(Path(out) / 'x', **({'filter': 'data'} if hasattr(tarfile, 'data_filter') else {}))
            tree = Path(out) / 'x'
            if edit == 'b.lean':
                write(tree, 'b.lean', 'b1\n')
            elif edit == 'a.lean':
                write(tree, 'a.lean', 'a0\n')
            real = subprocess.run

            def no_git(*args, **kw):
                raise AssertionError('the bytes check ran a subprocess')
            subprocess.run = no_git
            try:
                findings = run_bytes_check(tree, report=lambda _: None)
            except FreezeError as exc:
                findings = [str(exc)]
            finally:
                subprocess.run = real
            expect(label, findings, want)
    print(f'fg-finality-freeze selftest: PASS ({cases} cases)')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--root', default=str(Path(__file__).resolve().parent.parent))
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--history', action='store_true')
    mode.add_argument('--packages', action='store_true')
    mode.add_argument('--selftest', action='store_true')
    mode.add_argument('--base')
    ap.add_argument('--revision')
    ap.add_argument('--tip')
    a = ap.parse_args()
    try:
        if a.selftest:
            selftest()
            return 0
        if a.revision and not a.history:
            ap.error('--revision needs --history')
        if a.check:
            findings = run_bytes_check(a.root)
        elif a.history:
            findings = run_check(a.root, a.revision)
        elif a.packages:
            ch = Checker(a.root)
            ch.load()
            ch.check_packages()
            findings = ch.findings
            if not findings:
                print(f'fg-finality-freeze packages: PASS ({len(ch.record["packages"])} records)')
        else:
            if not a.tip:
                ap.error('--base needs --tip')
            ch = Checker(a.root)
            ch.load()
            ch.check_range(a.base, a.tip)
            findings = ch.findings
            if not findings:
                print(f'fg-finality-freeze range: PASS {a.base}..{a.tip}')
    except FreezeError as exc:
        findings = [str(exc)]
    for f in findings:
        print(f)
    if findings:
        print(f'fg-finality-freeze: FAIL ({len(findings)} findings)')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

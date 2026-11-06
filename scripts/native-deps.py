#!/usr/bin/env python3
"""Opt-in native dependency compilation: prepare once, then run a command under the guarded toolchain.

Local Lake configuration stays unchanged. `prepare` builds dependency libraries with Lake and records
their exact identity; `run COMMAND...` checks it and supplies a toolchain overlay whose Lean wrapper
checks again before every elaboration. No project library is precompiled.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/native-deps'
FLAGS = 'Lake-v4.35 shared; -O3 -DNDEBUG -DLEAN_EXPORTING; dependency-only-v1'
LIBS = [('batteries', 'batteries_Batteries'), ('importGraph', 'importGraph_ImportGraph'),
        ('Qq', 'Qq_Qq'), ('aesop', 'aesop_Aesop'), ('proofwidgets', 'proofwidgets_ProofWidgets'),
        ('plausible', 'plausible_Plausible'), ('LeanSearchClient', 'LeanSearchClient_LeanSearchClient'),
        ('mathlib', 'mathlib_Mathlib')]


def key():
    h = hashlib.sha256(FLAGS.encode())
    for name in ['lean-toolchain', 'lake-manifest.json', 'scripts/native-deps.py']:
        h.update((ROOT / name).read_bytes())
    return h.hexdigest()


def libraries():
    return [ROOT / f'.lake/packages/{pkg}/.lake/build/lib/lib{name}.so' for pkg, name in LIBS]


def verify(full=True, restored=False):
    try:
        record = json.loads((OUT / 'identity.json').read_text())
        if record['key'] != key():
            raise ValueError('pinned inputs or native flags changed')
        for path, saved in zip(libraries(), record['libraries'], strict=True):
            stat = path.stat()
            if (not restored and [stat.st_size, stat.st_mtime_ns] != saved['stat']) or (
                    full and hashlib.sha256(path.read_bytes()).hexdigest() != saved['sha256']):
                raise ValueError(f'library mismatch: {path.name}')
        return record
    except (OSError, ValueError, KeyError) as error:
        raise SystemExit(f'native-deps: REFUSED: {error}; run scripts/native-deps.py prepare')


def main():
    mode, *args = sys.argv[1:]
    if mode == 'key':
        print(key())
    elif mode in ('prepare', 'restore'):
        if mode == 'prepare':
            subprocess.run(['lake', 'build', 'Mathlib:shared'], cwd=ROOT, check=True)
        else:
            # Archive extraction may change timestamps and paths, but never the recorded contents.
            verify(restored=True)
        tc = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True).strip())
        OUT.mkdir(parents=True, exist_ok=True)
        overlay = OUT / 'toolchain'
        (overlay / 'bin').mkdir(parents=True, exist_ok=True)
        for path in tc.iterdir():
            if path.name != 'bin':
                dest = overlay / path.name
                if not dest.exists():
                    dest.symlink_to(path, target_is_directory=path.is_dir())
        for path in (tc / 'bin').iterdir():
            dest = overlay / 'bin' / path.name
            if path.name != 'lean' and not dest.exists():
                dest.symlink_to(path)
        wrapper = overlay / 'bin/lean'
        wrapper.write_text('#!/bin/sh\nexec python3 ' + repr(str(Path(__file__).resolve())) + ' lean "$@"\n')
        wrapper.chmod(0o755)
        record = {'key': key(), 'toolchain': str(tc),
                  'libraries': [{'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
                                 'stat': [p.stat().st_size, p.stat().st_mtime_ns]} for p in libraries()]}
        (OUT / 'identity.json').write_text(json.dumps(record))
    elif mode in ('run', 'lean'):
        record = verify(full=mode == 'run')
        if mode == 'run':
            env = dict(os.environ, LAKE_OVERRIDE_LEAN='true', LEAN_SYSROOT=str(OUT / 'toolchain'))
            os.execvpe(args[0], args, env)
        tc = Path(record['toolchain'])
        # Queries must retain the real toolchain identity; load native code only for our four libraries.
        sources = [a for a in args if a.endswith('.lean')]
        own = any(Path(a).name in ('ConsensusLean.lean', 'ConsensusLeanTest.lean', 'Solution.lean', 'Challenge.lean')
                  or any(p in ('ConsensusLean', 'ConsensusLeanTest') for p in Path(a).parts) for a in sources)
        native = [f'--load-dynlib={p}' for p in [tc / 'lib/lean/libLake_shared.so', *libraries()]] if own else []
        os.execv(str(tc / 'bin/lean'), [str(tc / 'bin/lean'), *native, *args])
    else:
        raise SystemExit('usage: native-deps.py key|prepare|run COMMAND...|lean ARGS...')


if __name__ == '__main__':
    main()

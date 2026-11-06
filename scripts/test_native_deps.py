#!/usr/bin/env python3
"""The native wrapper refuses stale pinned inputs and library contents before executing Lean."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('native_deps', Path(__file__).with_name('native-deps.py'))
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


class GuardTests(unittest.TestCase):
    def test_stale_inputs_and_libraries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            native.ROOT = root
            native.OUT = root / 'output'
            native.OUT.mkdir()
            (root / 'scripts').mkdir()
            for name in ['lean-toolchain', 'lake-manifest.json', 'scripts/native-deps.py']:
                (root / name).write_text(name)
            records = []
            for path in native.libraries():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'original')
                records.append({'sha256': native.hashlib.sha256(path.read_bytes()).hexdigest(),
                                'stat': [path.stat().st_size, path.stat().st_mtime_ns]})
            record = {'key': native.key(), 'libraries': records}
            (native.OUT / 'identity.json').write_text(json.dumps(record))
            native.verify()
            for name in ['lean-toolchain', 'lake-manifest.json', 'scripts/native-deps.py']:
                original = (root / name).read_bytes()
                (root / name).write_bytes(b'changed')
                with self.assertRaisesRegex(SystemExit, 'REFUSED.*pinned inputs'):
                    native.verify()
                (root / name).write_bytes(original)
            path = native.libraries()[0]
            path.write_bytes(b'stale!!!')
            with self.assertRaisesRegex(SystemExit, 'REFUSED.*library mismatch'):
                native.verify()
            # Even a same-size mutation with its timestamp restored fails the full content check.
            original_stat = records[0]['stat']
            native.os.utime(path, ns=(path.stat().st_atime_ns, original_stat[1]))
            with self.assertRaisesRegex(SystemExit, 'REFUSED.*library mismatch'):
                native.verify()


if __name__ == '__main__':
    unittest.main()

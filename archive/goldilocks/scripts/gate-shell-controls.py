#!/usr/bin/env python3
"""Test shell failure paths with a fake Lake. Real Lean checks run separately."""

import os
import json
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time


REPO = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix="gate-shell-controls-") as scratch:
    root = Path(scratch)
    scripts = root / "scripts"
    scripts.mkdir()
    (root / ".lake").mkdir()
    for name in ("check-fgsa-manifest.sh", "check-fg.sh", "gate-common.sh",
                 "unported.py", "unported-libraries.txt", "gate_timing.py"):
        shutil.copy2(REPO / "scripts" / name, scripts / name)
    for name in ('api-snapshot.py', 'api-snapshot-controls.py', 'fgsa-deep-controls.py'):
        (scripts / name).write_text("import os,sys\n"
            "mode = os.environ['CONTROL_MODE']\n"
            "sys.exit(20 if mode == 'legacy-fail' and __file__.endswith('api-snapshot.py') "
            "else 17 if mode == 'setup-fail' and 'controls' in __file__ else 0)\n")
    # check-fg.sh reads its FG module list from the inventory writer.
    (scripts / "write-check-inventories.py").write_text(
        "import types\n"
        "snapshot = types.SimpleNamespace(SCOPES={'fg': 'fg'},\n"
        "    source_modules=lambda scope: ['Control.FG'])\n")
    (scripts / "current-inventory.py").write_text("")
    bindir = root / "bin"
    bindir.mkdir()
    lake = bindir / "lake"
    lake.write_text("""#!/usr/bin/env python3
import os
from pathlib import Path
import signal
import sys
import time
mode = os.environ['CONTROL_MODE']
Path('calls').open('a').write(' '.join(sys.argv[1:]) + '\\n')
if mode == 'freeze':
    Path(sys.argv[sys.argv.index('--manifest') + 1]).write_bytes(b'entry\\n\\n\\n')
elif mode == 'signal':
    Path('started').touch()
    while True:
        time.sleep(0.05)
elif mode == 'deep-fail' and '--deep' in sys.argv:
    sys.exit(19)
elif mode == 'fail' or (mode == 'setup-fail' and '--write' in sys.argv):
    sys.exit(17)
""")
    lake.chmod(0o755)
    env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ["PATH"])

    def run(name, mode, *args, **extra):
        result = subprocess.run(
            ["bash", str(scripts / name), *args], cwd=root,
            env=dict(env, CONTROL_MODE=mode, **extra), capture_output=True, text=True,
        )
        return result

    for mode, neg, rc in (("pass", "0", 0), ("fail", "0", 17),
                          ("deep-fail", "0", 19), ("legacy-fail", "0", 20),
                          ("setup-fail", "1", 17)):
        result = run("check-fgsa-manifest.sh", mode, NEG=neg, AUDIT_TIMING="1")
        assert result.returncode == rc, result
        assert not list((root / ".lake").glob("fgsa-manifest*"))
        print(f"CONTROL manifest cleanup {mode} (rc {rc}): PASS")

    retained = root / '.lake/retained'
    result = run('check-fgsa-manifest.sh', 'pass', NEG='0', AUDIT_TIMING='1',
                 GATE_LOG_DIR=str(retained), GATE_STEP='fgsa-manifest')
    assert result.returncode == 0, result
    records = list(retained.glob('timings/fgsa-manifest/*.json'))
    assert len(records) == 7, records
    for path in records:
        record = json.loads(path.read_text())
        assert record['queued'] <= record['start'] <= record['slot_acquired'] <= record['end']
        assert record['rc'] == 0 and record['peak_rss_bytes'] is not None, record
        assert Path(str(path) + '.stdout').exists() and Path(str(path) + '.stderr').exists()
    assert not list((root / '.lake').glob('fgsa-manifest*'))
    print('CONTROL manifest retained seven timing records and separate streams: PASS')

    child = subprocess.Popen(
        ["bash", str(scripts / "check-fgsa-manifest.sh")], cwd=root,
        env=dict(env, CONTROL_MODE="signal", NEG="0"), start_new_session=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    try:
        deadline = time.monotonic() + 10
        while not (root / "started").exists():
            assert time.monotonic() < deadline, "signal control did not start"
            time.sleep(0.01)
        os.killpg(child.pid, signal.SIGTERM)
        output, _ = child.communicate(timeout=10)
        assert child.returncode == 143, (child.returncode, output)
        assert not list((root / ".lake").glob("fgsa-manifest*"))
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
    print("CONTROL manifest cleanup TERM (rc 143): PASS")

    result = run("check-fg.sh", "fail", "--research-only")
    assert result.returncode == 17 and "NEEDS FRESH FG BUILD" in result.stdout, result
    assert "build --no-build" in (root / "calls").read_text()
    result = run("check-fg.sh", "fail")
    assert result.returncode == 17 and "BUILD FAILED" in result.stdout, result
    assert "build --wfail" in (root / "calls").read_text()
    result = run("check-fg.sh", "pass", "--unknown")
    assert result.returncode == 2, result
    print("CONTROL FG modes: stale build, failed build, unknown option: PASS")

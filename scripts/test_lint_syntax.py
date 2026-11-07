#!/usr/bin/env python3
"""Compiled negative controls for every deferred syntax linter and a clean control."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
CASES = {
    "style.whitespace": "theorem probe (n: Nat) : n = n := rfl\n",
    "unreachableTactic": "theorem probe : True := by trivial <;> done\n",
    "style.multiGoal": "theorem probe : True ∧ True := by\n  constructor\n  trivial\n  trivial\n",
    "style.cdot": "theorem probe : True ∧ True := by\n  constructor\n  . trivial\n  . trivial\n",
    "unusedTactic": "theorem probe : 1 = 1 := by\n  change 1 = 1\n  rfl\n",
    "unnecessarySeqFocus": "theorem probe : True := by apply id <;> trivial\n",
}


def main():
    template = json.loads(subprocess.check_output([
        "lake", "query", "--json", "+ConsensusLean.Spec.Problem.Basic:setup"], cwd=ROOT))
    template["name"] = "Probe"
    for name in CASES:
        template["options"]["weak.linter." + name] = False
    with tempfile.TemporaryDirectory(prefix="lint-fixtures-") as tmp:
        tmp = Path(tmp)
        (tmp / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        setup = tmp / ".lake/build/ir/Probe.setup.json"
        setup.parent.mkdir(parents=True)
        (tmp / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
        (tmp / ".lake/build/lib").symlink_to(ROOT / ".lake/build/lib", target_is_directory=True)
        setup.write_text(json.dumps(template))
        # Keep compiled Lean controls, but make Lake's query response independent of saved
        # setups. The fresh response remains valid when the saved setup is stale or absent.
        fresh = tmp / "fresh.json"
        fresh.write_text(json.dumps(template))
        bin_dir = tmp / "bin"
        bin_dir.mkdir()
        query = bin_dir / "lake"
        query.write_text('''#!/usr/bin/env python3
import json, sys
from pathlib import Path
assert sys.argv[1:3] == ["query", "--json"], sys.argv
for target in sys.argv[3:]:
    module = target.removeprefix("+").removesuffix(":setup")
    if Path("query-fails").exists() or module not in ("Probe", "ConsensusLean.Probe"):
        print("fixture setup query failed: " + module, file=sys.stderr)
        sys.exit(1)
    setup = json.loads(Path("fresh.json").read_text())
    setup["name"] = module
    print(json.dumps(setup))
''')
        query.chmod(0o755)
        env = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}"}
        for name, body in [*CASES.items(), ("clean", "theorem probe (n : Nat) : n = n := rfl\n")]:
            options = "".join(f"set_option linter.{other} false\n" for other in CASES if other != name)
            (tmp / "Probe.lean").write_text(
                "module\nimport ConsensusLean.Init\n\n/-! # Lint control -/\n\npublic section\n\n"
                + options + "\n" + body)
            normal = subprocess.run(["lean", "Probe.lean", "--setup", str(setup), "--json"], cwd=tmp,
                                    capture_output=True, text=True)
            assert normal.returncode == 0, (name, "normal", normal.stdout, normal.stderr)
            assert not any(json.loads(line).get("severity") == "warning"
                           for line in normal.stdout.splitlines()), (name, normal.stdout)
            lint = subprocess.run(["python3", "-I", str(ROOT / "scripts/lint-syntax.py"), "Probe"],
                                  cwd=tmp, env=env, capture_output=True, text=True)
            if name == "clean":
                assert lint.returncode == 0, (name, lint.stdout, lint.stderr)
            else:
                assert lint.returncode != 0 and "linter." + name in lint.stdout, (
                    name, lint.stdout, lint.stderr)
            print(f"lint-syntax fixture: PASS ({name})", flush=True)
        (tmp / "Probe.lean").write_text(
            "module\nimport ConsensusLean.Init\n\n/-! # Pinned message control -/\n\n"
            "/-- info: Nat : Type -/\n#guard_msgs in\n#check Nat\n")
        result = subprocess.run(["python3", "-I", str(ROOT / "scripts/lint-syntax.py"), "Probe"],
                                cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode == 0, result
        print("lint-syntax fixture: PASS (pinned messages unchanged)")
        stale = dict(template, importArts={"Missing.OldImport": [["/missing/old.olean"]]})
        setup.write_text(json.dumps(stale))
        command = ["python3", "-I", str(ROOT / "scripts/lint-syntax.py"), "Probe"]
        result = subprocess.run(command, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode == 0, (result.stdout, result.stderr)
        setup.unlink()
        result = subprocess.run(command, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode == 0, (result.stdout, result.stderr)
        (tmp / "query-fails").touch()
        result = subprocess.run(command, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode != 0 and "Lake setup query failed" in result.stdout, result
        assert "lint-syntax: Probe" not in result.stdout and "PASS" not in result.stdout, result
        (tmp / "query-fails").unlink()
        print("lint-syntax fixture: PASS (stale/missing setups ignored; query failure closed)")
        # Selection is exercised through the CLI, with real Git state and a real Lean warning.
        subprocess.run(["git", "init", "-q"], cwd=tmp, check=True)
        for name in ("ConsensusLean", "ConsensusLeanTest", "Solution", "Challenge"):
            (tmp / (name + ".lean")).write_text("module\n")
        subprocess.run(["git", "add", "."], cwd=tmp, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=noreply@openai.com",
                        "commit", "-qm", "Fixture base"], cwd=tmp, check=True)
        changed = ["python3", "-I", str(ROOT / "scripts/lint-syntax.py"), "--changed", "HEAD"]
        # No Lean edit, an unrelated script, and a workflow must not select unbuilt roots.
        for path in ("scripts/other.py", ".github/workflows/check.yml"):
            target = tmp / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("# unrelated\n")
        result = subprocess.run(changed, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode == 0 and "PASS (0 modules" in result.stdout, result
        source = tmp / "ConsensusLean/Probe.lean"
        source.parent.mkdir()
        source.write_text("module\nimport ConsensusLean.Init\n\n/-! # Control -/\n\n"
                          "public theorem probe (n: Nat) : n = n := rfl\n")
        selected_setup = tmp / ".lake/build/ir/ConsensusLean/Probe.setup.json"
        selected_setup.parent.mkdir()
        template["name"] = "ConsensusLean.Probe"
        selected_setup.write_text(json.dumps(template))
        result = subprocess.run(changed, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode != 0 and "linter.style.whitespace" in result.stdout, result
        subprocess.run(["git", "add", "ConsensusLean/Probe.lean"], cwd=tmp, check=True)
        result = subprocess.run(changed, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode != 0 and "linter.style.whitespace" in result.stdout, result
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=noreply@openai.com",
                        "commit", "-qm", "Tracked control"], cwd=tmp, check=True)
        source.write_text(source.read_text().replace("(n: Nat)", "(n : Nat)"))
        result = subprocess.run(changed, cwd=tmp, env=env, capture_output=True, text=True)
        assert result.returncode == 0 and "PASS (1 modules" in result.stdout, result
        source.unlink()
        # Each elaboration-affecting path must expand to the unbuilt whole-library roots.
        for path in ("lakefile.toml", "lean-toolchain", "lake-manifest.json",
                     "scripts/pins.toml", "scripts/lint-syntax.py"):
            target = tmp / path
            original = target.read_text() if target.exists() else None
            target.write_text((original or "") + "\n")
            result = subprocess.run(changed, cwd=tmp, env=env, capture_output=True, text=True)
            assert result.returncode != 0 and "fixture setup query failed: ConsensusLean" in result.stdout, result
            if original is None:
                target.unlink()
            else:
                target.write_text(original)
        print("lint-syntax fixture: PASS (changed selection and configuration fallback)")
    # Real Lake/Lean integration: change both the imported module and constructor signature,
    # leaving the consumer's saved setup untouched as an artifact hit would.
    with tempfile.TemporaryDirectory(prefix="lint-fresh-setup-") as tmp:
        tmp = Path(tmp)
        (tmp / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        (tmp / "lakefile.toml").write_text('name = "setup-fixture"\n' + "".join(
            f'[[lean_lib]]\nname = "{name}"\n' for name in ("Probe", "Old", "New")))
        (tmp / "Old.lean").write_text("structure Run where\n  old : Nat\n")
        (tmp / "New.lean").write_text("structure Run where\n  current : Bool\n  extra : Nat\n")
        consumer = tmp / "Probe.lean"
        consumer.write_text("import Old\ndef probe := Run.mk 1\n")
        subprocess.run(["lake", "build", "+Probe"], cwd=tmp, check=True)
        saved = tmp / ".lake/build/ir/Probe.setup.json"
        stale = saved.read_text()
        consumer.write_text("import New\ndef probe := Run.mk true 2\n")
        subprocess.run(["lake", "build", "+New"], cwd=tmp, check=True)
        old = subprocess.run(["lean", "Probe.lean", "--setup", str(saved)], cwd=tmp,
                             capture_output=True, text=True)
        assert old.returncode != 0, old
        command = ["python3", "-I", str(ROOT / "scripts/lint-syntax.py"), "Probe"]
        result = subprocess.run(command, cwd=tmp, capture_output=True, text=True)
        assert result.returncode == 0, (result.stdout, result.stderr)
        assert saved.read_text() == stale, "setup query must not rely on refreshing the saved file"
        saved.unlink()
        result = subprocess.run(command, cwd=tmp, capture_output=True, text=True)
        assert result.returncode == 0, (result.stdout, result.stderr)
        (tmp / "New.lean").unlink()
        result = subprocess.run(command, cwd=tmp, capture_output=True, text=True)
        assert result.returncode != 0 and "Lake setup query failed" in result.stdout, result
        assert "PASS" not in result.stdout, result
        print("lint-syntax fixture: PASS (real Lake stale imports/signature, missing setup, failed query)")
        (tmp / "New.lean").write_text("structure Run where\n  current : Bool\n  extra : Nat\n")
        env = {**os.environ, "LAKE_CACHE_DIR": str(tmp / "cache"),
               "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true"}
        subprocess.run(["lake", "build", "+Probe"], cwd=tmp, env=env, check=True)
        shutil.rmtree(tmp / ".lake/build")
        env["LAKE_RESTORE_ARTIFACTS"] = "false"
        subprocess.run(["lake", "build", "+Probe"], cwd=tmp, env=env, check=True)
        olean = tmp / ".lake/build/lib/lean/Probe.olean"
        assert not olean.exists(), "control: cache hit without restoration leaves no local olean"
        env["LAKE_RESTORE_ARTIFACTS"] = "true"
        subprocess.run(["lake", "build", "+Probe"], cwd=tmp, env=env, check=True)
        assert olean.exists(), "full restoration must restore the local olean"
        assert not saved.exists(), "artifact restoration does not regenerate setups"
        print("lint-syntax fixture: PASS (artifact restoration recovers oleans, not setups)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

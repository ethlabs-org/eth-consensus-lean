#!/usr/bin/env python3
"""Compiled negative controls for every deferred syntax linter and a clean control."""
import json
from pathlib import Path
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
    template = json.loads((ROOT / ".lake/build/ir/ConsensusLean/Spec/Problem/Basic.setup.json").read_text())
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
                                  cwd=tmp, capture_output=True, text=True)
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
                                cwd=tmp, capture_output=True, text=True)
        assert result.returncode == 0, result
        print("lint-syntax fixture: PASS (pinned messages unchanged)")
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
        result = subprocess.run(changed, cwd=tmp, capture_output=True, text=True)
        assert result.returncode == 0 and "PASS (0 modules" in result.stdout, result
        source = tmp / "ConsensusLean/Probe.lean"
        source.parent.mkdir()
        source.write_text("module\nimport ConsensusLean.Init\n\n/-! # Control -/\n\n"
                          "public theorem probe (n: Nat) : n = n := rfl\n")
        selected_setup = tmp / ".lake/build/ir/ConsensusLean/Probe.setup.json"
        selected_setup.parent.mkdir()
        template["name"] = "ConsensusLean.Probe"
        selected_setup.write_text(json.dumps(template))
        result = subprocess.run(changed, cwd=tmp, capture_output=True, text=True)
        assert result.returncode != 0 and "linter.style.whitespace" in result.stdout, result
        subprocess.run(["git", "add", "ConsensusLean/Probe.lean"], cwd=tmp, check=True)
        result = subprocess.run(changed, cwd=tmp, capture_output=True, text=True)
        assert result.returncode != 0 and "linter.style.whitespace" in result.stdout, result
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=noreply@openai.com",
                        "commit", "-qm", "Tracked control"], cwd=tmp, check=True)
        source.write_text(source.read_text().replace("(n: Nat)", "(n : Nat)"))
        result = subprocess.run(changed, cwd=tmp, capture_output=True, text=True)
        assert result.returncode == 0 and "PASS (1 modules" in result.stdout, result
        source.unlink()
        # Each elaboration-affecting path must expand to the unbuilt whole-library roots.
        for path in ("lakefile.toml", "lean-toolchain", "lake-manifest.json",
                     "scripts/pins.toml", "scripts/lint-syntax.py"):
            target = tmp / path
            original = target.read_text() if target.exists() else None
            target.write_text((original or "") + "\n")
            result = subprocess.run(changed, cwd=tmp, capture_output=True, text=True)
            assert result.returncode != 0 and "ConsensusLean.setup.json" in result.stderr, result
            if original is None:
                target.unlink()
            else:
                target.write_text(original)
        print("lint-syntax fixture: PASS (changed selection and configuration fallback)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

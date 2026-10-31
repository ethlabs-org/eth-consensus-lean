#!/usr/bin/env python3
"""Seed-policy fixtures; no compiler or shared cache needed."""
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("worktree-setup.py").resolve()


class WorktreeSetupTest(unittest.TestCase):
    def test_seed_isolation_and_refusals(self):
        with tempfile.TemporaryDirectory() as tmp:
            source, dest = Path(tmp) / "source", Path(tmp) / "dest"
            for root in (source, dest):
                root.mkdir()
                for name, text in (("lean-toolchain", "leanprover/lean4:v4.35.0\n"),
                                   ("lakefile.toml", "name = 'fixture'\n"),
                                   ("lake-manifest.json", "{}\n")):
                    (root / name).write_text(text)
            outputs = (".olean", ".olean.server", ".olean.private", ".ilean",
                       ".ir", ".ir.sig", ".c", ".bc", ".ltar")
            linked = {"build/lib/lean/Foo" + suffix for suffix in outputs}
            linked.add("packages/pkg/.lake/build/lib/lean/Dep.olean")
            paths = (*sorted(linked), "build/lib/lean/Foo.trace",
                     "build/lib/lean/Foo.olean.hash", "build/ir/Foo.setup.json",
                     "build/ir/Foo.c.o", "build/bin/tool",
                     "build/lib/libFoo.so", "build/lib/libFoo.a", "build/bin/tool.rsp",
                     "packages/pkg/.lake/build/lib/lean/Dep.trace",
                     "packages/pkg/Foo.c", "packages/pkg/.git/config")
            for rel in paths:
                path = source / ".lake" / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(rel)
            (source / ".lake/packages/pkg/link").symlink_to("Foo.c")

            def run():
                return subprocess.run(["python3", "-I", str(SCRIPT), str(source), str(dest)],
                                      capture_output=True, text=True)

            # Configuration mismatch fails before publishing anything.
            (dest / "lakefile.toml").write_text("different")
            self.assertNotEqual(run().returncode, 0)
            self.assertFalse((dest / ".lake").exists())
            (dest / "lakefile.toml").write_bytes((source / "lakefile.toml").read_bytes())
            result = run()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((dest / ".lake/packages/pkg/link").is_symlink())
            for rel in paths:
                src, dst = source / ".lake" / rel, dest / ".lake" / rel
                self.assertEqual(src.read_bytes(), dst.read_bytes())
                self.assertEqual(src.stat().st_ino == dst.stat().st_ino, rel in linked, rel)
                # Model Lake's unlink-before-write for Lean outputs and its in-place
                # writes for bookkeeping/native tools; both must preserve source.
                if rel in linked:
                    dst.unlink()
                dst.write_text("rebuilt")
                self.assertEqual(src.read_text(), rel)
            self.assertNotEqual(run().returncode, 0)
            self.assertEqual((dest / ".lake/build/bin/tool").read_text(), "rebuilt")

    def test_build_symlink_is_rejected_atomically(self):
        with tempfile.TemporaryDirectory() as tmp:
            source, dest = Path(tmp) / "source", Path(tmp) / "dest"
            for root in (source, dest):
                root.mkdir()
                for name in ("lakefile.toml", "lake-manifest.json"):
                    (root / name).write_text("")
                (root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0")
            (source / ".lake/packages").mkdir(parents=True)
            (source / ".lake/build").symlink_to(source / ".lake/packages", target_is_directory=True)
            result = subprocess.run(["python3", "-I", str(SCRIPT), str(source), str(dest)],
                                    capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((dest / ".lake").exists())
            self.assertEqual(list(dest.glob(".lake-seed-*")), [])
            (source / ".lake/build").unlink()
            (source / ".lake/build/ir").mkdir(parents=True)
            (source / ".lake/build/ir/generated").symlink_to(
                source / ".lake/packages", target_is_directory=True)
            result = subprocess.run(["python3", "-I", str(SCRIPT), str(source), str(dest)],
                                    capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((dest / ".lake").exists())
            self.assertEqual(list(dest.glob(".lake-seed-*")), [])


if __name__ == "__main__":
    unittest.main()

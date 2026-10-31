#!/usr/bin/env python3
"""Seed a fresh worktree's .lake from a quiescent, same-filesystem warm checkout.

Only Lean 4.35 outputs which Lake unlinks before rebuilding are hard-linked.
Bookkeeping, native outputs and package sources get independent copies.
"""
import argparse
import os
from pathlib import Path
import shutil
import tempfile


# Lake/Build/Module.lean: clearOutputArtifacts, called before compileLeanModule.
# Do not include .hash, .trace or .setup.json: Lake writes those in place.
LEAN_OUTPUTS = (".olean", ".olean.server", ".olean.private", ".ilean",
                ".ir", ".ir.sig", ".c", ".bc", ".ltar")


def seed(source, destination):
    source, destination = source.resolve(), destination.resolve()
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        if (source / name).read_bytes() != (destination / name).read_bytes():
            raise ValueError(f"{name} differs; use a matching warm checkout")
    if (destination / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0":
        raise ValueError("hard-link policy is audited only for Lean v4.35.0")
    lake = destination / ".lake"
    if lake.exists() or lake.is_symlink():
        raise ValueError("destination .lake already exists; refusing to merge or overwrite")
    if not (source / ".lake/packages").is_dir():
        raise ValueError("source has no warm .lake/packages")
    if source.stat().st_dev != destination.stat().st_dev:
        raise ValueError("source and destination must be on the same filesystem")

    def ignore(directory, names):
        # Preserve source symlinks (e.g. batteries/docs/README.md is tracked as one),
        # but never alias writable build directories or outputs through symlinks.
        path = Path(directory)
        relative = path.relative_to(source / ".lake")
        in_build = relative.parts and (relative.parts[0] == "build" or (
            len(relative.parts) > 3 and relative.parts[0] == "packages"
            and relative.parts[2:4] == (".lake", "build")))
        for name in names:
            child = path / name
            if child.is_symlink() and (in_build or name in (".lake", "build")):
                raise ValueError(f"symlinked build tree is not supported: {child}")
        return []

    def copy_file(src, dst):
        path = Path(src)
        relative = path.relative_to(source / ".lake")
        # Restrict to actual build directories, not e.g. a dependency's source Foo.c.
        in_build = relative.parts[0] == "build" or (
            len(relative.parts) > 3 and relative.parts[0] == "packages"
            and relative.parts[2:4] == (".lake", "build"))
        if in_build and not path.is_symlink() and path.name.endswith(LEAN_OUTPUTS):
            os.link(src, dst)
        else:
            shutil.copy2(src, dst)
        return dst

    # Publish only a complete seed; failures (including cross-device mounts) leave no .lake.
    with tempfile.TemporaryDirectory(prefix=".lake-seed-", dir=destination) as tmp:
        staging = Path(tmp) / ".lake"
        staging.mkdir()
        for name in ("packages", "build"):
            if (source / ".lake" / name).exists():
                if (source / ".lake" / name).is_symlink():
                    raise ValueError(f"symlinked {name} tree is not supported")
                shutil.copytree(source / ".lake" / name, staging / name,
                                copy_function=copy_file, symlinks=True, ignore=ignore)
        staging.rename(lake)
    print(f"Seeded {lake} from {source}; run builds with LAKE_RESTORE_ARTIFACTS=true")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="quiescent warm checkout (never a live watcher tree)")
    parser.add_argument("destination", type=Path, nargs="?", default=Path.cwd(),
                        help="fresh worktree (default: current directory)")
    args = parser.parse_args()
    try:
        seed(args.source, args.destination)
    except (OSError, ValueError) as error:
        parser.exit(1, f"worktree-setup: {error}\n")


if __name__ == "__main__":
    main()

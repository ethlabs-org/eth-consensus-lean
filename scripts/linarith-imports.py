#!/usr/bin/env python3
"""Add `import ConsensusLean.Lemmas.Tactic.Linarith` to every module that calls plain linarith.

The front end (ConsensusLean/Lemmas/Tactic/Linarith.lean) only acts in modules that import it,
directly or through an import. This script gives it to each module of the default libraries that
calls plain `linarith`/`nlinarith` (no `!`, no `only`, no configuration: the only forms it changes)
and may import the Lemmas layer (scripts/boundaries.toml), never a trusted path (`trusted_paths`).
Comments, docstrings and strings are blanked before any matching, and only the module header
(`module`, import lines, blank lines and comments up to the first other line) counts as imports.
It adds one private import after the header's last import line and touches nothing else; a
module that imports the root `ConsensusLean` already reaches the front end and is left alone.

A module in `EXEMPT` is left without the import, for the reason recorded there (measured: the
front end does not make its elaboration cheaper). An entry that no longer applies (the module is
gone, calls no plain `linarith`, or imports the front end) is stale and fails both modes.

  python3 -I scripts/linarith-imports.py          # add the missing imports, list the files
  python3 -I scripts/linarith-imports.py --check  # list them and exit 1 if any is missing
"""
import argparse
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
FRONT_END = "ConsensusLean.Lemmas.Tactic.Linarith"
IMPORT = f"import {FRONT_END}"
LIBS = ("ConsensusLean", "ConsensusLeanTest")
CALL = re.compile(r"(?<![\w.'])n?linarith(?![\w'!?])(?!\s*(?:only\b|\(config\b|[+-][a-zA-Z]))")
IMPORT_LINE = re.compile(r"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$")
# Module -> why it stays without the front end. Instruction counts (`perf stat -e instructions:u`,
# the module elaborated alone) with and without the import.
EXEMPT = {
    "ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionCompatibility":
        "10.7% more instructions with it: its `nlinarith` needs the Nat casts, so the cheap attempt "
        "fails and the call runs twice",
    "ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift":
        "not cheaper with it (0.2% more instructions)",
    "ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read":
        "not cheaper with it (instructions unchanged)",
    "ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Cast":
        "not cheaper with it (instructions unchanged)",
}


def header(code):
    """The header's imported modules and the index of its last line (`module`/import lines,
    blank lines and comments, up to the first other line), read from the comment-stripped code."""
    imports, last = [], None
    for k, line in enumerate(code.split("\n")):
        stripped = line.strip()
        if not stripped:
            continue
        match = IMPORT_LINE.fullmatch(stripped)
        if match:
            imports.append(match.group(1))
            last = k
        elif stripped == "module" and last is None:
            last = k
        else:
            break
    return imports, last


def strip_comments(text):
    """Blank nested `/- -/` blocks (docstrings too), `--` line comments and string literals.

    Every newline survives, so line `k` of the result is line `k` of the source."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(" " + "\n" * text.count("\n", i, j + 1))
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def layers(root):
    config = tomllib.loads((root / "scripts/boundaries.toml").read_text())
    trusted = config["checks"]["trusted_paths"]
    may_import = []
    for layer in config["layer"]:
        if layer["name"] == "Lemmas" or "Lemmas" in layer.get("allow", []):
            may_import += layer["prefixes"]
    return trusted, may_import


def candidates(root):
    trusted, may_import = layers(root)
    for lib in LIBS:
        for path in sorted((root / lib).rglob("*.lean")):
            relative = path.relative_to(root).as_posix()
            name = ".".join(path.relative_to(root).with_suffix("").parts)
            if name == FRONT_END or any(relative == t or relative.startswith(t.removesuffix(".lean") + "/")
                                        for t in trusted):
                continue
            if not any(name == p or name.startswith(p + ".") for p in may_import):
                continue
            text = path.read_text()
            code = strip_comments(text)
            if CALL.search(code):
                yield path, name, text, code


def main(argv=None, root=ROOT, exempt=EXEMPT):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="report missing imports, change nothing")
    args = parser.parse_args(argv)
    missing, present, exempted, importing = [], 0, set(), set()
    for path, name, text, code in candidates(root):
        imports, last = header(code)
        # A module that imports the root ConsensusLean (some tests) already reaches the front end.
        if FRONT_END in imports or "ConsensusLean" in imports:
            present += 1
            if name in exempt:
                importing.add(name)
            continue
        if name in exempt:
            exempted.add(name)
            continue
        if last is None:
            raise SystemExit(f"linarith-imports: {path.relative_to(root)}: no module header found")
        missing.append(path)
        if not args.check:
            lines = text.split("\n")
            path.write_text("\n".join(lines[:last + 1] + [IMPORT] + lines[last + 1:]))
    for path in missing:
        print(path.relative_to(root).as_posix())
    stale = sorted(set(exempt) - exempted)
    for name in stale:
        why = "imports the front end" if name in importing else "no module that may import it calls plain linarith"
        print(f"stale exemption: {name} ({why})")
    verb = "missing" if args.check else "added"
    print(f"linarith-imports: {present + len(exempted) + len(missing)} calling modules, {present} already import "
          f"{FRONT_END}, {len(exempted)} exempt, {len(missing)} {verb}, {len(stale)} stale exemptions",
          file=sys.stderr)
    return 1 if stale or (args.check and missing) else 0


if __name__ == "__main__":
    sys.exit(main())

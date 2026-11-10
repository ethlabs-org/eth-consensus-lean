#!/usr/bin/env python3
"""Add `import ConsensusLean.Lemmas.Tactic.Linarith` to every module that calls plain linarith.

The front end (ConsensusLean/Lemmas/Tactic/Linarith.lean) only acts in modules that import it,
directly or through an import. This script gives it to each module of the checked libraries (the
`[[lib]]` entries of scripts/boundaries.toml: a library's root file and every file under its
directory) that calls plain `linarith`/`nlinarith` (no `!`, no `only`, no configuration such as
`(config := c)`, `(preprocessors := ps)` or `-flag`: the only forms it changes) and may import the
Lemmas layer, never a trusted path (`trusted_paths`). Comments, docstrings and strings are blanked
before any matching, and only the module header (Lean's `[module] [prelude]`, then `[public]
[meta] import [all] M` commands, whose tokens may be split over lines) counts as imports. The scan
is lexical: the word `linarith` or `nlinarith` outside comments and strings counts as a call unless
one of those forms follows (a `«linarith»` identifier does not count; a bare one, such as a
declaration named `linarith`, does).
It adds one private import on a new line right after the header's last token (anything that
followed that token on its line, a comment for instance, moves after the new import) and touches
nothing else; a module that imports the root `ConsensusLean` already reaches the front end and is
left alone.

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
# Not counted: identifier characters around the word (`foo_linarith`, `X.linarith`, `«linarith»`),
# `!`/`?` variants, and a following `only`, `(field := ...)` configuration or `-flag`/`+flag`.
CALL = re.compile(r"(?<![\w.'«])n?linarith(?![\w'!?»])"
                  r"(?!\s*(?:only\b|\(\s*[^\W\d][\w.']*\s*:=|[+-][a-zA-Z]))")
TOKEN = re.compile(r"\S+")
# Module -> why it stays without the front end. Instruction counts (`perf stat -e instructions:u`,
# the module elaborated alone) with and without the import.
EXEMPT = {
    "ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift":
        "no demonstrated gain (0.2% more instructions, within the 0.3% spread of the measurement)",
    "ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read":
        "no demonstrated gain (instructions unchanged)",
    "ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Cast":
        "no demonstrated gain (instructions unchanged)",
}

# The import commands, token by token: state -> {keyword: next state}; any other token in state
# "import"/"all" is the module name (the command ends), in any other state it ends the header.
HEADER_STEPS = {
    "command": {"public": "public", "meta": "meta", "import": "import"},
    "public": {"meta": "meta", "import": "import"},
    "meta": {"import": "import"},
    "import": {"all": "all"},
    "all": {},
}


def header(code):
    """The header's imported modules and the offset just past its last token, read from the
    comment-stripped code by Lean's header grammar `[module] [prelude] import*`, each import a
    `[public] [meta] import [all] M` command, tokens separated by any whitespace (newlines
    included). The offset is None without a header."""
    imports, end, state = [], None, "command"
    opening = ["module", "prelude"]  # the keywords that may still come before the imports, in order
    for match in TOKEN.finditer(code):  # stops at the first token after the header
        word = match.group()
        if word in opening and state == "command" and not imports:
            opening = opening[opening.index(word) + 1:]
            end = match.end()
        elif word in HEADER_STEPS[state]:
            state = HEADER_STEPS[state][word]
        elif state in ("import", "all"):
            imports.append(word)
            end, state = match.end(), "command"
        else:
            break
    return imports, end


def strip_comments(text):
    """Blank nested `/- -/` blocks (docstrings too), `--` line comments and string literals.

    Newlines stay and every other blanked character becomes a space, so an offset into the result
    is the same offset into the source."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            out.append("  ")
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            out.append("  ")
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, len(text))
            out.append("".join("\n" if c == "\n" else " " for c in text[i:j]))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def config(root):
    """The checked libraries, the trusted paths and the module prefixes that may import Lemmas."""
    cfg = tomllib.loads((root / "scripts/boundaries.toml").read_text())
    may_import = []
    for layer in cfg["layer"]:
        if layer["name"] == "Lemmas" or "Lemmas" in layer.get("allow", []):
            may_import += layer["prefixes"]
    return [lib["name"] for lib in cfg["lib"]], cfg["checks"]["trusted_paths"], may_import


def candidates(root):
    """Every module of a checked library that may import the front end and calls plain linarith:
    (path, module, source, comment-stripped source)."""
    libs, trusted, may_import = config(root)
    for lib in libs:
        for path in sorted({root / f"{lib}.lean", *(root / lib).rglob("*.lean")}):
            if not path.is_file():
                continue
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
        imports, end = header(code)
        # A module that imports the root ConsensusLean (some tests) already reaches the front end.
        if FRONT_END in imports or "ConsensusLean" in imports:
            present += 1
            if name in exempt:
                importing.add(name)
            continue
        if name in exempt:
            exempted.add(name)
            continue
        if end is None:
            raise SystemExit(f"linarith-imports: {path.relative_to(root)}: no module header found")
        missing.append(path)
        if not args.check:
            path.write_text(text[:end] + "\n" + IMPORT + text[end:])
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

#!/usr/bin/env python3
"""Doc checks of scripts/check.sh step 12 that need no build (both run in milliseconds).

names <index.lean> <doc.md>...
    Every token `Consensus.<...>` anywhere in the docs (prose, inline code and fenced code alike; the token runs to
    the next space or punctuation mark of `TOKEN_END`, trailing dots dropped; a closing `'`, `!` or `?` stays part
    of it) is a cited name: it must be a plain name (identifier characters only; anything else, e.g.
    `Consensus.«x»`, fails rather than being truncated) and be listed in the index as a line `example := ``Name`.
    The index may hold only `module`, `[public] import M`, those lines and comments (nested block comments and line
    comments), so every listed line is elaborated as written: no string literal, `#guard_msgs`, `#exit`, `open` or
    `namespace` can hide or redirect one. The index is built by `lake test`, and a resolved name literal ``Name
    fails unless Name is a declaration (`@Name` would also accept a field of a constant), so a cited name is checked
    to exist (as FLT's and Carleson's `checkdecls` check their blueprints). A missing doc or index, or no doc,
    fails.

codeowners <CODEOWNERS> <root> <owner> <path>...
    The patterns of the CODEOWNERS file are exactly the given paths (`[checks] trusted_paths` and
    `codeowners_extra` of scripts/boundaries.toml), once each, anchored (`/path`, or `/path/` when <root>/path is
    a directory), each owned by exactly <owner>, so the owner list cannot drift from the surface that CI's
    review-boundary job checks.

Each failure prints `FAIL[docs] ...`; the exit status is 1 on any failure.
"""
import re, sys
from pathlib import Path

COMPONENT = r"[\w'!?₀-₉ₐ-ₜ]+"  # \w is Unicode in Python 3
NAME = r"Consensus(?:\." + COMPONENT + r")+"
TOKEN_END = "`,;:()[]{}|*\"<>"
# A token starts after anything but a letter or digit (also after `'`, `.` of `_root_.`, `_` of `_emphasis_`).
TOKEN = re.compile(r"(?<![^\W_])Consensus\.[^\s" + re.escape(TOKEN_END) + r"]*")
INDEX_LINE = re.compile(r"module|(public )?import \S+|example := ``(" + NAME + r")")

def strip_comments(src):  # as scripts/check-boundaries.py: nested block comments and line comments become blanks
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; out.append("  "); continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; out.append("  "); continue
        if not depth and src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(src[i] if not depth or src[i] == "\n" else " "); i += 1
    return "".join(out)

def read(path, what, fails):
    try:
        return Path(path).read_text(encoding="utf-8")
    except OSError as e:
        fails.append(f"FAIL[docs] cannot read {what} {path}: {e.strerror}")
        return None

def names(index, docs):
    fails, listed = [], set()
    src = read(index, "name index", fails)
    if src is not None:
        for k, line in enumerate(strip_comments(src).splitlines(), 1):
            line = line.strip()
            if not line:
                continue
            m = INDEX_LINE.fullmatch(line)
            if not m:
                fails.append(f"FAIL[docs] {index}:{k}: not a `module`, `import` or `example := ``Name` line: {line[:60]}")
            elif m.group(2):
                listed.add(m.group(2))
    if not docs:
        fails.append("FAIL[docs] no doc files given")
    total = 0
    for d in docs:
        text = read(d, "doc", fails)
        if text is None:
            continue
        cited = set()
        for tok in (t.rstrip(".") for t in TOKEN.findall(text)):
            if re.fullmatch(NAME, tok):
                cited.add(tok)
            else:
                fails.append(f"FAIL[docs] {d}: `{tok}` is not a plain name (identifier characters only)")
        total += len(cited)
        for n in sorted(cited - listed):
            fails.append(f"FAIL[docs] {d} cites `{n}`, which {index} does not list (example := ``{n})")
    if not fails:
        print(f"  {total} names cited in {len(docs)} docs, all listed in {index}")
    return fails

def codeowners(path, root, owner, paths):
    fails, seen = [], set()
    text = read(path, "CODEOWNERS", fails)
    if text is None:
        return fails
    for k, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        pat, *owners = line.split()
        where = f"{path}:{k}: {pat}"
        if not pat.startswith("/") or pat == "/" or "//" in pat:
            fails.append(f"FAIL[docs] {where} is not anchored to the repository root"); continue
        p = pat.strip("/")
        if pat.endswith("/") and not (Path(root) / p).is_dir():
            fails.append(f"FAIL[docs] {where} has a trailing slash, but {p} is not a directory (write {pat.rstrip('/')})")
        if owners != [owner]:
            fails.append(f"FAIL[docs] {where} is owned by {' '.join(owners) or 'nobody'}, not exactly {owner}")
        if p in seen:
            fails.append(f"FAIL[docs] {where} is listed twice (the last match wins)")
        seen.add(p)
    want = set(paths)
    if not want:
        fails.append("FAIL[docs] no paths given")
    for p in sorted(seen - want):
        fails.append(f"FAIL[docs] {path} lists {p}, which is not a trusted path or a codeowners_extra entry")
    for p in sorted(want - seen):
        fails.append(f"FAIL[docs] {path} does not list {p}")
    if not fails:
        print(f"  {path} lists exactly the {len(want)} paths, each owned by {owner}")
    return fails

def main(argv):
    if len(argv) >= 2 and argv[0] == "names":
        fails = names(argv[1], argv[2:])
    elif len(argv) >= 4 and argv[0] == "codeowners":
        fails = codeowners(argv[1], argv[2], argv[3], argv[4:])
    else:
        print(__doc__, file=sys.stderr)
        return 2
    for f in fails:
        print(f)
    return 1 if fails else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

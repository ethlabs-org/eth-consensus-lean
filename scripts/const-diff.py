#!/usr/bin/env python3
"""Compare two constant dumps of scripts/ConstDump.lean: did a change alter anything but proofs? Report-only
(docs/notes/build-speed.md "Statement equivalence"); its self-test runs in check.sh, the comparison does not.

Compared: every constant whose scope is `root` or `reached` in either dump, that is every public constant and
every internal or private constant that a compared type or definition value refers to (transitively), with the
`implemented_by` targets and `partial` bodies of compared constants and the non-`Prop` field defaults of compared
structures (scripts/ConstDump.lean). A compared
constant fails when it is removed or added, or its kind, universe parameters (names, in order), type, value
(definition and opaque bodies, inductive shape, constructor and recursor data) or safety changes, or its axiom
set changes in either direction. Theorem proofs are not compared (proof irrelevance), also inside definitions and
statements (internal and private theorems, such as `foo._proof_1`, hash as one tag), nor are auxiliary and
private constants that no compared constant refers to (proofs may use them): those are counted. A constant that
moved module is reported. Axioms are collected over every copy of a theorem that several modules declare alike,
and such a name whose copies' axioms differ is compared.

Not compared: attributes (`@[simp]`, `@[instance]`, reducibility; `implemented_by` only through its target),
`@[extern]` code, notation and options, binder names and kinds, and the dependencies (same lake-manifest.json
is assumed). Hashes are 64-bit structural hashes, not collision-resistant: evidence for honest edits, not
against a constructed collision. Only the modules dumped are compared: `Challenge` (it declares the review
statements again, as `Solution` does) needs a dump of its own.

Every exception is named: `--allow-added N`, `--allow-removed N`, `--allow-type N`, `--allow-value N`,
`--allow-axioms N` (repeatable) accept that one difference of that one constant, are printed, and fail when they
match nothing. A proof written as a term inside a statement stays inline (a `by` block becomes `foo._proof_1`,
compared by proof irrelevance, and definitions abstract every nested proof), so changing such a term changes
the statement's hash: check the statement and `--allow-type` it.
A public reserved name that proofs realize on demand (`foo.congr_simp`) disappears when the last proof that
realized it changes; a user of the name realizes it again, so `--allow-removed` it after checking that.

Usage: python3 -I scripts/const-diff.py <base.tsv> <new.tsv> [--allow-added N]... [--allow-removed N]...
       [--allow-type N]... [--allow-value N]... [--allow-axioms N]...
Make each dump in its own built worktree:
  lake build const-dump && lake exe const-dump <out.tsv> ConsensusLean Solution ConsensusLeanTest
"""
import argparse
import sys

FIELDS = ("module", "kind", "levels", "type", "value", "safety", "axioms", "scope")


def load(path):
    d = {}
    with open(path) as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if len(p) != 1 + len(FIELDS) or p[-1] not in ("root", "reached", "-"):
                raise SystemExit(f"{path}: malformed line: {line!r}")
            if p[0] in d:
                raise SystemExit(f"{path}: duplicate constant {p[0]}")
            rec = dict(zip(FIELDS, p[1:]))
            rec["axioms"] = frozenset(a for a in rec["axioms"].split(",") if a)
            d[p[0]] = rec
    if not d:
        raise SystemExit(f"{path}: no constants")
    return d


def compare(a, b, allow):
    """(failures, notes) for base dump `a` and new dump `b`; `allow` maps a kind of difference to names."""
    fail, notes, used = [], [], set()

    def diff(what, n, text):
        if n in allow.get(what, ()):
            used.add((what, n))
            notes.append(f"{text} (allowed: --allow-{what})")
        else:
            fail.append(text)

    scope = {n for d in (a, b) for n, r in d.items() if r["scope"] != "-"}
    for n in sorted(scope):
        x, y = a.get(n), b.get(n)
        if y is None:
            diff("removed", n, f"removed {n}")
            continue
        if x is None:
            diff("added", n, f"added {n}")
            continue
        for f in ("kind", "levels", "safety"):
            if x[f] != y[f]:
                fail.append(f"{f} {n}: {x[f]} -> {y[f]}")
        if x["type"] != y["type"]:
            diff("type", n, f"type {n}: {x['type']} -> {y['type']}")
        if x["value"] != y["value"]:
            diff("value", n, f"value {n}")
        if x["axioms"] != y["axioms"]:
            gained, lost = sorted(y["axioms"] - x["axioms"]), sorted(x["axioms"] - y["axioms"])
            diff("axioms", n, f"axioms {n}:" + (f" +{gained}" if gained else "") + (f" -{lost}" if lost else ""))
        if x["module"] != y["module"]:
            notes.append(f"moved {n}: {x['module']} -> {y['module']}")
    for what, ns in sorted(allow.items()):
        for n in sorted(set(ns)):
            if (what, n) not in used:
                fail.append(f"--allow-{what} {n} matches no difference")
    rest = lambda d: sum(n not in scope for n in d)
    notes.insert(0, f"compared {len(scope)} constants; not compared (no compared constant refers to them) "
                    f"{rest(a)} -> {rest(b)}")
    return fail, notes


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("base")
    ap.add_argument("new")
    for what in ("added", "removed", "type", "value", "axioms"):
        ap.add_argument(f"--allow-{what}", action="append", default=[], metavar="NAME")
    a = ap.parse_args()
    allow = {"added": a.allow_added, "removed": a.allow_removed, "type": a.allow_type, "value": a.allow_value,
             "axioms": a.allow_axioms}
    fail, notes = compare(load(a.base), load(a.new), allow)
    for n in notes:
        print(n)
    for f in fail:
        print("FAIL", f)
    print(f"const-diff: {'FAILED' if fail else 'passed'} ({len(fail)} failures)")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())

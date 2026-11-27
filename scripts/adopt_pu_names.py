#!/usr/bin/env python3
"""Inventory and apply the P-U declaration rename, without elaborating Lean.

Run --report first. --check exits 1 while names remain; --write refuses all
unresolved public declaration collisions before changing any file. This tool
does not choose which stock proofs to delete: retire those in the adoption
series first, then rerun. Snapshots must be regenerated, not text-rewritten.

Only single primes belonging to declarations in the explicit shadow proof
tree are renamed. Double primes (including frameKey'') and arbitrary primed
local variables are not a blanket substitution target. Comments and strings
are preserved. Module paths stay unchanged in this adoption; moving the proof
tree is a follow-up. No destination is inferred from a matching basename.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys


G = "ConsensusLean/Instances/Goldilocks"
SOURCE = f"{G}/Lemmas/Shadow/PU"
MANIFEST = Path(__file__).with_suffix(".json")
# Explicit rewrite scope; no scripts, snapshots, fixtures, or vendored specs.
SCOPES = ("ConsensusLean", "ConsensusLeanTest")
ROOTS = ("ConsensusLean.lean", "ConsensusLeanTest.lean", "Challenge.lean", "Solution.lean")
# Canonical definitions explicitly retained by the adoption contract. Their
# primed copies may be removed only after the trusted P-U switch is present.
CANONICAL = {
    "Consensus.Goldilocks." + name for name in (
        "GoldilocksRun", "Growing.GoldilocksRun", "goldilocksNode",
        "GoldilocksTrace", "Store.IsViable", "Store.toFrame",
        "Store.HasViableDescendant", "Store.updateFinality", "Store.onBlock",
        "Node.frame", "Node.acCall", "Node.acProposal", "Node.acToFG",
        "Node.onBlock", "Node.onMessage", "Node.restart",
    )
}
LEGACY = (
    f"{G}/Lemmas/Growing/Healing/Kernel/FrameWindow.lean",
    f"{G}/Lemmas/Growing/Healing/Kernel/ResetRounds.lean",
    f"{G}/Lemmas/Healing/M1/FrameKey.lean",
    f"{G}/Lemmas/Healing/M1/FrameWindowCore.lean",
    f"{G}/Lemmas/Growing/Healing/Report/",
)
RETIRED_BRIDGES = {
    f"{SOURCE}/Viability.lean": {"isViable_imp_isViable", "isViable_iff_of_not_contest"},
    f"{SOURCE}/Frame.lean": {"viableTree_eq_of_gap", "viableTree_eq_union_of_top_clean",
                             "viableTree_eq_union_of_contest"},
}
IDENT = re.compile(r"[^\W\d][\w'₀-₉]*(?:\.[^\W\d][\w'₀-₉]*)*", re.UNICODE)
COMMAND = re.compile(
    r"(?m)^\s*(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(namespace|section|end|theorem|def|abbrev|structure|class|inductive|opaque|axiom)"
    r"(?:[ \t]+([^\s:({\[=]+))?")


def code_mask(text):
    """Keep code offsets/newlines, blank nested comments and string literals."""
    out = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                width, depth = 2, depth + 1
            elif text.startswith("-/", i):
                width, depth = 2, depth - 1
            else:
                width = 1
        elif string:
            if text[i] == "\\":
                width = min(2, len(text) - i)
            else:
                width = 1
                if text[i] == '"':
                    string = False
        elif text.startswith("--", i):
            stop = text.find("\n", i)
            width = (len(text) if stop < 0 else stop) - i
        elif text.startswith("/-", i):
            width, depth = 2, 1
        elif text[i] == '"':
            width, string = 1, True
        else:
            i += 1
            continue
        for j in range(i, i + width):
            if out[j] != "\n":
                out[j] = " "
        i += width
    return "".join(out)


@dataclass(frozen=True)
class Decl:
    name: str
    path: str
    line: int
    private: bool
    start: int
    end: int
    signature: str
    context: str


def declarations(text, path):
    masked = code_mask(text)
    stack = []
    # Top-level Lean commands delimit declaration bodies. Local tactic commands
    # are indented; comments are masked before searching for delimiters.
    boundaries = [m.start() for m in re.finditer(
        r"(?m)^(?=\S)(?:@\[|(?:public |private |protected |noncomputable |unsafe |partial )*"
        r"(?:theorem|def|abbrev|structure|class|inductive|opaque|axiom|namespace|section|end|"
        r"variable|include|omit|open|attribute|set_option)\b)", masked)] + [len(text)]
    for m in COMMAND.finditer(masked):
        kind, name = m.groups()
        if kind in ("namespace", "section"):
            stack.append(name if kind == "namespace" and name else "")
        elif kind == "end":
            if stack:
                stack.pop()
        elif name and IDENT.fullmatch(name):
            prefix = ".".join(n for n in stack if n)
            full = name.removeprefix("_root_.") if name.startswith("_root_.") else (
                f"{prefix}.{name}" if prefix else name)
            start = masked.rfind("\n", 0, m.start(1)) + 1
            end = next(b for b in boundaries if b > m.start(1))
            body = masked[m.end(2):end]
            depth = 0
            stop = len(body)
            for tok in re.finditer(r":=|\bwhere\b|[(){}\[\]]", body):
                if tok.group() in ("(", "{", "["):
                    depth += 1
                elif tok.group() in (")", "}", "]"):
                    depth -= 1
                elif depth == 0:
                    stop = tok.start()
                    break
            # Free variables have types supplied by preceding variable/include
            # commands. A textual signature match without these is unsafe.
            context = "\n".join(v.group() for v in re.finditer(
                r"(?ms)^variable\b.*?(?=^\S|\Z)|^include[^\n]*|^omit[^\n]*", masked[:start]))
            yield Decl(full, path, text.count("\n", 0, m.start(1)) + 1,
                       bool(re.search(r"\bprivate\b", m.group())), start, end,
                       body[:stop], context)


def unprime(atom):
    # A double prime is a distinct mathematical name, not the shadow marker.
    return re.sub(r"(?<!')'(?!')", "", atom).replace("_primed_", "_")


def files(root):
    return sorted({p for scope in SCOPES for p in (root / scope).rglob("*.lean")} |
                  {root / p for p in ROOTS if (root / p).is_file()})


def inventory(root):
    texts = {p.relative_to(root).as_posix(): p.read_text() for p in files(root)}
    decls = [d for p, t in texts.items() for d in declarations(t, p)]
    # Keep the reviewed base map even after the declarations have been renamed:
    # a later main merge can reintroduce an old reference without its definition.
    atoms = json.loads(MANIFEST.read_text())["rename_atoms"]
    for d in decls:
        if d.path.startswith(SOURCE + "/"):
            for atom in d.name.split("."):
                new = unprime(atom)
                if new != atom:
                    atoms[atom] = new
    # A stock private helper may use the same spelling as a shadow public
    # declaration (NInv.ac' is distinct from its field ac). Keep that atom
    # untouched until the public rename can be resolved by full Lean names.
    for d in decls:
        if d.private and not d.path.startswith(SOURCE + "/"):
            atoms.pop(d.name.split(".")[-1], None)
    return texts, decls, atoms


def map_name(name, atoms):
    return ".".join(atoms.get(a, a) for a in name.split("."))


def rewrite(text, atoms):
    masked = code_mask(text)
    edits = [(m.start(), m.end(), map_name(m.group(), atoms))
             for m in IDENT.finditer(masked) if map_name(m.group(), atoms) != m.group()]
    for start, end, new in reversed(edits):
        text = text[:start] + new + text[end:]
    return text


def collisions(decls, atoms):
    targets = defaultdict(list)
    for d in decls:
        if not d.private:
            targets[map_name(d.name, atoms)].append(d)
    return {name: ds for name, ds in sorted(targets.items())
            if len(ds) > 1 and any(map_name(d.name, atoms) != d.name for d in ds)}


def classification(name, decls):
    if name in CANONICAL:
        return "a", "Keep canonical definition; remove primed copy after the P-U Spec switch"
    stock = [d for d in decls if not d.path.startswith(SOURCE + "/")]
    if stock and all(d.path.startswith(LEGACY) for d in stock):
        return "b", "Legacy entry; step 5 must rewire surviving consumers before deletion"
    if any("/Milestones/" in d.path or "/Spec/" in d.path for d in stock):
        return "c", "Needs C0/planner owner; no Spec or Milestones text edits by this tool"
    return "d", "Needs review; no duplicate deletion or alias inferred"


def tokens(text, atoms):
    return re.findall(r"[^\W\d][\w'₀-₉]*|\d+|[^\s]", rewrite(text, atoms))


def body_equal(left, right, texts, atoms):
    if any(tokens(getattr(left, field), atoms) != tokens(getattr(right, field), atoms)
           for field in ("signature", "context")):
        return False
    def body(d):
        text = code_mask(texts[d.path][d.start:d.end])
        # Compare the declared command/body, excluding the declaration name.
        command = COMMAND.search(text)
        value = text[command.end(2) + len(d.signature):]
        # goldilocksAC is opened in the canonical Spec module.
        value = value.replace("AC.goldilocksAC", "goldilocksAC")
        return tokens(value, atoms)
    return body(left) == body(right)


def plan(texts, decls, atoms):
    clashes = collisions(decls, atoms)
    removed = []
    unresolved = {}
    for name, ds in clashes.items():
        cl, _ = classification(name, ds)
        renamed = [d for d in ds if map_name(d.name, atoms) != d.name]
        stock = [d for d in ds if map_name(d.name, atoms) == d.name]
        if cl in ("a", "c") and len(stock) == len(renamed) == 1 and body_equal(
                renamed[0], stock[0], texts, atoms):
            removed.extend(renamed)
        elif cl == "b":
            unresolved[name] = "b-retirement-pending"
        elif cl == "d" and len(renamed) == len(stock) == 1 and all(
                tokens(getattr(renamed[0], field), atoms) == tokens(getattr(stock[0], field), atoms)
                for field in ("signature", "context")):
            removed.extend(renamed)
        else:
            unresolved[name] = f"{cl}-mismatch"
            continue
    # Excluding a collision also excludes its component renames, including
    # namespace components shared by other declarations, to avoid partial types.
    blocked = {a for name in unresolved for d in clashes[name] for a in d.name.split(".") if a in atoms}
    active = {a: b for a, b in atoms.items() if a not in blocked}
    # Do not remove a duplicate whose redirect has been excluded indirectly.
    removed = [d for d in removed if all(a not in blocked for a in d.name.split("."))]
    redirects = defaultdict(set)
    for d in removed:
        name = map_name(d.name, atoms)
        cl, _ = classification(name, clashes[name])
        if cl in ("a", "c", "d"):
            winner = next(w for w in clashes[name] if w not in removed)
            redirects[d.path.removesuffix(".lean").replace("/", ".")].add(
                winner.path.removesuffix(".lean").replace("/", "."))
    result = dict(texts)
    by_file = defaultdict(list)
    removed.extend(d for d in decls if map_name(d.name, atoms).split(".")[-1] in
                   RETIRED_BRIDGES.get(d.path, set()))
    for d in removed:
        by_file[d.path].append(d)
    for path, ds in by_file.items():
        for d in sorted(ds, key=lambda d: d.start, reverse=True):
            result[path] = result[path][:d.start] + result[path][d.end:]
    for path, text in result.items():
        text = rewrite(text, active)
        additions = set()
        own = path.removesuffix(".lean").replace("/", ".")
        additions.update(redirects.get(own, ()))
        for m in re.finditer(r"(?m)^(?:public )?import (\S+)", text):
            additions.update(redirects.get(m.group(1), ()))
        additions.discard(own)
        additions -= set(re.findall(r"(?m)^(?:public )?import (\S+)", text))
        if additions:
            text = text.replace("module\n", "module\n" + "".join(
                f"public import {mod}\n" for mod in sorted(additions)), 1)
        result[path] = text
    return {p: t for p, t in result.items() if t != texts[p]}, unresolved, removed


def import_cycles(texts):
    graph = {p.removesuffix(".lean").replace("/", "."):
             re.findall(r"(?m)^(?:public )?import (\S+)", text) for p, text in texts.items()}
    seen, active, stack, found = set(), set(), [], []

    def visit(node):
        if node in active:
            found.append(stack[stack.index(node):] + [node])
            return
        if node in seen:
            return
        seen.add(node)
        active.add(node)
        stack.append(node)
        for dep in graph.get(node, ()):
            visit(dep)
        stack.pop()
        active.remove(node)

    for node in graph:
        visit(node)
    return found


def structure_plan(texts, decls, atoms):
    """Reviewed central rebinding; preserve unresolved methods for lane review."""
    names = {"LocalRun'", "GoldilocksRun'", "ResetPremisesUpTo'", "RunTrace'",
             "Reachable'", "CutStep'", "toLocalRun'", "finalitySpec_updateFinality'"}
    active = {a: unprime(a) for a in names}
    targets = {map_name(d.name, active): d for d in decls
               if not d.path.startswith(SOURCE + "/")}
    removed = []
    methods = []
    for d in decls:
        if not d.path.startswith(SOURCE + "/"):
            continue
        target = map_name(d.name, active)
        if target == d.name:
            continue
        stock = targets.get(target)
        if stock is None:
            continue
        leaf = d.name.split(".")[-1]
        if leaf in names:
            # Alias expansion for these two definitions was read back against
            # Reaches and RunTrace; every structure field is token-compared.
            aliases = {"Consensus.Goldilocks.RunTrace", "Consensus.Goldilocks.Node.Reachable"}
            if target not in aliases and leaf != "finalitySpec_updateFinality'":
                left = tokens(code_mask(texts[d.path][d.start:d.end]), atoms)
                right = tokens(code_mask(texts[stock.path][stock.start:stock.end]), atoms)
                if left != right:
                    raise ValueError(f"Structure fields differ: {d.name}")
            removed.append((d, stock))
        elif not leaf.endswith("'"):
            methods.append(d)
    result = dict(texts)
    for path in result:
        edits = []
        for d, _ in removed:
            if d.path == path:
                # Include attached doc comments and command-scoped opens.
                start = d.start
                prefix = result[path][:start]
                while True:
                    opening = re.search(r"(?s)(/--(?:(?!-/).)*-/\s*|open [^\n]+ in\s*)$", prefix)
                    if opening is None:
                        break
                    start = opening.start()
                    prefix = prefix[:start]
                edits.append((start, d.end, ""))
        for d in methods:
            if d.path == path:
                command = COMMAND.search(code_mask(result[path][d.start:d.end]))
                start = d.start + command.start(2)
                # Preserve the namespace qualification of the declaration.
                edits.append((start, d.start + command.end(2), command.group(2) + "'"))
        text = result[path]
        for start, end, value in sorted(edits, reverse=True):
            text = text[:start] + value + text[end:]
        text = rewrite(text, active)
        imports = {stock.path.removesuffix(".lean").replace("/", ".")
                   for d, stock in removed if d.path == path}
        imports -= set(re.findall(r"(?m)^(?:public )?import (\S+)", text))
        if imports:
            text = text.replace("module\n", "module\n" + "".join(
                f"public import {mod}\n" for mod in sorted(imports)), 1)
        result[path] = text
    return {p: t for p, t in result.items() if t != texts[p]}, methods


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    for flag in ("check", "write", "report"):
        mode.add_argument(f"--{flag}", action="store_true")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--approved-subset", action="store_true",
                        help="apply a/b/d-matching only; exclude c and d-mismatch component renames")
    parser.add_argument("--structures", action="store_true",
                        help="apply the reviewed central structure rebinding only")
    args = parser.parse_args()
    texts, decls, atoms = inventory(args.root)
    clashes = collisions(decls, atoms)
    changed, unresolved, removed = plan(texts, decls, atoms)
    if args.structures:
        changed, methods = structure_plan(texts, decls, atoms)
        unresolved = {}
        for d in methods:
            print(f"METHOD {d.path}: {d.name} -> trailing prime", file=sys.stderr)
    cycles = import_cycles(texts | changed)
    if args.report:
        print(json.dumps({"source": SOURCE, "scope": [*SCOPES, *ROOTS],
                          "rename_atoms": atoms, "changed_files": sorted(changed),
                          "classification": {n: dict(zip(("class", "action"), classification(n, ds)))
                                             for n, ds in clashes.items()},
                          "unresolved": unresolved,
                          "removed": [vars(d) for d in removed],
                          "import_cycles": cycles,
                          "collisions": {n: [vars(d) for d in ds] for n, ds in clashes.items()}},
                         indent=2, ensure_ascii=False))
        return 0
    if cycles:
        for cycle in cycles:
            print("IMPORT CYCLE " + " -> ".join(cycle))
        print("Refused: import cycles; no files written.")
        return 2
    if unresolved and not args.approved_subset:
        for name, ds in clashes.items():
            print(f"COLLISION {name}: " + "; ".join(f"{d.path}:{d.line} ({d.name})" for d in ds))
        print(f"Refused: {len(unresolved)} unresolved declaration collisions; no files written.")
        return 2
    if args.write:
        for path, text in changed.items():
            (args.root / path).write_text(text)
        checker = args.root / "scripts/check-boundaries.py"
        if checker.is_file():
            checked = subprocess.run([sys.executable, "-I", str(checker)], cwd=args.root,
                                     capture_output=True, text=True)
            if checked.returncode:
                for path in changed:
                    (args.root / path).write_text(texts[path])
                print(checked.stdout + checked.stderr)
                print("Refused: layer check failed; restored every proposed write.")
                return 2
    print(f"{'Rewrote' if args.write else 'Pending'} {len(changed)} files, {len(atoms)} rename atoms")
    return int(bool(changed) and args.check)


if __name__ == "__main__":
    sys.exit(main())

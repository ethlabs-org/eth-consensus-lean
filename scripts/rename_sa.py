#!/usr/bin/env python3
"""Rename the leftover "SA" (Slow Arming, the archived name of the Goldilocks available chain) to AC names.

Purely nominal: moves files and rewrites text by an ordered list of regex rules; no Lean is elaborated.
The rules are the name map. Every replacement keeps or shortens the line, except two Milestones module
paths and a section name, so the output needs no hand rewrapping and is a pure function of the input
tree (which `rebase-branch` relies on). Run it on any tree of verified-consensus (main, an in-flight
branch) or on a downstream tree that mirrors upstream paths; it is idempotent.

  rename_sa.py apply ROOT          move files (git mv when ROOT is a Git work tree) and rewrite tracked text
  rename_sa.py check ROOT          list every line the rules would still change (an old name left) and
                                   doubled "AC ... AC" prose, and count .lean lines over 100 characters
                                   (information only: main has some); exit 1 on a leftover or doubling
  rename_sa.py names < in > out    map full Lean names or module names (or any text) with the identifier
                                   rules only, such as for the name map of a downstream tree or an
                                   in-flight branch
  rename_sa.py dump-map BASE.tsv   print the `old ⇥ new` map of every constant and module name of a
                                   const-dump of the unrenamed tree that the rename changes
  rename_sa.py aliases BASE.tsv OUT.lean IMPORTS...
                                   write a module of `@[deprecated] alias old := new` for the public
                                   constants among the dump-map pairs of BASE.tsv (the same pairs, one
                                   source; for a downstream that must keep old names; unused here: module
                                   paths cannot be aliased and --wfail rejects deprecated uses)
  rename_sa.py rebase-branch REPO BRANCH RENAME_COMMIT
                                   replay BRANCH on RENAME_COMMIT: for each first-parent commit c of BRANCH
                                   after its merge base with RENAME_COMMIT, the change from apply(c^) to
                                   apply(c) is merged (git merge-tree, three-way) into the previous result,
                                   starting from RENAME_COMMIT. So every file of RENAME_COMMIT stays (also
                                   one that exists only there, such as the regenerated snapshots or the
                                   rename tooling), and every change of the branch arrives renamed. Authors,
                                   dates and messages are kept; the result is branch <name>-ac, BRANCH is
                                   unchanged. A conflict (such as a branch commit that edits a snapshot)
                                   stops it with the paths: replay that commit by hand, then regenerate.
  rename_sa.py selftest            fixtures: check's failing and passing verdicts, apply's idempotence,
                                   the aliases/dump-map agreement and the rebase-branch contract

Layout after the rename: the Goldilocks AC's files join the AC interface in Spec/AC and Milestones/Spec/AC.
The interface and the instance keep separate boundary layers (Instances.Goldilocks.Spec.AC and
Instances.Goldilocks.Spec.GoldilocksAC, likewise under Milestones), now with explicit module prefixes,
so the "any AC" layers still cannot import the Goldilocks AC. A new file under Spec/AC must be added to
one of the two prefix lists (check-boundaries.py fails on an unlisted module).

Snapshots (scripts/*snapshot.txt) are not rewritten: regenerate them with scripts/check.sh
--update-snapshot after the rename; their hashes cover names.

Const-diff (the rename changes names only), each dump in its own built tree:
  base:    lake exe const-dump base.tsv ConsensusLean Solution ConsensusLeanTest
           python3 scripts/rename_sa.py dump-map base.tsv > rename.map
           lake exe const-dump --map rename.map base-mapped.tsv ConsensusLean Solution ConsensusLeanTest
  renamed: lake exe const-dump new.tsv ConsensusLean Solution ConsensusLeanTest
  python3 -I scripts/const-diff.py base-mapped.tsv new.tsv    (and the same for Challenge)
(the base tree runs the renamed tree's const-dump binary under `lake env`, for `--map`).
"""
import contextlib, io, os, re, subprocess, sys, pathlib

G = "ConsensusLean/Instances/Goldilocks"
SPEC_DIRS = [f"{G}/Spec", f"{G}/Milestones/Spec"]

# Identifier and module rules: used on Lean code, names, configuration and docs. Order matters.
NAME_RULES = [
    # the test helper that held the name goldilocksAC (renamed in the tree by HELPER_RULE below); here for
    # full constant names in a const-diff dump
    (r"\bHealingLeavesCut\.goldilocksAC\b", "HealingLeavesCut.isGoldilocksACConst"),
    # the two Milestones SA modules whose names AC/ already holds
    (r"\bSpec([./])SA([./])Trace\b", r"Spec\1AC\2Premises"),
    (r"\bSpec([./])SA([./])Growing\b", r"Spec\1AC\2GrowingPremises"),
    # boundary layer names (labels, not module prefixes): the instance layers
    (r"(?<!ConsensusLean\.)\bInstances\.Goldilocks\.(Milestones\.)?Spec\.SA\b(?!\.)", r"Instances.Goldilocks.\1Spec.GoldilocksAC"),
    # module paths: Spec.SA.X / Spec/SA/X (also under Milestones) -> Spec.AC.X
    (r"\bSpec([./])SA\b", r"Spec\1AC"),
    # the two-validator test module TwoValidator/SA (the record and the AC on a chain frame); AC.lean exists
    (r"\bTwoValidator([./])SA\b", r"TwoValidator\1ChainAC"),
    # types and namespaces with SA as a camel-case part (also inside generated instance names)
    (r"(?<![A-Z])SATrace\b", "GTrace"),  # ACTrace is the generic AC trace; GoldilocksTrace the node run's
    (r"(?<![A-Z])SAParams", "ACParams"),
    (r"(?<![A-Z])SAState", "ACState"),
    (r"(?<![A-Z])SAPool\b", "ACPool"),
    (r"(?<![A-Z])SAFamily\b", "ACFamily"),
    (r"(?<![A-Z])SAOperations\b", "ACOperations"),
    (r"\bSAFacts\b", "ACFacts"),
    (r"\bSAUpTo\b", "GoldilocksACUpTo"),  # a section name; ACUpTo is the section above it in the same file
    (r"\bgoldilocksSA\b", "goldilocksAC"),
    # lemma names with an sa_ prefix (Compose.Growing.sa_*_upTo, Regimes.sa_tips)
    (r"\bsa_([A-Za-z]+_upTo|tips)\b", r"ac_\1"),
    # gf_ / Goldfish-vote naming -> head_, as in the pyspec; TeX escapes `\_` too
    (r"(?<![A-Za-z])goldfishScore", "headScore"),
    (r"(?<![A-Za-z])goldfishEligible", "headEligible"),
    (r"\bgf(\\?)_votes\b", r"head\1_votes"),
    (r"\\gfPool\b", r"\\headVotes"),
    (r"\bon(\\?)_goldfish(\\?)_vote\b", r"on\1_head\2_vote"),
    (r"\bgoldfish(\\?)_(score|eligible)\b", r"head\1_\2"),
    # the payload accessors, after the TeX `declared_head_votes` / `support_bits`; also their lemmas
    # (blockVotes_blk, mem_blockVotes, ...)
    (r"(?<![A-Za-z])blockVotes", "declaredHeadVotes"),
    (r"(?<![A-Za-z])blockSupport", "declaredSupportVotes"),
    # the namespace component and the word: Consensus.Goldilocks.SA -> .AC, `open SA`, `SA.foo`, prose,
    # SA-level (not FG-SA / plain-SA, historical names; not SAME, hSA: no word boundary)
    (r"(?<![-\w])SA(?![\w])(?!-(?!level))", "AC"),
]

# Prose rules, applied before NAME_RULES so the result does not read "the AC as an AC".
PROSE_RULES = [
    # docs/layout.md: the two AC layers that share Spec/AC
    (r"`Spec\.\{Common,FG,Frame,Trace,FGStore,AC,SA,Node,Run\}`",
     "`Spec.{Common,FG,Frame,Trace,FGStore,AC,GoldilocksAC,Node,Run}`; `Spec.AC` (the generic AC interface) "
     "and `Spec.GoldilocksAC` (the Goldilocks AC) are separate layers that share the directory `Spec/AC`, "
     "with explicit module prefixes"),
    (r"Goldilocks SA as an AC", "Goldilocks AC"),
    (r"\b([Tt])he SA as an AC\b", r"\1he Goldilocks AC"),
    (r"\bSA as an AC\b", "Goldilocks AC"),
    (r"\binterface and SA\b", "interface and Goldilocks AC"),
    (r"Schedule arithmetic \(SA\)", "Schedule arithmetic"),
    (r"\bAC, SA,", "AC,"),
    (r"\bAC,SA,", "AC,"),
    (r"\bAC or SA\b", "AC"),
    (r"\bAC/SA\b", "AC"),
    (r"\bAC, SA\b", "AC"),
    # the vote, its score, eligibility and walk; "Goldfish" naming the protocol (Goldfish with locks,
    # Goldfish's argument, the Goldfish head) stays: it cites the paper
    (r"\bGoldfish (vote|score|eligibility|walk)", r"head \1"),
    # TeX labels sec:sa-*, fig:sa-*, tab:sa-*, alg:sa-*
    (r"\b(sec|fig|tab|alg):sa\b", r"\1:ac"),
]

# Fixed rewraps for the lines the accessor names push over 100 characters, measured on the landed
# references migration (2e3127a8). Keyed by file (after the moves) and the exact renamed line; applied
# after the rules, so the pass stays a pure function of the tree. A key that no longer matches (the
# line changed upstream) is reported by `apply`, and `check` then lists the long line: update the table.
W = {}
def wrap(f, old, *new):
    W.setdefault(f, []).append((old, "\n".join(new)))

G_ = "ConsensusLean/Instances/Goldilocks/"
T_ = "ConsensusLeanTest/Goldilocks/"
wrap(G_ + "Lemmas/AC/Steps/Agree/Pool.lean",
     "      (tr.state y c).voteStamp x = ETime.of (tr.time k) ∧ ∃ B ∈ ℓ.frame.tree, x ∈ declaredHeadVotes B :=",
     "      (tr.state y c).voteStamp x = ETime.of (tr.time k) ∧",
     "        ∃ B ∈ ℓ.frame.tree, x ∈ declaredHeadVotes B :=")
wrap(G_ + "Lemmas/AC/UnlockViewOpponents.lean",
     "    (htree : ∀ C ∈ Φ.tree, C.slot = sp.slot t → ∀ v, v ∈ declaredHeadVotes C ∨ v ∈ declaredSupportVotes C →",
     "    (htree : ∀ C ∈ Φ.tree, C.slot = sp.slot t → ∀ v,",
     "      v ∈ declaredHeadVotes C ∨ v ∈ declaredSupportVotes C →")
wrap(G_ + "Lemmas/Compose/Service/SuffixWindow.lean",
     "        hsup x (by rw [AC.declaredSupportVotes, hpay]; exact hx) hxs (by simp [AC.ACParams.committee])",
     "        hsup x (by rw [AC.declaredSupportVotes, hpay]; exact hx) hxs",
     "          (by simp [AC.ACParams.committee])")
wrap(G_ + "Milestones/Statements/Healing/Run.lean",
     "    ∀ x ∈ declaredSupportVotes B, x.slot + 1 = s → ∀ y ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts s + sp.Δ) →",
     "    ∀ x ∈ declaredSupportVotes B, x.slot + 1 = s → ∀ y ∈ H, ∀ j,",
     "      tr.FirstCutFrom j (sp.ts s + sp.Δ) →")
wrap(G_ + "Spec/AC/Views.lean",
     "  (∀ v ∈ declaredHeadVotes B, v.slot + 1 = B.slot) ∧ (declaredSupportVotes B).Sublist (declaredHeadVotes B) ∧",
     "  (∀ v ∈ declaredHeadVotes B, v.slot + 1 = B.slot) ∧",
     "    (declaredSupportVotes B).Sublist (declaredHeadVotes B) ∧")
wrap(G_ + "Spec/AC/Views.lean",
     "    (declaredHeadVotes B).Nodup ∧ ∀ i : Fin n, ((declaredHeadVotes B).filter (fun v => v.val = i)).length ≤ 2",
     "    (declaredHeadVotes B).Nodup ∧",
     "    ∀ i : Fin n, ((declaredHeadVotes B).filter (fun v => v.val = i)).length ≤ 2")
D = T_ + "AC/DeclaredVotes.lean"
for P in ("P", "Pb"):
    wrap(D, f"  have := h {P} (mem_frm (by simp)) rfl b (Or.inl (by simp [{P}, prop, declaredHeadVotes])) (Set.mem_univ _)",
         f"  have := h {P} (mem_frm (by simp)) rfl b (Or.inl (by simp [{P}, prop, declaredHeadVotes]))",
         "    (Set.mem_univ _)")
wrap(D, "  refine ⟨⟨Pz, mem_frm (by simp), rfl, fun x hx _ _ => by simp [Pz, prop, declaredSupportVotes] at hx⟩,",
     "  refine ⟨⟨Pz, mem_frm (by simp), rfl,",
     "    fun x hx _ _ => by simp [Pz, prop, declaredSupportVotes] at hx⟩,")
wrap(D, "  merged_support.2 ⟨prop 3 ([a, b], [a]), mem_frm (by simp), rfl, by simp [prop, declaredSupportVotes],",
     "  merged_support.2 ⟨prop 3 ([a, b], [a]), mem_frm (by simp), rfl,",
     "    by simp [prop, declaredSupportVotes],")
wrap(D, "    by simp [prop, declaredHeadVotes], (shouldCount_st rfl).2 (Or.inr ⟨b, by simp, b', by simp, by decide,",
     "    by simp [prop, declaredHeadVotes],",
     "    (shouldCount_st rfl).2 (Or.inr ⟨b, by simp, b', by simp, by decide,")
wrap(D, "  refine ⟨(merged_votes hps).2 (Or.inr ⟨prop 3 ([a], []), by simp, by simp [prop, declaredHeadVotes],",
     "  refine ⟨(merged_votes hps).2 (Or.inr ⟨prop 3 ([a], []), by simp,",
     "    by simp [prop, declaredHeadVotes],")
wrap(T_ + "AC/LockRule.lean",
     "    ⟨fun v hv => by simp [declaredHeadVotes, B1] at hv, by simp [declaredSupportVotes, declaredHeadVotes, B1],",
     "    ⟨fun v hv => by simp [declaredHeadVotes, B1] at hv,",
     "      by simp [declaredSupportVotes, declaredHeadVotes, B1],")
wrap(T_ + "Regimes/ProposerHoldRun/Cast.lean",
     "    X.slot = 1 ∧ AC.declaredHeadVotes X = [] ∧ AC.declaredSupportVotes X = [] ∧ X.proposer = key 1 := by",
     "    X.slot = 1 ∧ AC.declaredHeadVotes X = [] ∧ AC.declaredSupportVotes X = [] ∧",
     "      X.proposer = key 1 := by")
wrap(T_ + "Runs/OneValidator/TickRun.lean",
     "    (w : Vote sp.n) (h : w ∈ (blockReceipt sp A t B).pool σ) : w ∈ A.pool σ ∨ w ∈ declaredHeadVotes B := by",
     "    (w : Vote sp.n) (h : w ∈ (blockReceipt sp A t B).pool σ) :",
     "    w ∈ A.pool σ ∨ w ∈ declaredHeadVotes B := by")
for n in ("declaredSupportVotes", "declaredHeadVotes"):
    wrap(T_ + "Runs/TwoValidator/AC.lean",
         f"theorem {n}_blk (k : Nat) : {n} (blk (k + 1)) = [vote w0 k, vote w1 k] := by",
         f"theorem {n}_blk (k : Nat) :",
         f"    {n} (blk (k + 1)) = [vote w0 k, vote w1 k] := by")
WRAPS = W


def rewrap(f, t, changed_by_rules):
    """Apply the fixed rewraps of file f to its renamed text t; report a key the rules produced but that
    is missing (only when the rules changed this file, so a second run stays quiet)."""
    for old, new in WRAPS.get(f, []):
        lines = t.split("\n")
        if old in lines:
            t = "\n".join(new if l == old else l for l in lines)
        elif changed_by_rules and new.split("\n")[0] not in lines:
            print(f"wrap not applied (line changed): {f}: {old[:80]}")
    return t


# the one helper that holds the target name goldilocksAC today (a test predicate); renamed first, only
# where it is still defined that way, so a second run does not touch the renamed goldilocksAC
HELPER_FILE = "ConsensusLeanTest/Goldilocks/Generic/HealingLeavesCut.lean"
HELPER_RULE = (r"\bgoldilocksAC\b", "isGoldilocksACConst")

BOUNDARIES = "scripts/boundaries.toml"
# the generated roots (`lake exe mk_all --lib <L> --module`): their imports are sorted by module name, so
# moved modules must be sorted again (check reports a root out of order)
ROOTS = ("ConsensusLean.lean", "ConsensusLeanTest.lean")


def sort_imports(t):
    lines = t.split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith(("public import ", "import "))]
    for i, l in zip(idx, sorted(lines[i] for i in idx)):
        lines[i] = l
    return "\n".join(lines)
TEXT_SUFFIXES = {".lean", ".md", ".tex", ".toml", ".json", ".py", ".sh", ".txt", ".tsv", ".yaml", ".yml", ""}
SKIP = {"scripts/spec-snapshot.txt", "scripts/instance-spec-snapshot.txt"}
# the rename's own tooling: its rules and fixtures name the old names on purpose
OWN = ("scripts/rename_sa.py",)


def skipped(f):
    return f in SKIP or f.startswith(OWN)
TSV_OLD_COLUMN = {"docs/notes/test-module-map.tsv"}  # column 1 holds historical module names: kept

# known non-leftover SA tokens, allowed by `check`
ALLOWED = [r"FG-SA", r"plain-SA", r"\bfgsa", r"\bSAME\b", r"\bhSA\b", r"ml-dsa", r"Runs\.SAHealing"]


def sub_all(rules, s):
    for pat, rep in rules:
        s = re.sub(pat, rep, s)
    return s


def map_names(s):
    return sub_all(NAME_RULES, s)


def map_text(s):
    return sub_all(NAME_RULES, sub_all(PROSE_RULES, s))


def tracked(root):
    if is_git(root):
        out = subprocess.run(["git", "-C", root, "ls-files", "-z"], capture_output=True, check=True).stdout
        return [p for p in out.decode().split("\0") if p and os.path.lexists(os.path.join(root, p))]
    return [str(p.relative_to(root)) for p in pathlib.Path(root).rglob("*")
            if p.is_file() and ".git" not in p.parts and ".lake" not in p.parts]


def is_git(root):
    return subprocess.run(["git", "-C", root, "rev-parse", "--is-inside-work-tree"], capture_output=True).returncode == 0


def module(path):
    return path.removesuffix(".lean").replace("/", ".")


def explicit_prefixes(files, d):
    """Module prefixes covering every Lean file directly or deeper under directory d (one per entry of d)."""
    heads = sorted({f[len(d) + 1:].split("/")[0].removesuffix(".lean") for f in files
                    if f.startswith(d + "/") and f.endswith(".lean")})
    return [module(d) + "." + h for h in heads]


def fmt(prefixes):
    lines, cur = [], "prefixes = ["
    for i, p in enumerate(prefixes):
        item = f'"{p}"' + ("," if i < len(prefixes) - 1 else "]")
        if len(cur) + len(item) + 1 > 118 and cur.strip() != "prefixes = [":
            lines.append(cur.rstrip())
            cur = " " * 12
        cur += item + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


def rewrite_boundaries(text, before, after):
    """Replace the module prefixes of the AC interface and SA layers by explicit lists: after the move both
    live under Spec/AC (and Milestones/Spec/AC), and layer prefixes must not overlap."""
    for d in SPEC_DIRS:
        ac, sa = module(d) + ".AC", module(d) + ".SA"
        if f'prefixes = ["{sa}"]' not in text:
            continue
        iface = explicit_prefixes(before, f"{d}/AC")
        inst = [p for p in explicit_prefixes(after, f"{d}/AC") if p not in iface]
        text = text.replace(f'prefixes = ["{ac}"]', fmt(iface)).replace(f'prefixes = ["{sa}"]', fmt(inst))
    for pre in ("", "untrusted milestone layer: "):
        text = text.replace(
            f'about = "{pre}AC interface, A.Reachable, Requirements, AC traces"',
            f'about = "{pre}the generic AC interface (any AC), A.Reachable, Requirements, AC traces; shares '
            f'Spec/AC with the separate Goldilocks AC layer (GoldilocksAC), hence explicit prefixes"')
        text = text.replace(
            f'about = "{pre}the SA as an AC (polymorphic in the FG payload); no FG import"',
            f'about = "{pre}the Goldilocks AC (polymorphic in the FG payload), a layer separate from the generic '
            f'AC interface whose directory Spec/AC it shares (explicit prefixes); no FG import"')
    return text


def apply(root):
    git = is_git(root)
    before = tracked(root)
    # 1. moves: Spec/SA and Milestones/Spec/SA into .../AC, the TwoValidator/SA test
    moves = {f: map_names(f) for f in before if re.search(r"(Spec|TwoValidator)/SA\b", f)}
    clash = [g for g in moves.values() if os.path.lexists(os.path.join(root, g))]
    if clash:
        sys.exit(f"move targets exist, nothing moved: {clash}")
    for f, g in sorted(moves.items()):
        pathlib.Path(root, g).parent.mkdir(parents=True, exist_ok=True)
        if git:
            subprocess.run(["git", "-C", root, "mv", f, g], check=True)
        else:
            os.rename(pathlib.Path(root, f), pathlib.Path(root, g))
    for d in sorted({str(pathlib.Path(root, f).parent) for f in moves}, reverse=True):
        try:
            os.removedirs(d)
        except OSError:
            pass
    after = [moves.get(f, f) for f in before]
    # 2. text
    changed = 0
    for f in after:
        p = pathlib.Path(root, f)
        if skipped(f) or p.suffix not in TEXT_SUFFIXES or not p.is_file() or p.is_symlink():
            continue
        try:
            s = p.read_text()
        except UnicodeDecodeError:
            continue
        t = s
        if f == BOUNDARIES:
            t = rewrite_boundaries(t, before, after)
        if f.endswith(HELPER_FILE) and re.search(r"meta def goldilocksAC\b", t):
            t = re.sub(*HELPER_RULE, t)
        if f in TSV_OLD_COLUMN:
            t = "\n".join("\t".join(c if i == 0 else map_text(c) for i, c in enumerate(l.split("\t")))
                          for l in t.split("\n"))
        else:
            t = map_text(t)
        if f.endswith(".lean"):
            t = rewrap(f, t, t != s)
        if f in ROOTS:
            t = sort_imports(t)
        if t != s:
            p.write_text(t)
            changed += 1
    print(f"moved {len(moves)} files, rewrote {changed} files")


def check(root):
    """Leftovers are the lines `apply`'s own rules would still change (one source for both), after
    removing the known non-leftovers. Returns the number of findings."""
    allowed = re.compile("|".join(ALLOWED))
    doubled = re.compile(r"\bAC (as an|and|or) AC\b|\bGoldilocks Goldilocks\b|\bAC, AC\b|\bAC,AC\b")
    n_left = n_long = n_dbl = 0
    for f in tracked(root):
        p = pathlib.Path(root, f)
        if skipped(f) or p.suffix not in TEXT_SUFFIXES or not p.is_file():
            continue
        try:
            lines = p.read_text().split("\n")
        except UnicodeDecodeError:
            continue
        if f in ROOTS and sort_imports("\n".join(lines)) != "\n".join(lines):
            print(f"UNSORTED {f}: imports not in mk_all order"); n_dbl += 1
        for i, l in enumerate(lines, 1):
            if f in TSV_OLD_COLUMN:
                l = "\t".join(l.split("\t")[1:])
            k = allowed.sub("", l)
            if map_text(k) != k:
                print(f"LEFT {f}:{i}: {l.strip()[:160]}"); n_left += 1
            if doubled.search(l):
                print(f"DOUBLED {f}:{i}: {l.strip()[:160]}"); n_dbl += 1
            if f.endswith(".lean") and len(l) > 100 and "http" not in l:
                print(f"LONG {f}:{i}: {len(l)}"); n_long += 1
    print(f"left {n_left}, doubled {n_dbl}, long {n_long} (information)")
    return n_left + n_dbl


def git_out(repo, *a, env=None):
    return subprocess.run(["git", "-C", repo, *a], capture_output=True, text=True, check=True, env=env).stdout.strip()


def rebase_branch(repo, branch, rename_commit):
    """Replay BRANCH on RENAME_COMMIT, renamed (see the module docstring for the contract)."""
    rename_commit = git_out(repo, "rev-parse", rename_commit)
    base = git_out(repo, "merge-base", rename_commit, branch)
    commits = git_out(repo, "rev-list", "--reverse", "--first-parent", f"{base}..{branch}").split()
    wt = pathlib.Path(repo).resolve().parent / f".rename-sa-{os.getpid()}"
    subprocess.run(["git", "-C", repo, "worktree", "add", "-q", "--detach", str(wt), base], check=True)
    renamed = {}

    def renamed_commit(c):  # a parentless commit holding apply(c)'s tree
        if c not in renamed:
            subprocess.run(["git", "-C", str(wt), "checkout", "-q", "--detach", "-f", c], check=True)
            subprocess.run(["git", "-C", str(wt), "clean", "-fdq"], check=True)
            with contextlib.redirect_stdout(io.StringIO()):
                apply(str(wt))
            subprocess.run(["git", "-C", str(wt), "add", "-A"], check=True)
            renamed[c] = git_out(str(wt), "commit-tree", git_out(str(wt), "write-tree"), "-m", f"renamed {c}")
        return renamed[c]

    head = rename_commit
    try:
        for c in commits:
            m = subprocess.run(["git", "-C", repo, "merge-tree", "--write-tree", "--name-only",
                                f"--merge-base={renamed_commit(c + '^')}", head, renamed_commit(c)],
                               capture_output=True, text=True)
            if m.returncode:
                sys.exit(f"{branch}: commit {c[:10]} conflicts when replayed on the rename:\n{m.stdout}")
            tree = m.stdout.split("\n")[0]
            name, email, date, msg = git_out(repo, "log", "-1", "--format=%an%x00%ae%x00%aI%x00%B", c).split("\0", 3)
            env = dict(os.environ, GIT_AUTHOR_NAME=name, GIT_AUTHOR_EMAIL=email, GIT_AUTHOR_DATE=date)
            head = subprocess.run(["git", "-C", repo, "commit-tree", tree, "-p", head], input=msg + "\n",
                                  capture_output=True, text=True, check=True, env=env).stdout.strip()
        out = branch.removeprefix("origin/") + "-ac"
        git_out(repo, "branch", "-f", out, head)
        print(f"{branch}: {len(commits)} commits replayed on {rename_commit[:10]}: branch {out} at {head[:10]}")
        return out
    finally:
        subprocess.run(["git", "-C", repo, "worktree", "remove", "--force", str(wt)], check=True)


def dump_pairs(path):
    """The `(old, new)` pairs of a const-dump of the unrenamed tree: every constant and module name the
    rename changes, with whether it is a constant (column 1) that may get an alias."""
    pairs = {}
    for l in open(path):
        name, mod = l.split("\t")[:2]
        for n, const in ((name, True), (mod, False)):
            m = map_names(n)
            if m != n:
                pairs[n] = (m, pairs.get(n, (m, False))[1] or const)
    return pairs


def aliasable(old):
    return not (old.startswith("_private") or any(c.startswith("_") for c in old.split(".")))


def dump_map(path):
    for old, (new, _) in sorted(dump_pairs(path).items()):
        print(f"{old}\t{new}")


def aliases(dump, out, *imports):
    pairs = [(o, n) for o, (n, const) in sorted(dump_pairs(dump).items()) if const and aliasable(o)]
    lines = ["module", *[f"public import {m}" for m in imports], "@[expose] public section", ""]
    lines += [f'@[deprecated {n} (since := "2026-11-23")] alias _root_.{o} := {n}' for o, n in pairs]
    pathlib.Path(out).write_text("\n".join(lines) + "\n")
    print(f"wrote {len(pairs)} aliases to {out}")
    return pairs


def selftest():
    """Fixtures for check, apply, aliases/dump-map and rebase-branch; prints ok/WRONG lines."""
    import tempfile
    bad = 0

    def verdict(ok, msg):
        nonlocal bad
        print(f"  {'ok' if ok else 'WRONG'}: {msg}")
        bad += not ok

    with tempfile.TemporaryDirectory() as tmp:
        t = pathlib.Path(tmp)
        # the fixtures are their own repositories (or none): Git must not find a checkout around TMPDIR
        ceiling = os.environ.get("GIT_CEILING_DIRECTORIES")
        os.environ["GIT_CEILING_DIRECTORIES"] = str(t.resolve())
        # check: each leftover line is a finding (also the ones a narrower pattern missed), non-leftovers not
        leftovers = ["def f := goldilocksSA sp", "instance : Inhabited Foo := instDecidableEqSAState",
                     "abbrev T := SATrace sp FGP ro", "open SA Node", "the SA as an AC", "\\label{sec:sa-locks}",
                     "\\mathsf{gf\\_votes}", "a Goldfish vote of slot s", "goldfishScore sp", "x ∈ blockVotes B",
                     "Consensus.Goldilocks.SA.Growing.foo", "sa_tips"]
        fine = ["FG-SA and plain-SA are history (fgsa-spec.tex)", "SAME W", "hSA : S ⊆ A", "ml-dsa-fv",
                "Goldfish with locks; the Goldfish head", "the AC interface"]
        d = t / "check"
        (d / "src").mkdir(parents=True)
        (d / "src/X.lean").write_text("\n".join(leftovers + fine) + "\n")
        with contextlib.redirect_stdout(io.StringIO()) as o:
            n = check(str(d))
        found = [l for l in o.getvalue().splitlines() if l.startswith("LEFT ")]
        verdict(n == len(leftovers) and len(found) == len(leftovers)
                and all(f"X.lean:{i}:" in found[i - 1] for i in range(1, len(leftovers) + 1)),
                f"check flags each of {len(leftovers)} leftover lines and none of {len(fine)} others ({n} findings)")
        r = subprocess.run([sys.executable, "-I", __file__, "check", str(d)], capture_output=True, text=True)
        verdict(r.returncode == 1, f"check exits 1 on findings (exit {r.returncode})")
        (d / "ConsensusLean.lean").write_text("module\n\npublic import ConsensusLean.Instances.Goldilocks.Spec.Run\n"
                                              "public import ConsensusLean.Instances.Goldilocks.Spec.SA.State\n")
        (d / "src/Y.md").write_text("the AC and AC\n")
        with contextlib.redirect_stdout(io.StringIO()) as o:
            n = check(str(d))
        verdict("DOUBLED " in o.getvalue(), "check flags doubled prose")
        (d / "ConsensusLean.lean").write_text("module\n\npublic import ConsensusLean.B\npublic import ConsensusLean.A\n")
        with contextlib.redirect_stdout(io.StringIO()) as o:
            check(str(d))
        verdict("UNSORTED ConsensusLean.lean" in o.getvalue(), "check flags a root out of mk_all order")
        (d / "ConsensusLean.lean").write_text("module\n\npublic import ConsensusLean.Instances.Goldilocks.Spec.Run\n"
                                              "public import ConsensusLean.Instances.Goldilocks.Spec.SA.State\n")
        with contextlib.redirect_stdout(io.StringIO()):
            apply(str(d))
            (d / "src/Y.md").write_text("the AC\n")
            n = check(str(d))
        r = subprocess.run([sys.executable, "-I", __file__, "check", str(d)], capture_output=True, text=True)
        verdict(n == 0 and r.returncode == 0, f"after apply: check passes (exit {r.returncode})")
        verdict((d / "ConsensusLean.lean").read_text().split("\n")[2:4] ==
                ["public import ConsensusLean.Instances.Goldilocks.Spec.AC.State",
                 "public import ConsensusLean.Instances.Goldilocks.Spec.Run"], "apply sorts a moved root import")
        with contextlib.redirect_stdout(io.StringIO()) as o:
            apply(str(d))
        verdict("moved 0 files, rewrote 0 files" in o.getvalue(), "apply is idempotent")
        # aliases and dump-map: one source
        dump = t / "base.tsv"
        dump.write_text("".join(f"{n}\t{m}\tdef\n" for n, m in [
            ("Consensus.Goldilocks.SA.goldfishScore", "ConsensusLean.Instances.Goldilocks.Spec.SA.ForkChoice"),
            ("Consensus.Goldilocks.SA.SAParams.mk", "ConsensusLean.Instances.Goldilocks.Spec.SA.Schedule"),
            ("Consensus.Goldilocks.SA.SAState.mk._flat_ctor", "ConsensusLean.Instances.Goldilocks.Spec.SA.State"),
            ("_private.ConsensusLean.Instances.Goldilocks.Spec.SA.State.0.Consensus.Goldilocks.SA.p",
             "ConsensusLean.Instances.Goldilocks.Spec.SA.State"),
            ("Consensus.Goldilocks.Compose.Growing.sa_voteAt_upTo", "ConsensusLean.Instances.Goldilocks.Lemmas.X"),
            ("Consensus.Goldilocks.Store.unchanged", "ConsensusLean.Instances.Goldilocks.Lemmas.X")]))
        with contextlib.redirect_stdout(io.StringIO()) as o:
            dump_map(str(dump))
        dm = dict(l.split("\t") for l in o.getvalue().splitlines())
        with contextlib.redirect_stdout(io.StringIO()):
            al = aliases(str(dump), str(t / "Aliases.lean"))
        consts = {l.split("\t")[0] for l in dump.read_text().splitlines()}
        verdict(all(dm.get(a) == b for a, b in al) and {a for a, _ in al} ==
                {a for a in dm if a in consts and aliasable(a)} and len(al) == 3 and len(dm) == 8,
                f"aliases are the public constants of dump-map ({len(al)} of {len(dm)} pairs)")
        # rebase-branch: the tip-only file and snapshot survive, the branch's changes arrive renamed
        g = t / "repo"
        g.mkdir()
        git = lambda *a: git_out(str(g), *a)
        env = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t"}
        os.environ.update(env)
        git("init", "-q", "-b", "main")
        spec = "ConsensusLean/Instances/Goldilocks/Spec"
        (g / spec / "SA").mkdir(parents=True)
        (g / "scripts").mkdir()
        (g / spec / "SA/F.lean").write_text("namespace Consensus.Goldilocks.SA\ndef goldfishScore := 1\n")
        (g / "scripts/instance-spec-snapshot.txt").write_text("old\n")
        git("add", "-A"); git("commit", "-qm", "base")
        git("checkout", "-qb", "feat")
        (g / spec / "SA/G.lean").write_text("open SA\ntheorem t : SA.goldfishScore = 1 := rfl\n")
        git("add", "-A"); git("commit", "-qm", "feat: G")
        (g / spec / "SA/F.lean").write_text("namespace Consensus.Goldilocks.SA\ndef goldfishScore := 1\n"
                                            "def SAParams := Nat\n")
        git("commit", "-qam", "feat: F")
        git("checkout", "-q", "main")
        (g / "scripts/tool.txt").write_text("only at the tip\n")
        git("add", "-A"); git("commit", "-qm", "tooling")
        with contextlib.redirect_stdout(io.StringIO()):
            apply(str(g))
        (g / "scripts/instance-spec-snapshot.txt").write_text("new\n")
        git("add", "-A"); git("commit", "-qm", "rename")
        with contextlib.redirect_stdout(io.StringIO()):
            out = rebase_branch(str(g), "feat", "main")
        files = set(git("ls-tree", "-r", "--name-only", out).split())
        show = lambda p: git("show", f"{out}:{p}")
        verdict({"scripts/tool.txt", f"{spec}/AC/F.lean", f"{spec}/AC/G.lean"} <= files
                and not any("/SA/" in f for f in files)
                and show("scripts/instance-spec-snapshot.txt") == "new"
                and "def ACParams := Nat" in show(f"{spec}/AC/F.lean")
                and "AC.headScore" in show(f"{spec}/AC/G.lean")
                and git("log", "--format=%s", f"main..{out}").split("\n") == ["feat: F", "feat: G"],
                "rebase-branch keeps the tip-only file and snapshot and replays both commits renamed")
        git("checkout", "-q", "feat")
        (g / "scripts/instance-spec-snapshot.txt").write_text("edited on the branch\n")
        git("commit", "-qam", "feat: snapshot")
        r = subprocess.run([sys.executable, "-I", __file__, "rebase-branch", str(g), "feat", "main"],
                           capture_output=True, text=True)
        verdict(r.returncode != 0 and "instance-spec-snapshot.txt" in r.stdout + r.stderr,
                "rebase-branch stops on a branch commit that edits a snapshot, naming it")
        if ceiling is None:
            del os.environ["GIT_CEILING_DIRECTORIES"]
        else:
            os.environ["GIT_CEILING_DIRECTORIES"] = ceiling
    print("rename_sa self-test:", "passed" if not bad else f"FAILED ({bad})")
    return 1 if bad else 0


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "apply" and len(sys.argv) == 3:
        apply(sys.argv[2])
    elif cmd == "check" and len(sys.argv) == 3:
        sys.exit(1 if check(sys.argv[2]) else 0)
    elif cmd == "selftest" and len(sys.argv) == 2:
        sys.exit(selftest())
    elif cmd == "names":
        sys.stdout.write(map_names(sys.stdin.read()))
    elif cmd == "dump-map" and len(sys.argv) == 3:
        dump_map(sys.argv[2])
    elif cmd == "aliases" and len(sys.argv) >= 4:
        aliases(*sys.argv[2:])
    elif cmd == "rebase-branch" and len(sys.argv) == 5:
        rebase_branch(*sys.argv[2:5])
    else:
        sys.exit(__doc__)

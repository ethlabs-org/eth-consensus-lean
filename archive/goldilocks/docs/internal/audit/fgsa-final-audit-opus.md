# G13 final audit (Opus): FG-SA model store library

Branch `fgsa-composition`, HEAD `8e8b61e`, worktree
`~/worktrees/available-chain-fgsa` (not changed by this audit). Date 2026-09-29.
Scope: the Lean checks of G13 (full build, soundness scans, script robustness,
headline statements against the blueprint, vacuity, merge readiness). The Astra
auditor covers the spec-faithfulness review without the compiler.

## Verdict

**READY WITH FIXES.** 0 BLOCKING, 0 MAJOR, 5 MINOR.

No finding changes a theorem, a statement or a model rule. The five minors are
two script-hardening gaps (each shown with a compiled negative control), two
wording corrections in the report and in `docs/MAP.md`, and one missing T7
input line. They can go in one small commit before the merge, or right after it.

## 1. Independent build

Scratch worktree `/Users/francesco/.claude/jobs/22f59f85/tmp/g13wt` (detached
at `8e8b61e`; `.lake/packages` symlinked; the copied build had every
`AvailableChainFGSA*` artifact deleted, so all 20 FGSA modules compiled from
source). No Lake artifact cache exists on this machine, so "Built" means a real
compile. The scratch worktree is removed.

```text
┌──────────────────────────────────────────────┬──────────────────────────────────────────┐
│ Command (scratch worktree)                   │ Result                                   │
├──────────────────────────────────────────────┼──────────────────────────────────────────┤
│ lake build --wfail AvailableChainFGSA        │ pass, 3376 jobs, 20 FGSA modules built   │
│ (FGSA artifacts deleted first)               │ from source, 0 warnings, 54 s            │
│ bash scripts/check-fgsa.sh                   │ exit 0: 784 constants, 431 theorems;     │
│                                              │ 782 lease-checked (2 generic skipped),   │
│                                              │ 107 lease arguments; negative control    │
│                                              │ rejected                                 │
│ lake build --wfail (all default targets)     │ pass, 3600 jobs (other libraries         │
│                                              │ replayed from the branch build)          │
│ Tests/Axioms.lean output                     │ 206 lines: 123 {propext, choice, Quot},  │
│                                              │ 53 {propext, Quot}, 22 {propext}, 8 none │
│ 206 `theorem` lines in Proofs/ vs 206        │ one-to-one; no private theorem; no       │
│ `#print axioms` lines                        │ theorem in Model/ or Statements/         │
│ grep sorry/admit/native_decide/axiom         │ only two words in comments               │
└──────────────────────────────────────────────┴──────────────────────────────────────────┘
```

All counts agree with the Task 13 report §4 (784/431, 107, 3600, 206 and the
123/53/22/8 split).

## 2. Independent soundness scans (own Lean scripts)

Scripts (kept for reference, outside every repository):
`/Users/francesco/.claude/jobs/22f59f85/tmp/G13Scan.lean`,
`G13Check.lean`, `G13Witness.lean`, `G13Outside.lean`, `G13Skipped.lean`.

`G13Scan.lean` does not use `collectAxioms`. It walks the constant graph
itself (types, definition values, theorem proofs, inductive constructors,
recursor rules).

```text
┌──────────────────────────────────────────────┬──────────────────────────────────────────┐
│ Check                                        │ Result                                   │
├──────────────────────────────────────────────┼──────────────────────────────────────────┤
│ Axioms reachable from all 784 FGSA constants │ closure of 13926 constants; axioms =     │
│ (proofs included)                            │ {propext, Classical.choice, Quot.sound}  │
│ sorryAx / hasSorry in any FGSA theorem value │ none; every theorem value is loaded      │
│ Statement closure (theorem types, def types  │ 2369 constants; 51 flagged, ALL core     │
│ and values; proofs excluded): unsafe, opaque │ Lean primitives (Nat.add … extern,       │
│ (incl. partial), implemented_by, extern      │ Lean.Name.* implemented_by,              │
│                                              │ String.Internal.length opaque); 0 in     │
│                                              │ AvailableChain.*                         │
│ FGSA-module constants outside the namespace  │ only compiler-generated names (eq_N,     │
│ AvailableChain.FGSA                          │ match_N, splitter, _simp, _proof, Repr   │
│                                              │ matchers); no hand-written declaration   │
│ Lease-scan skipped constants                 │ GridCO.recordGenuine.eq_1,               │
│                                              │ GridCO.admissionLevels.eq_1 (both        │
│                                              │ auto-generated equation lemmas)          │
│ Lease rule (project scan, reproduced)        │ 107 arguments, all slowLeasePolicy       │
└──────────────────────────────────────────────┴──────────────────────────────────────────┘
```

## 3. Script robustness (negative controls, compiled in the scratch tree)

I added a module `ZNeg` (imported by the root) with: a theorem with `sorry`, a
private theorem with `sorry`, a project `axiom` and a theorem that uses it, a
`native_decide` theorem, and a definition at the default `gridLeasePolicy`.

```text
┌──────────────────────────────────────────────┬──────────────────────────────────────────┐
│ Control                                      │ Result                                   │
├──────────────────────────────────────────────┼──────────────────────────────────────────┤
│ CheckFGSAAxioms: sorry, private sorry,       │ all 6 flagged (incl. the _private name   │
│ axiom, use of axiom, native_decide           │ and the _native aux axiom); exit 1. OK   │
│ CheckFGSALease: def at gridLeasePolicy       │ flagged. OK                              │
│ check-fgsa.sh built-in lease control         │ rejected, as expected. OK                │
│ Root-import check: `import …ZHidden` inside  │ NOT DETECTED: the check passes, ZHidden  │
│ a /- … -/ block of the root; ZHidden has a   │ (with sorry) is never compiled and the   │
│ sorry                                        │ axiom check never sees it → m1           │
│ Lease scan: generic `[LeasePolicy]` wrapper  │ NOT DETECTED: the wrapper is skipped;    │
│ in namespace AvailableChain.GridCO inside an │ the FGSA use of it at slowLeasePolicy    │
│ FGSA module, body `@gate gridLeasePolicy …`  │ passes → m2                              │
└──────────────────────────────────────────────┴──────────────────────────────────────────┘
```

The `--expect` option of the axiom script works as documented (suffix match;
each miss forces exit 2). The direct-import and closure checks use the same
line grep as m1; there, a commented import gives a false alarm, not a miss, so
they are conservative.

## 4. Headline statements against the blueprint

I printed each K-table name with `#check` (file `G13Check.lean`) and compared
it with `blueprint/00-outline.md` §3.1.

```text
┌──────────────────┬───────────────────────────────────────────────┬─────────────────────┐
│ K / bp id        │ Lean statement vs blueprint                   │ Status              │
├──────────────────┼───────────────────────────────────────────────┼─────────────────────┤
│ K1 bp.reconcile  │ reconcile_harmless_origin: FastOrigin F₀,     │ matches ("origin    │
│                  │ F₀ ⪯ F, hL, hG, hS → reconcile = S-update     │ witnesses imply     │
│                  │ only, S extends. admitBlock_reconcile_        │ preservation");     │
│                  │ harmless: CStoreInv, hL/hG/hS at the new F →  │ equality is         │
│                  │ obligations, genuine, fastWrite unchanged, S  │ stronger. hL over   │
│                  │ extends. No fastWrite premise                 │ due leases: stated  │
│ K2 comp.output-  │ ∀ Reachable: NestOK ∧ confirmed = S ∧ stable  │ matches; rfl parts  │
│ Nesting.v2       │ = confirmed                                   │ disclosed (DQ7)     │
│ K3 bp.frame,     │ reconcile_frame (13 fields), storeControls_   │ matches             │
│ bp.reconcile     │ reconcile, storeControls_eq, reconcile_idem   │                     │
│ K4 bp.store.v1   │ KitFG.StoreInv: closed, gen, Fmem, hmax =     │ every clause        │
│                  │ frontier, pair = lexMax, F ⪯ J, Fcar; J_mem;  │ covered             │
│                  │ F/pair/H monotone (process_*, clock_fg);      │                     │
│                  │ cumulative (process_/clock_cumulative)        │                     │
│ K5 local         │ preceq_of_eraseFG_preceq, compatible_iff_     │ matches (premise:   │
│ bp.carrier.v1    │ eraseFG, eraseFG_injOn under ViewRootInj;     │ local root inj. by  │
│                  │ viewRootInj_TF from CStoreInv                 │ construction, DQ2)  │
│ K5 cross-node    │ 4 theorems: CStoreInv, MetaInv at both +      │ matches, with the   │
│                  │ ContentAgree st st' (store-pair premise)      │ disclosed premise   │
│ K8 input         │ admitBlock_sufficient: wellFormed, parent     │ store part only;    │
│                  │ stored, slot ≤ Σ.s, fresh root, F ⪯ b → b in  │ F ⪯ b equals "com-  │
│                  │ base list and fgBlock in Σ.T                  │ patible, not stored"│
│ bp.activeView.v1 │ items 1–5 each present; item 6 (noVeto,       │ matches; antitone   │
│                  │ releaseCount = 0) is extra                    │ has the right       │
│                  │                                               │ direction           │
│ SA bridges       │ offGate (no premise but "not a gate time"),   │ premises as in the  │
│                  │ gate (hnew), block step sameF / movedF        │ report              │
└──────────────────┴───────────────────────────────────────────────┴─────────────────────┘
```

No statement is weaker than its blueprint statement without a report line. The
G13 check item (G9 m3) holds: `reconcile_harmless` is cited only at its
definition, in the proof of `reconcile_harmless_origin`, in `Tests/Axioms.lean`
and as "helper" in `docs/MAP.md:663`.

### Vacuity witnesses (`G13Witness.lean`, compiles; axioms of `notAgree`: the standard three)

Stores: `stX = process (clock initial 20) wa` and
`stY = process (process (clock initial 20) w1) wb`, with the honest roots of
`GridCO.propose`: `ba = node(genesis, 4, ⟨4⟩)`, `c1 = node(genesis, 1, ⟨1⟩)`,
`bb = node(c1, 2, ⟨4⟩)` (4·1 = 4, 1·1 = 1, 2·(1+1) = 4).

- Both stores are `Reachable` with non-genesis blocks, so `CStoreInv` and
  `MetaInv` hold at non-trivial states (premises are satisfiable).
- A bad hand-set state fails each invariant: `¬ CStoreInv pT stR0` (baseTree),
  `¬ NestOK stR0`, `¬ MetaInv` of a state with a duplicated wire.
- `¬ ContentAgree stX stY`: confirms the report claim that `ContentAgree` is
  false on honest-fork runs under the arithmetic roots (DQ10/I9).
- The conclusion of `rootInjectiveOn_across` is FALSE for (stX, stY): the
  `ContentAgree` premise is load-bearing, not decorative.
- An honest node that holds `ba` REFUSES the honest block `bb` (DQ2 root
  test): `bb ∉ (process (process stX w1) wb).base.blocks`. See m4.

### Report claims

No overclaim of a result. The cross-node results are correctly scoped to store
pairs under `ContentAgree`; the DQ10 root limit is stated and my witness
reproduces it. Two wording issues (m3) and one missing consequence (m4).

## 5. Merge readiness

`git merge-tree --write-tree main HEAD` against current `main` (`fe6c654`;
note: `main` moved from `3de09f0` to `fe6c654` during this audit, doc-only
commits): **no conflict** (tree `df107e08`). The expected conflicts do not
occur: `main` does not change `lakefile.toml` after the merge base `d415a7c`,
and its `docs/MAP.md` edits do not overlap the new last section. The branch
adds files only (37 files, 11032 insertions, 0 deletions); outside its own
files it touches only `lakefile.toml` (one `[[lean_lib]]`, one
`defaultTargets` entry) and `docs/MAP.md` (one appended section). `main`
changes no module in the FGSA import closure (Model, GridCO, SA, SimplexFG,
KitFG, Statements), no `lake-manifest.json` and no toolchain. `main`'s lock
and registry scripts import only `AvailableChainFramework` / `Registry`, so a
new default target does not affect them.

Merged tree (checked out in the scratch worktree, Framework/Registry
artifacts from the `main` worktree build, FGSA artifacts from step 1):
`lake build --wfail` pass (3609 jobs, all replayed: every trace matched), and
`bash scripts/check-fgsa.sh` passes (same counts as step 1).
Re-run `merge-tree` at merge time, because `main` is moving.

## 6. Findings

### MINOR

**m1. Root-import check accepts a commented import.**
`scripts/check-fgsa.sh:11-14`. The grep reads `import` lines in the root
without comment removal. A file whose only root import is inside `/- … -/`
passes the check, is never compiled (the lib roots are the root module only)
and is never seen by the axiom check. Compiled control: `ZHidden` with a
`sorry` passed. No such file exists now. Fix: pipe the root through the
existing `strip_comments` tokenizer before the grep, or (stronger) in
`CheckFGSAAxioms.lean` require that each `AvailableChainFGSA/**/*.lean` module
is in `env.header.moduleNames`.

**m2. Lease scan skips any generic declaration outside the namespace.**
`scripts/CheckFGSALease.lean:94-95`. The skip applies to every FGSA-module
constant whose name is not under `AvailableChain.FGSA` and that has a
`[LeasePolicy]` binder. This includes hand-written declarations in another
namespace and every `private` declaration (a `_private.…` name does not have
the prefix `AvailableChain.FGSA`). The body of a skipped constant is not
scanned, so a wrapper can fix `gridLeasePolicy` inside and be used at
`slowLeasePolicy`. Compiled control: `GridCO.sneakyGate` in an FGSA module
passed. Now: only 2 skipped, both auto-generated (`GridCO.recordGenuine.eq_1`,
`GridCO.admissionLevels.eq_1`), so there is no present defect. Fix: skip only
compiler-generated equation lemmas (last component `eq_<k>` / `eq_def`, via
`Lean.Meta.isEqnThm` or a name test), and scan the body of every other
constant with the bound-variable policy accepted only when the constant is
itself generic and its body passes the binder through.

**m3. "No premise" wording for `contentAgree_self`; "run premise" for
`ContentAgree`.** Task 13 report lines 42 and 161-162 say that
`contentAgree_self` needs no premise. The Lean statement is
`CStoreInv p st → MetaInv p st → ContentAgree st st`. Correct text: "no content
premise; it needs `CStoreInv` and `MetaInv`, which hold at every reachable
state". Also report line 158 and `docs/MAP.md:650` call `ContentAgree` a
"run premise". In the plan (DQ3) it is the STORE-PAIR form; the run premise is
`ContentRootInjective` (T7). Correct text: "store-pair premise (DQ3(b)); run
form `ContentRootInjective` in T7".

**m4. DQ10 consequence for T7: honest refusal, not only vacuity.** Report §5
(lines 159-165) says the root premises fail on honest forks and the theorems
that use them are then vacuous. It does not say that the MODEL itself then
refuses an honest block: with the DQ2 root test, a node that holds `ba`
refuses the honest `bb` with the same root (compiled witness above). The spec
idealizes distinct roots (spec 167, 521), so on such a run the model and the
spec differ, and the run form of K8 cannot hold for `bb`. This is inside the
declared DQ10 decision; add one T7 input line: "under DQ10 collisions the DQ2
root test refuses honest blocks; the K8 run form and every coverage claim need
`RootInjective` for this reason too".

**m5. Q1/Q5 grep is narrower than the Global Constraint text.**
`scripts/check-fgsa.sh:70` greps `ProtocolSpec|Generic\.Run|World|pendingRow`;
the plan text (Global Constraints, Q1/Q5) also names `Run`, `Env`,
`Interface` and `Claims`. I grepped these words: they occur only in comments
(`Model/Store.lean:51` "Run a GridCO step"). No present defect; the script
follows the plan's own grep. Fix (optional): add `\bEnv\b|Interface|Claims`
on stripped text, or record in the plan that the grep is the operative rule.

### Checked with no finding

Model-only caches not read by duties (DQ8) was G6 scope and I did not re-audit
it. Namespace rule: no hand-written declaration outside `AvailableChain.FGSA`.
File-scope rule: the branch edits no file of another library. Axiom coverage:
the axiom script loads private data and theorem proofs (the private-sorry
control proves it).

## 7. Validation summary

```text
┌──────────────────────────────────────────────┬──────────────────────────────┐
│ Command                                      │ Result                       │
├──────────────────────────────────────────────┼──────────────────────────────┤
│ lake build --wfail AvailableChainFGSA (clean │ pass, 20 modules from source │
│ FGSA artifacts)                              │                              │
│ bash scripts/check-fgsa.sh (branch, merged)  │ exit 0, exit 0               │
│ lake build --wfail (branch, merged)          │ pass 3600, pass 3609         │
│ lake env lean --run G13Scan.lean             │ exit 0; standard axioms only │
│ lake env lean G13Check.lean                  │ exit 0 (statements above)    │
│ lake env lean G13Witness.lean                │ exit 0 (+ negative control   │
│                                              │ that the file elaborates)    │
│ negative controls ZNeg / ZHidden / sneaky    │ ZNeg caught; ZHidden and the │
│                                              │ wrapper not caught (m1, m2)  │
│ git merge-tree main(fe6c654) HEAD            │ clean, tree df107e08         │
└──────────────────────────────────────────────┴──────────────────────────────┘
```

Not recompiled by me: the non-FGSA libraries (reused from the branch build and,
for the merged tree, from the `main` worktree build).

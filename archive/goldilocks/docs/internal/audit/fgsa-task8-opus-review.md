# G8 review: Task 8, output nesting (K2)

Reviewer: Opus (independent; did not write the code). Date: 2026-09-29.
Worktree: `~/worktrees/available-chain-fgsa`, branch `fgsa-composition`.
Commit under review: `10834ba` ("FGSA store: output nesting (K2)").
Plan: `docs/plans/2026-09-29-fgsa-model-store.md`, Task 8 (lines 1899–1939),
Global Constraints 10–11 (lines 393–394), review gates (lines 2409–2439).

## Verdict

**PASS.** No blocking finding. No major finding. Three minor findings. None
of them blocks the CHECKPOINT.

## Sources

```text
┌──────────────────────────┬──────────────────────────────────────────────────┐
│ Source                   │ Location                                         │
├──────────────────────────┼──────────────────────────────────────────────────┤
│ Blueprint (pinned)       │ blueprint/archive/00-outline-03afa5ae.md 475–485 │
│                          │ (sha256 03afa5ae… verified)                      │
│ Blueprint proof          │ blueprint/01-foundations.md §7, lines 372–392    │
│ Spec                     │ spec/archive/fgsa-protocol-2e884811.tex 558–569  │
│ Statement                │ AvailableChainFGSA/Statements/Store.lean:10–14   │
│ Proofs                   │ AvailableChainFGSA/Proofs/Nesting.lean:15–119    │
│ Definitions used         │ Statements/Invariants.lean:21–28 (Reachable,     │
│                          │ NestOK); Model/Store.lean:36–40, 57–72;          │
│                          │ Model/Clock.lean:25–55; Model/Handlers.lean:17–82│
└──────────────────────────┴──────────────────────────────────────────────────┘
```

## Check 1: statements against the blueprint

The blueprint `comp.outputNesting.v2`: "At every completed local event F⪯S
and both available accessors equal S, for every a and without synchrony,
including empty and vetoed gates. Premises: Base initialized execution."

`OutputNestingStored p` (Store.lean:13–14) is:
`∀ st, Reachable p st → NestOK st ∧ confirmed st = st.base.stableRecord ∧ stable st = confirmed st`.

```text
┌──────────────────────────────┬──────────────────────────────────────────────┐
│ Blueprint part               │ Lean                                         │
├──────────────────────────────┼──────────────────────────────────────────────┤
│ every completed local event  │ every `Reachable p` state. `Reachable` is an │
│                              │ over-approximation (Invariants.lean:10–20):  │
│                              │ any tick time, any wire, no input check.     │
│                              │ This makes the statement stronger.           │
│ F ⪯ S                        │ `NestOK`: `eraseFG st.fg.F ⪯ stableRecord`   │
│ both available accessors = S │ `confirmed st = S`, `stable st = confirmed`  │
│ every a, no synchrony        │ no fault or synchrony parameter exists       │
│ empty and vetoed gates       │ `gateStep_nest` has no premise on the gate   │
│                              │ result (Nesting.lean:32–33)                  │
│ Base initialized execution   │ `Reachable.init` = `initial p.n`             │
└──────────────────────────────┴──────────────────────────────────────────────┘
```

The spec defines three accessors: `get_finalized = Σ.F`,
`get_confirmed = S`, and `get_stable`, which returns the same tip (spec
558–561). The spec has no third tip. The statement covers the two stored
tips that the spec defines (F and S). It is not about a model-only cache
(`frozen`, `early`, `releaseSnapshots`, `goldfishRecord`, `base.proposals`
are not read). DQ7 records the reading "F ⪯ S ⪯ available" as this
statement. I agree with that reading.

`comp.outputNesting.v1` (Nesting.lean:16) is the blueprint text: for any
F, S, `F ⪯ (if F ⪯ S then S else F)`.

The seven statements in `Proofs/Nesting.lean` and the definition in
`Statements/Store.lean` are the plan code verbatim (compared line by line
with plan lines 1914–1931).

No statement is weaker than its blueprint statement. No new hypothesis:
`process_nest` and `clock_nest` take only `h : NestOK st`, which is the
induction hypothesis.

## Check 2: "no other invariant" and vacuity

The statement is not vacuous, and it is not only a fact about a normalized
field:

- `NestOK` is not a tautology. The fixture `stR0` has F = B1 and S = b1'
  (Tests/Smoke.lean:121), where `NestOK` is false.
- F moves under `process`. The state `stA` is built by `process` from a
  store with `now := 12`. There, F = B1 and S = b1 after `reconcile`
  (Smoke.lean:143–156). So the `reconcile` branch of `process_nest` has
  real content.
- S changes in two places only: the SA gate (`SA.gate` through `onView`)
  and `normalizeS`. `gateStep` always ends with `normalizeS`
  (Clock.lean:29). Every F change in `admitBlock` is followed by `reconcile`,
  which ends with `normalizeS` (Handlers.lean:74; Store.lean:68).
  `clockPre` keeps S by `rfl` in each of its eight branches
  (Nesting.lean:94–98). Thus a one-step preservation proof needs no other
  invariant. This agrees with bp01 §7: "The final normalization also
  enforces nesting in any input state."
- Conjuncts 2 and 3 are true by definition (`rfl`, Nesting.lean:115). See
  minor finding m1.

The statement does not claim safety or monotonicity of S. The blueprint and
the spec (line 568) also do not claim it.

The duties do not write the store: `headVote` returns a `Block`, `propose`
returns an `Option (Msg p.n)`, and `attest` returns `RowBody × Record`
(Model/Frame.lean:92, 144, 197). Λ is not a store field (DQ4). Thus the
local store events are `process` and `clock` only, and `Reachable` covers
them. The run lift is composition T7 (plan DQ7, Out of scope).

## Check 3: lease instance

`#check` on the built tree (pp.explicit):

```text
┌──────────────────────────────┬──────────────────────────────────────────────┐
│ Constant                     │ [LeasePolicy] argument                       │
├──────────────────────────────┼──────────────────────────────────────────────┤
│ GridCO.admitVote             │ none                                         │
│ GridCO.admitProposal         │ none                                         │
│ GridCO.admitVote_stable      │ yes (unused by the statement)                │
│ FGSA.admitProposal_stable    │ none                                         │
└──────────────────────────────┴──────────────────────────────────────────────┘
```

The one lease-parametric GridCO lemma, `admitVote_stable`, is applied as
`@GridCO.admitVote_stable GridCO.slowLeasePolicy _ _ _ _`
(Nesting.lean:60). This agrees with Global Constraint 11 and N3. No other
GridCO lemma is used. `clockPre_stable` uses `rfl` on the actual
definitions (`SA.release`, `GridCO.freeze`), so no instance can be selected
silently there.

`admitProposal_stable` (Nesting.lean:48–50) has `{n : Nat}` next to
`q : GridCO.Params`. This is not an M11 violation: M11 is about the FGSA
`Params` and `p.n`. In GridCO, `State n` does not depend on `q.n`, and the
GridCO lemmas have the same form (`admitVote_stable (p : Params) {n : Nat}`).

## Check 4: build and axioms

Scratch worktree at `10834ba` (detached), `.lake/packages` linked from the
main worktree, `.lake/build` cloned from it. I removed the build outputs of
`AvailableChainFGSA.Statements.Store`, `AvailableChainFGSA.Proofs.Nesting`
and the root module, so these modules were compiled again.

- `bash scripts/check-fgsa.sh`: exit 0. Output: "Built
  AvailableChainFGSA.Statements.Store", "Built
  AvailableChainFGSA.Proofs.Nesting", "Build completed successfully (3343
  jobs)"; root imports, native evaluation, direct imports, import closure
  and Q1/Q5 boundary pass; "checked 557 constants, 234 theorems"; "all FGSA
  checks pass". The counts agree with the execution note (plan line 1939).
- `#print axioms`: `outputNesting_stored`, `process_nest`, `clock_nest`,
  `admitProposal_stable`: `[propext, Classical.choice, Quot.sound]`.
  `outputNesting_v1`: `[propext]`. No `sorry`, no project axiom, no native
  evaluation.

The scratch worktree was removed after the check.

## Findings

### BLOCKING

None.

### MAJOR

None.

### MINOR

- **m1** (Statements/Store.lean:14; Proofs/Nesting.lean:115). Conjuncts 2
  and 3 are true by definition (Model/Store.lean:38–40). They give no fact
  beyond the accessor definitions. This is as the plan intends (DQ7: "The
  accessor conjuncts are `rfl`"). They are not a weakening, because the spec
  defines both accessors as S. They are useful as a regression check: if a
  later change gives `confirmed` or `stable` a different body, the `rfl`
  fails. No change is necessary. Optional: say "definitional" in the
  docstring, so that a reader does not count them as proved content.
- **m2** (Statements/Invariants.lean:27–28). `NestOK` reads the fields
  `st.fg.F` and `st.base.stableRecord`, not the accessors `finalized` and
  `stable`. For S, conjuncts 2–3 connect the field to both accessors. For F,
  the connection `finalized st = st.fg.F` is only definitional
  (Model/Store.lean:36) and is not in the statement. The result is correct.
  Optional for T1/T7 consumers: a one-line corollary
  `Block.Preceq (eraseFG (finalized st)) (stable st)` on reachable states,
  in the accessor vocabulary of spec 558–561.
- **m3** (Proofs/Nesting.lean:11–13, 67–69; plan line 1939). The text "every
  other step writes neither F nor S" is correct for completed events only.
  Inside `admitBlock`, the intermediate state `st1` (Handlers.lean:70–73)
  can have a moved F and the old S before `reconcile`. The statement does
  not claim `st1`, and the blueprint claims only completed events, so this
  is not a defect. Optional: add "completed" to the module docstring, so
  that a T7 author does not read nesting as a fact about sub-steps.

### Observations (no action)

- `admitProposal_stable` proves the vote fold locally because the GridCO
  `fold_stable` is private (History.lean:52). This is the fallback that the
  plan permits (R2; Task 10 text). The proof is short and correct.
- `Reachable` has no input check and allows backward clocks. Because it is
  an over-approximation, it makes `OutputNestingStored` stronger, not weaker.

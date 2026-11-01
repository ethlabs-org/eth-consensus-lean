# G10 review — Task 10 (admission agreement, block-step bridge, sufficiency)

Reviewer: Opus (independent; did not write the code). Date: 2026-09-29.
Commit: `3840172` (parent `a339fd8`), branch `fgsa-composition`.
Plan: `docs/plans/2026-09-29-fgsa-model-store.md`, Task 10 (lines 2033–2165),
Global Constraints (216–243), review gates G7–G12 and the blocking list
(2411–2433).
Blueprint: bp00 `R/blueprint/archive/00-outline-03afa5ae.md` §3.1 (sha256
`03afa5ae…`, as pinned), bp01 `R/blueprint/01-foundations.md` §10 (sha256
`989289cc…`, as pinned). Spec: `R/spec/archive/fgsa-protocol-2e884811.tex`
(acceptance 530–541, `on_block` 804–829). Comp: `R/codex/lean-composition-plan.md`
(sha256 `228dbe98…`) D3 and §4.3.

## Verdict: PASS

No BLOCKING finding. No MAJOR finding. Four MINOR findings. None of them
stops the checkpoint.

## Validation

- Scratch worktree at `3840172` (detached), `.lake/packages` symlinked, the
  `.lake/build` of the main worktree copied. I deleted every build output of
  `Proofs/Admission` and `Statements/Invariants`. Both modules compiled again
  (`Built AvailableChainFGSA.Statements.Invariants (3.7s)`,
  `Built AvailableChainFGSA.Proofs.Admission (3.7s)`).
- `bash scripts/check-fgsa.sh`: exit 0. `lake build --wfail AvailableChainFGSA`
  passes (3345 jobs, no warning). Root imports, native scan, direct imports,
  import closure and the Q1/Q5 grep print nothing. Axioms:
  `checked 640 constants, 307 theorems`.
- `CheckFGSAAxioms.lean --expect` with `Inv0`, the 17 planned names and the
  11 helpers: exit 0, every name is checked. `#print axioms` of
  `admitBlock_sufficient`, `base_admitProposal_accepts`,
  `admitBlock_accepted_eq`, `actView_admitBlock_sameF`,
  `actView_admitBlock_movedF`: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, `set_option`, `implemented_by`, `unsafe`,
  `local instance`, `private` or native evaluation in the two files.
- Scratch Lean checks (not committed; see Check 2 and Check 4).
- The scratch worktree and the scratch files are removed.

## Check 1 — statements against the plan and the blueprint

A script compared each declaration of the plan code block (Task 10, Step 1)
with the file after whitespace normalization, docstrings included.

- 16 of 17 statements are equal to the plan text (the `movedF` difference
  that the script reported is a split artifact at `:= fun c`; I compared it by
  eye: equal). All 17 docstrings are equal.
- `admitBlock_accepted_eq` (Admission.lean:286–297) has no
  `(h : Inv0 p st)`. Every other token is equal. A premise less gives a
  stronger statement. The execution note declares the change. See MINOR m1.
- The Task 10 code block of the plan did not change between `8947f48`
  (before Task 7) and `3840172`. The commit changes only the check boxes and
  the execution note of Task 10.
- Extra declarations (11 helpers) are the ones that the execution note lists.
  None of them adds a premise to a planned statement.

Each statement against its source:

```text
┌──────────────────────────────┬──────────────────────────────┬────────────────┐
│ Lean (Admission.lean)        │ Source                       │ Result         │
├──────────────────────────────┼──────────────────────────────┼────────────────┤
│ pickPair_some_spec :18       │ helper (selector soundness)  │ equal          │
│ parentFG_spec :28            │ spec 519–522 (roots          │ equal; iff,    │
│                              │ injective: parent is the     │ premise only   │
│                              │ block under B.parent)        │ rootInj        │
│ eraseFG_fgBlock, fgBlock_*   │ bp.carrier.v1 (erasure keeps │ equal (flat    │
│ :45–60                       │ parent, slot, root; DQ1)     │ form, DQ1)     │
│ toRow_forall₂ :69            │ audit M2; DQ12               │ equal          │
│ blockAccepted_of_wellFormed  │ DQ9, DQ14; spec 530–536      │ equal; exact   │
│ :86                          │                              │ Bool equation  │
│ rootTest_iff_blockTest :113  │ DQ2 (the two duplicate tests │ equal          │
│                              │ agree under a root premise)  │                │
│ fg_on_block_accepts :150     │ bp.frame.v1 ("FG.Store on    │ equal; no      │
│                              │ successful admission")       │ Inv0 (G4 d1)   │
│ base_admitProposal_accepts   │ comp §4.3 "small lemma"      │ equal; 7 exact │
│ :240                         │                              │ field equations│
│ admitBlock_accepted_eq :286  │ audit M4; spec 804–829 order │ stronger (no   │
│                              │ (admit, votes, finality,     │ Inv0)          │
│                              │ reconcile, rows)             │                │
│ actView_admitBlock_sameF     │ comp D3; J3                  │ equal          │
│ :370                         │                              │                │
│ actView_admitBlock_movedF    │ comp D3; J3; bp.reconcile.v1 │ equal          │
│ :412                         │ exact writes                 │                │
│ admitBlock_sufficient :464   │ bp.receiptCoverage.v1, bp01  │ equal under    │
│                              │ §10.1 last paragraph (K8     │ DQ2 (see Check │
│                              │ local step)                  │ 4, m2)         │
└──────────────────────────────┴──────────────────────────────┴────────────────┘
```

No statement is weaker than its blueprint statement without a report line.

## Check 2 — Inv0

- The definition (Invariants.lean:67–70) is the plan text: the FG store
  invariant, root injectivity of Σ.T, and the base list as Σ.T erased. It is
  the conjunction of the fields `fg`, `rootInj`, `baseTree` of `CStoreInv`.
- `git diff 2e684fa 3840172 -- Statements/Invariants.lean` adds only `Inv0`
  (6 lines at the end). `Reachable`, `NestOK`, `SACompat`, `FastOrigin` and
  `CStoreInv` do not change. So the G7 pass of those definitions stays valid.
- It is not vacuous and not trivial. Scratch proofs (compiled):
  `Inv0 p (initial p.n)` holds for every `p` (from
  `KitFG.storeInv_init p.E p.cfg`), and `Inv0` is false on the initial state
  with an empty base list (`baseTree` needs the erased genesis).
- It is ASSUMED in Task 10, not proved preserved. It is the premise of
  `rootTest_iff_blockTest`, `base_admitProposal_accepts` and three helpers.
  The three bridges and `admitBlock_sufficient` take `CStoreInv` and build
  `Inv0` from its three fields (Admission.lean:378, 427, 473).
- Where it is discharged: Task 11 (`cstoreInv_init`, `cstoreInv_process`,
  `cstoreInv_clock`, `storeInvariant`, plan lines 2193–2197, 2259–2262).
  `CStoreInv` on `Reachable` then gives `Inv0` on `Reachable`. There is no
  circularity: the accepted-block case of `cstoreInv_process` uses
  `base_admitProposal_accepts` with `Inv0` of the PRE-state, which comes from
  the induction hypothesis. G11 must check this call.

## Check 3 — G7 note on `base_admitProposal_accepts`

The G7 note asks that the lemma holds on the over-approximate `Reachable`:
any tick time, any wire, no input check. It does, and more:

- The statement has no `Reachable` premise at all. It holds for every state
  with `Inv0`, every `s`, `raw`, `support` and `rows`. Its only other premises
  are `hP` (the parent lookup) and `hacc` (the composite test). There is no
  `wellFormed` premise.
- Any tick time: `Time = Int`. The slot bound of `GridCO.admitProposal` is
  `(now / (4 * engine.Δ)).toNat`; the composite bound is
  `st.slot p = p.slotOf st.base.now`. The proof passes `hsl` from `hacc`
  directly as the GridCO bound (Admission.lean:252–255), so the two are the
  same term by definition, for every `now` (also negative, also `Δ = 0`).
- Any wire: the carried-vote fold is covered for every `raw` by
  `foldVotes_fields` (:194), an induction over the list. It writes only the
  vote pool and its stamps. The proposer test uses `s = b.slot` from `hacc`.
  The known-parent and new-block tests come from `Inv0` (`accepted_base_facts`,
  :138): the parent is the erased `P ∈ Σ.T`; a stored `b` has a stored FG
  block with the root of `b`, which `hacc` refuses.
- The GridCO fold lemmas are `private` (`Map.lean:467–487`). The plan allows a
  local fold proof in that case. The helpers unfold `GridCO.admitVote`; they
  are not copies of GridCO lemmas.

## Check 4 — sufficiency (`admitBlock_sufficient`)

bp01 §10.1 (last paragraph): "An absent block has its parent, is at a valid
nonfuture slot, has a valid proposer/row-round check, and extends the current
F, so it is admitted. These are the on_block guards, not merely a raw receipt
assumption." Spec 530–536: the store holds the parent, the slot is at most
Σ.s, the store does not hold the block, `Σ.F ⪯ B`.

```text
┌──────────────────────────────┬────────────────────────────────────────────┐
│ Blueprint condition          │ Lean premise (Admission.lean:464–469)      │
├──────────────────────────────┼────────────────────────────────────────────┤
│ checked block; valid         │ hwf : wellFormed p ⟨.proposer s, .proposal │
│ proposer / row-round check   │ b raw support rows⟩ (non-genesis, s =      │
│                              │ b.slot, parent slot, vote and row checks)  │
│ has its parent               │ hpar : b.parent ∈ st.base.blocks           │
│ valid nonfuture slot         │ hslot : b.slot ≤ st.slot p                 │
│ absent                       │ hfresh : ∀ c ∈ base.blocks, c.root ≠ b.root│
│                              │ (root freshness; DQ2)                      │
│ extends the current F        │ hF : Block.Preceq (eraseFG st.fg.F) b      │
│ store premise                │ h : CStoreInv p st                         │
└──────────────────────────────┴────────────────────────────────────────────┘
```

Conclusion: `b` is in the base list of `process p st ⟨…⟩`, and the FG block
`fgBlock P b rows` of the exact stored parent `P` is in Σ.T. This is
"admitted" on both sides of the store. It is the real statement, not a
trivial variant:

- The premises do not include the conclusion: `hfresh` excludes that `b` is
  already stored.
- The premises are jointly satisfiable. Scratch proof (compiled): for the
  smoke parameters `pT` and the state `{ base := { now := 4 } }` (slot 1), I
  proved `CStoreInv` field by field and applied `admitBlock_sufficient` to the
  slot-1 child of genesis with empty lists. All five premises close by
  `decide` or `simp`.
- The conclusion runs `process`, not `admitBlock`: the wire decode is part of
  the claim (`process … = admitBlock …` by `rfl`).
- The only difference from the blueprint text is "absent" versus "fresh
  root". It is the DQ2 decision (the model's duplicate test is by root), and
  `rootTest_iff_blockTest` is the declared bridge. With `b ∉ base.blocks` and
  the root premise of that lemma, `hfresh` follows in one step. So the run
  form of K8 (T7, out of scope) gets the blueprint premise from
  `RootInjective`. See MINOR m2 for the docstring.
- The proof follows the plan note: `baseTree` and `parentFG_spec` give `P`;
  `F ≠ b` from the fresh root; `F ⪯ b.parent = eraseFG P`; reflection
  (`preceq_of_eraseFG_preceq`, `viewRootInj_of_rootInj`) gives `F ⪯ P`, then
  `F ⪯ fgBlock P b rows`; `blockAccepted_of_wellFormed` closes `hacc`. Both
  branches (F moves or not) are proved; the moved branch uses
  `reconcile_frame` and `reconcile_fg`.

## Check 5 — lease instance, parameter indexing, imports, form

- Lease instance: the file uses no GridCO lemma. It uses only the GridCO
  definitions `admitProposal`, `admitVote`, `blockKnown`, `fromHead` and
  types. `#check @GridCO.admitProposal` and `#check @GridCO.admitVote` show
  no `[LeasePolicy]` argument (`GridCO/Model/Protocol.lean` has no section
  `variable`). So no explicit `GridCO.slowLeasePolicy` is needed, and none is
  missing.
- No free `n` next to `p : Params`: each declaration that takes `p` uses
  `State p.n`, `HeadWire p.n`, `RowWire p.n`, `FGBlock (Fin p.n)`. The
  declarations with `{n : Nat}` (`parentFG_spec`, `eraseFG_fgBlock`,
  `fgBlock_*`, `toRow_forall₂`, `admitVote_withBlocks`,
  `foldVotes_withBlocks`, `foldVotes_fields`, `admitProposal_of_accept`,
  `activeCompatible_eq`) take no `p : Params`; the GridCO helpers take
  `q : GridCO.Params`, which has no `n`.
- Imports: Admission.lean imports only `AvailableChainFGSA.Proofs.Reconcile`.
  The root imports `Proofs.Admission`. The script's direct-import and closure
  checks pass.
- File form: `module`, `public import`, `@[expose] public section`,
  `namespace AvailableChain.FGSA`, `end …`, `end`. Statements in
  `Statements/`, proofs in `Proofs/`.
- The J3 bridges: `sameF` states that the new active view IS
  `GridCO.admitProposal` on the old view (comp D3: "SA writes run unchanged on
  the view"). `movedF` states it as that admission, then reconcile's writes
  with the new F. The use of `KitFG.on_block_F_mono` (F only moves forward,
  so the new filter is inside the old one) is a standard FG lemma, not a
  premise. Both bridges use only the `Inv0` part of `CStoreInv`.

## Findings

BLOCKING: none.

MAJOR: none.

MINOR:

- **m1** — plan line 2110 versus `AvailableChainFGSA/Proofs/Admission.lean:286`
  (`admitBlock_accepted_eq`). The file drops `(h : Inv0 p st)`; the plan code
  block still has it. The change is stronger and is in the execution note.
  But the code block is the reference for G13 and for the Task 11 proof note
  of `admitBlock_reconcile_harmless` (plan line 2265), which calls this lemma.
  Fix: remove the premise from the plan code block, or add a one-line note
  next to the statement.
- **m2** — `AvailableChainFGSA/Proofs/Admission.lean:461–468`
  (`admitBlock_sufficient`). The docstring says "absent block … a fresh root"
  and cites bp01 §10.1, but not DQ2. The blueprint premise is "absent"; the
  Lean premise is root freshness. The difference has a report line (DQ2) and
  a bridge (`rootTest_iff_blockTest`), so the statement is not weaker without
  a report. Fix: add `DQ2` to the docstring tag. Optional (for T7): a
  corollary with `b ∉ st.base.blocks` and the root premise of
  `rootTest_iff_blockTest` in place of `hfresh`.
- **m3** — `AvailableChainFGSA/Proofs/Admission.lean:378, 427, 473`. The term
  `⟨h.fg, h.rootInj, h.baseTree⟩ : Inv0 p st` is written three times, and
  Task 11 will need it again. Optional: a named projection
  `CStoreInv.toInv0` in `Proofs/`.
- **m4** — `AvailableChainFGSA/Proofs/Admission.lean:53–61`. `fgBlock_parent`,
  `fgBlock_slot`, `fgBlock_root`, `fgBlock_rows` have no docstring, and the
  `fgBlock_notMem` docstring has no tag. Global Constraints ("Faithfulness")
  ask for a blueprint id or `[helper]` in each proof docstring. The plan text
  has the same gap. Fix: add `[helper]` docstrings.

## Notes for later gates (not G10 findings)

- G11: `Inv0` is only assumed in Task 10. Check that `cstoreInv_process`
  (accepted block) gets `Inv0` from the PRE-state `CStoreInv` and uses
  `base_admitProposal_accepts`, `update_finality_TF` and `eraseFG_fgBlock` for
  `baseTree` of the post-state.
- G11 (from G7, still open): `bp.store.v1` says `F, J ∈ T`; check the
  `J ∈ T` part against `KitFG.StoreInv`.
- T7: the run form of K8 needs `hfresh` from `RootInjective` and absence
  (m2), and `hwf` from `DeliveryWellFormed` (DQ14).

# Review: I9 plan, Task 9 (FG-SA) and its T7 fit

_2026-09-29. Reviewer: fgsa-impl (Claude), read-only. Plan:
`lean/available-chain/docs/plans/2026-09-29-i9-derived-roots.md` at main
24ecaaa (read with `git show`). FG-SA code read at main 24ecaaa (identical to
d0d913a for `AvailableChainFGSA/*`). T7 plan: branch `fgsa-composition-plan`
at d6871e4. No Lean was run; no Codex job was started._

## Verdict

**ADOPT WITH FIXES.** 0 BLOCKING, 3 MAJOR, 3 MINOR, 2 notes. The design of
Task 9 is right: the signed row wires (rounds included) go into the base body,
`rowsOk` binds them, and `ContentAgree` becomes a theorem on reachable stores,
which is what T7 needs. Three points must change before Task 9 runs: the
exact form of `rowsOk` (F1), the statement-text constraint against the FG-SA
erasure and root signatures (F2), and the place of the three-case lemma
instance (F3).

## (a) Completeness of Task 9

### F1 — MAJOR: `rowsOk` must be the canonical full-body test

Task 9 Step 1 defines `rowsOk b rw` as "decode `b.body` and compare its rows
component with `encList encRowWire rw`; the application component is free".
Step 2 then needs `eraseFG (fgBlock P b rows) = b` from `rowsOk` and
`eraseFG P = b.parent` (Review Focus 2). That does not follow.

- With `packBody app rw := encFGBody finCodec (lpair app (encList encRowWire
  rw)) (rw.filterMap RowWire.toRow?)`, the base body has TWO row components:
  the signed-wire code inside the first argument and the decoded-row code in
  the second. The stated `rowsOk` checks only the first.
- The decoders are not inverse to the encoders on every `Nat`. `lpair a b`
  writes exactly `bitLen b` low ones; a `Nat` whose decoded `b` has a zero top
  bit (so `bitLen b` is smaller than the counted ones) decodes to some `(a, b)`
  but re-encodes to a different number. `encList` has the same property.
- So a faulty proposer can send `b` whose body passes the component test but
  is not `packBody app rw` for any `app`. Then `fgBlock P b rows` (built from
  the decoded parts) erases to a block with another body, so
  `eraseFG (fgBlock P b rows) ≠ b` and the FG root differs from the base root.
  The base store gets `b` (`admitProposal`), `Σ.T` gets the other block, and
  `Inv0`/`CStoreInv` (base = erasure of `Σ.T`), the DQ2 duplicate test and
  `base_admitProposal_accepts` break.

Fix: define `rowsOk b rw := b.body == packBody (appOf b.body) rw`, where
`appOf` is the decoded application component. This is one state-free
equality. It gives `eraseFG (fgBlock P b rows) = b` by construction, it holds
for honest `propose` (`appOf (packBody 0 rw) = 0` by the decode laws), and it
still leaves the application component free. Use the SAME `rowsOk` function
in `wellFormed` and in `blockAccepted` (see (b)).

### F2 — MAJOR: statement texts and missing files

Global Constraint "Statements": "every theorem that a `Tests/Axioms.lean`
file prints, do not change as text". `AvailableChainFGSA/Tests/Axioms.lean`
prints all 206 FG-SA proof theorems. Task 7 gives `FGBlock.root C` an explicit
codec, and Task 9 gives `eraseFG` the law `(eraseFG C B).root = B.root C`.
If `C` is an explicit argument, the text of many printed theorems changes:

- `Proofs/Carrier.lean`: `eraseFG_slot`, `eraseFG_root`, `eraseFG_parent`,
  `eraseFG_eq_genesis`, `eraseFG_preceq`, `eraseFG_compatible`,
  `eraseFG_injOn`, … (generic in `V`);
- `Statements/Invariants.lean`: `CStoreInv.rootInj`, `Inv0`, `NestOK`,
  `wireTree`;
- every statement that names `eraseFG st.fg.F`: `Model/Store.lean`
  (`activeCompatible`, `normalizeS`), `Proofs/Fields.lean`,
  `Proofs/Nesting.lean` (`finalized_preceq_stable`), `Proofs/Reconcile.lean`
  (the K1 statements), `Proofs/StoreInv.lean`, `Proofs/ActView.lean`.

`Model/Store.lean`, `Proofs/Fields.lean`, `Proofs/Nesting.lean` and
`Proofs/Reconcile.lean` are not in Task 9's file list.

Fix (recommended): make the codec an instance argument, `class RowCodec (V)`
with `instance : RowCodec (Fin n)` (signer = `Fin.val`), and write
`FGBlock.root` and `eraseFG` with `[RowCodec V]`. Then `eraseFG B`,
`B.root` and `(eraseFG B).root = B.root` keep their text, and the constraint
holds for FG-SA. Otherwise, scope the constraint (it cannot hold for FG-SA as
written), list every changed FG-SA statement with old and new text, and add
the four files to Task 9. The same choice affects KitFG statements and pins
(Task 8).

### F4 — MINOR: the size spike does not cover the FG-SA body

Task 0 Step 3 measures the SimplexFG G02 chain with the r203 row encoders.
The FG-SA base body encodes the rows twice (signed wires and decoded rows),
and the row wires carry roots of earlier blocks, so the FG-SA growth factor
per level is about `2k+1`, not `k+1`. Add the FG-SA `packBody` shape and the
`stA` chain of `FGSA/Tests/Smoke.lean` to the spike, with the same stop rule.

### F5 — MINOR: regenerate `Tests/Axioms.lean`

The file is generated from the `theorem` lines of `Proofs/*` (store plan Task
13 Step 1). Task 9 adds theorems (`contentAgree`, the `rowsOk`, `packBody`
and erasure laws) and may rename or remove some. Step 6 should regenerate the
file, not only check it. The documented `--expect` command of the store plan
(15 names, including `rootInjectiveOn_across` and
`fg_eq_of_eraseFG_eq_across`) must keep working, or be updated in the report.

### Declarations that change (inventory)

```text
┌──────────────────────────────┬────────────────────────────────────────────────┐
│ Area                         │ Change                                         │
├──────────────────────────────┼────────────────────────────────────────────────┤
│ Model/Objects                │ eraseFG (codec; erasure law), packBody,        │
│                              │ rowsOk (F1), encRowWire                        │
│ Model/Handlers               │ fgBlock (decoded content), blockAccepted       │
│                              │ (+rowsOk; the root test becomes the duplicate  │
│                              │ test), wellFormed (+rowsOk)                    │
│ Model/Frame                  │ propose (rows first, packBody 0 rw); liveRoot, │
│                              │ deepest, fgSource, lexKey ties (new roots)     │
│ Model/Store (not listed)     │ activeCompatible, normalizeS use eraseFG (F2)  │
│ Statements/Invariants        │ CStoreInv.rootInj, Inv0 conjunct (filled by    │
│                              │ root_injective); MetaInv.wireTree (+rowsOk);   │
│                              │ ContentAgree unchanged as a definition         │
│ Proofs/Carrier               │ eraseFG_* (F2); viewRootInj_* become trivial   │
│ Proofs/Admission             │ eraseFG_fgBlock (needs F1), fgBlock_root (rfl  │
│                              │ → theorem), rootTest_iff_blockTest (its hinj   │
│                              │ premise becomes provable), base_admitProposal_ │
│                              │ accepts, admitBlock_sufficient(_absent)        │
│ Proofs/StoreInv, Metadata    │ preservation of the strengthened wireTree;     │
│                              │ NEW contentAgree (CStoreInv, MetaInv at both   │
│                              │ stores); contentAgree_self a corollary         │
│ Proofs/CrossNode             │ keep the ContentAgree premise in the text      │
│                              │ (constraint); add premise-free corollaries     │
│ Proofs/ActView, BlockAncestry│ binders; actView_admitBlock_* via erasure law  │
│ Proofs/Fields, Nesting,      │ only through eraseFG's signature (F2)          │
│ Reconcile (not listed)       │                                                │
│ Tests/RootCollision          │ positive: ba.root ≠ bb.root; ContentAgree;     │
│                              │ accept c1 then bb; duplicate bb refused        │
│ Tests/Smoke                  │ bodies; DQ2 case → duplicate; ties restated;   │
│                              │ new checks (Step 5)                            │
└──────────────────────────────┴────────────────────────────────────────────────┘
```

**ContentAgree becomes a theorem as T7 needs: yes, with F1.** For two stored
wires with `b.root = b'.root`: `Block.root_injective` gives `b = b'`;
`MetaInv.wireTree` (with `rowsOk`) gives `b.body = packBody app rw = packBody
app' rw'`; the injectivity of `lpair`, `encList` and `encFGBody` gives
`rw = rw'`. `CStoreInv` and `MetaInv` hold at every `Reachable` state (no
input check needed, because `rowsOk` is in `blockAccepted`). So T7.11 becomes
a corollary of the T7.5 bridge, with no run premise and no
`stored_proposal_delivered` for content.

## (b) `rowsOk` in `wellFormed` and the T7 hook plan

It fits. No conflict with the T7.7 partition, `excludes` or T7.8, under two
conditions.

- `rowsOk` is state-free, so a proposal with wrong rows is outside
  `DeliveryWellFormed.wire` and never delivered in a valid run. It adds no
  permanent refusal of a well-formed wire, so `excludes` needs no clause and
  the E4 reading "excludes = exactly the permanent refusals of well-formed
  objects" (plan 1b) still holds. T7.7's partition lemma (well-formed
  deliveries at reachable states: processed, excluded or temporary) is
  unchanged. `excludes_inert` is about excluded objects only, so it is
  unaffected.
- Condition 1: `wellFormed` and `blockAccepted` must use the SAME `rowsOk`
  (F1 form). If `blockAccepted` checked more than `wellFormed`, a well-formed
  proposal could be refused for good without exclusion, and T7.7 would stop.
- Condition 2 (F6 below): the lead or the user confirms that a content check
  in `wellFormed` is within D2 ("no wire check for ROOTS"). If `rowsOk` were
  only in `blockAccepted`, `excludes` would need a proposal clause (a
  state-independent permanent refusal), which the plan forbids.
- T7.8 is unchanged: the receipt split concerns HEADs, rows and
  F-compatibility; the rows inside a proposal are bound by `rowsOk`, the
  carried HEADs are not (note N1).
- T7 effects to record at the next T7 plan revision: T7.11 becomes a
  corollary (no premise, no closure conditions: r203 store-only needs none);
  T7.12 freshness = absence + `Block.root_injective`; the T7.0 diff check
  accepts the I9 commits; T7.2 `depsPresent` = `parentFG ≠ none`, which is the
  root lookup by `blockKnown_iff_root`.

### F3 — MAJOR: the three-case instance for FG-SA breaks the store boundary

Task 9 Step 4 says "Instantiate Task 1 Step 4 for `wellFormed` at :96", and
Task 1 Step 4 allows the generic lemma in `AvailableChainStatements/Generic`
"if it needs the run types". The FG-SA store library may not import
`AvailableChainStatements.*` (check-fgsa.sh direct allowlist and the compiled
allowlist in `CheckFGSAAxioms`), and its Q1/Q5 grep rejects the tokens `Run`,
`Env`, `ProtocolSpec`, `Generic.Run`. A run-typed instance in
`AvailableChainFGSA` fails `check-fgsa.sh`.

Fix: state the generic lemma run-free in `AvailableChainModel` (a store that
grows, a state-free predicate), which FG-SA may import; or leave the FG-SA
instance to the T7 run library (`AvailableChainFGSARun`, T7.7), where
`wellFormed` meets runs. Do not relax the store boundary for this.

### F6 — MINOR: confirm the D2 reading of `rowsOk`

D2 (user) says the parent-root check is the store lookup and that wire
checks for roots wait for a P2P spec. `rowsOk` is a wire check of CONTENT,
not of a root. The plan argues this; it fits T7 (see above). Because it is a
new `wellFormed` conjunct under a user decision about wire checks, record an
explicit confirmation (lead or user) in the plan's audit disposition.

## (c) check-fgsa.sh

- Lease scan: the new codec, encoders, `packBody` and `rowsOk` have no
  policy argument; the reach backstop (`gridLeasePolicy`, `LeasePolicy.mk`)
  is unaffected. The scan visits more imported definitions (the codec module),
  with no rule change. No break expected.
- Allowlist: `AvailableChainModel.Objects.Codec` and `AvailableChainSimplexFG.*`
  are allowed in every layer; `AvailableChainKitFG.*` only in Statements/ and
  Proofs/ (so `RowCodec` and the encoders must live in SimplexFG or FG-SA
  Model, not KitFG). The only break is F3 (Statements import, run tokens).
- Axioms: the codec proofs use `Nat.log2` and bit lemmas from Mathlib
  (standard axioms). `decide`/`decide +kernel` are allowed; the native scan
  forbids `native_decide`, so the fixture sizes must stay within kernel
  evaluation (F4). Coverage: every new FG-SA file must be imported by the root
  (build coverage check).
- Negative controls: none reads a root; they keep working.

## Notes

- N1 (pre-existing, not an I9 finding): a proposal wire's carried HEADs
  (`raw`, `support`) are not in the body. "Processed by root" (DQ9) counts a
  second wire with the same block and other carried HEADs as processed, so its
  carried HEADs are not handled through it. The HEADs have their own relay;
  T7.8 already treats carried HEADs through accepted proposals only.
- N2: the T7 plan (branch `fgsa-composition-plan`) should record, at its next
  revision, the I9 simplifications in (b) and the F1 `rowsOk` form.

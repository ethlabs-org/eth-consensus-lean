# G12 review — Task 12 (metadata invariant, cross-node carrier)

Reviewer: Opus (independent; did not write the code). Date: 2026-09-29.
Commit: `5c0230e` (branch `fgsa-composition`). Scratch worktree at
`5c0230e`, with `.lake/build` copied and the outputs of
`Statements/Invariants`, `Statements/Store`, `Proofs/Metadata`,
`Proofs/CrossNode` and the root module deleted so that they compile again.
The review test files are in `g12-opus-tests/` next to this report.

## Verdict

**PASS WITH FIXES.** 0 BLOCKING, 1 MAJOR, 3 MINOR.

All 14 planned items (3 statements and 11 theorems) have the plan text
exactly (script compare, whitespace normalized; each theorem signature
stops at `:=`). No statement is weaker than its blueprint statement. No
statement has a new premise. The build, the check script and the axiom
check are clean. Every lease-dependent GridCO constant in the new modules
has `GridCO.slowLeasePolicy` (term scan). The MAJOR finding is not a
code defect. It is a premise-scope decision: `ContentAgree` asks for more
than the proofs use, and no root design that is under discussion for I9
supplies the extra part. The fix is a report line or a plan decision.

## Validation

```text
┌──────────────────────────────────────────────┬──────────────────────────────────────┐
│ Check                                        │ Result                               │
├──────────────────────────────────────────────┼──────────────────────────────────────┤
│ bash scripts/check-fgsa.sh (scratch wt)      │ exit 0 (1:10 wall). "Built" for      │
│                                              │ Statements.Invariants, Statements.   │
│                                              │ Store, Proofs.Metadata, Proofs.      │
│                                              │ CrossNode, AvailableChainFGSA        │
│ root imports, native eval, direct imports,   │ pass                                 │
│ import closure, Q1/Q5 grep                   │                                      │
│ CheckFGSAAxioms --expect (the 11 theorems,   │ exit 0; 775 constants, 422 theorems; │
│ 6 helpers, MetaInv, ContentAgree,            │ every name found                     │
│ MetadataInvariant)                           │                                      │
│ #print axioms (7 public theorems)            │ propext, Classical.choice, Quot.sound│
│ sorry / admit / axiom / set_option in the    │ none                                 │
│ two new files                                │                                      │
│ Lease term scan (Lease.lean: every app with  │ 5 constants, all slowLeasePolicy.    │
│ a LeasePolicy argument, types and bodies of  │ Sanity: the same scan on StoreInv    │
│ the 4 changed modules, via import all)       │ finds the G11 M1 gridLeasePolicy use │
│ Invariants.lean, Store.lean vs 5e62302       │ additions only (+33/−0, +3/−0)       │
│ Non-vacuity (NonVac.lean)                    │ 3 bad states refute MetaInv; 1 state │
│                                              │ shows the genesis-wire gap (m1)      │
│ ContentAgree self (Self.lean)                │ compiles under a no-genesis-wire     │
│                                              │ hypothesis (m1)                      │
│ Weaker premise (Weak.lean)                   │ fg_eq_of_eraseFG_eq_across and       │
│                                              │ rootInjectiveOn_across compile from  │
│                                              │ block + rows equality only (M1)      │
└──────────────────────────────────────────────┴──────────────────────────────────────┘
```

## Checks requested by the coordinator

### 1. Statements against the plan and the blueprint

```text
┌─────────────────────────────┬──────────┬──────────────────────────────────────────┐
│ Item                        │ Plan     │ Blueprint                                │
├─────────────────────────────┼──────────┼──────────────────────────────────────────┤
│ MetaInv                     │ verbatim │ bp.store.v1 "old states/stamps are       │
│                             │          │ unchanged"; bp.frame.v1 §2.4 reads       │
│                             │          │ (original rows, original support, stamps,│
│                             │          │ row pool cap 2): covered                 │
│ ContentAgree                │ verbatim │ bp.carrier.v1 premise "Base full-content │
│                             │          │ root injectivity", store-pair form: equal│
│                             │          │ strength on stored wires (see M1)        │
│ MetadataInvariant           │ verbatim │ bp.store.v1, Reachable form              │
│ process_cumulative          │ verbatim │ T cumulative; old stamps unchanged       │
│                             │          │ (prefix); wires and pool only appended   │
│ clock_cumulative            │ verbatim │ "No tick changes the FG projection"      │
│ metaInv_init/process/clock, │ verbatim │ the §4.2 induction                       │
│ metadataInvariant           │          │                                          │
│ stored_wire_of_block        │ verbatim │ helper (row-position correspondence)     │
│ fg_eq_of_eraseFG_eq_across  │ verbatim │ bp01 §2.2 step 3, for two stores         │
│ preceq_iff_across           │ verbatim │ step 2 + step 4 (full iff)               │
│ compatible_iff_across       │ verbatim │ step 5 (Bool equality)                   │
│ rootInjectiveOn_across      │ verbatim │ step 6, two chains at two stores         │
└─────────────────────────────┴──────────┴──────────────────────────────────────────┘
```

The blueprint quantifies over "run blocks". The Lean form quantifies over
blocks that are stored at two stores that satisfy `CStoreInv`, `MetaInv`
and `ContentAgree`. The plan declares this restriction (DQ3; T7 does the
run lift). Both local premises follow from `Reachable` (`storeInvariant`,
`metadataInvariant`). So the only premise that is not local is
`ContentAgree`, and it is the premise that the plan names.

### 2. What `ContentAgree` assumes, and what can supply it

`ContentAgree st st'` (Invariants.lean:102): for two stored proposal
wires, equal roots of their erased blocks give equal payloads (erased
block with its parent chain, raw votes, support list, rows).

What it assumes, exactly:

- **Cross-store root injectivity.** With the local invariants, it gives
  `X.root = Y.root → X = Y` for every `X ∈ st.fg.TF`, `Y ∈ st'.fg.TF`
  (helper `fg_eq_of_root_eq_across`, CrossNode.lean:65). So it IS a
  RootInjective-type premise across the two nodes. It is not hidden: it is
  the declared purpose (DQ3(b), which reverses comp D4). But the reader
  must know that "ContentAgree" includes "no root collision between the
  two trees", not only "content binding".
- **No content equivocation under one root.** A faulty proposer can send
  two wires with the same erased block `b` and different rows to two
  honest nodes. Each node accepts its wire (the root is fresh locally).
  `ContentAgree` for that pair is then false.

What can supply it: nothing in the model. No codec binds a root to
content; `blockAccepted` checks only that the root is fresh in the local
tree. T7 must derive it from the run premise `ContentRootInjective`. Two
known classes of runs falsify that premise:

- Honest forks under the GridCO root formula `s·(parent.root+1)`
  (DQ10: `node(g,4)` and `node(node(g,1),2)` both have root 4). If node A
  stores the first and node B stores the second, `ContentAgree A B` is
  false, and every cross-node lemma is vacuous for that pair. This is the
  I9 root gap.
- Faulty content equivocation under one root (above).

The recommended I9 design (codex/root-nonce.md, r196:
`root = 1 + pair(parent.root, pair(slot, nonce))`, checked at admission)
removes the first class for erased blocks. It does not bind rows
(root-nonce.md lines 127–148 give the FG counterexample), and it binds
neither raw votes nor the support list. So with that fix alone,
`ContentAgree` is still a run premise, not a theorem. See M1.

### 3. `MetaInv` is not vacuous and has the planned fields

- It holds at init (`metaInv_init`, Metadata.lean:245).
- It fails on bad states (NonVac.lean, compiled): a stored wire of a
  non-genesis block when Σ.T = {g} (`wireTree`); a pool `[a, a]`
  (`poolNodup`); two block stamps against one base block (`stampKeys`).
- The fields `wireTree` (Invariants.lean:83) and `poolDecodes`
  (Invariants.lean:91) are present with the plan text. See m2 for the G6
  item 9 dependency.

### 4. No circularity in `metaInv_process`

`metaInv_process` (Metadata.lean:400) takes `CStoreInv p st` as a
premise. `metadataInvariant` (Metadata.lean:452) discharges it with
`storeInvariant p _ hst'` from `Proofs/StoreInv.lean`, which does not
import `Proofs/Metadata.lean`. `CStoreInv` has no `MetaInv` field. The
induction is on `Reachable` with the store invariant of the pre-state. No
cycle.

### 5. Invariants.lean

Only additions relative to `5e62302` (`git diff --numstat`: +33/−0).
Store.lean: +3/−0.

### 6. Lease instance, imports, free `n`

- Lease: 5 lease-dependent constants in the four changed modules
  (`GridCO.gate`, `gate_eq_writeKeys`, `gateWriteKeys`, `recordGenuine`,
  `admissionLevels`). All have `slowLeasePolicy`. The only explicit lemma
  is `@GridCO.gate_eq_writeKeys GridCO.slowLeasePolicy` (Metadata.lean:70).
- Imports: Metadata imports `Proofs.StoreInv`; CrossNode imports
  `Proofs.Metadata`; the root imports both. The closure check passes.
- Free `n`: no declaration takes FG-SA `p : Params` together with a free
  `n`. Note: `saGate_stamps (p : SA.Params) {n : Nat}` (Metadata.lean:55)
  has a free `n` next to an `SA.Params`, which also has a field `n`. The
  M11 rule names only FG-SA `Params`, and the helper copies the signature
  of `SA.gate`. No finding.

### 7. Build and axioms

See Validation. All clean.

## Findings

### BLOCKING

None.

### MAJOR

- **M1 — `ContentAgree` is stronger than the proofs use, and no I9 root
  design supplies the extra part.** `AvailableChainFGSA/Statements/
  Invariants.lean:102–104`. The four cross-node proofs use only two
  components of the payload equality: the erased block
  (`hpay.1`, CrossNode.lean:80) and the rows (CrossNode.lean:59). They do
  not use the raw votes or the support list. Weak.lean (compiled) proves
  `fg_eq_of_eraseFG_eq_across` and `rootInjectiveOn_across` from

  ```lean
  def ContentAgreeBR {n : Nat} (st st' : State n) : Prop :=
    ∀ s b raw sup rows, (⟨.proposer s, .proposal b raw sup rows⟩ : Wire n) ∈ st.proposals →
    ∀ s' b' raw' sup' rows', (⟨.proposer s', .proposal b' raw' sup' rows'⟩ : Wire n) ∈ st'.proposals →
    b.root = b'.root → b = b' ∧ rows = rows'
  ```

  and `ContentAgree → ContentAgreeBR`. The statement agrees with the plan
  (DQ3) and with the blueprint premise ("a root identifies the full
  content"), so this is not a weakened statement. But it matters for T7
  and for I9: with root-nonce plus a row code (`encRows`, root-nonce.md
  §"compatible extension"), the `b` and `rows` parts become admission
  theorems, and only the raw/support part stays a run premise. With the
  present statement, `ContentAgree` stays a run premise under every I9
  option that is on the table.
  Fix (coordinator decision), one of:
  (a) narrow `ContentAgree` to the erased block and the rows (plan
  change; the four theorems become stronger; about two proof lines
  change); or
  (b) keep it, and add a Task 13 report line: "Task 12 uses only the
  block and row parts of `ContentAgree`; the raw-vote and support parts
  are for later cross-node claims (name them) or are unused; the I9
  root-nonce fix does not discharge `ContentAgree`."
  Also add to the T7 inputs: the derivation of `ContentAgree` from
  `ContentRootInjective` needs a run lemma "every stored wire of a store
  is a payload that the node processed". Task 12 does not state it
  (`process_cumulative` gives only "append").

### MINOR

- **m1 — `MetaInv` does not exclude a stored wire of genesis, so
  `ContentAgree st st` does not follow from the local invariants.**
  `AvailableChainFGSA/Statements/Invariants.lean:82–95`. NonVac.lean
  (compiled) gives a state with two different stored wires of `g`
  (payload raw lists `[]` and `[a]`): `MetaInv` holds (`wireTree` accepts
  `B = g` with empty rows; `treeWire` excludes genesis), `CStoreInv` holds
  (it does not read `proposals`), and `ContentAgree st st` is false. The
  state is not reachable, because `blockAccepted` refuses genesis (`hg` in
  `metaInv_accepted`). With one more field
  `noGenesisWire : ∀ o ∈ st.proposals, Wire.block? o ≠ some .genesis`
  (preserved by the same `hg`), Self.lean (compiled) proves
  `contentAgree_self : CStoreInv p st → MetaInv p st → ContentAgree st st`.
  Reason to add it: a later claim that compares one node at two times, or
  one store with itself, then needs no run premise (with
  `process_cumulative`, the later store contains the earlier wires).
  Fix: add the field and `contentAgree_self`, or record the gap in the
  Task 13 report.
- **m2 — The G6 item 9 dependency on `MetaInv` is stated but not needed.**
  `AvailableChainFGSA/Statements/Invariants.lean:79–81` (and the plan
  note of `ff6a116`). `proposalRows` (Model/Frame.lean:132) filters pool
  rows by `(a.round?.map inI).getD false`, and `blockWireRows`
  (Model/Frame.lean:119) filters block rows the same way. A row that does
  not decode has `round? = none`, so it is never a candidate. So the
  grouping key is never `none` on every store, not only on `MetaInv`
  stores. The docstring claim is true, but the reason is the `round?`
  filter. Fix: change the docstring and the G6 note to name the filter
  (optional).
- **m3 — G11 M1 is still in the tree at `5c0230e`.**
  `AvailableChainFGSA/Proofs/StoreInv.lean:743`
  (`GridCO.ghostWalk_mem` at `gridLeasePolicy`). The Lease.lean scan
  confirms it. It is outside Task 12. Record it so that the G11 fix is
  not lost before G13.

## Notes (no action)

- Proof routes differ from the Step 2 sketch as the execution note says:
  `wire_block_mem` + fresh `b ∉ st.base.blocks` for `treeWire` uniqueness
  and `proposalsNodup`; structural induction for
  `fg_eq_of_eraseFG_eq_across`; `eraseFG_ancestor_preceq` for the
  backward direction of `preceq_iff_across`; `fg_eq_of_root_eq_across`
  for the two cross-store cases of `rootInjectiveOn_across`. Each route is
  sound; none adds a premise.
- `process_cumulative` does not state that the vote pool `base.votes`
  only grows. The plan and bp.store.v1 do not ask for it.

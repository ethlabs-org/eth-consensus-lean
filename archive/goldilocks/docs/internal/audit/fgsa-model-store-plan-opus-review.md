# FG-SA model and store plan: independent review (Opus)

Object: `docs/plans/2026-09-29-fgsa-model-store.md` at `7af69aa` (branch
`fgsa-composition`). Date: 2026-09-28. Read-only review. This file is not
committed.

**Verdict: REVISE.** I agree with the Astra report
(`fgsa-model-store-plan-audit-report.md`, r185). The design choices DQ1–DQ12
are sound. DQ2 is correct and it is the better option. The plan has one
blocking type error (Astra B1; I confirmed it with the compiler). It also has
the Astra majors and three new majors: the Q1 independence claim is too
strong, the coverage of `bp.activeView.v1` is incomplete, and the SA reuse
bridge covers only the clock step.

Authorities checked: the spec sha256 is `2e884811…` (it agrees). comp is
`228dbe98…` and bp01 is `989289cc…` (both agree). bp00 has changed since the
plan pinned it (Astra N4).

## 1. Compiler evidence

I compiled two scratch files from the worktree root with
`lake env lean <file>`, outside the repository (`/private/tmp/fgsa-rev/`).
There was no full build.

```text
┌──────────────────────────────────────────────┬──────────────────────────────┐
│ Check                                        │ Result                       │
├──────────────────────────────────────────────┼──────────────────────────────┤
│ structure Params extends SA.Params gives     │ OK (rfl)                     │
│ p.toParams, p.Δ, p.toParams.engine.Δ = p.Δ   │                              │
│ actView_onView (block-preserving f)          │ OK, 3-line proof             │
│ saGate_blocks from GridCO.gate_blocks        │ OK only with                 │
│                                              │ @… GridCO.slowLeasePolicy;   │
│                                              │ the default instance         │
│                                              │ elaborates the GRID gate     │
│ DQ10 root formula collision                  │ decide: root(genesis, 4) =   │
│                                              │ root(g1, 2) = 4, blocks      │
│                                              │ differ                       │
│ controls (p) (st : State n) :=               │ ERROR: Electorate (Fin p.n)  │
│   storeControls p.E p.cfg st.fg              │ vs Electorate (Fin n)        │
│ same with st : State p.n                     │ OK                           │
└──────────────────────────────────────────────┴──────────────────────────────┘
```

## 2. Findings

### BLOCKING

- **B1 (Astra B1, confirmed).** Every model function that applies `p.E`
  (`admitBlock`, `controls`, `fullTree`, `eligible`, `voterBlocks`,
  `headVote`, `fgInputs`, `attest`, …) takes `st : State n` with a free `n`.
  This does not type-check. Use `State p.n`, `Wire p.n`, `Fin p.n`
  throughout the parameter-dependent API.

### MAJOR (new)

- **J1. The Q1 independence claim is too strong.** The object layer uses the
  engine-v1 types `Auth Label n` (with `.proposer s` and a global `n`) and
  `Signed`. FRAMEWORK-DESIGN §2 E1 (engine v2) changes this:
  `Auth = seat ℓ (i : Fin (seats ℓ)) | none`, a proposal duty is a one-seat
  label, and `ProtocolSpec` has no global `n`. The payload `Msg n` also
  contains v1 `Signed` values (`HeadWire`, `RowWire`). On v1, T7 changes
  nothing in T3–T6. On a native v2 instance, T7 must re-type or decode
  `HeadWire`, `RowWire`, `Wire`, `baseAuth`, `liftHead?`, `RowWire.toRow?`
  and `round?`, and every auth match in `process`, `admitRow`,
  `blockAccepted` and `wellFormed`. The store, the invariants and the proofs
  can stay if T7 adds a decode adapter `v2 object → Wire p.n`. The SA base
  (`GridCO.State`) has the same v1 wires, so this dependency is inherited
  and cannot be removed. Fix: in the Q1 table, replace "No dependency" with
  "v1-typed objects; v2 needs a decode adapter or a re-typing of
  Objects/Handlers". Optionally, put all auth matching in one `decode` helper.
- **J2. `bp.activeView.v1` is only partly stated.** Task 7 has items 3
  (`actView_antitone`) and 5 (`blockExcluded_stable`), and membership. The
  blueprint (bp01 §5) has six items. Items 1 (A ⊆ T; g, F ∈ A), 2 (ancestor
  closure), 4 (the path from F to an active K is active) and 6 (K ⪯ F gives a
  release count of zero against K, and no veto) are missing. Item 6 is the
  base case of K11, and items 2 and 4 are K9 inputs. All are local and
  short. Add them, or remove the full `[bp bp.activeView.v1]` tag.
- **J3. The SA reuse bridge covers only `clock`.** Comp §1.2 says that every
  SA read is SA code on the active view. The plan proves this for the tick
  (`clock_eq_saClock_*`) and for a head vote (`actView_admitHead`), but not
  for an accepted block. Add
  `actView (admitBlock …) = GridCO.admitProposal … (actView st) …` when F
  does not move. This holds: `F ⪯ B` and `F ≠ B` give an active parent, and
  `b` is active. When F moves, use `actView_antitone`. Otherwise T11/T12
  cannot move GridCO one-step lemmas across block deliveries. Also record
  this limit: GridCO invariants proved by induction over GridCO steps
  (`ReceiptPrefix`, `∀ b ∈ blocks, ∃ stamp`) apply to `base`, not to the
  view. The view's block list shrinks when F moves, and it keeps the stamp
  rows of inactive blocks.

### MAJOR (Astra, I agree)

- **M1** (carried-row input check). See also m3.
- **M2** (cross-node content premise; K5 is only local). DQ3(b) is
  acceptable, but it reverses comp D4 ("no new run premise"). Say this, and
  list the premise as a new assumption of every FG-SA claim that compares FG
  state across nodes (T8, T10, T12).
- **M3** (K1 fast-write premise). The invariant is local. It needs no run:
  - For every row `(r, xs) ∈ fastWrite` and every `B ∈ xs`, either
    `savedGenuine r = some (some C)` with `B ⪯ C`, or `B ⪯ eraseFG F`.
  - Also: `dom fastWrite ⊆ dom genuine`, with one row for each label.

  A gate keeps this invariant because the guard gives a fresh label, and
  the members are prefixes of the saved `h`. Reconcile keeps it because of
  bp01 §6.3: if C is emptied, then `B ⪯ F'`. The other steps do not write
  these fields. Put these clauses in `CStoreInv`. State K1 in the blueprint
  form, with the old F₀ ⪯ new F and no fast-write premise. The plan text
  says this "needs write origins over a run". That is wrong.
- **M4** (metadata invariant: the `proposals` wire ↔ the FG block rows,
  stamps, one row for each key).
- **M5** (imports). Correction to the proposed fix: plan 1a does not change
  `AvailableChainStatements` (phase-1a plan, line 65). Thus the cheaper fix
  is to say "no DIRECT import". The transitive dependency through GridCO
  proofs is then disclosed and allowed. Do not copy GridCO lemmas into this
  library. Extend the grep to all five direct-import names.
- **M6** (axiom `--expect` syntax). I did not check it.

### MINOR

- **m1.** `clock_eq_saClock_gate` hides `fw` in an existential. K6
  (bp01 §8.4) needs the exact value
  `fw = fastSet p (pre-gate view) s`. State it (Astra has the same point).
- **m2.** Task 10 lists `admitBlock_accepted_eq`, `fgBlock_notMem`,
  `fgBlock_parent/slot/root` as outputs, but gives no statements. Also add
  the sufficiency direction that K8 needs (bp01 §10.1: "an absent block has
  its parent, a valid slot, a valid proposer and row rounds, and extends F,
  so it is admitted"). Under `CStoreInv`, when `parentFG`, `blockAccepted`
  and a fresh root hold, `b ∈ (process p st o).base.blocks`.
- **m3.** `wellFormed`: the flat wire carries `b.parent.slot` and the row
  rounds. Thus the parent-slot test and the row-round test are syntactic.
  Put them in `wellFormed` (with M1's row-body check). Then the only
  refusals in `blockAccepted` are temporary ones (future slot, missing
  parent), a duplicate, and `F ⋠ B`. This helps the E4 outcome
  classification in v2 (`RelayFeasible`). For T7: define `processed` for a
  proposal by root (`∃ Y ∈ TF, Y.root = b.root`), so that the DQ2 refusal is
  "already processed" and not a permanent refusal without a report.
- **m4.** DQ2 rationale. The extra refusal never fires for ANY processed
  block (not only an honest block) under `RootInjective`. Every regime
  (`SleepyRegime`, `OutageRegime`, `RecoveryRegime`, in
  `Statements/Generic/Regimes.lean`) contains this premise. For T7, add
  `rootTest_iff_blockTest` under `RootInjective`. There is also a small
  bonus: `rootInj` + `baseTree` give GridCO's
  `RootInjectiveBelow st.base.blocks` locally.
- **m5.** DQ5 text: `SA.gate` is not fully without a once-guard.
  `recordGenuine` under `slowArming` already writes `genuine` only once. The
  composite guard adds the S, G, lease and fastWrite skip. The `hnew`
  premise is easy in T7. `ScheduleWellFormed` (`nodup`, `tick_public`) gives
  one tick per node and public time, and only the tick at `gateTime s`
  writes label `s`. Caveat for v2: a restart (`restore`) that loses
  `genuine` would allow a second evaluation.
- **m6.** The spec `on_tick` (spec 709–730) has no freeze step and no early
  step. The spec derives frozen and early pools at read time (spec 463–471).
  The caches `frozen`, `early` and `releaseSnapshots` (M8) do not agree with
  the leak-ledger rule "the model stores no derived value that the spec does
  not store". Declare them as model-only caches, as DQ8 does for G. They
  are necessary for the exact clock bridge.
- **m7.** DQ10: the honest root formula collides (compiled; see §1). This
  comes from GridCO. `RootInjective` can fail because of honest proposals
  alone, so liveness theorems are vacuous on such runs. Do not claim fresh
  honest roots.
- **m8.** `deepest` (Astra N2). Use the spec tie rule (greater root), as
  `liveRoot` does. Or prove "each fastWrite set is a chain": its members are
  prefixes of one result, and reconcile only filters. This is a store fact.
  It is not a lease-origin fact, although finding (a) of Task 6 says so.

## 3. Answers to the review questions

**Q1. DQ1–DQ12.** I agree with all twelve recommendations. The conditions
are these.

```text
┌──────┬──────────┬───────────────────────────────────────────────────────┐
│ DQ   │ Answer   │ Condition                                             │
├──────┼──────────┼───────────────────────────────────────────────────────┤
│ DQ1  │ keep (a) │ the flat wire gives the full erased parent chain (more│
│      │          │ than the spec root reference); equal under            │
│      │          │ RootInjective, because BlockInRun holds all ancestors │
│ DQ2  │ keep (a) │ see below                                             │
│ DQ3  │ keep (b) │ say that it reverses comp D4; new claim premise (M2)  │
│ DQ4  │ keep (a) │ agrees with spec 352–353 and v2 E5 (recordOwn does    │
│      │          │ not change base; the policy writes only the record)   │
│ DQ5  │ keep (a) │ m5                                                    │
│ DQ6  │ keep (a) │ —                                                     │
│ DQ7  │ keep     │ the accessor conjuncts are rfl; the run form waits    │
│      │          │ for T7, so comp T6 is not complete here               │
│ DQ8  │ keep     │ extend to frozen/early/releaseSnapshots (m6)          │
│ DQ9  │ keep     │ m3                                                    │
│ DQ10 │ keep     │ m7                                                    │
│ DQ11 │ keep     │ —                                                     │
│ DQ12 │ keep     │ also check row bodies (M1)                            │
└──────┴──────────┴───────────────────────────────────────────────────────┘
```

DQ2 in detail:

- The spec says "Block roots are distinct" (spec 167) and "Roots are
  injective, so the parent is the block that the store holds under the root
  B.parent" (spec 520–521). Under these premises, the root test and the
  block test are equivalent.
- In the run, `RootInjective` (on erased blocks, over every processed or
  emitted payload and its ancestors) gives the same equivalence for every
  processed block. Every AC regime contains this premise. Thus Clean safety,
  P1 and healing lose no behaviour.
- Option (b) is worse. With a same-root, different-parent block, TF loses
  root injectivity. Then `lexMax`/`pickPair` and `storeInv_on_block` become
  conditional in every store lemma.
- The local freshness does NOT give the cross-node content equality
  (Astra M2). Two nodes can admit the same erased block with different rows.
  This is DQ3's premise, not DQ2's.

**Q2. Q1 and Q5 independence.** Q5: the plan is independent of it (there is
no Interface and no Claims; the accessors are plain functions). Q1: on v1
there is no rewrite. On native v2, see J1. The `Reachable` closure lifts to
both engines if T7 shows that each run state is a projection of a reachable
state. On v1 the node state is `State` + record + pendingRow. On v2, E5 keeps
`base` unchanged. The own-row processing is a `deliver` step of `admitRow`.
The Λ handling is correct: Λ is outside `State`, `attest` is a pure
function, and the State transitions do not depend on the signing policy.
This fits the v2 E5 isolation laws and FRAMEWORK §7.3 `APTemplate`.

**Q3. Use by T7–T14.** These items must change: K1 (M3, m1), K4 metadata
(M4), K5 across nodes (M2), activeView (J2), block-step bridge (J3), and
acceptance sufficiency for K8 (m2). The hypotheses are easy to discharge:
`hnew` (m5), `hinj` in `parentFG_spec` (it comes from `CStoreInv`), and
`hC` in the helper form after M3.

**Q4. Reuse.** Every cited SA, GridCO, SimplexFG and KitFG name exists with
a signature that fits. Traps:

- The `LeasePolicy` instance (see §1). `GridCO.gate_blocks p.engine`
  compiles silently for the GRID gate.
- `pickPair_eq_of_unique` gives only the sufficient direction of
  `parentFG_spec` (Astra).
- Imports (M5).

The `onView` technique is sound. `actView_onView` has a 3-line proof, and
the four steps that `onView` runs keep `blocks`. The state of the gate after
the restore is correct: every field except `blocks` comes from the gate on
the view, and those fields read only the active blocks. The proof cost is
J3.

**Q5. Scope.** There is no scope creep: the duties in Task 6 are comp T3 §4.5
work. These comp T3–T6 items are left out, and the plan declares them: the
run form of T6, the hooks (§4.6), pendingRow/Λ (§4.4 step 6), and the
cross-node part of K5. The missing local pieces are J2, J3, M3, M4 and m2.
The size estimate (3.3–4.3k lines) must grow by about 0.3–0.5k lines for
these pieces.

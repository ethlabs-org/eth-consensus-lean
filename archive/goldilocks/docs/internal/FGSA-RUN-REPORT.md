# FG-SA run library report

_Plan: `docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11 (branch of the
plan: worktree available-chain-fgsa-plan, read at 0432f6a). Library:
`AvailableChainFGSARun` (the plan leaves the name open, §3.1; this report uses
the plan's working name). Check: `bash scripts/check-fgsa-run.sh`. The T7.13
report extends this file._

## T7.0 records

Source: the T7.0 report (`codex/reports/t7-0-report.md` in the research
tree, 2026-09-29), verdict PASS WITH RECORDS. The items below are copied from
its §1 (base) and §7 (D1–D8, the records that the plan must carry). Its items
D9–D12 are of class "none" (no record needed): D9 (Delivery.lean differs from
469463f only in docstrings), D10 (the T7.6 item 3 route holds), D11 (a note
for T7.2: `FGSA.parentFG_isSome_iff_root` takes `CStoreInv p st`, so the
root-lookup reading of `depsPresent` needs `CStoreInv`, which the T7.5 bridge
gives at reachable states), D12 (procedure: build `AvailableChainKitV2` before
the manifest check).

### Base

```text
┌────────────────────────────┬────────────────────────────────────────────────────────────────┐
│ Item                       │ Value                                                          │
├────────────────────────────┼────────────────────────────────────────────────────────────────┤
│ Base commit                │ 1aa6885e0b78a6b15d0b3eb35ed0599a64dc6302 ("docs:               │
│                            │ PHASE2A-REPORT final gate state"), worktree                    │
│                            │ ~/worktrees/available-chain-t7, branch fgsa-t7, clean tree     │
│ Phase gate (1) I9          │ 3403e58 is an ancestor of the base                             │
│ Phase gate (2) 2a          │ docs/V2-API.md present; V2Manifest --check exit 0; anchor      │
│                            │ AvailableChain.Framework.V2.anchor present (checked by the     │
│                            │ manifest script)                                               │
│ Phase gate (3) spec sync   │ 1944bb8 (61df54a c43cd52 312542a 66a2dc5) is an ancestor;      │
│                            │ base anchor 713f56f (8e15977, 227dbf5) is an ancestor of it    │
│ Phase gate (4) base        │ 1aa6885 contains all three merges                              │
│ main now                   │ 3e48c9f = 1aa6885 + one docs commit (ARCHITECTURE); no Lean,   │
│                            │ lakefile or script change                                      │
│ Store reference base       │ d0d913a (plan §0, key "store"); ancestor of the base           │
└────────────────────────────┴────────────────────────────────────────────────────────────────┘
```

### Records D1–D8

- **D1 (rename: record).** §3.1a writes some names without their
  sub-namespace. Fully qualified: `AvailableChain.V2.Run.{stateBefore,
  stateBeforeTime, readAt, final, emitsAt, tickIdx?, emittedAt, emits,
  processes, handlesAt, acceptsAt, holder, ownSeats, stateBefore_succ,
  step_tick_eq, tickIdx?_spec, emittedAt_eq_emitsAt,
  mem_emittedAt_iff_emits}`; `AvailableChain.V2.{tick, tick_decomp,
  tick_asleep}`; `AvailableChain.V2.ProtocolSpec.{Object, objSelfVisible}`;
  `AvailableChain.V2.Isolation.{base_tick, foldl_recordOwn_base}`. §3.1
  says only "in `AvailableChain.V2`"; that is true as a prefix only.
- **D2 (rename: record).** The restore forms that §3.1a describes in prose
  have names: `AvailableChain.V2.Engine.stateBefore_stable_clock_restore`
  (hrestore_now, SWF, restore step; no `restartFree`) and
  `AvailableChain.V2.Engine.stateBefore_field_prefix_restore`. The Kit also
  has `_noRestart` forms: `stateBefore_now_source_noRestart`,
  `stateBefore_now_le_event_noRestart`, `stateBefore_now_mono_noRestart`,
  `stateBefore_invariant_noRestart`, `stateBefore_stable_clock_noRestart`,
  `clock_field_origin_noRestart` (all in `AvailableChain.V2.Engine`).
- **D3 (none; record the tool).** `stateBefore_invariant` has no separate
  "factors through base" variant. It takes the `recordOwn` step premise.
  `AvailableChain.V2.Engine.recordOwn_preserve_of_base (iso) (Q : iso.Base →
  Prop)` discharges that premise for a predicate on the base.
- **D4 (none; note for T7.6 item 3).** `clock_field_origin` also takes
  `field init = []` and `∀ st o, field (process st o) = field st` (an
  EQUALITY). For the saved-label list `genuine.map Prod.fst`, T7.6 must
  show that FG-SA `process` (with the `reconcile` in admission) keeps the
  label list exactly. The plan says that `reconcile` keeps labels; the
  premise is as 2a planned, so this is not a premise change.
- **D5 (rename: record).** `AvailableChain.GridCO.excludes : GridCO.Params →
  {n} → GridCO.State n → GridCO.Wire n → Bool` has no `[LeasePolicy]`
  argument. "Bind at `slowLeasePolicy`" has nothing to bind. FG-SA calls it
  at `p.toParams.engine`, as `admitHead` calls `admitVote`. Only
  `GridCO.gateFrom`, `GridCO.clockFrom`, `GridCO.gate`, `GridCO.clock`
  take the policy (FG-SA: `SA.gateFrom`, `SA.clockFrom` at
  `slowLeasePolicy`).
- **D6 (rename: record).** SA has no named genesis equality. The three
  equalities `SA.confirmation p st r = SA.confirmationFrom p .genesis st r`,
  `SA.gate … = SA.gateFrom p .genesis …`, `SA.clock … = SA.clockFrom p
  .genesis …` hold by `rfl` (checked in `FGSACheck.lean`, a scratch file of T7.0). Grid CO has the
  named `GridCO.confirmation_eq_from_genesis`, `GridCO.gate_eq_from_genesis`,
  `GridCO.clock_eq_from_genesis`.
- **D7 (rename: record).** The anchor forms of the Grid CO gate lemmas are
  `GridCO.gateFrom_blocks` (`Proofs/Map.lean:954`),
  `GridCO.gateFrom_eq_writeKeys` (`Proofs/Map.lean:695`),
  `GridCO.gateFrom_target_origin` (`Proofs/GenuineHistory.lean:32`),
  `GridCO.confirmationFrom_mem` (`Proofs/RecordSlots.lean:151`, conclusion
  `B = a ∨ B ∈ st.blocks`), and the extra `GridCO.confirmationFrom_extends`
  (`Proofs/Goldfish.lean:132`, `a ⪯ B`). The genesis names stay as
  corollaries. T7 reaches them only through FG-SA store theorems.
- **D8 (rename: record, citation).** `FGSA.fgHead_stored` is at
  `AvailableChainFGSA/Proofs/StoreInv.lean:756`, not `:749` (T7.W text);
  the spec sync moved it. `FGSA.rootInj_all` is still at `:120`.

### Other names from the T7.0 report

- RunCheck (T7.10; report §3): `AvailableChain.V2.Engine.{allTicks,
  allDeliveries, emittedBy}` and `AvailableChain.V2.Engine.{allTicks_spec,
  allDeliveries_spec, emittedBy_spec}`, in the module
  `AvailableChainKitV2.RunCheck` (file `AvailableChainKitV2/RunCheck.lean`,
  frozen Kit entries). `toyRun_valid` is
  `AvailableChain.V2.Tests.Toy.toyRun_valid`
  (`AvailableChainKitV2/Tests/Toy.lean:341`). Where the report and the plan
  differ on a name, T7 uses the report.

## T7.1 Library skeleton and checks

Files: the `lakefile.toml` entry `AvailableChainFGSARun` (own root, in the
default targets), the root `AvailableChainFGSARun.lean`,
`AvailableChainFGSARun/Tests/Axioms.lean`, `scripts/check-fgsa-run.sh`,
`scripts/CheckFGSARunAxioms.lean`, `scripts/CheckFGSARunLease.lean`.

The check script is adapted from `scripts/check-fgsa.sh` (plan §3.1):

- Kept from the store check (G13 and fold-verify fixes): the comment
  tokenizer; the fail-closed header parser (`!UNPARSED`); `find -L -iname
  '*.lean'`; the root-import check; the native-evaluation grep; the text
  allowlist and the same allowlist again on the compiled import data; build
  coverage; the axiom scan; the lease check with the own-parameter rule and
  the reachability backstop (the rules of `CheckFGSALease.lean`, on the run
  roots); the negative controls of the store check, adapted to the run tree
  (the auditor's files in `scripts/fgsa-controls/` are reused).
- Changed: the allowlist is the layer table of §3.1; the closure test also
  forbids `AvailableChainLStar`; there is no Q1/Q5 boundary grep (the run
  library is the run layer).
- New: the v1/v2 name-clash rule (no plain, `hiding` or `renaming` open or
  export of `AvailableChain.V2`, no selective list with `Auth` or `Signed`,
  no namespace with a component `V2`); the used-constant check (no library
  constant uses a constant of `AvailableChainKit.*`,
  `AvailableChainStatements.*`, `AvailableChainGridCO.Proofs.*` or
  `AvailableChainModel.Generic.Run`; generated equation lemmas of other
  libraries are skipped, as in the lease check). New controls: the v1 engine,
  v1 Kit, v1 statements and Grid CO proof imports (text and compiled); the
  name-clash forms (also in a `.LEAN` file and a linked directory, with a
  selective open that must pass); used constants of the v1 Kit, the v1
  statements, the v1 engine, and a Grid CO proof predicate in a statement
  (the T7.W wrapper rule).
- G-walk control (lead, the T7.W wrapper statement rule): the used-constant
  check scans declaration TYPES as well as values. The control
  `negctl_walkWrapper_proofPredicate` states `GridCO.RootInjectiveBelow
  st.base.blocks` and is proved by the store lemma
  `FGSA.rootInjectiveBelow_base` (allowed), so only its type names the
  forbidden constant; the check must print "FORBIDDEN CONSTANT:
  AvailableChain.FGSA.Run.negctl_walkWrapper_proofPredicate uses
  AvailableChain.GridCO.RootInjectiveBelow (AvailableChainGridCO.Proofs.Roots)".
  It imports `AvailableChainFGSA.Proofs.StoreInv`. After the T7.W merge, the
  lead's text (import `AvailableChainFGSA.Proofs.Head`, the same theorem)
  replaces it; the script has that text in a comment. The lead's namespace
  `AvailableChain.FGSARun` is changed to the library namespace
  `AvailableChain.FGSA.Run`.

Validation at T7.1 (Mac, `pgrep -x lean | wc -l` = 0 before each run):
`lake build --wfail AvailableChainFGSARun` exit 0 (4 jobs);
`bash scripts/check-fgsa-run.sh` exit 0 (0 constants, 592 closure modules,
13 negative controls rejected as expected, the G-walk control included);
`lake env lean --run scripts/V2Manifest.lean --check` exit 0 (280 entries in
17 modules). At T7.1 the library has no declaration, so the script passes
`--allow-empty` to the two compiled checks. T7.2 removes the option from both
scripts and passes an `--expect` list to the axiom script.

## T7.2 The protocol, label families and isolation

Files: `Model/Protocol.lean` (`AppCodec`, `unitCodec`, `RunLabel`, `Node`,
`Obj`, the adapter `toAuth`, `ofAuth`, `toWire`, `ofWire`, `toWireEquiv`,
`ofHead`, `ofRow`, `duties` with `duties_spec` and `duties_nodup`, `withApp`,
`actS`, `act`, `recordRow?`, the store hooks `depsS`, `processedS`,
`excludesS`, `handlesS`, `carriesS`, and `fgsa`); `Model/Families.lean`
(`fgsaFamilies`, `fgsaIso`); `Proofs/Protocol.lean` (the lemmas of the task
text and a few more, below); `Tests/Protocol.lean` (the smoke tests). All
names are in the namespace `AvailableChain.FGSA.Run`.

Differences from the plan text (for review gate R-A):

- The field Λ of `Node` is `record`, not `rec`: Lean reserves `Node.rec` for
  the recursor of the structure. The lemma names of the plan stay
  (`restore_rec`, `clock_rec`, `process_rec`); they read `nd.record`.
- Layout: the plan names `Model/Protocol.lean` and `Model/Families.lean`.
  The proofs that are fields of `fgsa`, `toWireEquiv` and `fgsaIso`
  (`duties_spec`, `duties_nodup` with the helper `slotOf_offset`, the
  inverse laws, `act_base`, `hooks_base`, `separation`) are in these Model
  files, as in `GridCO/Model/Protocol.lean`. The other lemmas are in
  `Proofs/Protocol.lean`, and the smoke tests in `Tests/Protocol.lean`.
  `rowsOk_withApp` needs the store lemma `appOf_packBody`
  (`AvailableChainFGSA.Proofs.Carrier`), which only `Proofs/` and `Tests/`
  may import.
- `duties t` takes the three candidates from the slot of `t` (the action
  time of round `r` is in slot `rR + 1`) and keeps each one whose act time is
  `t`. Each candidate has its own constructor, so `duties_nodup` does not use
  the residues `0`, `Δ`, `2Δ` mod `4Δ`; `duties_spec` uses `Δ > 0` and
  `R ≥ 1` (from `R ≥ 2`).
- `rowsOk_withApp` is stated on the proposal output: if
  `(propose p st s).map (withApp a) = some m`, then `m` is a proposal whose
  block is `.node H s (packBody a rows)` with its carried `rows`, `rowsOk`
  holds, and the application value is `a`.
- Added (not in the task text): `DecidableEq` instances for
  `(fgsa p c).Label` and `(fgsa p c).Payload` (the projections do not unfold
  at instance transparency; the smoke tests and later concrete runs need
  them); `recordOwn_rec`, `act_fg`, `act_prop`, `act_prop_zero`;
  `singleSeat_prop` and `linked_selfVisible` (the family facts of the task
  text); `tick_st` (the store after a tick is `FGSA.clock` of the store
  before it, from `Isolation.base_tick`); the adapter lemmas
  `ofWire_toWire`, `toWire_ofWire`, `toWire_injective`, `toWire_ofHead`,
  `toWire_ofRow`.

Choices inside the task text (for review gate R-A):

- `processed` of a proposal is the duplicate-root test of `blockAccepted`,
  `∃ Y ∈ st.fg.TF, Y.root = b.root` (DQ9). Its reading as "the erased block
  is stored" is a later lemma (I9 erasure-root law and
  `Block.root_injective`).
- `excludes` of a proposal is `blockExcluded st b`, with no `processed`
  guard (the task text). So a stored block that F later excludes is both
  processed and excluded. The HEAD clause (`GridCO.excludes`) and the row
  clause have the guard "not stored".
- `handles` of a proposal: the gate is the acceptance test of `admitBlock`
  (`parentFG st b = some P` and `blockAccepted`), and the handled objects are
  the raw HEADs (`ofHead`) and the rows (`ofRow`), as Grid CO `handles` (raw
  HEADs only; the support list is metadata). `carries` is structural: raw
  HEADs, support HEADs and rows.
- `depsPresent`, `processed`, `excludes` and `handles` read the object only
  through `(toWire p o).decode`; a malformed wire has no dependency, is not
  processed and is not excluded. `carries` reads the payload.
- `withApp a` on a proposal whose block is a node rebuilds the body as
  `packBody a rows` from the carried rows; every other payload does not
  change. On the I9 `propose` output this replaces only the application
  value (`withApp_zero`).

## T7.2 Adapter lemmas and `excludes_inert` (lead GO, 2026-09-29)

Adapter lemmas (M8, `codex/scratch/a0-s3c-read-layer-fit.md` §2.7), in
`Proofs/Protocol.lean`. T7.7 reuses them.

```text
┌──────────────────────┬──────────────────────────────────────────────────────┐
│ Lemma                │ Statement                                            │
├──────────────────────┼──────────────────────────────────────────────────────┤
│ ofRow_injective      │ Function.Injective (ofRow p)                         │
│ ofHead_injective     │ Function.Injective (ofHead p)                        │
│ ofRow_auth           │ (ofRow p a).auth = ofAuth p a.auth                   │
│ processedS_ofRow     │ a.decode? = some (r, i, body) →                      │
│                      │   processedS p st (ofRow p a) = decide (a ∈ rowPool) │
│ excludesS_ofRow      │ a.decode? = some (r, i, body) →                      │
│                      │   excludesS p st (ofRow p a) = rowExcl p st a r i    │
│ handlesS_ofRow_iff   │ handlesS p st o (ofRow p a) ↔ o = ofRow p a ∨        │
│                      │   ∃ s b raw sup rows P, decode = .block …,           │
│                      │   parentFG st b = some P, blockAccepted … = true,    │
│                      │   a ∈ rows                                           │
└──────────────────────┴──────────────────────────────────────────────────────┘
```

With them: `decode_eq_vote`, `decode_eq_row`, `decode_eq_block` (the decoder
inverted, as iff lemmas; F1b.6 uses `decode_eq_block`) and `rowWire_decode`.

The row clause is defined once, in `Model/Protocol.lean`: `rowCount st r i`
(the rows of seat `i` and round `r` in the pool) and `rowExcl p st a r i`
(`a` not in the pool, and old or capped). `excludesS` uses `rowExcl`, with no
change of behaviour; `excludesFixed` uses `rowCount`; `rowExcl_iff` gives the
Prop form `a ∉ st.rowPool ∧ (r + p.wF < p.round (st.slot p) ∨ 2 ≤ rowCount
st r i)`.

`excludes_inert` (`Statements/Excludes.lean`, `Proofs/Excludes.lean`):

- One state. `excludesS_inert : excludesS p st o = true →
  FGSA.process p st (toWire p o) = st`, for EVERY store `st`, and
  `excludes_inert c : ∀ nd o, (fgsa p c).excludes nd o = true →
  (fgsa p c).process nd o = nd`. This is the frozen `HooksSound` field
  `excludes_inert`. It uses the three lemmas of the lead's input:
  (i) `Internal.lt_sub_one_iff_add_one_lt : r < cur - 1 ↔ r + 1 < cur`;
  (ii) `row_wire_roundtrip` (a row decode gives back the signed row);
  (iii) `admitBlock_of_blockExcluded : blockExcluded st b = true →
  admitBlock p st s b raw sup rows = st`. HEAD: the Grid CO exclusion makes
  `admitVote` return the base (local reproof; T7 imports no Grid CO proof
  module). Row: `admitRow_of_rowExcl`. Unsigned or malformed: `process`
  returns `st`.
- One step. `excludesS_process : excludesS p st o = true →
  excludesS p (FGSA.process p st w) o = true` (a delivery of any wire keeps
  an exclusion); `excludesS_clock` (a tick that does not move the clock
  back keeps it).
- One epoch. `EpochStep p mono` is one store step of a restart epoch: a
  delivery (`FGSA.process`) or a tick (`FGSA.clock`); with `mono = true`, a
  tick does not move `base.now` back. `Epoch p mono` is its reflexive
  transitive closure; `Epoch.weaken : Epoch p mono st st' → Epoch p false
  st st'`.

  ```lean
  theorem excludes_inert_epoch {st st' : State p.n} (hE : Epoch p true st st')
      {o : Obj p} (h : excludesS p st o = true) :
      excludesS p st' o = true ∧ FGSA.process p st' (toWire p o) = st'
  theorem excludesFixed_inert_epoch {mono : Bool} {st st' : State p.n}
      (hE : Epoch p mono st st') {o : Obj p} (h : excludesFixed p st o = true) :
      excludesFixed p st' o = true ∧ FGSA.process p st' (toWire p o) = st'
  ```

  `restartFree` is not a premise. `excludesFixed` is the part of the
  exclusion that does not read the clock (HEAD equivocation, the row cap,
  the proposal clause); it holds on an epoch with any ticks. Only the
  old-label HEAD and row clauses need `mono = true`.
- Runs. `epoch_of_restartFree`: on `restartFree rho v i j` the stores of `v`
  from `stateBefore i` to `stateBefore j` are an `Epoch p mono`; with
  `mono = true`, the premise `hmono` says that no tick of `v` in `[i, j)`
  moves the store clock of `v` back. Corollaries:

  ```lean
  theorem excludes_stable_epoch (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (v : V)
      (o : (fgsa p c).Object) {i j : Nat} (hij : i ≤ j) (hrf : V2.restartFree rho v i j)
      (hmono : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.tick v t) →
        (V2.Run.stateBefore E rho k v).st.base.now ≤ t)
      (h : (fgsa p c).excludes (V2.Run.stateBefore E rho i v) o = true) :
      (fgsa p c).excludes (V2.Run.stateBefore E rho j v) o = true ∧
        (fgsa p c).process (V2.Run.stateBefore E rho j v) o =
          V2.Run.stateBefore E rho j v
  ```

  `excludesFixed_stable_epoch` is the same for `excludesFixed`, with no
  `hmono` (it holds on every restart-free interval of every run).

Notes and open items:

- `fgsaIso.Base = State p.n` is forced, not a choice: the proposal is an AP
  label, and its hooks read F and the FG block store (`blockExcluded`,
  `parentFG`). The I-2 bridges add a separate Channels structure and a
  base-transport law; they do not shrink `fgsaIso.base` to `nd.st.base`.
- The `HooksSound` field `excludes_stable` is assembled in T7.7 from
  `excludes_stable_epoch` and the T7.4 clock laws: `hmono` follows from
  `ScheduleWellFormed` by the Kit law `stateBefore_now_le_event`, with
  `fgsaClock : V2.Engine.ClockLaws (fgsa p c)` (`now nd = nd.st.base.now`)
  and `fgsa_hrestore_now`. T7.2 does not do T7.4 or T7.7.
- I-3: option B is decided. `depsS` does not change; the law takes a
  `Timely` premise and holds at the states of scheduled runs. Astra R-A
  refinement: the conclusion is post-delivery `processed ∨ excludes`,
  because the in-delivery row cap can refuse a carried row that was not
  excluded before the delivery (Astra item 1). The lead and lean-framework
  own the law.
- The exact descriptions of the handlers (for example "a HEAD is processed
  iff its base vote is stored") hold under the store invariant only (Astra
  item 2). This is not a `HooksSound` violation: `HooksSound` asks for no
  such description.
- `recordOwn` does not put the own row into `rowPool`. This is the
  divergence that T7.10 approves (Astra item 3).
- `EpochStep` over-approximates the store steps of a scheduled run: it
  allows any wire and any tick time. The own record (`recordOwn` does not
  change the store, `recordOwn_st`) and events of other nodes are covered
  by reflexivity (Astra).
- Placement: the theorems are in `Proofs/Excludes.lean`;
  `Statements/Excludes.lean` holds only `EpochStep`, `Epoch` and
  `excludesFixed`. The general-purpose helpers (`grid_*`,
  `lt_sub_one_iff_add_one_lt`, `slotOf_mono`, `saGateFrom_vn`,
  `clockPre_vn`, `gateStep_vn`, `foldl_vn`, `admitRow_base`,
  `foldl_admitRow_base`, `ite_reconcile`, `eraseDups_nodup'`) are in the
  namespace `AvailableChain.FGSA.Run.Internal`, not `private` (private
  names hit the checker gap below). T7.7 can use `process_votes_subset` and
  `clock_vn` (the plan's `clock_votes`).
- Checker gap. A `simp` or `split` over a Grid CO definition with a
  `match o.auth, o.payload` (the shared matcher `GridCO.headLabel?.match_1`)
  makes Lean generate a PRIVATE matcher equation in this library. That
  equation uses `_sparseCasesOn_1.else_eq` constants, whose home module is
  `AvailableChainGridCO.Proofs.Map`. The used-constant check refuses it:
  its skip rule for generated equation lemmas (`generatedEqn`) does not see
  `_private` names. Workaround in the proofs: `grid_excludes_congr`,
  `grid_admitVote_now`, `grid_admitVote_votes_subset` and
  `grid_admitVote_keeps` use `unfold` and case analysis on the wire, not
  `simp` or `split` over that matcher. They stay as they are.
- Checker fix (commit "T7.1 check: used-constant owner mapping for generated
  equations"). `scripts/CheckFGSARunAxioms.lean` judges a generated USED
  constant by its owner: `generatedOwner` strips the private prefix
  (`privateToUserName?`) and the generated last components `eq_<k>`,
  `eq_def`, `splitter`, `else_eq`, `_sparseCasesOn_<k>` and
  `congr_eq_<k>`, one at a time, until the name is a declared constant. The
  check accepts the constant only if the owner is a definition in a module
  that is not forbidden. `generatedEqn` (the skip of a CHECKED constant)
  uses the same owner mapping, so it also sees private names. The rule has
  no list of names. Controls: NEGATIVE, `negOwnerRoots` rewrites with
  `GridCO.RootInjectiveBelow.eq_def` (Grid CO proofs) and is refused
  through the owner; POSITIVE, `posOwnerSplit` and `posOwnerSimp` `split`
  and `simp` over `GridCO.admitVote` and `GridCO.excludes` and pass. The
  positive control fails under the old rule (two `FORBIDDEN CONSTANT` lines
  for `headLabel?.match_1.eq_2`) and passes under the new one. After the
  v4.34.1 port the owner map is in the library `AvailableChainCheckSupport`
  (`scripts/AvailableChainCheckSupport/GeneratedOwner.lean`; imports only
  `Lean`; not a default target, the check scripts build it first); a grep in
  `scripts/check-fgsa.sh` shows that no protocol library imports it.
- Guards: every public theorem of `Proofs/Protocol.lean` and
  `Proofs/Excludes.lean` has a `#print axioms` line in `Tests/Axioms.lean`;
  `--expect` lists the main outputs; a negative control checks that a name
  in `--expect` that the scan does not find fails with `NOT CHECKED`.

Lease checks on the owner map (`scripts/CheckFGSALease.lean`,
`scripts/CheckFGSARunLease.lean`): a generated constant (also with a private
name) whose owner is a definition outside the scanned roots is skipped, and
its owner is inspected.

- No control separates the old rule (`eq_<k>`/`eq_def`, owner
  `n.getPrefix`) from the new one. The old rule was stricter than needed,
  never unsound: it scanned a private generated constant as an ordinary
  constant, and no current generated constant has a policy parameter.
- Safety of the new rule: every generated constant that it skips has its
  owner inspected, and the policy is checked at every use of the constant.
- Controls (in `check-fgsa.sh` and `check-fgsa-run.sh`): NEGATIVE, the owner
  of an `eq_def` carries the default policy (`ownerFixedGate`) and is
  refused; OWNER PATH ONLY, the equation `ownerBetaGen.eq_1` has a policy
  parameter, is realized in the scanned module and skipped, and the only
  report is the inspection of its owner (a policy bound by a beta-redex);
  POSITIVE, `split` and `simp` over `GridCO.admitVote` and `GridCO.excludes`
  give no report.
- Effect on the libraries: more generated constants are skipped (store 18 →
  51, run 8 → 27), with the same lease arguments and the same backstop reach.
  Eight compiler helpers of `AvailableChain.Auth` (`noConfusion`, `elim`,
  …), which have no policy, are no longer inspected; the backstop still
  reaches them.

A0 build checks (`scripts/check-build.sh`): the proof modules use `public
section` (check (b)); the two `respectTransparency` uses have a reason comment
and an allow entry (check (h)); F-13 is baselined for the four per-protocol
names (check (i)); the library has `globs = ["AvailableChainFGSARun.*"]` and
its root imports no Tests module (check (e), B7). `check-fgsa-run.sh` checks
the Tests modules as extra roots, and its root check refuses a root import of
a Tests module. The T7 allow lists accept `AvailableChainGridCO.Model.Walk`
(E-3).

Port to v4.34.1: `processedS_ofRow` and `handlesS_ofRow_iff` now also show
`Classical.choice`. It enters through `Finset.instSetLike` (the proposal
clause of `processedS`, `∃ Y ∈ st.fg.TF`, and `parentFG` →
`SimplexFG.pickPair` in `handlesS`): `Finset.instSetLike._proof_1` →
`Multiset.Nodup.ext` → `List.perm_ext_iff_of_nodup` →
`Classical.propDecidable`. This is the path that the port rule accepts.

Validation (branch `fgsa-t7-2` on the ported main `b97209a`, Lean v4.34.1;
Mac, `pgrep -x lean.orig` below 3 before each build):

```text
┌──────────────────────────────────────────────┬──────────────────────────────┐
│ Command                                      │ Result                       │
├──────────────────────────────────────────────┼──────────────────────────────┤
│ lake build --wfail AvailableChainFGSARun     │ pass (3185 jobs)             │
│ bash scripts/check-fgsa-run.sh               │ pass; 19 controls behave as  │
│                                              │ expected                     │
│ bash scripts/check-fgsa-run.sh (T7.2 commit  │ pass; 14 controls (no owner  │
│   alone, before the checker fix)             │ controls)                    │
│ bash scripts/check-fgsa.sh                   │ pass; 21 controls behave as  │
│                                              │ expected                     │
│ lake env lean --run scripts/V2Manifest.lean  │ pass                         │
│   --check                                    │                              │
│ Tests/Axioms.lean (99 lines)                 │ only propext, Classical.     │
│                                              │ choice, Quot.sound; no       │
│                                              │ sorryAx                      │
└──────────────────────────────────────────────┴──────────────────────────────┘
```

## Own-row self-delivery (own-row audit item, Option 1)

The FG action tick records the released row in Λ only (`recordOwn_st`); the
row enters the sender's store through a delivery event (the T7.10 divergence
above). The specification text (`fgsa-protocol.tex`, paragraph "Lean model of the
own FG row") states that a node that processes its own row in the tick
has the store trajectory of the Lean run with the row's self-delivery placed
at the action time, first among that time's deliveries. The results below
record the transfer argument in Lean. No Statements, Claims, manifest or
fixture changed.

Definition. For a run `rho`, an action time `t` and the cut index `n` (the
number of events with key at most `(t, 1)`, from `exists_cut` on the sorted
schedule), the spec-like run of `rho` at `t` is the run with events
`rho.events.take n ++ ds` and horizon `t`, where `rho.events.take n` is the
prefix through the ticks at `t` (all restarts, ticks and deliveries before
`t`, then the restarts and ticks at `t`), and `ds` lists one self-delivery
`.deliver u (row) t` for each sender `u` with an FG action tick at `t`, in
any order. The table is for the one-sender case (`ds = [the own row of v]`).
For more than one sender: `Base₂.snoc_ownRow_other` for Base₂, and repeated
`HealthyPrefix₂.snoc_ownRow` / `Recovery₂.snoc_ownRow` (with
`hkey_snoc_deliver`, `hlast_snoc_of_ne`, `V2.D.Run.getElem?_snoc_of_lt`,
`V2.D.Run.emitsAt_snoc_of_lt`). Not proved for `CleanPrefix₂`, `Clean₂` and `Outage₂`.

Coverage. The append laws alone (`ExecutionValid.snoc_selfDelivery` and the
`snoc_ownRow` forms) need every event at or before key `(t, 2)`, so with
`tick_total` they apply only to a run whose horizon is `t`. The cut and the
`ownRow_run` forms cover an arbitrary valid run `rho` with a tick of `v` at
`t` that releases the row, for exactly these regimes and action times:

```text
┌───────────────────────────┬──────────────────┬────────────────────────────────┐
│ Regime of rho             │ Action time t    │ Regime of the spec-like run    │
├───────────────────────────┼──────────────────┼────────────────────────────────┤
│ Base₂                     │ any              │ Base₂                          │
│ HealthyPrefix₂ b₀ ΔF      │ b₀ ≤ t           │ HealthyPrefix₂ b₀ ΔF           │
│ HealthyPrefix₂ b₀ ΔF      │ t ≤ b₀           │ HealthyPrefix₂ t ΔF            │
│ CleanPrefix₂ b₀ ΔF        │ b₀ ≤ t           │ CleanPrefix₂ b₀ ΔF             │
│ CleanPrefix₂ b₀ ΔF        │ t ≤ b₀           │ CleanPrefix₂ t ΔF              │
│ Clean₂ ΔF                 │ any              │ Clean₂ ΔF                      │
│ Recovery₂ G ΔF            │ any              │ Recovery₂ G ΔF                 │
│ Outage₂ fast T b₀ b₁ ΔF   │ b₁ ≤ t           │ Outage₂ fast T b₀ b₁ ΔF        │
│ Outage₂ fast T b₀ b₁ ΔF   │ b₀ ≤ t ≤ b₁      │ Outage₂ fast T b₀ t ΔF         │
└───────────────────────────┴──────────────────┴────────────────────────────────┘
```

Not covered by these theorems: `Outage₂` for `t < b₀`. Lowering the prefix cut to `t` requires
`T + (if fast then 4 * p.Δ else L p - 3 * p.Δ) ≤ t`. The original `lag` field does not imply this stronger bound. Every claim quantifies over all valid runs, so it covers the
spec-like runs. The results are not a full run embedding (Option 2 of the
analysis): a claim read at a time after `t` is read on the original run,
where the own row arrives by delivery within the regime's bound.

- `fgsa_emitOk_row` (`AvailableChainFGSARun/Proofs/SelfDelivery.lean`):
  `EmitOk` for every FG row released at a tick of a valid run. The `fresh`
  field is `fgsa_emitted_row_fresh`: the own row is not in `rowPool` before
  the tick, from `rowPool_provenance`, `UnforgeableSignatures`,
  `fgsa_emitOnceUnder` and the schedule order. `fgsa_emitOk_fg` covers every
  object released at an FG seat.
- `executionValid_snoc_selfDelivery` (same file) and `Base₂.snoc_ownRow`
  (`AvailableChainFGSAProofs/Proofs/Shared/SelfDelivery.lean`): the run with
  the same-time self-delivery of the own row appended after the last event
  of the sender is `ExecutionValid` and keeps `Base₂`
  (`namedRootCollisionFree_snoc_row`: a row delivery adds no named body).
  `partialSynchronyBy_snoc_selfDelivery` and
  `healthyPrefixDeliveryBy_snoc_selfDelivery` (run file): the per-object
  delivery premises survive the append for any released object that carries
  nothing; the relay obligations of the new acceptance are the broadcast
  obligations of the emission, with the same deadline.
- The cut (run file, generic in the protocol): `exists_cut`,
  `executionValid_cut`, `cut_key_le` and `cut_lastEvent` (the `hkey` and
  `hlast` premises of the append laws hold by construction),
  `stateBeforeTime_cut`, and for FG-SA `namedRootCollisionFree_cut`,
  `partialSynchronyBy_cut` and `healthyPrefixDeliveryBy_cut` (the latter for
  a prefix cut at most `t`). `executionValid_ownRow_run` composes cut and
  append.
- The regime records: `Base₂.cutAt`, `Base₂.ownRow_run`,
  `Base₂.ownRow_run_exists` and `Base₂.snoc_ownRow_other`
  (Shared/SelfDelivery); `HealthyPrefix₂.cutAt` and `.ownRow_run` (for
  `b₀ ≤ t`), `HealthyPrefix₂.cutAt_le` and `.ownRow_run_le` (for `t ≤ b₀`,
  prefix cut lowered to `t` through `healthyPrefixDeliveryBy_of_le`),
  `CleanPrefix₂.ownRow_run` and `.ownRow_run_le` (participation at `t` from
  `partBefore` when `t < b₀`, from `partAt` when `t = b₀`),
  `Clean₂.ownRow_run`, `Recovery₂.cutAt` and `.ownRow_run`,
  `Outage₂.ownRow_run` (for `b₁ ≤ t`), with the `snoc_ownRow` forms
  (`AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean`).

All theorems use only `propext`, `Classical.choice` and `Quot.sound`. They
close the own-row audit item as a recorded transfer argument.

**Verdict: REVISE. Do not start Task 1 from this version.**

The main store design agrees with the frozen spec. The plan correctly keeps
the cumulative tree, applies SA to the active view, preserves admitted
proposal metadata, uses the live FJ controls, and normalizes S after gates
and finality changes. However, the proposed model has a dependent-type error,
an incomplete ingress check, and incomplete interfaces for K1, K4, and K5.
The import rule and the proposed proof reuse also conflict. Correct these
items and audit the changed sections before G0 closes.

```text
┌──────────┬───────┬──────────────────────────────────────────────────────┐
│ Severity │ Count │ Main effect                                          │
├──────────┼───────┼──────────────────────────────────────────────────────┤
│ BLOCKING │ 1     │ Model functions use two unrelated committee sizes.   │
│ MAJOR    │ 6     │ Validation, proof scope, imports, and axiom command. │
│ MINOR    │ 5     │ Tests, total functions, source pins, and scheduling. │
└──────────┴───────┴──────────────────────────────────────────────────────┘
```

Audit: r185, 2026-09-28. This is a plan and source audit, not a compiled
certificate for the proposed library. No full build was run. Only this
report was written in the repository. No commit was made.

**Evidence and source versions**

The following short names identify files in the findings. Line numbers refer
to the files read during this audit.

- `plan`: `docs/plans/2026-09-29-fgsa-model-store.md`, at HEAD
  `7af69aa74ca9d0ec6f31fcbed797e5fd81d6487a`, branch `fgsa-composition`.
- `R`: `/Users/francesco/ethereum/research/async-resilient-committees/tip-stability`.
- `spec`: `R/spec/fgsa-protocol.tex`. Verified SHA-256:
  `2e88481117ba3e663c559f95218ce545aba5639f201063c1942dc5599adb9787`.
- `bp00`: `R/blueprint/00-outline.md`. Current SHA-256:
  `03afa5ae814606ac7c75525766f8b17926616a8e858b26deef1a59152fb64ad5`.
  This differs from the plan's `6057f9b5…` pin; see N4.
- `bp01`: `R/blueprint/01-foundations.md`. SHA-256:
  `989289cce1d761adfae3bc91b0358ff858b59d1151678d8d99d547a08f8eb3ea`.
- `comp`: `R/codex/lean-composition-plan.md`. SHA-256:
  `228dbe980a2dbf6071d156725c6327925f76284445d69be030730a0671eaf309`.
- Lean paths below are relative to the worktree root. Workspace proof and
  build rules were read from `/Users/francesco/ethereum/lean/AGENTS.md`.

The initial Git status was clean. There was no local `AGENTS.md` or
`state.md` to load. The task's single-file write restriction takes priority
over the general session-log rule.

**B1 — BLOCKING: `n` and `p.n` are unrelated in the FG calls**

Evidence: `plan:882–894`, `plan:1050–1056`, `plan:1073–1076`,
`plan:1097–1100`, `plan:1205–1214`.
`Params.E` has type `Electorate (Fin p.n)` (`plan:427`). The functions above
take `st : State n`, whose FG store has type `Store (Fin n)`. For example:

```lean
def controls (p : Params) (st : State n) : Controls (Fin n) :=
  storeControls p.E p.cfg st.fg
```

`storeControls` uses one identity type for its electorate, input store, and
result (`AvailableChainSimplexFG/Store.lean:25,77–79`). This application
requires `Fin p.n` and `Fin n` to be definitionally equal. No binder supplies
that equality. The same problem affects `on_block`, `storeFrame`, `hOf`,
`HeadFields.ofBlock`, and `createRow`. SA's unindexed parameter adapter does
not make this FG application valid.

Required change: use `st : State p.n`, `Wire p.n`, and `Fin p.n` throughout
the parameter-dependent composite API. Alternatively, index `Params` by
`n`. Keep size-polymorphic helpers only where they do not use `p.E`.
Update downstream statements and fixtures together. Do not add casts or an
extra equality premise to each public theorem as a substitute for one
consistent API.

This finding follows from the source signatures. The scratch compiler
attempt was blocked before elaboration; it did not produce a Lean error
certificate. See validation below.

**M1 — MAJOR: a carried row can fail its own input check and still pass block validation**

Evidence: `plan:910–924`; `spec:234–237`, `spec:505–518`.
The standalone row branch rejects `.vote 0 root flag`. The block branch
checks only `a.round?.isSome` for each row. Thus a signed slot-1 proposal
with empty vote lists and a carried `.seat (.fg 0) i` row whose height is
zero passes the proposed `wellFormed`. The same row fails validation when
delivered alone. The block's round check also passes (`plan:873–875`).

The spec requires every carried row to pass its own check. The omission is
not covered by DQ12: correct authentication shape does not imply a valid
height pair. A height-zero row may have no chain-state effect, but it still
enters metadata and can enter the row pool. That is a different input model.

Required change: define one row-body validation helper and use it for both
standalone and carried rows. Require height at least one for a nonempty
height pair. Do not add an unsupported positive-height requirement to the
finality pair: the spec does not give that requirement. `BlockId` already
represents a present root; `Option FinalityPair` represents absence.

Add positive and negative tests for the same row in both delivery forms.
Keeping `process` separate from ingress is acceptable, as in the spec.
Document that `Reachable` currently permits unchecked inputs and is an
over-approximation; T7 must establish `wellFormed` at actual handler calls.

**M2 — MAJOR: local root freshness is not the full K5/content bridge**

Evidence: `plan:219–221`, `plan:570`, `plan:612–633`, `plan:1516–1517`,
`plan:1597`; `bp01:37–82`; `comp:229–234,406–410`.

DQ2 is valid under the spec's full-block root idealization. On a valid
input universe, a root match means that the block is already stored, so
root-based refusal and full-block duplicate refusal agree. The spec does
not need to process two different full blocks with one root. The stronger
refusal is a reasonable total definition outside that universe.

However, root freshness at each receiver proves only local injectivity.
Consider two wires with the same erased parent, slot, and root, but different
valid row lists. Two receivers can each admit one wire as their first block
with that root. Each local `TF` remains root-injective. The two constructed
FG blocks differ, and their erasures are equal. The existing AC
`RootInjective` cannot reject this case: it compares geometric `Block`
values, which are already equal
(`AvailableChainStatements/Generic/Conditions.lean:25–31`).

The proposed two-chain lemma requires both blocks in one root-injective
set (`plan:628–629`). It does not supply that premise for blocks at different
nodes. This matters for accountable safety, client/run lifting, and the
later joint safety proof. DQ2 must not make these obligations disappear.

Required change: specify the full-content premise now, even if T7 binds it
to a run later. Its scope must include genesis, all relevant proposals, and
their parent paths. Equal roots must identify the canonical full content,
including the ordered signed rows with rounds and the base vote/support
data. State the cross-store reconstruction and row-position correspondence
obligations. Prove that a checked row list loses no occurrence when mapped
by `filterMap RowWire.toRow?`.

DQ1's flat wire representation can remain. Parent reconstruction is sound
when parent geometry and full content have a common meaning across nodes.
`eraseFG (fgBlock P b rows) = b` is necessary but does not prove that common
meaning. Label Task 2 as the local carrier algebra until the full-content
bridge is supplied; do not mark all of blueprint K5 complete.

DQ3 can remain a run premise instead of a hash check. This is an explicit
change from comp D4, and the later public results must name the stronger
premise. DQ10's arithmetic root formula is not a content encoder. It also
has ordinary geometric collisions: a child at slot 2 of a root-1 block and
a child of genesis at slot 4 both get root 4. Do not claim fresh honest
roots from that formula. Root/content validity must cover honest emissions
as well as received faulty proposals, or the root construction must change.

**M3 — MAJOR: the advertised K1 theorem assumes the missing conclusion for fast writes**

Evidence: `plan:1421–1432`, `plan:1596`; `bp01:345–361`;
`bp00:456–462`; `comp:393–397`.

`reconcile_harmless` is a true and useful filter lemma. Its `hC : SACompat st`
also requires every historical fast-write member to be compatible with the
new F. Blueprint K1 derives that fact from origins, compatibility of saved
bodies and leases, and monotone F. The blueprint explicitly requires the
case where the original saved body was emptied by an earlier F.

The report note in Task 9 acknowledges the stronger premise, but the scope
table still calls K1 a completed T5 result. The future tasks need the K1
form without an independent fast-write compatibility premise. Such a
premise must not become a new Clean or P1 assumption.

Required change: retain this helper and add the local origin invariant
needed to discharge its extra premise. One useful shape says that each
remaining fast-write member B either precedes its still-saved original body
or already precedes the current F. Preserve this over gates, deliveries,
and reconciliation. Then state K1 for a reachable state with F replaced
by a descendant, before reconciliation. Compatibility hypotheses should
refer to that new F.

This argument needs transition history, but it does not require the generic
engine: the plan already defines a local `Reachable` induction. It can be
done in T5. If it is moved to a later task, revise the completion claim and
give that task an explicit statement and dependency before T12/T13 use K1.

**M4 — MAJOR: K4 does not yet include the immutable metadata facts of the blueprint**

Evidence: `plan:1256–1264`, `plan:1469–1478`, `plan:1490–1539`;
`bp00:424–434`; `bp01:167,192–196,222–243,250–259`.

`CStoreInv` relates the two block sets and includes the FG cache invariant.
It gives no relation between an admitted FG block and its full proposal
wire. It also gives no stamp uniqueness or stamp-preservation fact. The
admission equation lists blocks, leases, genuine results, S, and time, but
omits the new block stamp and both proposal lists. This leaves the HEAD
merge and row-inclusion reads without their advertised local metadata
interface. A fabricated state can satisfy `CStoreInv` and have an empty or
unrelated `proposals` list.

Required change: add separate local invariant fields or theorems for:

- Cumulative FG and erased trees, and unchanged old block/vote stamps.
- Exact insertion of the accepted block stamp and the original proposal
  wire; no insertion on refusal.
- One full admitted proposal for each non-genesis stored block, under the
  content convention of M2; its FG projection has the same ordered rows.
- The row-pool uniqueness and per-identity/per-round cap used by
  `proposalRows`, and uniqueness of lease targets and evaluated labels used
  by `leaseOf` and `fastWriteAt`.

Some of these can be separate results instead of fields in `CStoreInv`.
Run-level receipt times, causal signatures, and emission origins can remain
in T7. Distinguish them from the local preservation equations that T5 can
already prove. Keep `NestOK` separate if desired; T6 supplies it from
`Reachable`.

**M5 — MAJOR: the proposed GridCO proof imports reach a forbidden library**

Evidence: `plan:145`, `plan:1232`, `plan:1490`. The source import path is:

```text
AvailableChainGridCO.Proofs.Map
  → AvailableChainGridCO.Proofs.Relay                 (Map.lean:2)
  → AvailableChainGridCO.Proofs.Goldfish              (Relay.lean:2)
  → AvailableChainGridCO.Proofs.Basic                 (Goldfish.lean:2)
  → AvailableChainGridCO.Statements.Contract          (Basic.lean:2)
  → AvailableChainStatements.Generic.Claims          (Contract.lean:3)
```

`GenuineHistory`, `History`, and `RecordSlots` also reach this dependency.
The simple model imports and `AvailableChainKitFG.Correspondence` do not
reach the forbidden libraries in the inspected source graph.

Required change under the stated no-Statements boundary: prove the needed
small field, membership, and gate-origin lemmas locally from model imports.
Do not edit another library to extract them in this task. If the intended
rule excludes only direct imports, say so explicitly and disclose the
transitive Statements dependency. The current grep checks neither that
closure nor all five forbidden library names (`plan:543–545`). A proof
dependency is still present when its name is absent from the new source.

**M6 — MAJOR: the final axiom command is incompatible with the copied parser**

Evidence: `plan:638`, `plan:1552`;
`scripts/CheckFGAxioms.lean:42–50,63–72`.
The parser accepts one `--expect` followed by names. It sets
`expected := args.drop 1`. The proposed command repeats `--expect` before
each name. Every later `--expect` is therefore treated as a constant name
and causes exit 2. The final checkpoint cannot pass as written.

Use one flag followed by all eight names. Also change both the source
import and the explicit `importModules` array when copying the scanner;
changing only the top import and module-prefix predicate would leave the
scanner loading the old libraries. Test an expected name that exists and
one that does not. Keep the transitive axiom whitelist and the build-before-
scan rule. These are sound choices.

**N1 — MINOR: some smoke tests do not test the stated failure mode**

Evidence: `plan:783–818`, `AvailableChainGridCO/Model/Protocol.lean:300–308`,
`AvailableChainSimplexFG/Store.lean:166–174`.
At `stA`, time is 12 and the current slot is 3. The carried `v0` has label 1,
so the vote pool rejects it even if a faulty handler unpacks the refused
block. The round-0 rows of `B1'` are also the rows already carried by `B1`.
Their pool admission is a duplicate. The unchanged-pool checks therefore
do not detect premature carried-object calls.

Use a conflicting slot-3 block with a label-2 vote and a fresh admissible
row. First show that separate calls would admit those objects. Then show
that delivery in the refused block changes no field. Also test a duplicate
block and a future-round row refusal.

`stR1` is not established as reachable: it writes leases and results by hand
(`plan:806–813`). Call it a handler-integration fixture or construct those
fields through gates. Add tests for a vetoed gate, a fast renewal whose
deadline does not change, a slow-only renewal, and a proposal that leaves
the active view but must remain in the HEAD merge. The frozen-support test
alone does not test that last requirement.

**N2 — MINOR: `deepest` silently uses a unique-maximum rule instead of the root tie rule**

Evidence: `plan:1188–1190,1218`; `spec:260–262,1327–1335`.
For two different members at the same maximum depth, `pickPair` returns
`none`; the spec's general deepest rule selects the greater root. The
scheduled FG source set should be a chain, so this difference need not
occur on a valid execution. The plan has not supplied that proof.

Either implement lexicographic maximum by depth and root, or prove before
the model handoff that every source candidate set has a unique deepest
member. A fast-write set is formed from prefixes of one gate result and
later only filtered, so this local fact need not wait for a generic run.
Likewise, prove that `fgHead` is stored and that `fgBlockOf` succeeds before
claiming that the fallback head fields at `plan:1208` are unreachable.

**N3 — MINOR: exact SA reuse needs a scheduled-input qualification**

Evidence: `spec:683–694,1195–1205`;
`AvailableChainGridCO/Model/Protocol.lean:397–406`; `plan:1238–1243`.
The spec's release equivocation set uses votes stamped before `q_r`.
GridCO's release test uses all stored label-r votes for equivocation, but
uses the strict cutoff for resolved supporters. These agree at the first
scheduled release tick, before same-time deliveries. They need not agree
on fabricated states or on a repeated/backward clock after later votes
have arrived. `Reachable` permits such clocks.

This does not refute K2 or local F monotonicity. State the distinction:
arbitrary-clock `Reachable` is a proof over-approximation; exact spec
simulation requires the scheduled event order from T7. Do not claim an
unconditional equality of release helpers on arbitrary stores. A fresh
label premise on `clock_eq_saClock_gate` is appropriate; do not add fault,
synchrony, or FG-safety assumptions to this algebraic bridge.

**N4 — MINOR: source and report pins need correction**

`plan:31` pins a different bp00 hash from the current file. Re-pin the
intended blueprint and review its changes before G0 closes. This audit used
the current foundations statements at `bp00:399–482` and the matching bp01.
`plan:355` gives `fgsa-model-store-plan-audit.md`; the requested report is
`fgsa-model-store-plan-audit-report.md`. DQ1 points to Task 11 for
`eraseFG_fgBlock`, but its statement is in Task 10 (`plan:1458–1459`).

**N5 — MINOR: task dependencies and the proof gate are inconsistent**

Evidence: `plan:327–344`, `plan:1220`, `plan:1545–1562`.
Task 2 is a proof task before G6, while G6 says it must occur before any
proof task. Task 5's tests consume `stA` from Task 4 even though its table
dependency is only Task 3. The tasks marked parallel also edit the same
root imports and smoke-test file, and some edit the same statement file.

Change G6 to “before store proof tasks”, add the real fixture dependency,
and assign one owner for shared-file edits if tasks run in parallel.
Increase the estimates for Tasks 2, 7, and 11 if the strict import boundary
requires local proofs, and budget the missing K1/metadata invariants.
The general task order is otherwise workable. Keep module builds during
development, one library checkpoint, and the full project build only at
the final handoff. The check script already builds the library; avoid a
second identical checkpoint build unless something changed.

**Definition-by-definition source coverage**

“Match” below means that the proposed rule agrees at its stated valid call
site, subject to B1 and the listed representation obligations. It does not
mean that the proposed code was compiled.

```text
┌─────────────────────────────┬─────────────┬──────────────────────────────┐
│ Definition group            │ Spec lines  │ Result                       │
├─────────────────────────────┼─────────────┼──────────────────────────────┤
│ Params; E; cfg              │ 154–158,    │ Match. Unit weights; δt = 0  │
│                             │ 273–285     │ remains allowed.             │
│ round; slotOf; actionTime;  │ 197–223,711 │ Match. At a_r the slot is    │
│ Label.actTime               │             │ rR+1; R≥2 keeps round r.     │
│ RowBody; RowWire; toRow?;   │ 225–255     │ Forms match; fixed signer    │
│ Msg; Wire; base/lift maps   │             │ link and M1/M2 remain.       │
│ eraseFG; parentFG; fgBlock  │ 519–523     │ Geometry is suitable. M2.    │
│ State; initial; outputs     │ 339–353,    │ Match with declared caches   │
│                             │ 486–503,    │ and projection omissions.    │
│                             │ 558–569     │ See text below.              │
│ activeCompatible; actView;  │ 355–379     │ Match. onView must retain    │
│ onView                      │             │ only block-preserving steps. │
│ normalizeS; reconcile;      │ 441–461,    │ Match. Saved labels remain;  │
│ leaseOf; fastWriteAt        │ 474–484,    │ no new lease/result. Unique  │
│                             │ 874–894     │ map keys need M4.            │
│ blockExcluded               │ 178–182     │ Match. Ancestors of F are    │
│                             │             │ compatible, not excluded.    │
│ admitHead                   │ 831–842     │ Match to GridCO.admitVote.   │
│ admitRow                    │ 433–439,    │ Match for checked rows;      │
│                             │ 844–857     │ full-row cap, no pruning.    │
│ blockAccepted; admitBlock;  │ 530–542,    │ Correct order and refusal    │
│ process                     │ 804–829     │ shape. B1, M1, M2 apply.     │
│ wellFormed                  │ 505–528     │ Carried-row check missing.   │
│ fastSet; gateStep           │ 754–782     │ Match: raw result saved,     │
│                             │             │ once-guard, fast-only set,   │
│                             │             │ final normalization.         │
│ clock                       │ 683–694,    │ Match on scheduled ticks;    │
│                             │ 709–752     │ extra caches are inert. N3.  │
│ controls; fullTree;         │ 616–646,    │ Match: full live controls,   │
│ erasedList                  │ 982–1037    │ view-local witnesses.        │
│ liveRoot                    │ 648–664,    │ Match: full filtered tree,   │
│                             │ 1086–1098   │ depth/root order, else Z.    │
│ eligible; headInTree;       │ 1039–1114   │ Match: band on the parent,   │
│ getHead                     │             │ score and current slot.      │
│ proposalsAt; voterBlocks    │ 598–614,    │ Match: admitted proposals    │
│                             │ 1219–1234   │ and paths, original stamps.  │
│ headVotes; headSupport;     │ 423–430,    │ Match to 2e884811: carried   │
│ headVote                    │ 1276–1302   │ support reads cumulative T.  │
│ proposerVotes/Support;      │ 1236–1253   │ Match except root creation   │
│ propose                     │             │ needs explicit M2 premise.   │
│ chainWireRows;              │ 544–556,    │ Correct window, chain        │
│ blockWireRows; proposalRows │ 1255–1274   │ exclusion, pool-first cap;   │
│                             │             │ metadata invariants in M4.   │
│ fgHead; fgBlockOf;          │ 666–681,    │ Correct source/head split;   │
│ deepest; fgSource; fgInputs │ 1315–1338   │ fallback obligations N2.     │
│ attest                      │ 1304–1313,  │ Pure client projection.      │
│                             │ 1346–1414   │ Own-row processing in T7.    │
└─────────────────────────────┴─────────────┴──────────────────────────────┘
```

The inherited chain/client reductions need explicit documentation. The FG
module omits `σ.nj`, whose initialized and updated value is always false in
this spec (`spec:501,940–960`; `ChainState.lean:18,129–149`). Its client
therefore uses the false-ν branch (`Client.lean:95–119`). This is a valid
specialization, not an old-rule error. `Record` also omits `Λ.timeouts`,
which the spec writes but never reads (`Client.lean:15–26,122–126`;
`spec:1409–1411`). Document this as a projection, rather than full record
equality. Deriving `σ[B]` instead of storing it is valid if M2/M4 establish
immutable full content. Freeze, early, release-snapshot, and G caches are
extra SA fields; no FG-SA duty may use stale resolved flags from them.

The text diff from `bd942ca0` to `2e884811` changes no FG chain transition,
client, finality-acceptance, or FJ-frame pseudocode. The plan implements the
three relevant newer rules: no deletion from T, admitted proposal signatures
remain in the HEAD merge, and carried support tests T. The old
`Pins.lean:99–100` spec pin is therefore usable for that unchanged FG code,
with this explicit version bridge. It is not the authority for the new
composite rules.

**Decisions DQ1–DQ12**

```text
┌──────┬───────────────────┬───────────────────────────────────────────┐
│ ID   │ Audit answer      │ Required condition or change              │
├──────┼───────────────────┼───────────────────────────────────────────┤
│ DQ1  │ Keep flat wire    │ Cross-store content and row-position M2.  │
│ DQ2  │ Keep root refusal │ Equivalent on full-content valid inputs;  │
│      │                   │ local freshness is not global K5.         │
│ DQ3  │ Premise is viable │ Specify full-content scope now; bind T7.  │
│ DQ4  │ Keep Λ separate   │ Record/emission order and own-row admit   │
│      │                   │ remain mandatory T7 obligations.          │
│ DQ5  │ Keep once-guard   │ Empty and vetoed labels stay evaluated.   │
│ DQ6  │ Keep live reads   │ Do not read frozen resolved flags.        │
│ DQ7  │ Accept v2 reading │ F ≤ S; confirmed = stable = S.            │
│ DQ8  │ Keep unused G     │ Declare it extra; no duty/output reads.   │
│ DQ9  │ Keep hooks out    │ Pure ingress must be complete (M1).       │
│ DQ10 │ Conditional only  │ Arithmetic roots prove no freshness or    │
│      │                   │ content binding; see M2.                  │
│ DQ11 │ Accept early tags │ T15 pin check must use corrected sources. │
│ DQ12 │ Keep auth refusal │ Also validate carried row bodies (M1).    │
└──────┴───────────────────┴───────────────────────────────────────────┘
```

DQ7 is the correct reading. There is no third independent available output
in `spec:558–569`. The stored theorem should not assert global safety or
unconditional S monotonicity. Its proof over the larger local transition
closure is appropriate. The run lift remains in T7, as the plan states;
composition T6 is not fully complete until that lift exists.

**Lean reuse, decidability, and proof strength**

All principal names cited for reuse were found. The significant interfaces
are as follows:

- `SA.Params`, its `engine` adapter, and `SA.confirmation`, `gate`, `clock`,
  `release`, `prefixSupport`, and schedule aliases exist at
  `AvailableChainSA/Model/Protocol.lean:11–19,37–49,68–91`. `SA.gate` and
  `SA.clock` explicitly use `GridCO.slowLeasePolicy`. Keep that explicit
  policy when applying a generic GridCO gate lemma; the default instance
  is the GridCO policy (`GridCO/Model/Protocol.lean:15–20`).
- Vote and proposal field lemmas exist at `GridCO/Proofs/Map.lean:443–455,
  498–517`; stable preservation at `History.lean:60–68`; release subset at
  `Basic.lean:140`; gate block preservation at `Map.lean:940`; confirmation
  membership at `RecordSlots.lean:150`; gate target origin at
  `GenuineHistory.lean:32`. Their statements support the intended local
  arguments. Their import closure causes M5.
- `KitFG.pickPair_eq_of_unique` is a sufficient-condition theorem, not the
  full lookup equivalence (`Correspondence.lean:37–39`). Add a selector
  soundness argument for the forward direction of `parentFG_spec`.
- `KitFG.ancestor_closed_of_parent_closed` exists at
  `Correspondence.lean:322`. `storeInv_init`, `on_block_of_accepted`,
  `on_block_F_mono`, `storeInv_on_block`, and
  `storeControls_eq_fjControls` exist at lines 338, 440, 450, 462, and 509.
  `storeInv_on_block` needs
  `FGBlock.Preceq st.F B → ViewRootInj (insert B st.TF)`. Fresh roots plus
  parent closure can supply it in the composite accepting branch.
- `update_finality_TF`, `update_finality_h_max`, and
  `update_finality_pair` exist at `Correspondence.lean:253,260,268`. The
  latter two give equations; use order lemmas to derive monotonicity.
- `HeadFields.ofBlock` and `createRow` exist at `Client.lean:70,147` with
  one common electorate identity type. `createRow` returns a row and a
  function-valued record. Comparing the row-body projection is decidable;
  comparing arbitrary records is not an intended smoke test.
- The B1/B2/B3/B1′/stF fixtures exist. The pT numeric schedule and threshold
  calculations are consistent: `a_1 = d_2 = 14`, current slot 3, round 1,
  τ = 2, L = 7. The proposed successful fast-gate deadline 21 is correct.

`eraseFG` is structural recursion; the other new algorithms use finite
filters, folds, or the existing fuel-bounded GHOST. No new termination
problem was found. Bounded Finset quantifiers are decidable with the
available equality instances. `pickPair` has an executable unique-member
decision procedure (`SimplexFG/Frame.lean:69–85`). The smoke tests mostly
compare decidable fields, avoiding function equality and the known
whole-store equality reduction issue (`SimplexFG/Store.lean:122–125`).
Successful elaboration and kernel reduction still need to be checked after
B1. Changing a proposition to a Bool does not cure a type error.

The proposed `module`, `public import`, `@[expose] public section`, namespace,
and closing `end` layout matches existing library files. Keep model
definitions, public `Prop` statements, and proofs separate. Treat executable
audit scripts as scripts, with the copied scanner's import/main structure;
the universal library-header instruction needs that small exception.

K2, K3, local F monotonicity, and the proposed local store-preservation
statements need no fault bound, synchrony, positive timeout delay, or
assumption that an honest F is safe. Do not add these to make proofs pass.
The local K5 reflection premise is legitimate; the cross-node content
premise is a separate obligation. `clock_eq_saClock_gate` legitimately
requires an unsaved label. Its existential `fw` is sufficient for base-state
reuse, but a separate exact `fastSet` equation is needed for source origins.

The active-view results should also expose ancestor closure, genesis/F
membership, and unchanged stamps/pools, as in `bp00:437–442`. These follow
from the carrier/store facts. Later Clean safety, P1, and 6Δ inclusion still
need K6–K11, receipt-or-coverage, and the joint induction. None follows from
local nesting alone. Preserve the plan's exclusion of an `a ≤ f` assumption
from Clean/P1 reasoning.

**Validation and close conditions**

Read-only checks covered the plan, the frozen spec, both blueprint files,
the composition plan, the named Lean definitions and proof signatures, the
old FG plan, the axiom scanner, and the source import graph. The frozen
spec hash and HEAD matched the request. The spec-version diff was checked
directly. No internet source was needed: all authorities were local and
explicitly supplied.

One scratch file was created at `/private/tmp/r185/Types.lean`. It contains
the plan's Objects excerpt and minimal checks of the mismatched FG calls.
Command, from the worktree root:

```text
lake env lean /private/tmp/r185/Types.lean
```

The global Lean throttle tried to use its shared lock directory under
`/Users/francesco/ethereum/lean/decoupled-consensus-model/collab/orch/locks`.
The sandbox denied those operations. `pgrep -fl lean` also could not read
the process list. The waiting command was interrupted with exit 130. No
scratch proof or smoke test was successfully compiled. The throttle was
not bypassed, no further compile was attempted, and no build or axiom-scan
pass is claimed.

Before implementation, close B1 and M1–M6 with concrete plan edits. Correct
the tests and source pins, and make every remaining total-function or
scheduled-input qualification explicit. Repeat G0 on those edits. At G6,
check the corrected definitions against the inventory above. At the final
gate, require a warning-free build, the corrected axiom scan, and a K-id
table that separates completed local facts from the remaining run lifts.

# FG-SA architecture map

**Current policy — 2026-10-09.** APIs and anchors can change. Generate the current
snapshots, then review all additions, removals, statements, and dependency changes.
Older freeze, append-only, no-widening, and zero-rename rules below are history.
They do not set current acceptance rules. Kernel, proof, source, and import checks
still apply. A snapshot update does not approve a changed claim.


_Shared map for three sessions. Created 2026-09-29 from DC-simplify's
draft 1. One screen per section; detail goes in the linked documents.
Update it when a module, an interface, a constraint or the milestone order
changes, and tell the other sessions._

```text
┌────────────────┬──────────────────────────────────┬─────────────────────┐
│ Session        │ Owns                             │ Map sections        │
├────────────────┼──────────────────────────────────┼─────────────────────┤
│ DC-simplify    │ spec, blueprint, research        │ §1–§2, §6–§7        │
│ (tip-stability)│                                  │                     │
│ lean-framework │ engine, framework, I9, 2a/2b/2c, │ §3–§4               │
│                │ 1c                               │                     │
│ fgsa-lean      │ T7/T1, F0–F6 (FG-SA claims in    │ (reports to both)   │
│                │ Lean); docs/FG-COMPOSITION.md    │                     │
│                │ (registry, pins)                 │                     │
│ all            │ milestones, links                │ §5, §8 (shared)     │
└────────────────┴──────────────────────────────────┴─────────────────────┘
```

## 1. Goal and priority

- Target: **FG-SA fully specified and verified** (user, 2026-09-29).
  FG-SA = the plain SA available chain (AC) + the DC finality gadget (FG),
  with the FJ root rule.
- Order: FG-SA needs first, then SA (its base), then the rest. Grid CO,
  SA-PC, L* and SimplexFG work is DEFERRED, not deleted; existing code and
  registry entries stay and stay green (user clarification, 2026-09-29).
- End state: the current spec is reviewed, and every main blueprint claim is a
  checked Lean theorem about FG-SA runs.

## 2. Protocol architecture (paper)

```text
┌──────────────────────────────────────────────────────────────────────┐
│ Substrate: cumulative tree Σ.T (fixed σ, stamps), admission F ⪯ B,   │
│ receipt premise                                                      │
├───────────────────────────────┬──────────────────────────────────────┤
│ AC = plain SA                 │ FG = DC finality gadget              │
│ votes, leases, fast/slow      │ rows, chain states σ, F, J, h_max,   │
│ lock, genuine results,        │ window W of ≤ K_W justifications,    │
│ available output              │ finality acceptance, Λ record        │
├───────────────────────────────┴──────────────────────────────────────┤
│ Composition: joint selection functions                               │
│ live_root · HEAD eligibility · C_fg · proposer head · finality head  │
│ (triple (h_j, J, h_F); finality_pair is FG's client function on it)  │
└──────────────────────────────────────────────────────────────────────┘
 AC → joint: X_r and leases; HEAD votes in the substrate pools (T-VOTE);
          AC services to the joint selections (H2′, HEAD clauses of H2.A
          and H3). S enters proofs only (T-START, T-SMONO).
 joint → FG: C_fg; the finality-head triple, also with no source; the
          carrier chain (honest proposals from slot s+2 have K ⪯ parent
          and carry rows, T-ROWS).
 FG → joint/AC (frame): FJ root Z + contest band; floor lo also relaxes
          AC eligibility; F for act(Σ), admission, reconcile, and the
          gate walk from Σ.F.
```

- Minimal AC→FG channel (blueprint 01 §1, r212/r212b): source
  candidates/C_fg and the carrier chain. The head selections read the
  substrate vote pools directly (proposer: previous-slot pool; finality
  head: current-slot pool), as `propose_block` and `get_fg_vote` do. So
  "HEAD votes are not a third AC→FG stream" holds for this partition
  only: the finality head reads HEAD votes through the joint function.

- The glue goes both ways by design (user): AC creates targets for FG; FG
  feeds back restrictions on the tree. Modular-spec study
  (`tip-stability/codex/scratch/modular-spec-study.md`): the spec splits
  into substrate, FG module, AC module and a composition section; no
  protocol change is needed.
- Proofs compose by induction over the trace index, as in DC. Clean and
  P1 use their stated channel properties; 6Δ inclusion also uses the
  proposer's full-tree walk (a joint function). The finality kernel is a
  composition theorem: it uses the healing witness, source/carrier facts,
  H2′, the HEAD clause of H2.A, H3/H4, the composition services
  T-START/T-SMONO/T-EXACT/T-VOTE/T-WALK, T-ROWS with matching-state bit
  persistence, and FG/substrate facts. The recorded finality claim set is
  the recurrence route only: FF5–FF7 from `HEALING_INPUT` through the
  FGoodE_W/Tail_W kernels. QF2/QF4 (Qual/Skip routes, Rec_sT/Rec_skipT,
  B_Q/B_skip) remain open extensions (user, 2026-10-01).
  Healing supplies one common witness tuple (r_G, u₀, M, r*, s*, C*)
  through H.22, and μ = μ(run, GST) as a function of the run, not a
  witness field; H-time supplies the GST bound.
- Lean consequence: v2 `Isolation` cannot express the channels
  (`fgsaIso` puts the whole FG store in base), so F0 adds channel files
  in the FG-SA claims library (`Channels`, `ChannelProps`, `Compose`).
- Transport: two delivery families (user, 2026-10-01). Blocks, HEAD/SA
  votes and their relays use Δ; gossiped FG rows and their relays use
  Δ_F ≥ Δ; a row carried in a block arrives with the block (Δ). Rows
  travel packed in the block body (I9 `packBody`, `rowsOk` in
  `wellFormed`); the block root commits to them. Carriage uses the carrier
  offset κ. In Lean, Δ_F is a regime parameter bound by the family-indexed
  delivery premise (`PartialSynchronyBy`), not an `Env` field.
- FG-SA finality is an FG-SA-specific WINDOW fold over the unchanged
  SimplexFG fold (user, 2026-10-01): FG-SA no longer uses SimplexFG's
  latest-only finality fold. The window keeps ≤ K_W justifications
  (K_W ≥ 2); target/progress steps are unchanged, and a height bridge
  (blueprint 01 §3.1a) transfers height facts between the two folds.
- Design rules (user): stay close to DC and justify every divergence;
  a bounded window of ≤ K_W justifications (K_W ≥ 2), not the latest
  certificate only; outputs nest by construction; FG never vetoes
  blocks; timeliness only on sending.
- Authority (window + Δ_F, final 2026-10-01; SHA-256 prefixes):
  `spec/fgsa-protocol.tex` 59bb0dda; blueprint 00 e4a145dc, 01 7a160200
  (§3.1 window invariants, §3.1a height bridge), 21 eaef7cfe, 22 8b7eaffe,
  23 7332c7a0. Previous authority: `spec/fgsa-protocol.tex` (adopted c1ea1db0, 2026-09-29;
  replaces 4e85ff34 with two changes: the pre-GST delivery clause of the
  partial-synchrony premise (OD6, as v2 `PartialSynchrony`) and the
  healing-interface names aligned with the blueprint;
  `spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md`; 4e85ff34 made the SA
  walk start at Σ.F). Blueprint line citations use the 4e85ff34 numbering.
  Proofs: `blueprint/` (00 outline; 01 foundations; 02
  Clean; 03 P1 and inclusion; 21 healing with `HEALING_INPUT`; 22
  finality).

- ROOT-DIGEST-2 uses recursive `NamedProposal` values. Each value keeps its exact named
  parent, body, ordered signed rows, raw HEAD list, and support list. `Block` and `FGBlock`
  remain geometric projections. Admission requires the exact named parent in `namedBodies`,
  rechecks the body and digest, and keeps the incoming value. Missing parents are dependencies.
- FG-SA uses root-mode GridCO/SA. HEAD wires, vote keys, stamps, counts, and equivocation
  use root identifiers. A read resolves one identifier in the cumulative store domain. No
  body or multiple distinct bodies leave the vote unresolved. Active views keep that domain;
  filtering the tree cannot remove ambiguity. Deferred protocols keep legacy block mode.
- The named run scope contains directly delivered proposals, honest prefix-held proposals,
  and their named ancestors. It includes rejected delivered bodies. Equal roots in this scope
  identify full recursive content. HEAD-only names and emitted-only tips add no scope seeds.
  Genesis enters through a held body or ancestry. `Base₂` keeps one idealization field.
- Duty `ACReads` is mode-indexed. FG-SA uses root-mode reads; legacy interfaces remain.
  The [ROOT-DIGEST-2 option-3 exception](FGSA-API.md#root-digest-2-option-3-exception)
  records the representation and frozen statement changes. The closed `fgsaClaims` type,
  claim fields, bounds, and prior exceptions remain.
- Integration order: compile and sign the W1 model/interface checkpoint; then run W2 proof
  work and W3 fixture/document work in separate trees. After W2 lands, the owner runs W3b
  for manifests, exact-hash allow data, catalog lock records, paired costs, and all gates.
  The lead applies the separate spec/blueprint patch. Historical pins stay unchanged.

## 3. Lean architecture (available-chain)

Layers (design §1). L0, L1, LM, L2 and L3 import nothing from L4–L6.

```text
┌────┬────────────┬──────────────────────────────────────────────────────┐
│ L  │ Layer      │ Lean libraries                                       │
├────┼────────────┼──────────────────────────────────────────────────────┤
│ L0 │ Engine     │ AvailableChainModel (objects; Block with stored      │
│    │            │ roots after ROOT-DIGEST; v1 Generic engine);         │
│    │            │ AvailableChainEngineV2/Engine (v2, from 2a)          │
│ L1 │ Conditions │ AvailableChainStatements (v1); EngineV2/Conditions,  │
│    │            │ EngineV2/Laws (Isolation, HooksSound, OutputsFactor) │
│ LM │ Modules    │ AvailableChainSimplexFG (FG store, chain states,     │
│    │            │ client, evidence)                                    │
│ L2 │ Facets     │ Framework/Facets; v2 Interface (EngineV2)            │
│ L3 │ Catalog    │ AvailableChainFramework (Claim, Profile, Catalog/*)  │
│ L4 │ Instances  │ GridCO (policy-generic; SA = GridCO at               │
│    │            │ slowLeasePolicy), SA, FGSA, SAPC, LStar;             │
│    │            │ Registry/Instances                                   │
│ L5 │ Kits       │ AvailableChainKit (v1), AvailableChainKitV2,         │
│    │            │ AvailableChainKitFG (FG proofs, Pins);               │
│    │            │ AvailableChainFGCompose (generic FG run composition) │
│ L6 │ Registry   │ AvailableChainRegistry, catalog.lock, MATRIX.md      │
└────┴────────────┴──────────────────────────────────────────────────────┘
```

A0 step 2 adds `AvailableChainGeneric`, a default library with separate
Statements and Proofs modules in Pure, V2 and AC. Statements expose definitions
and `f_def` lemmas; Proofs have a public section without `@[expose]`.
`AvailableChainGeneric.lean` imports the 21 modules below in order. The library
glob also builds Tests; the facade does not import Tests. Paths below are
relative to `AvailableChainGeneric/` and omit `.lean`.

```text
┌──────────────────────────┬──────────────────────────────────────────────┐
│ Module                   │ Role                                         │
├──────────────────────────┼──────────────────────────────────────────────┤
│ Statements/Pure/Quorum   │ qF; FaultQ, FaultX and Batch bounds          │
│ Statements/Pure/FirstBad │ AGRule, FirstFailure, WindowRule, RetroAt    │
│ Statements/Pure/Schedule │ Patterns, recurrence and window definitions  │
│ Statements/Pure/Walk     │ Suffix premises and E-4 walk statements      │
│ Statements/Pure/Props    │ CompatOn/At, MonoOn, BelowOn, ServedOn       │
│ Statements/Pure/PCQuorum │ qN = ⌈3n/4⌉, qA = ⌈n/2⌉; PC count contracts  │
│ Statements/Pure/PCRank   │ PC record, Formed, rank, pickPC, preferPC    │
│ Statements/Pure/PCFloor  │ pcFloor output floor and its contracts       │
│ Statements/V2/Reads      │ Run indices, pubFloor, HonestSlot, Pending   │
│                          │ E-9 time/index statement PROVED              │
│ Statements/V2/Counts     │ faulty and awakeHonest                       │
│ Statements/V2/Obs        │ Time observations with optional proposals    │
│ Statements/V2/Interface  │ FinalityInterface extends the v2 interface   │
│ Statements/V2/Receipt    │ DeliveryWithin; E-9 statements PROVED        │
│ Statements/V2/Regimes    │ Regime cores, LabelSync, LabelFacts, SeedAt  │
│ Statements/V2/Duty/      │ PC companion over Duty runs: DC mirrors      │
│   PCCompanion            │ (InBy, PersistsFrom, IncludedFrom, …),       │
│                          │ PCInterface, PCArmedRegime, PCIncluded,      │
│                          │ PCCompanion (statements only)                │
│ Statements/AC/Reads      │ ACReads, ACLaws, gate and reconcile reads    │
│ Proofs/Pure/FirstBad     │ Strong induction for the FirstBad rules      │
│ Proofs/Pure/Schedule     │ Pattern, window and recurrence facts         │
│ Proofs/Pure/BlockOrder   │ Block order, compatibility and path facts    │
│ Proofs/Pure/PCQuorum     │ qN/qA intersection, honest seat, uniqueness  │
│ Proofs/Pure/PCRank       │ Rank preorder; preferPC total, monotone,     │
│                          │ idempotent; folds; same-slot PC target       │
│ Proofs/Pure/PCFloor      │ pcFloor cases, target bound, nest, monotone  │
│ Proofs/V2/Fields         │ ownRecord_fold_restart                       │
│ Proofs/V2/Reads          │ E-9 time/index bridge                        │
│ Proofs/V2/Induction      │ Invariant and interval lifts; kept_from_seed │
│ Proofs/V2/Receipt        │ E-9 proofs; two DeliveryWithin producers     │
│ Proofs/V2/Regimes        │ Six LabelSync and LabelFacts facts           │
│ Proofs/AC/Output         │ output_step_of_restartFree                   │
│ Tests/Axioms             │ Kernel axiom audit of every public theorem   │
│ Tests/FoldRestart        │ Two special cases of the restart fold        │
│ Tests/Schedule           │ Window-bound and recurrence examples         │
└──────────────────────────┴──────────────────────────────────────────────┘
```

PC-SA is UNPORTED for the sleep wake-time restore interface (decision 2026-10-10).
`scripts/unported-libraries.txt` excludes its five libraries from compiled gates,
manifests, API snapshots and DCK targets. Source checks still apply. The PC-SA API
and deep snapshot are retained; `docs/PCSA-API.md` is STALE-UNPORTED. After the port,
remove all five list entries, restore PC-SA build and audit inputs, update its
snapshots, remove the stale header, and run the full gate.

- PC-SA PC layer (2026-10-05; `pcsa-decisions.md`, 3n/4 version and R-g):
  `PCQuorum` (thresholds `qN`, `qA`; two `qN` sets share `qA` seats; honest
  seat in a `qA` set; one block per slot with a `qN` exact-HEAD set),
  `PCRank` (abstract PC record with acker seats; rank by slot, then a tie
  key; `preferPC` keeps the rank-maximal PC; two formed PCs of one slot
  have one target) and `PCFloor` (available output = `S` if the PC target
  is `⪯ S`, else the target; target bound, nesting below the output,
  monotonicity). Import constraint: Pure layer, closure Mathlib +
  `AvailableChainModel.Objects.*` + Generic Pure only (GLY F-4, F-12); no
  V2, AC, GridCO or FG-SA import. Consumer: the PCSA family.
- PC persistence companion (2026-10-05; `pcsa34-r3.md` §5.4, App. B):
  `Statements/V2/Duty/PCCompanion` over Duty runs, modelled on the frozen v1
  `StrongClaims` (`AvailableChainStatements/Strong`, unchanged). `PCArmedRegime`
  is `StrongArmedRegime` with lag 3Δ, `a < q_A n`, `HealthyPrefixDeliveryBy`
  from the run start to `b₀` (ARM-healthy) and no restart; `PCIncludedRegime`
  has full participation and `4a ≤ n`. Both take a label family `Fam` with
  `CStar` and `n` seats per label (validator count = seat count, as `cstar` in
  FG-SA `Base₂`) and `delayPos` (the instance pins `delayOf`). Import constraint: S/V2 rule
  (GLY-SV2): Generic Pure and V2 statements, EngineV2 Engine/Conditions/Laws.
  PC-SA does not instantiate this companion: `PCArmedRegime` and
  `PCIncludedRegime` do not bound the faulty FG seats, so an unrestricted
  instance is false. The PC-SA-native forms replace it: stage 1
  `ArmHealthyClaim`, `StrongIncludedClaim` (over every FG mode with
  `StageOneFrame`; the AC-only instance `pcsaAC` discharges it by
  `AcOnlyFrameClaim`), stage 2 `ArmHealthyStageTwoClaim`,
  `StrongIncludedStageTwoClaim` (`Clean₂`, `a ≤ f`, no frame premise) in
  `AvailableChainPCSAClaims`.
- PC-SA shared proof layer (2026-10-07; stage 1 and stage 2). Paths are
  under `AvailableChainPCSAProofs/Proofs/`. `Shared/` holds lane-neutral run
  and store facts; it imports only `Foundations`, `Shared` and the allowed
  upstream layers, never a lane. Stage 1 moves `Certificates`,
  `HeadSupport`, `RunEvidence` and `StoreEvidence` from `PC/` to `Shared/`;
  the four `PC/` modules stay as compatibility shims that import the
  `Shared/` module, so open lanes keep their `PC/` imports. Stage 1 also
  adds the PC relay layer: `CollectClosed`, `StageStore` (the stage-1 store
  invariant; it keeps the names `OutageStore` and `pcsa_outage_*` from the
  move), `StageRun`, `RelayStore`, `RelayRun` (whole-PC relay and
  `pcsa_keyHeld_accepted`) and `PCViews` (best-PC rank, view target,
  installed-PC acceptance, PC retention). Stage 2 adds `Proposal` (the honest
  proposal is built at the proposer post-clock state: parent and `N.pc`),
  `Clock` (`pcsaClock`, `pcsa_clock_now`, `pcsa_process_now`), the body
  layer `BodyScope`, `TreeReceipt`, `BodyPersistence`, `BodyAdmission` and
  `BodyReceipt` (body origin, and `pcsa_body_relay_admitted`: a relayed
  accepted body is admitted by a deadline `d`, given the relay step to `d`)
  and `BodyRelay` (the same over a `DeliveryWithinOn` premise with the lane's
  deadline map). Stage 2b adds `HonestProposal`: the rows of an honest
  proposal pass R6, so no receiver excludes it; under `DeliveryWithinOn` each
  honest receiver holds its wire and a valid carried PC
  (`pcsa_honest_proposal_receipt`; `pcsa_honest_proposal_from_vote` from
  `v_s`, and `pcsa_honest_proposal_early` at the early read).
  Shared keeps the `HealthyPrefixDeliveryBy` wrapper
  (`pcsa_body_relay_before_deadline` in `Shared/BodyReceipt`, through
  `Shared/Relay`), used by Outage and Clean. The other lanes supply the relay
  step from their own delivery premises through `BodyRelay` (Recovery: the
  RECOVERY deadline `max t z_{s-1} + Δ`; Formation: `FormationPrem.delivery`).
  Stage 3 adds `VoterView`: every stored slot-`s` proposal is the honest one, so
  its PC is the only carried PC; every frozen PC of slot `s - 1` has a
  whole-PC acceptance by `z_{s-1}`, so under the deadline `max t z_{s-1} + Δ`
  its key is held at the proposer before `t_s`, and every honest voter view at
  `v_s` has the proposer target (`pcsa_commonView_of_delivery`, the F3 field of
  `FormationPrem`). These lemmas are the Formation lane's `pcsa_formation_*`
  lemmas with smaller premises, without the lane prefix (Shared carries no lane
  names); Formation drops its copies when it switches.
  The CI restart (2026-10-08) adds `CleanWindow`, the delivery window of the
  clean induction from a label `j₀`. `StrictFrom E rho T₀ cut` is non-row
  delivery with a deadline `dl t` that is `t + Δ` from the floor `T₀` and at
  most `max t T₀ + Δ` before it. Converters: `pcsa_strictFrom_of_healthy`
  (`HealthyPrefixDeliveryBy`, any `T₀`), `pcsa_strictFrom_of_sync`
  (`PartialSynchronyBy`, `T₀ = t_GST`) and `pcsa_strictFrom_of_within` (a
  `DeliveryWithinOn` premise with deadline `max t T₀ + Δ`, as
  `FormationPrem.delivery` with `T₀ = z_{s-1}`). `CleanWindow E rho j₀ T₀ b₀`
  adds `Base₂`, the cut, `T₀ ≤ t_{j₀}` and `a < h_j` at each label `j ≥ j₀` with
  `e_j ≤ b₀`; `Clean₂` gives it with `j₀ = 0`, `T₀ = 0`, and the RECOVERY
  components give it with `T₀ = t_GST`. The `_win` lemmas of `Shared/Relay`,
  `Shared/BodyReceipt` and the Clean lane take `StrictFrom` (or `CleanWindow`);
  the old `HealthyPrefixDeliveryBy` names are wrappers with unchanged types.
  `Clean/StampFrom.pcsa_clean_honestProposal_stamped_from` proves pre-freeze
  stamping in this window from equal honest HEADs and the awake N quorum.
  It needs `T₀ ≤ z_s` for the proposal at `s + 1`. It does not use
  `CleanRestartSeed`; recovery can use its conclusion to supply a seed stamp.
- PC-SA CI restart from a label `a` (2026-10-08; steps 4a, 4b, 5a and K2).
  The clean induction restarts at a seed label `a > 0` with seed block `A`.
  Shared modules:
  `Shared/SlotOrder` holds the slot-order facts that were in
  `Recovery/LockWindow` (`RecoverySlotOrdered`, `StoreSlotOrdered`,
  `ResultsSlotBound`, `pcsa_reachable_slot_order`, `pcsa_stored_strict_slots`,
  `pcsa_result_prefix_slot`, `pcsa_saved_result_slot`); `Recovery/LockWindow`
  keeps the four `recovery_` names as one-line wrappers with unchanged types.
  `Shared/LockRankSafe` is the store-level lock rank invariant
  (`pcsa_lock_rank_compatible`, `pcsa_live_lock_rank_compatible`), copied from
  `Recovery/LockRank` on `pcsa-recov-long`; the Recovery names become wrappers
  when that branch lands. `Shared/StampKeep` keeps PC stamps after their
  install (root uniqueness). `Shared/RestartSeed` defines the positive seed
  `CleanRestartSeed a A` (`0 < a`, `A.slot = a`, a PC `(a, A)` stamped before
  `z_a` at every honest node, every honest HEAD and proposal of label `a` is
  `A`, every result of label `a` is `A`, every lock from `z_a` to the input of
  gate `a` is `⪯ A` (`locksFromFreeze`), and `ArmConcl a A (a + 1)`), and K1:
  from `z_a`, the proposer PC, the voter snapshot and the gate rank have slot
  `≥ a`. `Shared/RestartSuffix` defines the output interface
  `RecoveredSuffixInvariant s P cut` with eight fields: `resultsChain`,
  `pcChain`, `pcResults`, `selected`, `recordOrigin`, `recordMono`,
  `gateAdvance` and `honestGate`.
  Clean modules: `LockFromCut` (K3: a lock after a cut index was stored at the
  cut or written by a later own gate), `RestartRecord` (K4: after gate `a`
  the record is `A`), `RestartRoots` (the root at `v_{a+1}` is `A`; the root
  sources and ack dissemination from `a`), `RestartState` (the seven-field
  state `CleanStateFrom a j`: results, HEADs above results, equal HEADs,
  PC/result pairs, roots, ack/HEAD and ack/result coverage, every label
  quantifier from `a`), `RestartKernels` (the joint-step kernels from `a`),
  `RestartStep` (the joint step and `pcsa_restart_state_from`, for every
  `j ≥ a` with `d_j ≤ cut`), `RestartOutputs` (record history from gate `a`
  and `pcsa_restart_suffix_invariant`, over `CleanWindow E rho a T₀ cut`,
  `StageOneFrame`, `FaultsBelowQA` and the seed) and `RestartLocks` (K2:
  `pcsa_restart_locks_from_freeze` proves `locksFromFreeze`; every stored
  lock rank comes from an earlier own gate below `a`, so the held seed PC
  ranks above it).
  K2 and K4 are in Clean: they use Clean record and lock provenance, and K2
  needs no Recovery lemma. `pcsa_cleanRestartSeed_mk` builds the seed from
  `0 < a`, `A.slot = a`, the stamp, the HEADs, the proposal, the results,
  `ArmConcl` and `z_a ≤ horizon`.
  `Assembly/Recovery` supplies the seed from Formation and C8, and the
  horizon window from RECOVERY. The Formation conclusion supplies the seed
  stamp. `Clean/RestartStamp` supplies the stamps for later honest slots.
- PC-SA Formation (C7; 2026-10-08). Paths are under
  `AvailableChainPCSAProofs/Proofs/`. The Formation proofs are the
  `Clean/Formation*` modules; `Clean/FormationExport` collects them. It is an
  ordinary Clean module, not a lane Export. The layer checker grants one exact
  edge for it, `Assembly.Formation → Clean.FormationExport`
  (`scripts/check-layers.py`); no other module may import it across lanes.
  `Shared/FormationWindow` holds the pre-freeze interface
  `FormationPreFreezePrem`: `FormationPrem` with the delivery cut at
  `freezeTime s` and the Formation deadline `max t z_{s-1} + Δ`.
  `FormationPrem` carries the F4 clause `FormationRootReachable` (the
  proposer walk from the carried PC target, or `Z`, reaches `liveRoot`);
  `HealedSourcePrem` carries the same clause at `r * p.R`. Parts 1–4 of the
  conclusion follow from `FormationPreFreezeInputs`; the gate counts
  (`Clean/FormationGateCounts`) give part 5. `Assembly/Formation` proves
  `FormationClaim` (`pcsa_formationClaim`) and `FormationSourceClaim`
  (`pcsa_formationSourceClaim`, through `Finality/Export`) with no open input.
  `Clean/FormationRetainedTree` and `Clean/FormationRetainedBack` prove the
  five retained HEAD facts; `Clean/FormationFrozenRaw` proves the frozen raw
  relay from the Clean windowed HEAD relay (`StrictFrom` at `T₀ = z_{s-1}`).
  See `Clean/FormationOPEN.md`.
- PC-SA finality safety (P12): `Foundations/FGSafetyBridge` converts the PC
  reads and applies Compose `SafetyAccountable`, `SafetyCount`,
  `SafetyMonotone`, and `SafetySlashing` through four exact `COMPOSE_EDGES`.
  `Foundations/FinalitySafety` supplies the six run bodies. `Finality/Export`
  proves the two pure fields with KitFG and closes all eight frozen claims.
  `Assembly/Finality` supplies `PCSAClaims.finality` with
  `pcsaSafetyFinalityClaims`. Both FG modes are covered. Count retains
  all-run carriage; honest non-slashing uses stored-row carriage.
- PC-SA recovery lock history (2026-10-08). `Recovery/LockRank` proves the
  held-PC rank invariant for live locks. `Recovery/LockHistory` retains exact
  rows and ranks across receipts and clocks outside gates. It locates the gate
  at the start of the final uninterrupted interval of a row and its rank.
  The derived write witness keeps that interval, the fresh gate, the current
  result, the preceding saved window, the write rank, and the exact deadline.
  `recovery_live_lock_last_write` supplies it at an actual post-clock read.
- PC-SA recovery anchor (2026-10-08). `Recovery/AnchorBase` bounds the
  proposer base from one node's anchor stamp and the C8 strong-output bound.
  `Recovery/FirstSlot` proves the first formation slot and its separate
  `RecoveryRootReachable` clauses from the anchor and saved-result bounds.
  `Assembly/Recovery` supplies three wrappers:
  `pcsa_recovery_cleanSaved_from_anchor` bounds saved results below the anchor;
  `pcsa_recovery_anchor_from_shortBreak` supplies the anchor proposal, stamp,
  ARM, and C8 conclusion; `pcsa_recovery_firstSlot_short` supplies the first
  formation slot and its separate root clauses from `ShortBreakPrem`.
- PC-SA Outage items (2026-10-06): `AvailableChainPCSAClaims/Statements/OutageItems`
  holds the statement-only items of the Outage lane: `LockRow`, the ARM-healthy
  items `CleanHeldPCRelay`, `CleanArmAcks`, `CleanArmItems` (5.4.2) and the slow
  P1 boundary `CleanSlowBoundary`, `CleanSlowItems` (5.5 steps 1–2). They are
  not claims. A lane module may import them (Statements are upstream of every
  lane); the proofs stay in their lanes. The pending-label Clean claims
  (`CleanResultsNonemptyClaim`, `CleanResultsChainPendingClaim`,
  `CleanDisseminationPendingClaim`) and `CleanBlockReceiptClaim` (the relay item) are
  in `Claims/Clean`, outside the `PCSAClaims` record. C8 ARM-healthy uses the
  vote-time HEAD cone `CleanVoteConeItems` and C10 slow P1 uses the full HEAD
  cone `CleanConeItems` (`Outage/CleanBridge`). The Outage assembly proves both
  from the Clean cone theorems and closes C8 (`pcsa_armHealthyClaim`) and C10
  (`pcsa_slowP1Claim`) with no open hypothesis (see
  `AvailableChainPCSAProofs/Proofs/Outage/OPEN.md`).
  `Outage/BlockReceipt` proves block receipt from the Shared body relay;
  Assembly/Outage packages it as `CleanBlockReceiptClaim`.
- KitFG definition modules: `StoreInvDef` holds the unchanged `StoreInv`;
  `ViewLock` states the strict height bound; `HonestRows` holds the three
  honest-row premises. Each uses `@[expose] public section`.
- KitFG `Certificates` adds E-15 row-step commutativity and idempotence,
  fold permutation and duplicate removal, and transition equality by row set.
- KitFG FG-fold consumption (pure SimplexFG facts, 2026-10-01): `FinalityConsume`
  (finality write from quorum coverage), `HeightConsume` (target/progress
  advance), `NoEarlyMixed` (early crossing is justified; first height edge;
  plateau J), `RowHistory` (row-occurrence history). FG-SA uses them on the
  window fold only through the height bridge; the finality lemmas stay
  SimplexFG facts.
- KitFG window core (height bridge, blueprint 01 §3.1a): definition modules
  `HeightCoreDef` (FGHeight projection without finality fields, HeightRowsEq
  selector condition, deriveWithSelector on the same block geometry,
  HeightStepBridge, HeightFoldRefinement) and `HeightLawsDef` (FGHeightLaws);
  proofs `HeightFold`, `HeightBridge`, `HeightLaws`, `HeightConsumeTransfer`,
  `HeightHistoryTransfer`. FG-SA supplies the window instance
  (`HeightFoldRefinement` for its raw window fold); KitFG never imports FGSA.
- KitFG window certificate (migration stage 2, 2026-10-02): definition modules
  `CertificateCoreDef` (FGFinality projection, TargetQCAt, JustificationBirth,
  FGCertificateLaws), `CertificateSelectionDef` (entries keyed by (j, X) with
  their quorum; greatest-ready selection read from the pre-finality list;
  pruned lower entries covered by X ⪯ F with no own QC; eviction gives no
  coverage; pruneCertEntries), `StoreSafetyDef` (F-lock with explicit fault /
  no-slash premises) and `ProvenanceCoreDef`. Shared cores, with no
  `CertificateSimplex` in their import closure: `AccountableCore`, `CrossingCore`,
  `ProvenanceCore` (forms that need only the height laws take FGHeightLaws),
  `SelectionCore` (FGSelectionLaws.of_core, FGCertificateLaws.of_selection),
  `StoreSafety`. SimplexFG adapters: `CertificateSimplexDef`,
  `CertificateSimplex`, `StoreSafetySimplex`. Existing KitFG proofs stay
  unchanged; the cores are added companions. FG-SA proves the window instance
  (FG2) and calls the cores.
- KitFG frame bridge (for the FG5 switch, 2026-10-02): `FrameBridgeDef` states
  these SimplexFG readers over a height view v: frontier, lexMax, filteredFrom,
  storeControls, storeFrame, fjControls and fjFrame (`…View`); `FrameBridge`
  proves each equal to its view form under `HeightBridge E cfg v`, plus
  hOf_of_bridge. They read only height fields. SimplexFG is unchanged. Readers
  of the finality fields (on_block, update_finality) are not covered; FG5
  replaces them with the window store.
- KitFG frame geometry (LF8, FG5 job J1, 2026-10-02): `FrameGeometry` states the
  frame facts that FG-SA took from `StoreInv` over `FGStoreInvariant H f` in
  view form (controls = FJ controls, full frame, crossed-prefix height,
  no-contest, contest, retention), by the structural route (J carrier from
  `pair`, `hmax`, `gen`), plus `mem_filteredFromView`.
  `JustificationLawsDef` adds `FGJustificationLaws H` (J entry, J height,
  J zero), with `FGJustificationLaws.of_bridge` for every bridged view.
  `CausalCapCore.finalityCap_row_of_certificate` is the finality-cap row over
  `FGCertificateLaws`.
- FGSA E-11 adds `LeaseBelowOutputStore` in `Statements/Invariants` and
  `StoreBundle` with `StoreBundleInvariant` in `Statements/Store`. The bundle
  has cstore, meta, nest and lease fields; the E-11 statements are PROVED.
- `AvailableChainFGSA/Proofs/LeaseOutput` proves the E-11 stored-target invariant.
- `AvailableChainFGSA/Proofs/StoreBundle` proves E-11 by bundle induction
  (`storeBundleInvariant`).
- FG-SA window (stages 1–2, on main; additive until the switch J4):
  `Model/Window` (window state with ≤ K_W retained justifications, the raw
  fold `transition p K`, `derive p K`, R6W row validity), `Model/WindowStore`
  (window store and viable tree); `Statements/WindowHeight` and
  `Statements/WindowCertificate` (projections, pre-finality state);
  `Proofs/WindowHeightBridge` (windowHeightBridge, window height laws),
  `WindowInvariant` (structural window invariants), `WindowSelection` and
  `WindowCertificates` (the KitFG certificate and selection records),
  `WindowProvenance` (provenance forms), `WindowHistory`, `WindowStore`
  (store invariant over the window views), `Statements/WindowEntries`
  (`RetainedW`, `CoveredW`: the window key (j, U)), `WindowLiveness` and
  `WindowRetention` (pure stage-4 bit, retention and exact-row facts).
  Since J4 (2308c42): the model runs the window fold. `heightView` =
  projectHeight of `Window.derive p p.K_W`; `finalityView` = certificate
  finality; `admitBlock` checks every row with R6W (`rowValidW`) against one
  pre-fold `Window.parentState`; the client reads window head finality. The
  height bridge keeps the shared source projection and the height-only Claims
  readers equal until J6. `scripts/CheckFGSAOldReads.lean` audits that no
  active declaration reads the old fold's finality.
- 07-H adds Claims `Fold` for height batches, raw action-history inputs in
  `Phases`, and `Claims/Healing` adapters. `Foundations/RowService` proves
  strict all-emissions receipt at ΔF, parent-valid selection, and height
  coverage on the current fold. `HeightMatch` is explicit at height consumers.
  `TRowsSelect` remains the R7 validity selector. Finality-bit ports wait for 07-F.
- FG-SA healing lane (S5 CONE): `Proofs/Healing/PostResetCone` proves the
  cone step at each event cut; `PostResetConeFrame` supplies the common pivot
  and floors; `PostResetConeHeads` bounds source and live-lease heads;
  `PostResetConeInput` assembles the cone input; `PostResetConePool` proves
  the honest-seat and frozen-pool bounds; `PostResetConeReceipts` proves
  receipt and batch-seat facts. `Tests/HealingPostResetCone` checks the step,
  the empty cut and the run projection. Paths are under `AvailableChainFGSAProofs/`.
- FG-SA healing lane (RE-BIND): `Proofs/Healing/PostResetConeAt` projects the
  cone at a bounded HEAD label; `PostResetJointStep2` supplies the opening
  and service steps from the cone at the step cut.
- `AvailableChainFGSARun` (T7.2) holds the v2 protocol, label families,
  isolation, wire adapters, and exclusion proofs, with separate Tests.

- SYN L58: `Proofs/Assembly/Root` imports the `FGSAClaims` facade and the named
  lower Assembly modules `Foundations`, `Shared`, `Clean`, `Outage`, `Finality`,
  `ResetArrival`, `WeakContinuation`, `WeakContinuationGrowth`, and
  `WeakContinuationGrowthSeed`. The other layer rules still apply.

- WC plan r2.1, §8 Job 4; DC: SAME source witness before continuation.
  `Proofs/Assembly/WeakContinuation` takes the H-time producer from Root.
  It selects the source witness, constructs one seed, then replays the seed
  and supplies the 34 separate [L] premises for each continuation.
  `Proofs/WeakContinuation/Live` combines seeded safety with `wc_checkpoint`.
  `WeakContinuation/Export` re-exports this helper and replay for Assembly.
  Its four Statement inputs use the actual Job 2 producers. The result contains
  safety, persistent inclusion, and growth at `t + G' + 6 * p.Δ`.
  `Proofs/Shared/Claims` projects the live claim to the safety claim.
  Root fills the appended `FGSAClaims.weakContinuationLive` field with the
  named `healing_hTimeClaim`. Its source has no search input. Full Root
  compilation still needs the P-H2 joint induction and Healing.Export.
  Assembly/WeakContinuation imports WC Export and Shared/Claims; it imports
  no Assembly module.

- FG-SA outage continuation under (V): `Proofs/Outage/ContinuationTiming`,
  `ContinuationInduction`, `ContinuationReceipt`, `ContinuationFrame`,
  `ContinuationGate`, and `ContinuationJoint` prove the continuation body.
  `Proofs/OutageContinuation/Export` exports `outageContinuation_claim_of`.
  `Proofs/Shared/Claims` uses `outageContinuation_of_body` to bridge the body
  to the amended `OutageContinuationClaim`. `Assembly/Root` uses the named
  foundation and finite Clean producers from the Round 15 handoff.
  The exact lane import exception
  in `scripts/check-layers.py` permits `OutageContinuation.Export` to import
  exactly the six `Outage/Continuation*` modules listed above. No other lane
  import allowance changes. `FGSAClaims` is unchanged; this is a companion claim.

- WC corruption growth adds `fgsa_weakContinuationGrowthClaim` in
  `Proofs/Assembly/Root`, without changing the frozen `FGSAClaims` field.
  `Assembly/WeakContinuationGrowthSeed` selects one bounded source witness.
  `WeakContinuationGrowth/Replay` transfers retained local traces through
  the inclusive endpoint, with separate source and continuation cut indices.
  `Assembly/WeakContinuationGrowth` joins the nonempty suffix branch with
  weak participation and the empty suffix branch with prefix-only replay.
  The claim keeps safety, both outputs, inclusion, and conditional growth
  under the whole-run `FinalitySlashableBound` premise.

How the pieces meet:
- FG-SA store: `FGSA.State` keeps a root-mode `GridCO.State`, an FG store, and pools.
  GridCO proofs use `slowLeasePolicy`; FG store facts come from KitFG. Duty `ACReads`
  carries the HEAD mode. Deferred protocols retain their legacy block-mode reads.
- ROOT-DIGEST-2: `NamedProposal` keeps every ancestor's body and signed lists.
  `namedProposal` sets the six-field digest; `namedContentOk` checks it. Admission
  requires the exact named parent, keeps the received named value, and also checks
  the FG-parent projection. The I9 BODY codec remains the row/geometry projection.
  HEAD targets are identifiers. Resolution uses the cumulative domain even in active views.
  Standalone legacy GridCO, LStar, and SAPC keep `nodeRoot`.
- Named run scope: directly delivered proposals and honest prefix-held named bodies,
  closed under named ancestry. Rejected deliveries are seeds. HEAD-only identifiers
  and emitted-only tips are not seeds. `RootBlockInRun` is the existential erasure
  projection. `Base₂.idealization` has the one `NamedRootCollisionFree` field.
  Its DC-shaped clause identifies full named ancestors of either scoped tip.
  `FGSARun/Proofs/NamedScope` proves named equality and geometric projections;
  `FGSARun/Proofs/Roots` supplies origins. `KitFG/RootScopeDef` keeps the explicit
  pure two-chain premise.
- Store safety: `FGStoreSafety` takes `StepOK`; `StoreStepRoots` requires
  root uniqueness on the inserted tree. `KitFG/StoreSafetyDef` defines this
  interface. `storeStepRoots_of_blockAccepted` proves it at admission.
  Option-3 exceptions r2.1–r2.2 require uniqueness on each exact walked
  tree; r2.3 adds body scope for `eraseFG B` to `CPPrefix` after honest
  membership. See [the exception record](lock-log/root-digest/README.md).
- Generic FG finality safety (2026-10-07). `AvailableChainFGCompose` states
  the safety contracts (`Statements/SafetyReads`, `SafetyStore`,
  `SafetyClient`, `SafetyClaims`) and proves the accountability fields 3-5 in
  `Proofs/SafetyStore` and `Proofs/SafetyAccountable`, the client and count
  results in `Proofs/SafetyClient` and `Proofs/SafetyCount`, finalized
  monotonicity in `Proofs/SafetyMonotone`, and field 8 (honest non-slashing)
  in `Proofs/SafetySlashing`. FG-SA supplies the laws in
  `Shared/FGSafetyClient`, `Shared/FGSafetyStore` and `Shared/FGSafetyScope`.
  `Foundations/FGSafetyBridge` states these results at the FG-SA reads:
  accountability, the pool count, client safety and row origins, finalized
  monotonicity and honest non-slashing. `Accountable`, `Client`,
  `ClientOrigin`, `FinalizedSafety` and `HonestNeverSlashed` call the bridge.
  Its public types use only FG-SA terms, with the `FinalityRunBlock` body
  expanded, because `Foundations/Accountable` imports the bridge. Its four
  Compose imports are the exact pairs `Foundations.FGSafetyBridge` →
  `AvailableChainFGCompose.Proofs.SafetyAccountable`, `.SafetyCount`,
  `.SafetyMonotone` and `.SafetySlashing` (`COMPOSE_EDGES` and
  `laneUpstream`). The five callers reach the Compose proofs only through
  the bridge.
- FG-SA on engine v2 (T7): `Node = {st, rec}`, `base = st`, `rec = Λ`
  (durable). Label families: HEAD labels AP and fresh (`CStar`); FG labels
  `Linked`; proposal labels AP and `SingleSeat`, one label per slot
  (`Interface.propLabel_injective`).
- Walks: `ghost` takes an anchor. The base has `confirmationFrom a`,
  `gateFrom a` and `clockFrom a` (713f56f); the old names are the genesis
  forms. SA uses genesis; FG-SA uses Σ.F (spec sync, 1944bb8).

`AvailableChainFGCompose` is the generic FG run-composition library (L5). The
facade imports the 13 modules below; the library glob also builds Tests.
Paths are relative to `AvailableChainFGCompose/` and omit `.lean`.

```text
┌──────────────────────────┬─────────────────────────────────────────────────────┐
│ Module                   │ Role                                                │
├──────────────────────────┼─────────────────────────────────────────────────────┤
│ Statements/EventReads    │ Shared event cuts and inclusive time reads          │
│ Statements/CoreReads     │ FG core reads, core/head laws and source service    │
│ Proofs/SourceHead        │ Core store, head, source and carrier consequences   │
│ Statements/SafetyReads   │ Wire, record, output, scope and safety reads        │
│ Statements/SafetyStore   │ Store, order and scope law records                  │
│ Statements/SafetyClient  │ Wire, client and unit-weight law records            │
│ Statements/SafetyClaims  │ Generic run accountability and agreement contracts  │
│ Proofs/SafetyStore       │ Reachability, replay, delivery origins and scope    │
│ Proofs/SafetyAccountable │ Run/store accountability and agreement; fields 3–5  │
│ Proofs/SafetyClient      │ Client trace, record fold and emitted-row safety    │
│ Proofs/SafetyCount       │ Fault attribution and slashable bound; field 6      │
│ Proofs/SafetyMonotone    │ Finalized monotonicity; field 7                     │
│ Proofs/SafetySlashing    │ Stored-row origins and honest non-slashing; field 8 │
└──────────────────────────┴─────────────────────────────────────────────────────┘
```

Tests: `Axioms` and `SafetyAxioms` are the audits; `Reads`, `Restart` and
`SafetyReads` check the read contracts; `SafetyControls` holds the positive
behavior controls (unordered inclusive reads, repeated rows, a two-seat swap,
a lost durable record, an emitted-only tip). `scripts/check-fg-compose-controls.py`
compiles the matching negative forms and requires their exact diagnostics.

The two adapters: FG-SA enters through `AvailableChainFGSAProofs/Proofs/Foundations/FGSafetyBridge`
(laws in `Shared/FGSafetyClient`, `Shared/FGSafetyStore`, `Shared/FGSafetyScope`);
PC-SA enters through `AvailableChainPCSAProofs/Proofs/Foundations/FGSafetyBridge`
(laws in `Foundations/FGSafetyClient`, `FGSafetyClientLaws`, `FGSafetyStore`,
`FGSafetyScope`; bodies in `FinalitySafety`; claims in `Finality/Export` and
`Assembly/Finality`).

Engine v2 decisions (design §2), one line each:
- E1 duties and keys: `Auth = seat ℓ i | none`; a proposal duty is a
  one-seat label; no global `n`.
- E2 seats: `seats ℓ`, `Run.seatOf ℓ`; committee models are conditions
  (`CStar`, `Linked`, `SingleSeat`).
- E3 weights: later additions (seat multiplicity plus conditions).
- E4 delivery outcomes: a delivery calls the handler; exclusions are
  explicit; deliverability (`RelayFeasible`) comes in plan 1c.
- E5 own-signature record: `selfVisible`, `recordOwn`, atomic tick;
  `Isolation` factors the AP part through `base`, so AC facts transport to
  the AP projection.
- E6 restart (superseded by the sleep port below):
  `restart v t`, `st ↦ restore (durable st)`. Ruling Y keeps
  the last local tick value and the anti-slashing record. Restore resets
  the other store fields, adds no tick or duty, and ignores restart time `t`.
  The six restart-permitting claims remain proved: ClientSafetyClaim,
  WholeRunAccountableClaim, WholeRunAgreementClaim, EventPrefixAgreementClaim,
  FaultCountSlashableBoundClaim, and HonestNeverSlashedClaim.

- E6 restart (sleep v6): `restart v t`, `st ↦ restore (durable st) t`.
  Restore keeps the FG state, blocks, named bodies, proposals, rows, obligations,
  stable output, and anti-slashing record. It clears volatile vote state and
  sets both the clock and restart marker to the exact wake time `t`. A wake
  restarts before any tick or delivery at that time. Duties and confirmation
  updates require the uniform previous-slot join cutoff. This supersedes the
  earlier ruling Y account. See `docs/SLEEP-LEDGER.md` for proof status.
- P-Fi sleep consumers: `Finality/RecoveryScope` derives local restart intervals,
  join bounds, and confirmed readers from continuous Recovery awake time.
  `RestoreReads` preserves finality and held rows through restore. `TickRead`
  relates exact joined tick reads to time cuts. RowsBatch and TailBatch use
  joined voters and exact receiver services. Export has explicit vote, action,
  and Tail receipt suppliers. These suppliers remain proof obligations; a
  conditional export does not establish the unconditional public service claim.


FG-SA sleep restart, P-Cl1 Round 2 (2026-10-10): restore uses the exact wake
time and keeps the FG store, block tree, proposals, obligations and stable
record. Saved genuine rows, fast-write rows, HEAD votes and stamps belong to
the current receiver epoch. A wake can erase those rows. Clean proofs do not
obtain `NoRestart` from `Base₂`.

`Clean/GateEpoch` proves the executed gate guard, the backward awake interval
and the joined witness. `Clean/StateEpoch` proves kept-state restart facts,
current-epoch state facts and the earlier joined gate used by T10.
`Clean/Service` supplies HEAD history, readiness and stamp retention in the
receiver's own epoch. `Clean/EpochSaved` constructs the current saved row
needed by arming. The Count callers use one explicit receiver anchor for all
service and path obligations. The P-Cl1 core is CLOSED; P-Cl2 owns the public
wrappers and the Safety transport handoff. See [SLEEP-LEDGER.md](SLEEP-LEDGER.md)
and [P-Cl1.handoff.md](../scripts/dev-pkg/P-Cl1.handoff.md).

## 4. Constraints

- Proofs: no `sorry`, `admit`, `native_decide` or new axioms;
  `decide +kernel` is allowed. Every gate runs an axiom check.
- Toolchain v4.34.1, Mathlib d13f23b7; never `lake update`; never a new `lean_exe`
  (scripts run with `lake env lean --run`). The Mac has 3 Lean slots
  (check `pgrep -fl lean` first); FCR builds run on the NUC.
- Landing check-fg skip (lead ruling 2026-10-03): `scripts/check-fg.sh` runs
  on the Mac only (its pin check hashes archived research files). A merge-tier
  landing may skip it when `python3 scripts/fg-closure.py --changed <main>
  <head>` exits 0: the diff touches no file of the FG closure at either
  revision. The closure is: every file that the lakefile globs of the targets
  check-fg builds match (AvailableChainKitFG.* includes its Tests), their
  in-repo import closure and that of the Lean scripts check-fg runs;
  check-fg.sh, its helpers and the files they name; lakefile, toolchain,
  manifest. The closure is recomputed at each landing, any script error means
  "run check-fg", and each skip logs its line. `--selftest` runs the negative
  controls. FULL-tier gates and the daily full main run always run check-fg.
- Lock: `scripts/CatalogLock.lean` hashes the dependency closure of every
  declaration in the locked modules (framework, statements, catalog; not
  the protocol libraries). A change needs an expected-name list,
  `--write`, a clean `--check`, and a lock-log entry in
  design §8. Any catalog difference requires a snapshot update and review.
- Current API snapshots: `docs/{V2,GEN,FGSA,PCSA}-API.md` record each public
  declaration, module, kind, and hash. `scripts/V2Manifest.lean --scope <scope>
  --write` updates one manifest; `--check` requires complete current coverage.
  V2 engine entries retain anchor coverage. Update existing anchors when needed;
  a new engine declaration does not require a milestone-specific anchor.
  `docs/api/fgsa-deep.json` and `docs/api/pcsa-deep.json` record full kernel
  dependencies. `scripts/api-diff.py` reports the union of changed public roots
  with old/new statements, changed nodes, and paths. Review the complete diff.
- T7 import guard: the FG-SA run library imports no v1 Kit, v1
  Statements, v1 engine or `GridCO.Proofs.*` directly, and a used-constant
  check backs the rule (the import closure cannot be v1-free). FG-SA
  reaches Grid CO walk and score lemmas through wrappers in
  `AvailableChainFGSA.Proofs.*` (option b2; `fgHead_stored` is the
  precedent). Wrapper statements use only model-level constants. The move
  of the pure lemmas to `GridCO/Walk/` (about 70 declarations) is deferred.
- DC Lean is a reference, not a dependency (`using!`, R ≥ 3).
- Process: a plan per phase with an audit; a task review for each task and
  a final branch review; Claude + Astra before big decisions, a full audit
  before major ones; decisions taken without the user are logged. Codex
  always with `-c service_tier="fast"`. Commits by explicit path;
  worktrees under `~/worktrees/`.

- FG finality safety (P13). `AvailableChainFGCompose` is the generic run-composition
  library. Its Statements and Proofs have separate import permissions.
  Compose imports no protocol model, run, Claims, Framework or Registry library.
  Protocol adapters import Compose only through exact `COMPOSE_EDGES`.
  FG-SA safety proofs enter through `Foundations/FGSafetyBridge`, with four
  exact targets: `SafetyAccountable`, `SafetyCount`, `SafetyMonotone` and
  `SafetySlashing`. PC-SA uses the same four targets from its own
  `Foundations/FGSafetyBridge`. PC law producers cover both `.on` and `.idle`.
  Pure fields 1–2 use KitFG directly; Compose supplies run fields 3–8.
  Monotonicity requires sorted execution and `NoRestart`. Client safety and
  honest non-slashing retain durable Λ and do not gain those premises.
  All-run carriage and stored-row carriage are distinct contracts.
  `scripts/check-fg-finality-coverage.py` checks that every public declaration
  of the safety modules is audited. The retired S0 freeze is historical. The gate
  step `FGSAGrowth-axioms` audits the growth companion
  (`Tests/WeakContinuationGrowthAssemblyAxioms`).
- Blueprint coverage (D10). `scripts/check-fgsa-blueprint.py` checks the
  current blueprint snapshot (`docs/blueprint/fgsa/`) against the reviewed map
  `docs/FGSA-BLUEPRINT-LEAN.json`, with `scripts/CheckBlueprintClaims.lean`
  for the compiled theorems (a FULL-tier gate step). A pass means every
  blueprint item is accounted for; OPEN items remain open. Historical pins
  keep their original scope.
- Generic API: `docs/GEN-API.md` records Statements types and values;
  `lake env lean --run scripts/V2Manifest.lean --scope gen --check` checks it.
  A Statements edit updates the current manifest; its diff is reviewed.
- Before a branch-to-branch merge without a gate, run `bash scripts/check-gly-rules.sh`
  and `SKIP_CONE=0 bash scripts/check-build.sh` on the merge result after a full build.
- `bash scripts/check-build.sh` runs all checks below after a full build.
  `docs/LEAN-ARCHITECTURE.md` gives the module and import rules.

```text
┌───────┬─────────────────────────┬──────────────────────────────────────────┐
│ Check │ Script (scripts/)       │ Rule                                     │
├───────┼─────────────────────────┼──────────────────────────────────────────┤
│ (a)   │ check-module-headers.py │ module headers and public imports        │
│ (b)   │ check-expose.py         │ Proofs expose only allowed definitions   │
│ (c)   │ rebuild-cone-test.sh    │ A proof-only edit rebuilds one module    │
│ (d)   │ CheckProofEqns.lean     │ Proofs export no new equation lemmas     │
│ (e)   │ check-layers.py         │ Module imports follow the layer rules    │
│ (f)   │ shake-report.sh         │ Unused imports; report only, no --fix    │
│ (g)   │ chain-depth.py          │ Longest import chain; report only        │
│ (h)   │ check-transparency.py   │ Transparency option position and reasons │
│ (i)   │ check-gly-rules.sh      │ GLY rules and per-rule baselines         │
└───────┴─────────────────────────┴──────────────────────────────────────────┘
```

## 5. Milestones

### P0 shared FG extraction

P0 uses the approved 2026-10-11 plan. Its snapshot rule applies to this extraction.
Start with P0z0 baseline records. Then complete P0a restart/read/count laws and P0b1
window definitions/transport. P0b2H precedes P0b2C; P0b3 follows P0b2. P0c1 fixes
observations after P0a/P0b1; P0c2 fixes reset/service laws, and P0c4 fixes historical
reads. P0c3 follows P0c4 and adds the dependency contract. Healing consumers follow
P0d1/P0d2 and P0d6a, then P0d3, P0d4, P0d5a–P0d5d, and P0d6b. Finality starts
at P0d7a1 after P0b3 and P0d6a, then follows P0d7a2–P0d7a5 and P0d7b.
P0d7b also waits for P0d6b reset assembly.
P0zI supplies exact central entries at each landing; P0zF checks combined closure.

Keep every old FG-SA public name, owner, kind, complete type, binder name,
visibility, definition body, structure constructor, equation, and definition
closure. Add shared definitions and proofs; change only old theorem proof bodies
to use generic results through private fieldwise conversions and correspondence
proofs. Generic snapshots and inventories permit additions only. A changed old
snapshot entry is a STOP. Keep the frozen FG-SA window representation and prove
its correspondence with the shared representation. SimplexFG holds executable
window definitions; KitFG holds pure views, contracts, correspondence, and proofs;
FGCompose holds protocol-parametric statements and shared run consumers. Generic
modules must not import protocol models, runs, Claims, or lane Export modules.

Keep the reset time separate from the service start. Historical high sources
must remain in scope; gate label qR and action HEAD label qR+1 remain separate.
Historical accepted-body reads use the cumulative store. P0c3 closes the dependency
contract, its pure consequences, controls, and real FG-SA accepted-tree/leaf
projection. P1-Driver supplies the full queue/refusal driver and timed completion
proofs. PC-SA remains UNPORTED until its later suppliers and implementation close.

P0c3a (A7) adds one explicit, read-free reconstruction step after raw restart entry.
The step keeps body, refusal, pending, notification, and original-receipt observations.
The drain closes before body replay. P1 supplies the trace and step laws; P2d supplies
saved M and the missed freezes, including the `lastCompleted` equal-cut rule.

P0c3b (A11) adds one read-free `rebuild` step per local restart, also with no replays.
It runs after the post-drain replays and before the final drain, at the wake time, and
keeps the same five observations as reconstruction. P1 c1 appends it to `runEvent`;
PC2RestartBinding binds it to the cumulative scan and normalization.

```text
┌────┬──────────────────────────────────────┬──────────────────────────┐
│ M  │ Content                              │ Status 2026-09-30        │
├────┼──────────────────────────────────────┼──────────────────────────┤
│ 1  │ I9 derived roots + engine v2 core    │ done: I9 3403e58; 2a     │
│    │ (2a)                                 │ 1aa6885                  │
│ 1+ │ Post-I9: walk anchor                 │ anchor 713f56f and spec  │
│    │ (`confirmationFrom`/`gateFrom`);     │ sync 1944bb8 done; Pins  │
│    │ FG-SA spec sync (walk from F, Pins)  │ re-pin next (fgsa-lean)  │
│ 2  │ T7/T1: FG-SA run instance on v2,     │ T7.0 base ready;         │
│    │ FGSAClaims, registry map             │ T7.2 landed (30a843f)    │
│ A0 │ Step 2: Generic statements and kits  │ I01–I23, I25 landed;     │
│    │ plus the build checks and manifest  │ I24 close gate in review │
│ 3  │ 1c for FG-SA: run construction and   │ to plan; order (before   │
│    │ inhabitation for every horizon       │ 2b/2c) waits for user    │
│ 4  │ F0 statement layer → F1 foundations  │ scoped; F0–F2 draft      │
│    │ → safety lane (Clean, P1/inclusion)  │ running                  │
│    │ ∥ liveness lane (finality kernel,    │                          │
│    │ healing) → F6 GST bounds             │                          │
│ -  │ Deferred: 2b lift, 2c (restart       │ deferred                 │
│    │ extension, I1 floor), Grid CO items, │                          │
│    │ anchor + pruning optional claim      │                          │
└────┴──────────────────────────────────────┴──────────────────────────┘
```

P13 is the final FG finality-safety integration package. It does not close
the broader blueprint OPEN items (`docs/FGSA-BLUEPRINT-OPEN.md`).

Window migration (stages, `tip-stability/codex/reports/window-migration.md`
§1): 0 close the current no-round migration (06/07, Δ_F delivery) → 1 add
the window core (additive; SimplexFG unchanged; height bridge) → 2 prove
the interfaces (height transfers, provenance, window store invariants) →
3 switch FG-SA to the window fold once → 4 finish 07-F and re-freeze →
5 prove liveness on the window API.

Stage 3 is split (lead rulings, `tip-stability/codex/reports/fg5-rulings.md`
with its addendum): readers and invariants are ported green BEFORE the switch,
and only the instance swap is atomic.

```text
┌────┬────────────────┬──────────────────────────────────────────────────────┐
│ Job│ Owner          │ Scope                                                │
├────┼────────────────┼──────────────────────────────────────────────────────┤
│ J0 │ both           │ land w3 (FG4 + FG2), LF5 fixes + LF6 + LF7, achfix   │
│ J1 │ lean-framework │ LF8: frame geometry over FGStoreInvariant,           │
│    │                │ FGJustificationLaws, generic finality-cap row        │
│ J2 │ fgsa-lean      │ FG5a: Params.K_W (2 ≤ K_W); Model/WindowViews; view- │
│    │                │ form readers, bridge-equal; no meaning change        │
│ J3 │ fgsa-lean      │ FG5b: store invariants → FGStoreInvariant (views     │
│    │                │ still simplex); WindowStoreInv removed               │
│ J4 │ fgsa-lean      │ FG5c, ATOMIC: views and updaters → window fold, R6W  │
│    │                │ admission, window head fields; instance proofs.      │
│    │                │ DONE 2308c42 (J0–J3 and J5 also done)                │
│ J5 │ lead           │ review of J4 (two models)                            │
│ J6 │ fgsa-lean      │ FG5d: height-only Claims readers → H (cosmetic)      │
│ J7 │ fgsa-lean      │ IF.3(b) producer on the window (SO-COV)              │
└────┴────────────────┴──────────────────────────────────────────────────────┘
```

## 6. Decisions that shape the architecture

- ROOT-DIGEST-2: the run premise identifies full recursive named proposals.
  FG-SA checks the digest and exact named parent and uses root-mode HEAD handling.
  The I9 BODY codec supplies row and geometry projections. Legacy GridCO, LStar,
  and SAPC keep `nodeRoot`. The option-3 exception retains the closed claim fields.
- Restart: interim form keeps Λ and resets the store; the faithful form
  (Λ + anchor at F) comes with the optional anchor feature.
- SA walk starts at F (user, 2026-09-29).
- Pruning: an optional claim "prunable at F", not an obligation; no root
  set needed.
- Leak claims: parked; not in the first verification target.

## 7. Open architectural questions

- Interface gap: CLOSED in the blueprint (r212/r212b, 2026-09-29):
  `HEALING_INPUT` split with H5/H6, exact map to the spec's H0–H4, kernel
  dependency list, scoreSuffix for X ⪰ D. Open: align the spec's
  `HEALING_INPUT` names (next spec revision, with the OD6 pre-GST
  sentence).
- Registry: new ids fj.descent.v2, fj.twoChanges.core.v2,
  ap.headReachesLo.v6 (blueprint 21); the three old ids are WITHDRAWN for
  current use (policy §0; v5 still true in its scope); fj.frame.v4 comes
  with r213. The re-pin commit (fgsa-lean) follows r213.
- Representation option (needs a proof first): filter AC records by the
  current F at read time, as DC does, instead of the reconcile write.
- The post-gate cut: F0–F2 draft uses a new reader `afterTicks` (no v2
  change).
- One-repair healing is open. Healing bounds (k ≤ 2R+1, G = 8Δ): B_H
  stays 295Δ/343Δ as the general target (the F6 Lean target). Separate
  bounds: HG.7 upper 268Δ/312Δ; HG.8a upper 204Δ/240Δ (lemma L4-R, no
  cut change, no spec change; in review, then r213). Lower bound
  89Δ−1 tick / 105Δ−1 tick for Δ ≥ 2 (reviewed VALID). The cut change B
  (196Δ/228Δ) is a documented option only.

## 8. Where the detail is

- Research (tip-stability): `state.md`, `log.md`, `spec/`, `blueprint/`,
  `codex/`.
- Lean: `docs/FRAMEWORK-DESIGN.md` (framework), `docs/FG-COMPOSITION.md`
  (FG composition), `docs/MAP.md` (contract to Lean), `docs/audit/`.
- FG finality safety: `docs/FG-FINALITY-SAFETY-S0.md` (freeze),
  `docs/FG-FINALITY-SAFETY-S0-inherited.json` (inherited S0 differences with
  commit provenance), `docs/FGSA-BLUEPRINT-LEAN.json` (blueprint → Lean map),
  `docs/FGSA-BLUEPRINT-OPEN.md` (OPEN items), `docs/blueprint/fgsa/SOURCE.json`
  (blueprint snapshot provenance).
- Lean module rules: `docs/LEAN-ARCHITECTURE.md`; Generic Statements API:
  `docs/GEN-API.md` (checked by `V2Manifest --scope gen --check`).
- Plans (`docs/plans/`): framework-phase0, phase1a-gate-catalog,
  phase1b-instances, fg-module, fgsa-model-store (all closed);
  i9-derived-roots (merged 3403e58); phase2a-engine-v2-core (merged
  1aa6885; `docs/PHASE2A-REPORT.md`);
  fgsa-composition-t7-t1 (r11 adopted, 2ec3003; in
  `~/worktrees/available-chain-fgsa-plan`).

- PC-SA long-break transport (2026-10-08). `Recovery/LockTransport` holds
  lane-neutral receipt and pool facts from label `g`. `Assembly/Recovery`
  proves all seven suppliers from lane exports. PC key receipt uses only early
  and vote cutoffs. The run wrapper has no OPEN transport premise.

- PC-SA lock overlap (2026-10-08). `Recovery/LockOverlap` proves mix-time
  expiry, overlap compatibility, and PC relay compatibility at the write
  and within a surviving interval. `Recovery/LockView` proves the voter-view
  rank bound.

- PC-SA recovery rank dissemination (2026-10-08). `Recovery/LockStamp` derives
  a held key before the early cutoff from the actual PC stamp history, then
  relays its rank before the freeze. `Recovery/LockView` retains that rank
  in later voter candidates and proves K for pending writes and surviving
  rows, including PCs carried by proposals. Existing lock signatures stay fixed.

- PC-SA surviving-lock coverage (2026-10-08). `Recovery/LockDomain` proves
  the cumulative resolution domain. `LockCounts` transfers a saved gate
  result to the actual next voter pool. `LockBatch` gives later honest
  batch counts. `LockFollow` proves F′ from the last write and exact-row
  survival, then derives preceding HEAD coverage from a live read.

- PC-SA long proposal paths (2026-10-08). `Recovery/ProposalPaths` transfers
  the actual preceding honest HEAD batch into the proposer pools. It proves
  the walk from the selected base reaches the live root and the voter F4
  lease clause. Both use the survival proof in `LockFollow`.

- PC-SA long first-slot assembly (2026-10-08). `Recovery/LongFirstSlot`
  constructs `FormationPrem` and the explicit proposer-root walk conjunct.
  `Recovery/Export` proves the predicate conversion with the defining equation.
  `pcsa_recovery_firstSlot_long_of_run` selects a bounded slot from the long
  claim premises. The Formation literal also uses the existing root proof.

- PC-SA restart stamps (2026-10-08). `Clean/RestartStamp` derives equal
  honest HEADs from the restarted state at the predecessor gate. It applies
  `Clean/StampFrom` to stamp each later honest proposal by its freeze.
  The proof needs the freeze inside the window, not the current gate.
  `Clean/Export` and the PC-SA proof facade export the module.

- PC-SA short recovery (2026-10-08). `Assembly/Recovery` proves
  `pcsa_fastRecoveredClaim (p) : FastRecoveredClaim p` without an extra
  premise. `pcsa_recovery_suffixInputs_short` connects Formation, C8 and the
  restarted outputs. `Recovery/Export` keeps the conditional interface as
  `pcsa_fastRecoveredClaim_of_inputs` with its original type.

- PC-SA long recovery (2026-10-08). `Assembly/Recovery` proves
  `pcsa_longBreakRecoveredClaim (p) : LongBreakRecoveredClaim p` without an
  extra premise. `pcsa_recovery_suffixInputs_long` uses the existing specified
  first-slot proof. The final claim retains `hafter` from `long_recovery_slot`
  for the horizon window. The long first-slot proof is unchanged.
  `Recovery/Export` keeps `pcsa_longBreakRecoveredClaim_of_inputs` with its
  original type. Both recovery claims now have complete suffix suppliers.

## FG-SA port (historical records)

The [plan](plans/fgsa-port-r2.md), [source census](FGSA-PORT-CENSUS.md),
[ownership register](FGSA-PORT-OWNERS.json), and
[PC-SA baseline](FGSA-PORT-PCSA-BASELINE.json) record the port at its original basis.
Future changes use current snapshots and a base-to-target review report. Do not
maintain the fixed port totals, path owners, or change ledger as acceptance data.
Open proof obligations in the reports remain open until their proofs are complete.

## FG-SA port WP16 first-pass handoff

The h+i+j switch uses the accepted tree above F for canonical reads.
Ruling V requires FrameNext inputs. Legacy frame declarations remain comparison objects.
The [change record](FGSA-PORT-CHANGES.json) gives exact data and source attribution.
The [first-pass report](FGSA-PORT-FINAL-REPORT.md) lists checks and pending packages.
WP08, WP10, WP12b, and WP15 are still open on this base. No final gate pass is recorded.

## FG-SA port WP16 second pass

The merged WP08 and WP10 frame inputs use FrameNext. WP13v2 repairs the tests.
The complete Formation/Run build passes on source base `e961df94` (3,856 jobs).
The change record gives complete source statements, change commits, and review snapshots.
Ruling Z permits the proved partial Spec construction to land. The full independent
source interpreter, matched-cut equivalence, and claim transfer remain open.
Ruling Y and the WP12d Spec move are pending on this source base.

P-H2 sleep helper boundary: OpeningGateRead supplies enabled/joined fast-write facts and gate geometry. OpeningTicks supplies awake vote/action ticks. RecoveryScope and ResetScope supply durable content, local action/read epochs and exact recovery cutoffs. ReleaseScope supplies expiry membership. OpeningGateSupport uses joined release counts and GateReceiptScope; its reset adapter keeps per-object services explicit. RecoveryService builds proposal and target service from accepted objects, their original anchors and receiver epochs. These helpers do not replace retained HEAD replay history or original proposal emission. HealingOpeningSupport keeps its six audits in its own module, with no test-to-test import. The serial production audit fragment imports only production modules.

P-H2 Round 4–5 opening, reset and search boundary (sleep-ph2d):
FrontierSeedDefs holds the service-independent FrontierSeedQualification and its
prior-slot cutoff proof. FrontierSearchDefs imports this definition module, so
its search definitions do not import the open FrontierSeed service proof.
Reset and the internal reset/search horizon, deadline and budget use recoveryStart.
The public ResetArrivalConcl already uses this cut. Its legacy Assembly adapter
and the post-reset step producers remain open.

RecoveryScope defines WitnessReceiptScope and WitnessHeldScope at actual joined
reads, with strict-deadline receiver floors. HeadWitnessReceiptScope selects one
K/W pair with its full-tree, HEAD, ancestry and source-floor facts.
PhaseWitnessReceiptScope selects only the frontier/top/contest witnesses.
RecoveryService builds proposal and target service from original accepted objects
and their exact anchors and receiver epochs. Selected service producers remain open.

OpeningServiceScopes bounds permanence by its actual post-GST phase. Its transfer
factory takes that phase, the selected fast write, source bounds and LabelSyncOn.
OpeningServiceGate passes the hSync it already constructs. RepairServiceScopes
uses the earlier slotStart(s-2) cut for repaired proposal service. Its consumers
project the committed H1 RepairHeadServices with the actual ip/x/N and emission.
Opening gate-cover calls use H1's SupportGateScope and its joined batch.
FrontierServiceScopes bounds reads by the seed's GST cut, interval and horizon.
FrontierServiceGate converts those assumed read services to enabled gate and
joined release scopes. This conversion does not construct object services.

FrontierService constructs RetainedExactHeadRunGeometryOn at joined receivers
and uses RegimesService _on APIs. Original proposal ReceiverService and fresh
HEAD transport keep their send time, handler window, history and receiver epoch.
CommonEntry obtains SameLabelServiceScope from its selected fast-write source.
FrontierSearchFull uses RMonoAll and durable membership. Its service factories,
the indexed H1 permanence/carrier/reset/settlement requests, the bounded
confirmed-reader supplier at suffix prefixes, and the mixed Assembly tests remain open.
The complete H2 critical path is not closed.

HealingH2RecoveryAxioms and HealingH2ResetRiseAxioms import production modules only.
Their active command inventories have 38 and 24 entries. HealingH2ServiceAxioms
remains open with 130 commands. The six opening mechanism audits stay in their
own test module. The canonical H2 fragment has 205 commands and production-only
imports; serial audit integration remains a separate obligation. FrontierOpen
exports only named declarations; generated proof matchers remain private.
No public Claims statement changed.

P-H1 Round 6 healing service boundary (sleep-ph1g):
SupportRecovery defines HealingWindow and StrongHealingWindow with integer cutoffs.
A transport bound at vote(s) does not supply a joined batch. Window 1 supplies
that batch; Window 2 supplies a repaired proposal's preceding batch. SupportTicks
proves the seat/node cardinality bridge through the HEAD-seat CStar bijection.
DescentLoss derives Window 1 at a high source from oldRowHeights and recoveryStart.
HealingCarriersAt fixes the receiver at an actual honest joined tick, with a
post-GST anchor and a finite deadline. It serves the selected admissible K/W,
not every durable TF member. Event/output reads retain service from an earlier
actual joined tick. ProposalSupportScope records the actual proposal or gate time.
SupportPermanenceServices is indexed by one actual phase. healing_tPerm_at returns
Transfers for a source with Window 1. Its link to public TPerm remains open.
RepairHeadServices is indexed by the actual ip/x/N. Its retained service takes the
receiver floor; its target receipt follows from that same proposal service.
Repair gates take enabledness and GateReceiptGeometry. Suppressed gates create
no receipt demand. Frontier slow factories take the saved-window sync bound.
The local repair lease covers and all ten aggregate producers remain OPEN/P-H1.
See scripts/dev-pkg/P-H1.round6-producers.md and P-H1.round6-handoff.md.

P-H2 Round 6 uses recoveryStart for phase and attempt entry. The per-phase
SupportPermanenceServices API serves both body arms. No local fast dispatcher or
early one-lease cleanup is used. Saved-window transport retains GST. Settlement
selects its witnesses, proves the receiver floor, and uses an actual bounded
joined tick. The phase factory and remaining frontier/post-reset producers stay
open; see scripts/dev-pkg/P-H2.round6-handoff.md.

JOINED START (lead ruling, P-H1 Rounds 7-8): every healing intermediate statement
(TDel, TPerm, ProposalGap, TRepair, TCommon, TFrontier, ResetArrival*, AttemptValid,
RPhase, RenewedPromotionConcl) starts at Jst = recoveryStart p E, not at GST.
Jst - GST lies in [6Δ, 10Δ-1] and depends only on GST mod 4Δ. Saved-window
transport premises stay at GST. RowPermissionAt/Claim stay at GST (proved without
a healing contract). Top-level Claims/Healing* deadlines and constants are unchanged.
From Jst every honest reader and every source-label voter is joined, so there is
one joined-phase permanence API; no early fast-only supplier and no early one-lease
cleanup exist. Fast first transfer: relay rule plus the reader joined at release(s).
Slow arm: lease expiry plus same-label uniqueness. A pre-GST lease that is still live
at release(sStar) (k > 2R+3) is released by a later full post-Jst batch.
Plan: tip-stability codex/jobs/joined-start-plan.md; ruling in sleep-join-port-notes.md.

- FG-SA sleep continuation, P-Ou Round 10: `Outage/ScopedPrefix` selects
  regressions only at actual joined emitted HEADs. Its no-regression branch
  constructs the restored seed from the arming certificate, then produces
  bounded results and the event state. Its first-event selection also produces
  the causal prefix at the actual first regression read.
  It also proves frozen-path membership at an actual joined read, using durable
  trees and the local stamp epoch. The first-regression retained score and
  uncontested path producers remain P-Ou obligations.
  `Outage/ScopedContinuation` starts the marker suffix after gate `max(m,r+k)`.
  An early marker does not provide the intervening finite prefix.
  Its later HEAD producer uses actual joined readers and prior event history.
  `Outage/ScopedCatchUp` produces the W reader's actual gate, batch and epoch;
  it proves the finalized output branch. The other W output branch and the
  complete public exporters remain open. Public claims are unchanged.

P-Ou Round 11: ScopedScores, ScopedRoots and ScopedPaths construct the first
actual regression marker from the regime, arming certificate and causal prefix.
Selected path service uses the current receiver floor, actual joined read and
post-GST prior label. The crossing source uses P-Fd sourceDiscipline_qcOrigin.
The finite bridge after that marker and the complete public exporters remain open.

P-Ou ScopedBridge now constructs the finite bridge and global restored scoped
HEADs. Same-label readers use their own frame, and subsequent labels use the
first marker. Both event branches reach inclusive covered public reads after the
seed. Earlier read assembly, W stable catch-up and legacy public ports remain open.

P-Ou Rounds 12-13 (sleep-pou12/13): ScopedEarly proves the early reads, HEADs, F and
duties at finite cuts; ScopedClose gives the protected Outage result under Close's own
OutagePrem (no NoRestart, no duties_and_outputs). The finite Clean history/output
suppliers stay at the lane boundary. ScopedArming selects fast, slow and empty-G
certificates; ScopedJoint joins the early reads, the covered suffix and the actual W
gate. Assembly/OutagePublicInputs builds every finite Clean field from a named
producer; its audit module prints their axioms. Dependency order: protected Outage
is proved from named suppliers; W suffix preservation and lease compatibility at the
actual post-handover W gate are proved.

P-Ou Round 15 adopts OUTAGE-CONT-REPAIRED. The old OutageWSeed is false: a
common-ancestor result can retain a conflicting S (node 7 at 106 in wseed-run).
Statements/OutageContinuation adds OutageRepairReady only to continuation output
reads. Covered readers use inclusion; a reader with B below F uses finality; any
other qualified reader supplies an actual post-handover gate with an already
compatible S or a genuine result that is not below old S. ScopedCatchUp proves
outage_repair_gate_seed at that supplied gate and applies outage_stable_compatible_suffix
through the inclusive read, including restarts and same-time deliveries.
ScopedJoint and OutageContinuation/Export have no W-seed callback. The complete
outage_continuation_public_suppliers theorem uses named foundation and finite Clean
producers. HEAD and F safety, Join readers, protocol declarations and FGSAClaims
fields are unchanged. This is an INTENTIONAL FG-SA sleep adaptation: conditional
safety after a repairing gate, not SAME as DC stableAsynchronyResilient. No fixed
repair deadline is asserted. P-As owns the Root call and global audit integration;
the exact replacement is scripts/dev-pkg/P-Ou.round15-handoff.md.

P-H1 joined-start boundary, Rounds 7-9:
Healing intermediate contracts start at recoveryStart p E. It is the single
protocol-parameter start Jst; saved-window transport still starts at GST.
RowPermissionAt and RowPermissionClaim keep their proved GST form. Top-level
Healing deadlines and constants are unchanged. Permanence services are indexed
by one actual bounded phase. The universal TPerm wrapper consumes that phase
factory; P5 production closure remains open. No early fast-only permanence or
early one-lease cleanup producer is used in the joined-start route.

ReceiptProducers constructs selected original proposal and HEAD services from
RecoverySleep₂, with public anchors, finite deadlines and local receiver epochs.
RecoveryProducers supplies selected carriers, geometry-guarded gates, complete
RepairHeadServices.scopes and selected prior-source receipts. Ordinary and reset
delivery have recovery adapters that construct their services. P1/P2 HEAD relay
factories remain open, including their carried cap cases.
No conditional assembly or fixture is a producer for those fields.
The positive execution fixture now preserves its old event prefix and extends
to horizon 310, beyond the complete joined-start H-time budget of 309.

P-Ou Rounds 12-13 (sleep-pou12/13): ScopedEarly proves the early reads, HEADs, F and
duties at finite cuts; ScopedClose gives the protected Outage result under Close's own
OutagePrem (no NoRestart, no duties_and_outputs). The finite Clean history/output
suppliers stay at the lane boundary. ScopedArming selects fast, slow and empty-G
certificates; ScopedJoint joins the early reads, the covered suffix and the actual W
gate. Assembly/OutagePublicInputs builds every finite Clean field from a named
producer; its audit module prints their axioms. Dependency order: protected Outage
is proved from named suppliers; W suffix preservation and lease compatibility at the
actual post-handover W gate are proved; the continuation exporter still needs
OutageWSeed (Outage/ScopedCatchUp, O11-W-SEED); P-As assembly and the global audit
integration remain pending.

P-H2 Round 7: RepairCover gives each lease split the services of its selected
joined-start phase. FrontierGateScope bounds carriers by the capped endpoint v.
FrontierService selects the proposal parent at its source and bounds the current
receiver certificate before it calls indexed RepairHeadServices.target and .scopes.
RecoveryService consumes ReceiptProducers for the selected HEAD carrier and constructs
service for the actual self proposal. PhaseService constructs selected witness receipts
from their original acceptance at a recovery anchor, including a non-public anchor.
Its strict event spread and frozen HEAD proof permit restarts. healing_rPhase_recovery
produces all five RPhase clauses from RecoverySleep₂, RMonoAll and RXing. The attempt
and search consumers use the named phase receipt producer. Budget constants and
GST saved-window transport bounds stay unchanged. H1 phase/relay factories and H2
all-cut post-reset source closure remain separate obligations until their checks pass.

P-H2 Round 7 post-reset boundary: the outer T-contract uses the ordinary/reset
recovery delivery adapters and passes the exact opening, repair and frontier
factories. The R-contract uses the sleep-safe phase producer and the durable
provenance leaves. The raw gate guard now requires its actual synchronous enabled
gate. H6 consumes the geometry-guarded local gate factory. The H2-prime first
reader uses the original accepted body and the receiver's freeze-to-read epoch.
Equal-label high sources use the restart-aware same-label service producer.
The selected HEAD receipt producer also exists; OpeningServiceScopes no longer
requests an unused carrier field. All-cut opening, cone, raw-transfer and lease
assemblies are still OPEN/P-H2. Their legacy consumers are not sleep producers.

P-H1 Round 10 HEAD boundary:
Shared/Relay adds HeadRelayLocalServiceScope, HeadRelayReceiptScope and four
receipt consumers. The local service keeps the original index, epoch and window.
Under non-exclusion at the strict deadline, its service field permits either
local processing or an exact remote ReceiverService. The receipt adapter uses
fgsa_head_stamp_before_read and keeps votes and stamps through the same epoch.
The receipt evidence is a stored HEAD or two stamped cap witnesses at the read.
The older object-only scope remains a compatibility interface for other lanes;
healing P1/P2 no longer request it for every raw object.
Healing/HeadRelay proves local carried provenance through the actual restart
model, with the joined reader's label cutoff. A carried third HEAD can be refused
without an acceptance or a relay for that object. Healing/RelayProducers relays
its two stored witnesses instead. P1 and P2 use the narrower receipt scope;
RecoveryProducers supplies their complete recovery factories. Honest late HEAD
reads no longer need an artificial object delivery window before their own read.
Tests/HealingHeadCap replays the actual local handlers: a proposal carries a
third HEAD after the first two votes capped the seat. The proposal and raw HEAD
remain present, but the third HEAD is absent from the vote pool and clean support.
This local handler check is not a complete ExecutionValid adversarial fixture.

P-H1 Round 10 phase production:
RecoveryProducers now supplies P1-P10 from RecoverySleep₂ and named Foundations,
with each actual source, reader, finite deadline and receiver floor guard kept.
P5 is healing_support_permanence_recovery; both PhaseBody arms use produced
services. SlowSupportScope.late keeps the full joined batch. Its saved window
uses GST synchrony, lease expiry and same-label uniqueness. Fast transfer uses
the actual joined release reader and its clean threshold support.
Healing/RecoveryPerm proves healing_tPerm_recovery for every bounded phase after
Jst, with no phase-service callback. P-As supplies fgsa_rMonoAll, fgsa_rXing and
fgsa_leaseOrigins_lastWrite across the existing Foundation boundary. No new
public Claims premise, deadline, constant, or early-case producer is added.
Healing/RepairLeaseRecovery supplies repair_lease_cover_two_at and
repair_lease_cover_one_at with P-H2's exact phase-service signatures. Round 11
uses the matching P5 record through healing_tPerm_at. A private last-write split
proves expiry for old rows and phase-local Transfers for later rows. Neither
adapter needs a whole-run TPerm step. P-H2 owns its caller imports.
The N4 adapter healing_ready_batch_release_compat_recovery constructs its first
and gate scopes. A later full batch releases incompatible leases of every age;
there is no bound on k and no claim that Jst expires every earlier lease.
Tests/HealingRecoveryPermAxioms audits the new producers. The actual finite
NonVacuity/HealingRun fixture has nvPerm from the universal producer and named
Foundations. The four complete adversarial replays still have exact P-H1
obligations; local handlers and clock regressions are not execution certificates.

P-H1 Round 11 regression boundary:
Tests/HealingStaleLeaseReplay checks actual process/clock/acRestart folds for k=3
and k=4. It checks the retained old lease and failed HEAD, parent and S reads.
Tests/HealingSlowLeaseReplay admits parent-first height certificates through
handlers, then checks the saved B result, incompatible joined HEAD and slow write.
Tests/HealingSplitBatchReplay admits the contested height-3 certificate prefix.
It checks the strict WB stamps, 2/3 joined batch, release count 3<4, live B root
at proposal 254 and expiry before the incompatible label-254 HEAD.
Healing/RegressionFixture holds the common data and local handler folds. It has
no service producer or full-run certificate. The tests import this P-H1 module.
These are local folds, not full ExecutionValid or signature-origin certificates.
Tests/HealingReplayObligations names the exact remaining full-run existential
goals, including same-prefix extensions to horizons 2070 and 2080. Those goals
remain OPEN/P-H1. NonVacuity/HealingRun applies both local adapters to the actual
positive horizon-310 RecoverySleep₂ execution with produced P5 services.

P-As Round 9 Assembly boundary (sleep-pas9):
Assembly/Outage supplies the finite healthy sleep prefix. Root uses the P-Ou
exporter and that supplier. Finality monotonicity permits retained-store restarts.

Assembly/Healing uses joined-start promotion and the named finite proposal
receipt producer. Assembly/ResetArrival supplies every Foundation input for
healing_postReset_inv_recovery, healing_h0_extension_recovery,
healing_localInput_recovery and healing_fullInput_recovery. The suppliers are
RMonoAll, emitted names, joined last writes, RXing, RQCOrigin, RCap, TSrc,
held-row origins, finality cap and head, row coverage and receipt, progress batch
coverage and fold, FaultQ, and honest quorum. No successor step is assumed by
these four Assembly adapters.

The selected Assembly lemmas have no explicit extension, localInput, fullInput
or inv argument. Full reset arrival and HTimeClaim use the returned extension
and full input. HealingInputClaim uses the local input at tstar <= horizon.
Extension changes only u and QStar. The complete recoveryStart budget and both
independent finite HG.5 guards remain. The older conditional composition APIs
remain available; the final claims and fgsaClaims use the closed producers.
There is no all-TF receipt or whole-run NoRestart premise.

HealingPackages and HealingFirst use horizon 310. HealingReset uses horizon 304.
Their restore calls already pass the exact restart time in the merged base.
All three source checks pass. FinalityClaims uses horizon 411 and Jst budget 309;
Adversarial uses horizon 300 and Jst budget 261. Their actual proposal tests use
slots 78 and 66. The prior prefixes and delayed pre-GST messages stay unchanged.
Public Claims/Statements, budgets, protocol sources and Proofs/Healing stay unchanged.

All 68 assigned P-As targets are GREEN. Full Healing.Export, HTimeClaim and
Root build with --wfail. The complete eight FG-SA libraries and test libraries
also pass --wfail. The canonical audit removes eight references to removed
Outage declarations and corrects 14 moved proof owners. It adds four existing
witness and Root rows and the four new Assembly producers. The 36 misplaced test rows
stay in six local strict audits. Canonical coverage uses the actual audit commands.
Canonical coverage passes for all 12 audits. DCK and compiled export checks pass.
The full manifest passes FG-SA, legacy, V2, Generic and Compose snapshots, then
stops on its PC-SA imports: Model/Protocol:449 has the old restore arity.
This inherited PC-SA port remains with the lead. The full manifest is not PASS.
Final evidence and exact public premises are in P-As.round9-handoff.md.

P-H2 Round 8 (sleep-ph2i): RecoveryProducers now constructs FrontierReadScope
with its seven current fields. Only its body changes. RepairCover imports the
P-H1 RepairLeaseRecovery adapters and removes the duplicate local proofs.
Healing.Export imports RecoveryPerm. Its promotion permanence callback uses
RecoverySleep₂. The renewed promotion producer keeps its Jst conclusion and
all three deadlines. The exact Export body passes a separate kernel probe.

Recovery produces the repair, opening and frontier aggregate scopes. Opening
gates require their selected GateReceiptGeometry. The callers prove this
geometry from covering HEADs and the current receiver floor. The new retained
cone floor proof uses the actual proposal parent before receipt service.
healing_frontierSearch_recovery supplies HG.5 from the named Foundations and
these produced scopes. Both finite rise and row horizon guards stay separate.

Post-reset opening uses retained services and local recovery epochs. Its gate
proofs use the saved-gate interface; they export no new matcher equations.
Reset transfer is produced only under its release horizon. The joint induction
produces P9 loss service, and its opening and service successors use RMonoAll
and joined writes. Cone receipts use fresh HEAD service and exact stamp epochs.
The cone successor is a guarded induction step. PostReset, H6, H2-prime and
THigh now construct their former service-factory inputs from recovery.

The H0 completion and healed consumer bodies compile at the selected witness.
HealingInputExport retains explicit field obligations at the full Jst horizon.
Full H0 extension, local HealingInput and the universal HealingInputOfH0 result
remain OPEN through the unproduced joint invariant. The reset-lease, lease and
raw successors still need their sleep ports. No all-cut source closure is
claimed. The map has 105/114 GREEN targets; nine retain P-H2. Exact obligations:
scripts/dev-pkg/P-H2.round8-handoff.md. No public claim, budget sum, GST saved
window or GST RowPermissionAt bound changes.


P-H2 Round 9 (sleep-ph2j): PostResetLeaseMove uses the actual bounded read,
the selected source supporter and the receiver floor. Receipt is at freeze;
TF content is durable. LeaseStep and RawStep use produced P1/P2/P10 scopes,
HeadRelayLocalServiceScope and local frozen epochs. Written reset extensions
supply a full recovery batch window. The fast arm releases every conflicting
lease, including a live pre-GST lease when k > 2R+3; it does not assume expiry.
The bounded output-suffix companion requires its vote time to be within the
run horizon. Its two uses prove this guard from actual bounded gate ticks. The
original H1 consumer keeps its exact statement and wraps this companion.
HealingInputExport constructs all six joint steps, inv, the selected full-H0
extension, local HealingInput and full HealingInput. Local input requires only
tstar <= horizon. Full input keeps the complete Jst horizon and budget sum.
Only u and QStar change in the extension. The remaining arguments are named
Foundation producers, row service and progress/finality laws. Healing.Export
exposes these producers. Tests use producer modules and named Foundation leaves;
there is no new test-to-Export or Healing-to-Foundations import.

Round 9 validation: all original 114 P-H2 targets are GREEN; the map also includes
one bounded support target. DCK strict audits and export checks pass. The full
manifest passes the FG-SA, legacy, V2, generic and Compose snapshots. Its claim
snapshot needed H1 test callers and P-As Assembly/NonVacuity ports at that
checkpoint. P-H2 Round 10 and P-As Round 9 close those ports. The final P-As
handoff records full Root closure and the inherited PC-SA manifest blocker.


### P0c1 — observations, paired selection, channels, and timing

`AvailableChainFGCompose.Statements.Observations` reads the cumulative FG store.
`Selection` pairs source and head at one post-clock state and equates those inputs
with the signing client. Its FG-SA private instance uses `Reachable`; its separate
joined law uses the actual fresh action under `ExecutionValid`.
`Timing` preserves the 0/1/2/3/5/6 delta offsets and signed slot arithmetic.
`Channels` preserves raw authentication, exact wire witnesses, and nested Options.
`ChannelLaws` translates RXing, RCap, RStrat, and all three RQCOrigin cases.
The source-service leaf retains the old gate, ancestry, and fastAt conjunction.
`Proofs.ObservationTransport` connects the paired read to `tick_rows`.
`Proofs.Timing` supplies the unchanged FG-SA action-time theorem through a private
clock instance. Private adapters are in `FGSAProofs.Proofs.Shared.FGCompose`.
Both `Tests.P0c1` modules check inhabited reads and reject the weaker interfaces.
FG-SA public definitions and snapshots stay fixed. PC-SA remains UNPORTED.

## Provisional integration gate

`bash scripts/gate.sh --integration --base REF` runs all positive checks and
package G0 checks. It defers the recorded generic negative controls only for
an eligible, clean, committed candidate on a branch other than main/master.
The result is provisional. It cannot write a FULL stamp, sign a FULL receipt,
or authorize main. Main requires FULL `--neg` and Mac `check-fg` on the exact
final candidate. Normal checker-path and control selection rules are unchanged.

Existing production Lean files must preserve all old source bytes. The selector
accepts exact import additions in a simple module header. It also accepts new
single-line numeric `def` declarations at the end of a file that contains only
that simple declaration grammar, imports, blank lines, and `public section`.
Declaration, import, and scope removal are refused. Other source edits are
unclassified and require the full gate. Existing test/control files are refused.

`--reviewed-extraction SOURCE:TARGET` records explicit review of one exact module
extraction. TARGET must be a new production module with the complete old SOURCE
content, byte for byte. SOURCE must retain its old simple module/import header
and replace its `public section` and body with a public import of TARGET.
The record binds both commits and the source/target SHA-256 hashes. The selector
checks preservation again at gate completion. Partial extraction, changed bodies,
removed facade imports, and overlapping extraction records are refused.
`--reviewed-allow FILE` remains limited to exact policy-data additions and retains
all generic controls. Neither review option can authorize checker logic edits.

The required shallow manifests `docs/GEN-API.md` and `docs/FGSA-API.md` permit
only structural declaration additions in the generated format. Every old name,
library, owner module, kind, digest, and metadata field must remain unchanged.
Counts must match the parsed rows and modules. Old row and module order is
preserved. Deep snapshots require separate old-entry and metadata preservation.
Other checker Markdown has no exemption. `checker-paths.txt` is unchanged.

Permitted Python coverage constants use separate literal schemas. `ORDER`
contains exact module suffixes; `CLAIMS_STRUCTURES` contains simple structure
names; `SAFETY_FIELDS` contains exact field labels, including `assembled package`.
`REQUIRED_MODEL_SCOPE` contains exact model owner/name pairs. Additions must
preserve all old entries and have no duplicates or wildcards. The surrounding
Python AST and shell wrapper must remain unchanged.

### P0d1 — phase order and settlement

`AvailableChainFGCompose.Statements.Phase` defines the cumulative frontier,
phase evidence, effective events, settled frames, intervals, and all five
`RPhase` clauses. Lower finality movement does not end a phase.
`Statements.PhaseReceipts` keeps the selected frontier, top, and contest
witnesses at `i + 1`, with the actual receiver, joined read, and strict deadline.
The receipt predicate can use the c2 target service or a frozen protocol service.
The consumer also takes its proved receipt-to-held consequence at that deadline.

`Proofs.Healing.PhaseFrame`, `PhaseOrder`, and `PhaseSettle` own the shared
proofs. They use the full store and certificate laws, observation equations,
order, cumulative retention, crossing, and explicit timing and receipt inputs.
Settlement constructs a joined tick between one and two delta after the event.
It returns the phase interval at three delta and each bounded post-clock frame.
The F-root case retains its accepted finality certificate.

The four FG-SA phase files use private core projections and preserve their
public statements. `PhaseService` keeps the concrete receipt factories.
`Tests.P0d1` in Compose checks phase and deadline controls; the FG-SA adapter
test checks all five clauses and the actual recovery receipt producer.
PC-SA remains UNPORTED and must supply its own service and receipt proofs.
P0d7a3 owns FGCompose Statements/FinalityKernel and Proofs/Finality/MiddleSupport
and Middle. FG-SA keeps its public middle record and theorem signatures. Private
fieldwise adapters bind the same service point, selected early carrier, fresh entry,
and through-action caps. The conditional shield route uses the published d7a2 seed
leaves and historical transfer, including the cutoff-to-service-start gap.

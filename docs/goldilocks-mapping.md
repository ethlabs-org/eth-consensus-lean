# Goldilocks mapping (skeleton)

From the Goldilocks references to the Lean definitions, milestones and names (foundation plan §4: one mapping
file per instance). Every Lean name here is fully qualified (namespace `Consensus`) and must be listed in
`ConsensusLeanTest/Index.lean`, whose build checks that it exists (check.sh step 12).

**Status: skeleton.** The only Goldilocks Lean today is the pre-foundation baseline
(`ConsensusLean/Instances/Goldilocks/{Spec,Statements}/Baseline.lean`): the round-model FG-SA numbers and the properties
sheet. It is **not approved** and no proof targets it (issue #38). The first slice (issue #10) re-derives the
statements from the current spec and fills the "First slice" table; each row then gets a read-back by an agent
that did not write it (`CONTRIBUTING.md` "Statements").

## References

All in fradamt-agent/goldilocks, `spec/`:

| Id | Document | Role |
|---|---|---|
| FGSA | `fgsa-protocol.tex` | FG-SA in the round model: the source of the baseline's numbers |
| SPEC | `fgsa-spec.tex` | the current Goldilocks spec (with loose BJ, goldilocks#14, and weakened E1, goldilocks#15) |
| CLAIMS | `goldilocks-claims.tex` (draft, goldilocks#12) | the claims and proof DAG that the instance statements will transcribe |

## Baseline (pre-foundation, not approved)

| Reference | Definition | Milestone | Lean name |
|---|---|---|---|
| FGSA: outputs confirmed (available and stable) and finalized (final) | output schema | — | `Consensus.Shape.goldilocksSchema` |
| FGSA: slots of `4Δ` | time grid | — | `Consensus.Shape.goldilocksGrid` |
| FGSA: one proposer per slot; committee kinds are placeholders | skeleton | — | `Consensus.Shape.goldilocksSkeleton` |
| FGSA: round length `R`, lock lifetime `lockK`, look-back `eta` | parameters | — | `Consensus.Shape.FGSAParams` |
| FGSA: catch-up, heal, latency, outage budget, progress | contract (pinned numbers) | — | `Consensus.Shape.goldilocksContract`, `Consensus.Shape.goldilocks_admissible`, `Consensus.Shape.reference_bounds` |
| intended properties (pre-foundation lists) | reviewed target: bindings, acceptance, extras | — | `Consensus.Shape.GoldilocksTarget`, `Consensus.Shape.GoldilocksBindings`, `Consensus.Shape.GoldilocksExtraAt` |

## First slice (issue #10)

CLAIMS pin: `goldilocks-claims.tex` at goldilocks `00df7945`. SPEC pin: `fgsa-spec.tex` at goldilocks
`95681941` (flattened SHA-256 `2a5519bc`). Milestone `M₁` (FG safety) is about the pure FG: chains, chain
states and the client. Its run-level nodes (G0.3, G0.4, G0.6, C0.2, G1.4, G1.5) come with
`Refinement/Defs.lean` in a later milestone.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | SPEC `shared/fg.tex` §Attestations and chain state; parameters | FG parameters, quorum `q = ⌈2n/3⌉`, `K_W = 2` | — | `Consensus.Goldilocks.FG.FGParams`, `Consensus.Goldilocks.FG.FGParams.q` |
| — | SPEC `shared/fg.tex` attestation, chain state, `bound` | attestation, FG view of a block, chain state | — | `Consensus.Goldilocks.FG.Att`, `Consensus.Goldilocks.FG.FGBlock`, `Consensus.Goldilocks.FG.ChainState`, `Consensus.Goldilocks.FG.ChainState.bound` |
| — | SPEC `shared/fg.tex` Figure "FG: state transition" (loose BJ gate) | `valid_attestation`, `process_attestation`, `process_height_events`, `state_transition`, the chain fold | — | `Consensus.Goldilocks.FG.Att.WellFormed`, `Consensus.Goldilocks.FG.ChainState.validAtt`, `Consensus.Goldilocks.FG.ChainState.processAtt`, `Consensus.Goldilocks.FG.FGParams.heightEvents`, `Consensus.Goldilocks.FG.FGParams.stateTransition`, `Consensus.Goldilocks.FG.FGParams.chainState` |
| — | SPEC `shared/fg.tex` §Validator client (entry-state read, set-valued timeouts, lock-first `height_pair`) | record, `permits`, `finality_pair`, `height_pair`, `create_attestation`, a client run | — | `Consensus.Goldilocks.FG.Record`, `Consensus.Goldilocks.FG.Record.createAtt`, `Consensus.Goldilocks.FG.Record.run` |
| — | SPEC `shared/fg.tex` §Slashing conditions (weakened E1) | E1, E2, slashable | — | `Consensus.Goldilocks.FG.slashable` |
| G1.1 | CLAIMS G1.1 | quorum intersection | `M₁` | `Consensus.Goldilocks.FG.QuorumIntersection` |
| G0.2 | CLAIMS G0.2 (a), (c) part, (d) without the entry blocks, (e) | chain-state invariants | `M₁` | `Consensus.Goldilocks.FG.ChainInvariants` |
| G0.2 | CLAIMS G0.2 (b), (h), (i) | height step, entry constancy | `M₁` | `Consensus.Goldilocks.FG.HeightStep` |
| G0.7 | CLAIMS G0.7 (c) | gated consumption (I7 restated) | `M₁` | `Consensus.Goldilocks.FG.GatedConsumption` |
| G0.8 | CLAIMS G0.8 | finality before the gate | `M₁` | `Consensus.Goldilocks.FG.FinalityBeforeGate` |
| G0.9 | CLAIMS G0.9 (a) | retention | `M₁` | `Consensus.Goldilocks.FG.Retention` |
| G0.9 | CLAIMS G0.9 (b) | the window `K_W = 2` | `M₁` | `Consensus.Goldilocks.FG.RetentionThroughAppend` |
| G0.10 | CLAIMS G0.10 | aggregation at a bound entry | `M₁` | `Consensus.Goldilocks.FG.Aggregation` |
| G0.5 | CLAIMS G0.5 | client safety | `M₁` | `Consensus.Goldilocks.FG.ClientSafety` |
| G1.3 | CLAIMS G1.3 (G1.2 is its proof's core lemma) | accountable safety, chain level | `M₁` | `Consensus.Goldilocks.FG.AccountableSafety` |
| — | the milestone | all of the above | `M₁` | `Consensus.Goldilocks.FG.FGSafety` |

Not transcribed in `M₁`: G0.2 (f), (g) (quorum witnesses on the chain; used inside the G1.3 proof) and (c)'s
`F ⪯ J ⪯ T_h ⪯ L` with the entry blocks (they need parent links, which `FGBlock` lists leave implicit), G0.7 (a)
(it restates the definition) and (b) (target bits persist while the height is current: not covered, `HeightStep` says nothing of the
target bits; deferred), F.1–F.4 (schedule,
tree, digests, readiness: run-level or generic). Witnesses in `ConsensusLeanTest/GoldilocksFG.lean`, labelled by kind there: (a) `conflicting_finalizations`; (b)
`oneValidator_finalizes`, `bound_entry_after_justification`, `gate_keeps_target_quorum`; and the G0.9 (c) limit
witness `window_drops_unfinalized` (the window drops an unfinalized pair).

Refinement obligations recorded for the run-level milestone: the client's input `(h_c, T_c)` is read as
`(σe.h, σe.Th)` of the entry state `σe = Σ.σ[T_c]` (true because the entry block's own state has `Th = T_c`,
`HeightStep`); `h_c = ⊥` (no source) is modelled by omitting the input; `Att.WellFormed` is composition's wire check folded into
`stateTransition` (the run level shows that the handlers' checks give it); the fold has no duplicate-root check
(`fg_on_block`), so roots of a chain need not be distinct at this level; digests map to roots (NoColl).

## Common and Frame (shared base of FGStore and ACBase)

One section per Goldilocks milestone follows (Common/Frame, then FGStore, ACBase, ACSteps, Compose/AnyAC, Persist,
Service, Healing, Regimes, Refinement); a milestone's statements PR edits only its own section, so parallel PRs do
not collide (consensus-lean#50).

CLAIMS pin: `goldilocks-claims.tex` at goldilocks `d9ea8d86` (goldilocks#21). Layout: decomposition §4.1
(workbench `repos/goldilocks/notes/architecture/decomposition.md`). The statements are not a milestone of their
own: `FGStore` and `ACBase` use them.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | SPEC `shared/composition.tex` §Blocks | block (parametric in the FG and AC payloads), digest, root check | — | `Consensus.Goldilocks.Block`, `Consensus.Goldilocks.Digest`, `Consensus.Goldilocks.Block.RootOk` |
| — | SPEC `shared/composition.tex` §Blocks (tree, `⪯`, compatible) | ancestry inside a set of blocks; coherent set (F.2, F.3 on a set) | — | `Consensus.Goldilocks.ParentIn`, `Consensus.Goldilocks.Anc`, `Consensus.Goldilocks.Compatible`, `Consensus.Goldilocks.Coherent` |
| — | SPEC `shared/composition.tex` §Model; `shared/fg.tex` `δ_t` | shared parameters, quorum, public time, `slot(t)` | — | `Consensus.Goldilocks.Params`, `Consensus.Goldilocks.Params.q`, `Consensus.Goldilocks.Params.IsPublic`, `Consensus.Goldilocks.Params.slotOf` |
| — | SPEC `shared/composition.tex` §"The FG frame"; `fgsa-spec.tex` `viable_ancestor` | frame, viable tree, viable ancestor, rooted tree | — | `Consensus.Goldilocks.Frame`, `Consensus.Goldilocks.Frame.viableTree`, `Consensus.Goldilocks.Frame.IsViableAncestor`, `Consensus.Goldilocks.Frame.viableAncestor`, `Consensus.Goldilocks.Frame.Rooted` |
| G0.4 (frame) | CLAIMS G0.4 (frame) | a well-formed frame | — | `Consensus.Goldilocks.FrameOK` |
| G0.3 (frame) | CLAIMS G0.3 (frame) | a frame step `⊑_B`, its closure, a frame sequence | — | `Consensus.Goldilocks.FrameStep`, `Consensus.Goldilocks.FrameEvol`, `Consensus.Goldilocks.FrameSeq`, `Consensus.Goldilocks.FrameSeqIn` |
| F.2 | CLAIMS F.2 (tree mathematics) | antisymmetry, ancestors form a chain, deepest common ancestor | Common | `Consensus.Goldilocks.AncAntisymm`, `Consensus.Goldilocks.AncTotal`, `Consensus.Goldilocks.DeepestCommonAncestor` |
| F.3 | CLAIMS F.3 | a collision-free digest determines the block | Common | `Consensus.Goldilocks.DigestDeterminesBlock` |
| — | SPEC `shared/composition.tex` §Model (`slot(t)`) | the slot of a time | Common | `Consensus.Goldilocks.SlotOfSpec` |
| G0.4 (frame) | CLAIMS G0.4 (frame), consequences | viable ancestor exists, is unique, is a candidate itself; viable tree ancestor-closed; tree parent-closed | Frame | `Consensus.Goldilocks.ViableAncestorExists`, `Consensus.Goldilocks.ViableAncestorSelf`, `Consensus.Goldilocks.ViableTreeAncestorClosed`, `Consensus.Goldilocks.FrameParentClosed` |
| G0.3 (frame) | CLAIMS G0.3 (frame), consequences | a step adds exactly `B`; retention; never returns; enters once | Frame | `Consensus.Goldilocks.FrameStepAddsBlock`, `Consensus.Goldilocks.FrameRetention`, `Consensus.Goldilocks.FrameNeverReturns`, `Consensus.Goldilocks.FrameEntersOnce` |
| — | the bundles | all of the above | Common, Frame | `Consensus.Goldilocks.CommonStatements`, `Consensus.Goldilocks.FrameStatements` |

Not transcribed: F.5 (schema), which is Mathlib's `WellFounded.induction`; F.2's "deepest, ties by root order"
(the SA's fork choice defines it where it is used); F.3's "a root determines the whole chain of its block" (a
consequence of `DigestDeterminesBlock` along parent edges, stated where a store needs it). Deviations: F.3 needs
`B.proposer = C.proposer`, because composition.tex digests `(parent root, slot, attestations, AC payload)` without
the proposer (the node's blocks have the slot proposer, asserted by `state_transition`); its collision-freedom is
about the two blocks' contents, not the whole digest. `Frame` carries `F` as a field (composition.tex derives it
as the root of the tree; under `FrameOK` it is that root). `FrameOK` adds "roots injective on the tree", which
`fg_on_block`'s duplicate-root test gives. The sequence statements of G0.3 (frame) assume that the trees lie in
one coherent set `U` (at a node, the accepted tree): frames alone allow a block that left the tree to come back
under a reused root. Witnesses in `ConsensusLeanTest/GoldilocksFrame.lean`,
all kind (a): `frameOK_Φ₀`, `frameOK_Φ₁`, `step_Φ₀_Φ₁`, `step_Φ₁_Φ₂`, `seq_hyps`.

## FGStore

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `c4928a76` (goldilocks#21 merged). Statements about the FG states that
the handlers reach, at one node; part 2 (G1.4, G1.6–G1.10, over FG traces) waits for `Spec/Trace`.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | SPEC `shared/fg.tex` §Attestations (`δ_t`, proposer, genesis) | FG parameters from the shared ones; node block; FG view; genesis | — | `Consensus.Goldilocks.Params.fg`, `Consensus.Goldilocks.NodeBlock`, `Consensus.Goldilocks.Block.fgView`, `Consensus.Goldilocks.Params.genesisBlock` |
| — | SPEC `shared/composition.tex` §State | `Σ` (tree and chain states by root), its tree, ancestry, initial state | — | `Consensus.Goldilocks.Store`, `Consensus.Goldilocks.Store.tree`, `Consensus.Goldilocks.Store.Anc`, `Consensus.Goldilocks.Store.init` |
| — | SPEC `shared/fg.tex` §Finality caches and frame | `fg_contest`, `head_height_floor`, `get_fc_root`, `is_viable`, `has_viable_descendant`, `fg_to_ac` | — | `Consensus.Goldilocks.Store.Contest`, `Consensus.Goldilocks.Store.headHeightFloor`, `Consensus.Goldilocks.Store.fcRoot`, `Consensus.Goldilocks.Store.IsViable`, `Consensus.Goldilocks.Store.HasViableDescendant`, `Consensus.Goldilocks.Store.toFrame` |
| — | SPEC `shared/fg.tex` Figure "FG: handlers" | `fg_on_attestation`, `update_finality`, `fg_on_block`; store steps; reachable states | — | `Consensus.Goldilocks.Store.onAttestation`, `Consensus.Goldilocks.Store.addAtts`, `Consensus.Goldilocks.Store.LexLt`, `Consensus.Goldilocks.Store.updateFinality`, `Consensus.Goldilocks.Store.onBlock`, `Consensus.Goldilocks.Store.Step`, `Consensus.Goldilocks.Store.Reachable` |
| — | SPEC `shared/fg.tex` Figure "FG: handlers" | `fg_attest`, `proposal_attestations` | — | `Consensus.Goldilocks.Store.attest`, `Consensus.Goldilocks.Store.OnChain`, `Consensus.Goldilocks.Store.proposalAttestations` |
| G0.1 (store) | CLAIMS G0.1 (store) | `Σ.σ[B]` is the fold over `B`'s chain | FGStore | `Consensus.Goldilocks.Store.LinkedFromGenesis`, `Consensus.Goldilocks.Store.ChainStateOfChain` |
| F.2 | CLAIMS F.2 (at the store) | the accepted tree is coherent and rooted at genesis; it only grows | FGStore | `Consensus.Goldilocks.Store.AcceptedTree`, `Consensus.Goldilocks.Store.TreeGrows` |
| G0.3 | CLAIMS G0.3 | cache invariants | FGStore | `Consensus.Goldilocks.Store.CacheInvariants` |
| C0.2 | CLAIMS C0.2 (the `Σ` half) | the finalized tip moves only to descendants | FGStore | `Consensus.Goldilocks.Store.FinalizedMonotone` |
| G0.3 (frame) | decomposition §2 D (the FG kernel) | an acceptance is a frame step | FGStore | `Consensus.Goldilocks.Store.AcceptIsFrameStep` |
| G0.4 (height) | CLAIMS G0.4 (height) | `fg_to_ac(Σ)` is well formed; the head height floor | FGStore | `Consensus.Goldilocks.Store.FrameRealization` |
| G0.2 (c), (h) | CLAIMS G0.2 (c), (h) at the store; the `M₁` refinement obligation on `(h_c, T_c)` | the entry, finalized and justified roots of `σ[B]` name accepted ancestors; the entry state has `B`'s height and entry | FGStore | `Consensus.Goldilocks.Store.EntryStateOfSource` |
| — | the bundle | all of the above | FGStore | `Consensus.Goldilocks.Store.FGStoreLocalAt`, `Consensus.Goldilocks.Store.FGStoreLocal` |

Modelling notes: `Σ.T` and `Σ.σ` are kept by root (the store's duplicate test is by root, so a held root names one
block); genesis takes an AC payload `acp₀` (never read). Restart keeps `Σ`, so it is no store step. Not yet
stated: G0.3's "a block that leaves `Φ.tree` never returns" (it is `FrameNeverReturns` along the frames of
`AcceptIsFrameStep`, with `U` the union of the trees, by `AcceptedTree`, `TreeGrows` and `FrameRealization`);
G0.1 (store)'s "does not depend on the node, the arrival order or the time" (it follows from `ChainStateOfChain`
under NoColl in F.3's form, and is stated with part 2, where two stores meet); G1.9 (statement not fixed). Witnesses in `ConsensusLeanTest/GoldilocksFGStore.lean`, kind (a): `init_reachable`, `accepts_b₁`.

## ACBase

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `c4928a76` (goldilocks#21 merged). SPEC pin: `fgsa-spec.tex`
at goldilocks `95681941` (§"Available chain: Goldilocks"). Layout: decomposition §2 D, §3.1, §4.1 (workbench
`repos/goldilocks/notes/architecture/decomposition.md`, rev 5). Milestone `ACBase` covers the AC module's L0 nodes:
the AC interface over frames, reachable AC states, the AC trace contract with `Sync_AC` and `Carry`, the
Goldilocks SA, and F.1, A0.1–A0.9. The A1 step lemmas are `ACSteps`.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | `Spec/Trace` (decomposition §2 D, `Trace`) | the component trace carrier: cuts, events, positions, labels, structural stuttering, awake | — | `Consensus.Goldilocks.Trace`, `Consensus.Goldilocks.Trace.state`, `Consensus.Goldilocks.Trace.CallAt` |
| — | SPEC `shared/composition.tex` §"The available chain" | the AC interface (nine functions, executable), duty heads, emissions with their read point, calls | — | `Consensus.Goldilocks.ACInterface`, `Consensus.Goldilocks.DutyHead`, `Consensus.Goldilocks.Emission`, `Consensus.Goldilocks.ACInterface.Call`, `Consensus.Goldilocks.ACInterface.step` |
| C0.5 (a), (b); CLAIMS §"How to read the DAG" | reachability: the frame law, the input contract, one coherent set | initial frame, call law, reachable states | — | `Consensus.Goldilocks.ACInterface.InitialFrame`, `Consensus.Goldilocks.ACInterface.FrameIn`, `Consensus.Goldilocks.ACInterface.CallOK`, `Consensus.Goldilocks.ACInterface.CallStep`, `Consensus.Goldilocks.ACInterface.ReachableAt`, `Consensus.Goldilocks.ACInterface.Reachable` |
| A0.6, A0.9 | SPEC `shared/composition.tex` requirements 1–4; CLAIMS A0.9 (requirement 5) | the interface requirements over reachable states | — | `Consensus.Goldilocks.ACInterface.HeadOK`, `Consensus.Goldilocks.ACInterface.AtReachable`, `Consensus.Goldilocks.ACInterface.ReqHeads`, `Consensus.Goldilocks.ACInterface.ReqSource`, `Consensus.Goldilocks.ACInterface.ReqOutputs`, `Consensus.Goldilocks.ACInterface.ReqParent`, `Consensus.Goldilocks.ACInterface.ReqPayload`, `Consensus.Goldilocks.ACInterface.Requirements` |
| C0.5 (a), (b); CLAIMS §Runs | the AC trace (decomposition §2 D, `AC.LocalRun`) | labels (call, frame, emissions), the trace contract | — | `Consensus.Goldilocks.ACLabel`, `Consensus.Goldilocks.ACTrace`, `Consensus.Goldilocks.ACLocalRun` |
| — | CLAIMS §Premises `Sync[a,b]` (with acceptance relay) | `Sync` over an AC trace, wake-adjusted deadlines | — | `Consensus.Goldilocks.SyncAC`, `Consensus.Goldilocks.ACTrace.deadline`, `Consensus.Goldilocks.ACTrace.lastWake` |
| — | SPEC §"Schedule", §"State" | SA parameters, `t_s = 4Δs`, votes, payload, locks, state, initial state, joined | — | `Consensus.Goldilocks.SA.SAParams`, `Consensus.Goldilocks.SA.SAParams.ts`, `Consensus.Goldilocks.SA.Vote`, `Consensus.Goldilocks.SA.Payload`, `Consensus.Goldilocks.SA.Lock`, `Consensus.Goldilocks.SA.ETime`, `Consensus.Goldilocks.SA.SAState`, `Consensus.Goldilocks.SA.SAState.initial`, `Consensus.Goldilocks.SA.joined` |
| — | SPEC §"Votes and views" | blocks by root, deepest (ties by root order), payload check, admission, resolution, views, merged view, counting, voter block tree | — | `Consensus.Goldilocks.SA.InTree`, `Consensus.Goldilocks.SA.lookup`, `Consensus.Goldilocks.SA.deepest`, `Consensus.Goldilocks.SA.validPayload`, `Consensus.Goldilocks.SA.admitVote`, `Consensus.Goldilocks.SA.resolutionTime`, `Consensus.Goldilocks.SA.voteView`, `Consensus.Goldilocks.SA.latestView`, `Consensus.Goldilocks.SA.mergedVoteView`, `Consensus.Goldilocks.SA.equivocators`, `Consensus.Goldilocks.SA.supporters`, `Consensus.Goldilocks.SA.voterBlockTree` |
| — | SPEC §"Locks" | live locks, anchor, veto, add_locks, opponents, unlock | — | `Consensus.Goldilocks.SA.liveLocks`, `Consensus.Goldilocks.SA.getAnchor`, `Consensus.Goldilocks.SA.conflictsWithLock`, `Consensus.Goldilocks.SA.addLocks`, `Consensus.Goldilocks.SA.opponents`, `Consensus.Goldilocks.SA.unlock` |
| — | SPEC §"Fork choice", §"Confirmation" | score, eligibility, walk, head; the update, the optimistic confirmation, the confirmed tip | — | `Consensus.Goldilocks.SA.goldfishScore`, `Consensus.Goldilocks.SA.ghost`, `Consensus.Goldilocks.SA.getHead`, `Consensus.Goldilocks.SA.acHead`, `Consensus.Goldilocks.SA.updateConfirmation`, `Consensus.Goldilocks.SA.optimisticConfirmation`, `Consensus.Goldilocks.SA.acConfirmed` |
| — | SPEC §"Node actions", §"Joining and restart" | the vote, the handlers, the proposal, the FG update, the restart; the SA as an AC | — | `Consensus.Goldilocks.SA.tryVote`, `Consensus.Goldilocks.SA.acOnMessage`, `Consensus.Goldilocks.SA.acOnBlock`, `Consensus.Goldilocks.SA.acOnTick`, `Consensus.Goldilocks.SA.acProposal`, `Consensus.Goldilocks.SA.acToFG`, `Consensus.Goldilocks.SA.acRestart`, `Consensus.Goldilocks.SA.goldilocksSA` |
| — | CLAIMS `Carry` (before A1.1), `h_t` (§Runs), §Premises fault bound | over SA traces | — | `Consensus.Goldilocks.SA.SATrace`, `Consensus.Goldilocks.SA.CarryAt`, `Consensus.Goldilocks.SA.Carry`, `Consensus.Goldilocks.SA.JoinedAt`, `Consensus.Goldilocks.SA.FaultBound` |
| F.1 | CLAIMS F.1 (a), (b), (c) | slot arithmetic; lock expiry; joining | `ACBase` | `Consensus.Goldilocks.SA.SlotArithmetic`, `Consensus.Goldilocks.SA.LockExpiry`, `Consensus.Goldilocks.SA.JoinedFrom`, `Consensus.Goldilocks.SA.JoinedAwake` |
| A0.1 | CLAIMS A0.1 | pool capacity, admission slots, stamps, carried votes, stamps along parent edges | `ACBase` | `Consensus.Goldilocks.SA.PoolCap`, `Consensus.Goldilocks.SA.AdmissionSlots`, `Consensus.Goldilocks.SA.StampStable`, `Consensus.Goldilocks.SA.CarriedVotes`, `Consensus.Goldilocks.SA.StampParent` |
| A0.2 | CLAIMS A0.2 | resolution is stable; support heads in the tree, opponents of `Φ.F` | `ACBase` | `Consensus.Goldilocks.SA.ResolutionStable`, `Consensus.Goldilocks.SA.SupportInTree` |
| A0.3 | CLAIMS A0.3 | supporters, opponents, majority chain, optimistic chain, merged-view opponents | `ACBase` | `Consensus.Goldilocks.SA.SupportersAntitone`, `Consensus.Goldilocks.SA.OpponentsMonotone`, `Consensus.Goldilocks.SA.MajorityChain`, `Consensus.Goldilocks.SA.OptimisticChain`, `Consensus.Goldilocks.SA.MergedOpponents` |
| A0.4 | CLAIMS A0.4 (a)–(f) | live locks on one chain and viable; locks move back; unlock idempotent; no fallback; FG candidates | `ACBase` | `Consensus.Goldilocks.SA.LiveLocksChain`, `Consensus.Goldilocks.SA.MovesBack`, `Consensus.Goldilocks.SA.LocksMoveBack`, `Consensus.Goldilocks.SA.UnlockIdempotent`, `Consensus.Goldilocks.SA.UnlockNoFallback`, `Consensus.Goldilocks.SA.CandidatesChain` |
| A0.5 | CLAIMS A0.5 | lock to tip | `ACBase` | `Consensus.Goldilocks.SA.LockToTip` |
| A0.6 | CLAIMS A0.6 | requirements 1–4 for the SA | `ACBase` | `Consensus.Goldilocks.SA.InterfaceRequirements` |
| A0.7 | CLAIMS A0.7 | the restart state; a joined node erased no recent vote | `ACBase` | `Consensus.Goldilocks.SA.RestartState`, `Consensus.Goldilocks.SA.JoinedKeepsVotes` |
| A0.8 | CLAIMS A0.8 | one vote per slot, across restarts | `ACBase` | `Consensus.Goldilocks.SA.OneVotePerSlot` |
| A0.9 | CLAIMS A0.9 | requirement 5 for the SA | `ACBase` | `Consensus.Goldilocks.SA.ProposalPayloadValid` |
| — | decomposition §2 D (not a claims node) | the AC trace contract gives reachable states | `ACBase` | `Consensus.Goldilocks.LocalRunReachable` |
| — | the milestone | all of the above | `ACBase` | `Consensus.Goldilocks.SA.ACBase` |

Modelling choices:

- **Signatures** are not modelled, as for the FG's attestations (#44). The signer of a vote is its `val`, every
  committee is `V`, unforgeability is a run premise, and the payload check keeps only the slot clause and the
  support clause (A0.9's "valid seat signature" has no Lean counterpart).
- **Blocks by name.** The AC holds roots. "`H ∈ Φ.tree`" means the tree holds a block with that root.
- **Time.** Stamps live on `WithBot (WithTop Time)`, with `timestamp[genesis] = −∞`. A vote or block the AC never
  accepted reads `+∞`, which no rule reads at a reachable state.
- **"Deepest, ties by root order"** is defined in `SA` over the depth inside the frame tree, and the smaller root
  wins a tie; the same rule breaks the walk's score ties.
- **The walk** is bounded by the size of the frame tree (`FrameOK.finite`).
- **The restart** replays in a parent order that is a parameter of the SA (`Consensus.Goldilocks.SA.ReplayOrder`).
  The spec leaves the sibling order open, and the order matters for the two-vote cap and the pool order
  (goldilocks#26). Every statement quantifies over all replay orders.
- **The own vote's re-entrant `try_vote`** is not unfolded: it returns at once because `voted_slot = s` is written
  first.
- **Placement.** The generic interface cannot name votes or joining, so `Carry`, `h_t` and the fault bound are in
  `Spec/SA/Trace`, not `Spec/AC/Trace`.
- **`Sync` over the AC trace.**
  - Every receipt by an honest node is a send, since honest nodes forward every object they receive (composition.tex
    §"Model"). So the message clause triggers on every honest send or receipt in `[a, b]`, not only the first.
  - The message must be processed at a time in `[τ, deadline)`. A processing before `τ` does not count, such as a
    vote refused by admission because it arrived before its slot.
  - The claims' literal wording ("first receives … is processed … before") admits that earlier processing, and
    then A1.1 and A1.2 have counterexamples (goldilocks#28).
- **Reachability.** It starts at time `0`, with genesis as the slot-0 block with no parent and the AC's genesis
  payload (`InitialFrame`; for the SA, two empty lists).
- **Unforgeability.** The AC trace contract does not carry it; ACSteps adds it as a premise over AC traces, for
  A1.1, A1.8 and the honest non-equivocation that A1.2 and A1.3 use.
- **Proposal requirements** (`ReqHeads`' first clause, `ReqParent`, `ReqPayload`) are stated at slot starts,
  where the node calls `ac_proposal`. The other requirements hold at every later time.

Witnesses in `ConsensusLeanTest/GoldilocksAC.lean`, all of kind (a): `initial_reachable`, `proposal_at_slot_one` and
`localRun_one_tick`. The same file writes decomposition §4.7 case 1 (A1.3 per vote, a test of the AC trace contract,
not a milestone statement) as `CaseOneA13`.

## ACSteps

Nothing cited yet; the milestone's statements PR fills this section.

## Compose/AnyAC

Nothing cited yet; the milestone's statements PR fills this section.

## Persist

Nothing cited yet; the milestone's statements PR fills this section.

## Service

Nothing cited yet; the milestone's statements PR fills this section.

## Healing

Nothing cited yet; the milestone's statements PR fills this section.

## Regimes

Nothing cited yet; the milestone's statements PR fills this section.

## Refinement

Nothing cited yet; the milestone's statements PR fills this section.

## Exclusions

What the model leaves out, and why. Generic exclusions (static adversary, equal weights, one `Δ`, no
responsiveness claim, no transaction validity, …) are in README "Scope". For the baseline, the sheet's module
docstring (`ConsensusLean/Instances/Goldilocks/Statements/Baseline.lean`) lists the intended properties not yet stated
(§3), those stated weaker than intended, and the migration obligations. Known differences between the baseline
and SPEC (issue #38): lock lifetime and outage budget, FG attestations after every tick instead of once per
round, and the loose-BJ bounds (`K_W = 2`, general `Δ_F`). The first slice replaces this paragraph with one row
per exclusion: what is left out, why, and which claim it affects.

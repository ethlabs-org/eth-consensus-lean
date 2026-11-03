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

All in the Goldilocks repository (`fradamt-agent/goldilocks`, archived for the team at `ethlabs-org/goldilocks-archive`), `spec/`;
a snapshot (at `23f5fdaa`) is in this repository at [`archive/goldilocks/spec/`](../archive/goldilocks/spec/):

| Id | Document | Role |
|---|---|---|
| FGSA | [`fgsa-protocol.tex`](../archive/goldilocks/spec/fgsa-protocol.tex) | FG-SA in the round model: the source of the baseline's numbers |
| SPEC | [`fgsa-spec.tex`](../archive/goldilocks/spec/fgsa-spec.tex) | the current Goldilocks spec (with loose BJ, goldilocks#14, and weakened E1, goldilocks#15) |
| CLAIMS | [`goldilocks-claims.tex`](../archive/goldilocks/spec/goldilocks-claims.tex) (draft, goldilocks#12) | the claims and proof DAG that the instance statements will transcribe |

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

Refinement obligations recorded for the run-level milestone: the client's input `(h_c, T_c)` is read as `(σe.h,
σe.Th)` of the entry state `σe = Σ.σ[T_c]` (true because the entry block's own state has `Th = T_c`,
`HeightStep`); `h_c = ⊥` (no source) is modelled by omitting the input; `Att.WellFormed` (`h ≥ 1`; a finality pair
has `h_f < h`) is the form that fg.tex §Attestations gives every attestation, which composition §Blocks checks on
the wire for every attestation a block carries, folded into `stateTransition`; `valid_attestation` alone does not
imply it (an attestation that names the chain's own entry with a finality pair at `h_f ≥ h` passes its first
branch), and a block that fails it is refused here where the node drops it before `fg_on_block`, the same outcome
(the run level shows that the handlers' checks give it); the fold has no duplicate-root check (`fg_on_block`), so
roots of a chain need not be distinct at this level; digests map to roots (NoColl).

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
the proposer (in a run, a block delivered to an honest node has its slot's proposer by the run law
`LocalRun.proposerCredential`; the model's `state_transition` no longer asserts it, `docs/decisions.md`
2026-10-31); its collision-freedom is about the two blocks' contents, not the whole digest. `Block.input : Nat` is the engine's header input
(`encodeTxs mempool`), which the spec folds into the AC payload (the AC fixes its payload's encoding): it is
digested, compared by F.3 and `NoCollOn`, written by the proposer's tick and read by no handler
(`docs/decisions.md`, "Goldilocks instance"). `Frame` carries `F` as a field (composition.tex derives it
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
| — | decomposition §2 D (`FG.LocalRun`); claims C0.4, C0.5 (c) | FG state with the record; the execution law of an FG call; an FG trace; the FG trace contract (initial state, execution, trees in `U`, time order, signing at public times, own proposal first and from the pool, attest before receipts, unforgeability) | — | `Consensus.Goldilocks.FGState`, `Consensus.Goldilocks.FGLabel.Step`, `Consensus.Goldilocks.FGLabel.processed`, `Consensus.Goldilocks.FGTrace`, `Consensus.Goldilocks.FGTrace.SignAt`, `Consensus.Goldilocks.FGTrace.AcceptAt`, `Consensus.Goldilocks.FGTrace.ProcessAt`, `Consensus.Goldilocks.FGLocalRun` |
| G1.4 | CLAIMS G1.4 | finalized safety over FG traces | FGStore (part 2) | `Consensus.Goldilocks.Store.FinalizedSafety` |
| G1.10 | CLAIMS G1.10 (the core, with the own proposal; decomposition §4.7 case 2) | quorum-free entries | FGStore (part 2) | `Consensus.Goldilocks.Store.namers`, `Consensus.Goldilocks.Store.QuorumFreeEntries` |
| — | the part-2 bundle | the above, at one and at every parameter set | FGStore (part 2) | `Consensus.Goldilocks.Store.FGStoreTraceAt`, `Consensus.Goldilocks.Store.FGStoreTrace` |
| — | CLAIMS §"L1: components / Finality gadget" (notation: entry, window, `D`); theorem.md (r9) §1–§2 | an entry block; an honest proposal (P5's inclusion rule); the good window `GW(E, a, k_F)` (P1–P6; P7 is `FGLocalRun`); a block that justifies an entry without leaving its height first | FGStore (part 3) | `Consensus.Goldilocks.Store.IsEntry`, `Consensus.Goldilocks.Store.HonestProposal`, `Consensus.Goldilocks.Store.GoodWindow`, `Consensus.Goldilocks.Store.JustifiesEntry` |
| G1.6 | CLAIMS G1.6 (theorem A) | bound entry | FGStore (part 3) | `Consensus.Goldilocks.Store.BoundEntry` |
| G1.7 | CLAIMS G1.7 (theorem B) | unbound entry, two windows | FGStore (part 3) | `Consensus.Goldilocks.Store.UnboundEntry` |
| G1.8 | CLAIMS G1.8 (corollary C) | (a) crossing bound; (b) coverage after failed entries | FGStore (part 3) | `Consensus.Goldilocks.Store.Crossing`, `Consensus.Goldilocks.Store.Coverage` |
| G1.9 (a) | CLAIMS G1.9 (a) | cache acceptance per `update_finality` call | FGStore (part 3) | `Consensus.Goldilocks.Store.afterJustification`, `Consensus.Goldilocks.Store.CacheAcceptance` |
| — | the part-3 bundle | the above, at one and at every parameter set | FGStore (part 3) | `Consensus.Goldilocks.Store.FGStoreServiceAt`, `Consensus.Goldilocks.Store.FGStoreService` |

Modelling notes: `Σ.T` and `Σ.σ` are kept by root (the store's duplicate test is by root, so a held root names one
block); genesis takes an AC payload `acp₀` (never read). Restart keeps `Σ`, so it is no store step. Not yet
stated: G0.3's "a block that leaves `Φ.tree` never returns" (it is `FrameNeverReturns` along the frames of
`AcceptIsFrameStep`, with `U` the union of the trees, by `AcceptedTree`, `TreeGrows` and `FrameRealization`);
G0.1 (store)'s "does not depend on the node, the arrival order or the time" (it follows from `ChainStateOfChain`
under NoColl in F.3's form, and is stated with part 2, where two stores meet); G1.9 (b) (statement not fixed in the claims); G1.10's C1.1 scope (a)–(c) (Compose), and `Sync` over FG traces (with the statements that need it).
Witnesses in `ConsensusLeanTest/GoldilocksFGStore.lean`, kind (a): `init_reachable`, `accepts_b₁`, `idle_localRun`, `relay_localRun`.

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
| — | SPEC §"Votes and views" | blocks by root, deepest (ties by root order), payload check, admission, resolution, views, merged view, counting, voter block tree, vote domain (**deviation**, not in SPEC: `docs/decisions.md` 2026-11-02, full-tree fallback; the voter block tree, or the whole tree when it has no viable block) | — | `Consensus.Goldilocks.SA.InTree`, `Consensus.Goldilocks.SA.lookup`, `Consensus.Goldilocks.SA.deepest`, `Consensus.Goldilocks.SA.validPayload`, `Consensus.Goldilocks.SA.admitVote`, `Consensus.Goldilocks.SA.resolutionTime`, `Consensus.Goldilocks.SA.voteView`, `Consensus.Goldilocks.SA.latestView`, `Consensus.Goldilocks.SA.mergedVoteView`, `Consensus.Goldilocks.SA.equivocators`, `Consensus.Goldilocks.SA.supporters`, `Consensus.Goldilocks.SA.voterBlockTree`, `Consensus.Goldilocks.SA.voteDomain` |
| — | SPEC §"Locks" | live locks, anchor, veto, add_locks, opponents, unlock | — | `Consensus.Goldilocks.SA.liveLocks`, `Consensus.Goldilocks.SA.getAnchor`, `Consensus.Goldilocks.SA.conflictsWithLock`, `Consensus.Goldilocks.SA.addLocks`, `Consensus.Goldilocks.SA.opponents`, `Consensus.Goldilocks.SA.unlock` |
| — | SPEC §"Fork choice", §"Confirmation" | score, eligibility, walk, head; the update, the optimistic confirmation, the confirmed tip | — | `Consensus.Goldilocks.SA.goldfishScore`, `Consensus.Goldilocks.SA.ghost`, `Consensus.Goldilocks.SA.getHead`, `Consensus.Goldilocks.SA.acHead`, `Consensus.Goldilocks.SA.updateConfirmation`, `Consensus.Goldilocks.SA.optimisticConfirmation`, `Consensus.Goldilocks.SA.acConfirmed` |
| — | SPEC §"Node actions", §"Joining and restart" | the vote (its head walks the vote domain: the **deviation** of `docs/decisions.md` 2026-11-02, full-tree fallback), the handlers, the proposal, the FG update, the restart; the SA as an AC | — | `Consensus.Goldilocks.SA.tryVote`, `Consensus.Goldilocks.SA.acOnMessage`, `Consensus.Goldilocks.SA.acOnBlock`, `Consensus.Goldilocks.SA.acOnTick`, `Consensus.Goldilocks.SA.acProposal`, `Consensus.Goldilocks.SA.acToFG`, `Consensus.Goldilocks.SA.acRestart`, `Consensus.Goldilocks.SA.goldilocksSA` |
| — | CLAIMS `Carry` (before A1.1), `h_t` (§Runs), §Premises fault bound | over SA traces | — | `Consensus.Goldilocks.SA.SATrace`, `Consensus.Goldilocks.SA.CarryAt`, `Consensus.Goldilocks.SA.Carry`, `Consensus.Goldilocks.SA.JoinedAt`, `Consensus.Goldilocks.SA.FaultBound` |
| F.1 | CLAIMS F.1 (a), (b), (c) | slot arithmetic; lock expiry; joining | `ACBase` | `Consensus.Goldilocks.SA.SlotArithmetic`, `Consensus.Goldilocks.SA.LockExpiry`, `Consensus.Goldilocks.SA.JoinedFrom`, `Consensus.Goldilocks.SA.JoinedAwake` |
| A0.1 | CLAIMS A0.1 | pool capacity, admission slots, stamps, carried votes, stamps along parent edges | `ACBase` | `Consensus.Goldilocks.SA.PoolCap`, `Consensus.Goldilocks.SA.AdmissionSlots`, `Consensus.Goldilocks.SA.StampStable`, `Consensus.Goldilocks.SA.CarriedVotes`, `Consensus.Goldilocks.SA.StampParent` |
| A0.2 | CLAIMS A0.2 | resolution is stable; support heads in the tree, opponents of `Φ.F` | `ACBase` | `Consensus.Goldilocks.SA.ResolutionStable`, `Consensus.Goldilocks.SA.SupportInTree` |
| A0.3 | CLAIMS A0.3 | supporters, opponents, majority chain, optimistic chain, merged-view opponents (reading: the claim's "slot-`(s+1)` voter" is a reachable state whose last call is in slot `σ + 1`; its parenthetical "for the carried votes, A0.1 under its timing condition" is the proof route, not a premise, so the statement has no acceptance-time premise; A0.1's condition, a block accepted at `t` with `slot(t) = B.slot`, agrees with the call-time premise for a slot-`(σ+1)` block of the merged view only if that block was not accepted in an earlier slot; the statement is proved as stated) | `ACBase` | `Consensus.Goldilocks.SA.SupportersAntitone`, `Consensus.Goldilocks.SA.OpponentsMonotone`, `Consensus.Goldilocks.SA.MajorityChain`, `Consensus.Goldilocks.SA.OptimisticChain`, `Consensus.Goldilocks.SA.MergedOpponents` |
| A0.4 | CLAIMS A0.4 (a)–(f) | live locks on one chain and viable; locks move back; unlock idempotent; no fallback; FG candidates | `ACBase` | `Consensus.Goldilocks.SA.LiveLocksChain`, `Consensus.Goldilocks.SA.MovesBack`, `Consensus.Goldilocks.SA.LocksMoveBack`, `Consensus.Goldilocks.SA.UnlockIdempotent`, `Consensus.Goldilocks.SA.UnlockNoFallback`, `Consensus.Goldilocks.SA.CandidatesChain` |
| A0.5 | CLAIMS A0.5 | lock to tip | `ACBase` | `Consensus.Goldilocks.SA.LockToTip` |
| A0.6 | CLAIMS A0.6 | requirements 1–4 for the SA | `ACBase` | `Consensus.Goldilocks.SA.InterfaceRequirements` |
| A0.7 | CLAIMS A0.7 | the restart state; a joined node erased no recent vote | `ACBase` | `Consensus.Goldilocks.SA.RestartState`, `Consensus.Goldilocks.SA.JoinedKeepsVotes` |
| A0.8 | CLAIMS A0.8 | one vote per slot, across restarts | `ACBase` | `Consensus.Goldilocks.SA.OneVotePerSlot` |
| A0.9 | CLAIMS A0.9 | requirement 5 for the SA | `ACBase` | `Consensus.Goldilocks.SA.ProposalPayloadValid` |
| — | decomposition §2 D (not a claims node) | the AC trace contract gives reachable states | `ACBase` | `Consensus.Goldilocks.LocalRunReachable` |
| — | the milestone | all of the above, at one and at every SA parameter set | `ACBase` | `Consensus.Goldilocks.SA.ACBaseAt`, `Consensus.Goldilocks.SA.ACBase` |

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
- **`Sync` over the AC trace** (claims at goldilocks `a470648c`, #30 and #32):
  - An honest node forwards an AC message when its AC admits it, also from the payload of an accepted block. A
    refused receipt is not forwarded.
  - So the message clause triggers on every honest send or admission in `[a, b]` (`ACInterface.holdsMsg`; for the
    SA, the vote is in its pool after the call and was not before). The restart's replay is excluded, because it
    re-processes blocks already accepted and sends nothing (A0.7).
  - The message must be processed at a time in `[τ, deadline)`. A processing before `τ` does not count.
  - goldilocks#28 has the counterexamples to the earlier "first receives … processed before" wording.
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

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `a470648c` (goldilocks#30, #32). SPEC pin: `fgsa-spec.tex` at goldilocks `95681941`.
Layout: decomposition §3.1, §3.2. Milestone `ACSteps` covers the AC module's L1 step lemmas over AC traces of the SA:
A1.1, A1.2, A1.3, A1.4, A1.5, A1.8 and A1.9. A1.2–A1.4 and A1.8 are per vote; A1.9 is per `ac_to_fg` call. A1.6 and
A1.7 are run-level (Service). The healing kernels A1–A5 of healing-simple are not claims nodes yet.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | SPEC §"Confirmation" (named parts of the update and the optimistic check) | the update's path, fast test, fast selection and counted votes; the optimistic selection; the block receipt | — | `Consensus.Goldilocks.SA.confirmationPath`, `Consensus.Goldilocks.SA.FastTest`, `Consensus.Goldilocks.SA.fastSelect`, `Consensus.Goldilocks.SA.fastCounted`, `Consensus.Goldilocks.SA.optimisticSelect`, `Consensus.Goldilocks.SA.blockReceipt` |
| — | CLAIMS §"L1 / Available chain" (events of the step lemmas) | votes and their viability; updates, results, fast lock writes of either origin with counted votes; `ac_to_fg` returns; proposals | — | `Consensus.Goldilocks.SA.VoteExtends`, `Consensus.Goldilocks.SA.CastAt`, `Consensus.Goldilocks.SA.ViableAtVote`, `Consensus.Goldilocks.SA.EarlierVotesExtend`, `Consensus.Goldilocks.SA.UpdateAt`, `Consensus.Goldilocks.SA.ResultAt`, `Consensus.Goldilocks.SA.FastUpdateAt`, `Consensus.Goldilocks.SA.OptimisticPoint`, `Consensus.Goldilocks.SA.OptimisticLockAt`, `Consensus.Goldilocks.SA.FastLockAt`, `Consensus.Goldilocks.SA.ToFGAt`, `Consensus.Goldilocks.SA.ProposalAt` |
| — | CLAIMS §Runs (unforgeable signatures); FG acceptance (slot proposer) | honest objects over an AC trace; the bundle with the trace contract | — | `Consensus.Goldilocks.SA.HonestObjects`, `Consensus.Goldilocks.SA.ACRun` |
| A1.1 | CLAIMS A1.1 | proposer and voters agree on unlocking | `ACSteps` | `Consensus.Goldilocks.SA.ProposerVotersAgree` |
| A1.2 | CLAIMS A1.2 | first transfer, per vote | `ACSteps` | `Consensus.Goldilocks.SA.FirstTransfer` |
| A1.3 | CLAIMS A1.3 | next transfer, per vote | `ACSteps` | `Consensus.Goldilocks.SA.NextTransfer` |
| A1.4 | CLAIMS A1.4 (a), (b) | optimistic is fast: the transfer (per vote), the next update | `ACSteps` | `Consensus.Goldilocks.SA.OptimisticTransfer`, `Consensus.Goldilocks.SA.OptimisticNextUpdate` |
| A1.5 | CLAIMS A1.5 | source age | `ACSteps` | `Consensus.Goldilocks.SA.SourceAge` |
| A1.8 | CLAIMS A1.8 | result transfer, per vote | `ACSteps` | `Consensus.Goldilocks.SA.ResultTransfer` |
| A1.9 | CLAIMS A1.9 | source compatibility after the cut, per call | `ACSteps` | `Consensus.Goldilocks.SA.SourceCompatible` |
| — | the milestone | all of the above, at one and at every SA parameter set | `ACSteps` | `Consensus.Goldilocks.SA.ACStepsAt`, `Consensus.Goldilocks.SA.ACSteps` |

Modelling choices:

- **Unforgeability and FG acceptance** are premises over the AC trace (`HonestObjects`; the coordinator's decision
  on #54). Honest votes held by an honest node, in its pools or carried by its frame's blocks, were emitted earlier
  by their validator's node. Every frame block has its slot's proposer. An honest proposer has at most one block per
  slot. `Spec/Run` discharges them through the projection.
- **Events inside a call** are named through the SA's own functions:
  - the update's fast selection, with the votes it counts, at the tick of `t_s + 6Δ`;
  - the optimistic check at its receipt states and after each own vote's admission (`OptimisticPoint`).
  "Writes a fast lock on `B`" means the test selects `B`. The stored lock can be moved back, as the claims note.
- **The A1.5 conclusion** "is the block of a fast lock written after `τ`" reads: at or below the block of a fast
  lock of a slot `s'` with `slot(t) ≤ s' + 2` that the node wrote at a cut after `τ` (a lock moves only back).
- **A1.9** follows the claims at goldilocks `688e287b` (goldilocks#33). The calling node `x` either (i) cast its
  slot-`(s+1)` vote before the call, with `Φ.F` and `fc_root` compatible with `B` at that vote's call (its
  unlocking), or (ii) restarted after `t_s`. It is no longer a vacuous "at each unlocking": consensus-lean#66
  shows that form is false. C1.1 discharges the disjunction by C0.4.
- **A1.2** follows the claims' text without a writer-pool hypothesis. That condition (A1.8 (d)) follows from
  `Sync`, because votes admitted from a block's payload are forwarded too (goldilocks#32). Without that forwarding,
  A1.2 would be false through block-carried votes (goldilocks#28).

Witness in `ConsensusLeanTest/GoldilocksAC.lean`, kind (a): `acRun_one_tick` (the hypothesis `ACRun` is
satisfiable). §4.7 case 1 (`CaseOneA13`, written with ACBase) has the same shape as `NextTransfer`.

## Compose/AnyAC

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `4ea71d05` (goldilocks#21, #23–#36; C0.5 (b) from #36). SPEC
pin: `shared/composition.tex` at goldilocks `a470648c` (§"State", §"Node", Figure "Node: handlers and duties"). Layout:
decomposition §2 D (`Node`), §3.1 (the "Node" row), §4.1, §4.2 (the `ComposeAnyAC` layer). Milestone `Compose/AnyAC`
covers the node parametric in the AC (`Spec/Node`) and the composition nodes C0.1–C0.5 stated at one node for **any**
AC meeting requirements 1–5 (`ACInterface.Requirements`); no SA, no run, no engine. The run-level composition
(C1.1, Service, Healing, Regimes) is over `Spec/Run`, later.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | SPEC `shared/composition.tex` §State | the node state `(Σ, 𝒜, Λ)` for an AC whose blocks carry attestation lists; its initial state; the frame `fg_to_ac(Σ)` | — | `Consensus.Goldilocks.NodeAC`, `Consensus.Goldilocks.NodeState`, `Consensus.Goldilocks.Node.init`, `Consensus.Goldilocks.Node.frame` |
| — | decomposition §1.5 (cuts are component calls); CLAIMS C0.5 | the cuts: an FG call with its observations (`FGLabel`, in `Spec/FG/Store/Label` so that FG traces share it), an AC call with its `ACLabel`; the AC calls with the frame recomputed | — | `Consensus.Goldilocks.FGLabel`, `Consensus.Goldilocks.Cut`, `Consensus.Goldilocks.Node.acCall`, `Consensus.Goldilocks.Node.acProposal`, `Consensus.Goldilocks.Node.acToFG` |
| — | SPEC `shared/composition.tex` Figure "Node" | the handlers: `on_block`, `on_ac_message`, `on_attestation`, a restart, `propose_block` (the block it makes), `attest` | — | `Consensus.Goldilocks.Node.onBlock`, `Consensus.Goldilocks.Node.onMessage`, `Consensus.Goldilocks.Node.onAttestation`, `Consensus.Goldilocks.Node.restart`, `Consensus.Goldilocks.Node.mkBlock`, `Consensus.Goldilocks.Node.proposeBlock`, `Consensus.Goldilocks.Node.attest` |
| C0.4 | SPEC §Node (`on_tick`); CLAIMS C0.4 | the tick steps as data, their order, the proposer test, one step, the fold, `on_tick` | — | `Consensus.Goldilocks.Node.TickStep`, `Consensus.Goldilocks.Node.tickSteps`, `Consensus.Goldilocks.Node.Proposes`, `Consensus.Goldilocks.Node.tickStep`, `Consensus.Goldilocks.Node.runSteps`, `Consensus.Goldilocks.Node.onTick` |
| — | SPEC §Model, §Node, §Blocks (wire checks) | top-level events and their handler; the wire checks of a delivery | — | `Consensus.Goldilocks.Node.Event`, `Consensus.Goldilocks.Node.exec`, `Consensus.Goldilocks.Node.WireOK` |
| C0.4 | SPEC §Model, §Node (restart, tick, then the objects of a time); decomposition §2 D (`Node.Reachable`) | the phase of a node in a time; configurations; when an event may run; one event; reachable configurations | — | `Consensus.Goldilocks.Node.Phase`, `Consensus.Goldilocks.Node.Phase.at`, `Consensus.Goldilocks.Node.Config`, `Consensus.Goldilocks.Node.Config.init`, `Consensus.Goldilocks.Node.EventOK`, `Consensus.Goldilocks.Node.Event.phaseAfter`, `Consensus.Goldilocks.Node.Step`, `Consensus.Goldilocks.Node.Reaches`, `Consensus.Goldilocks.Node.Reachable` |
| C0.5 | CLAIMS C0.5; decomposition §2 D (`I_link`, pointwise projection) | the law of one cut; a chain of cuts | — | `Consensus.Goldilocks.Node.CutStep`, `Consensus.Goldilocks.Node.CutChain` |
| A0.6, A0.9 | CLAIMS A0.6, A0.9 (consequences); C0.1 at the AC; C0.5 (c) | for any AC meeting requirements 1–5: the tips are nested, the proposal parent, the source and every duty head are held and extend `Φ.F` | Compose/AnyAC | `Consensus.Goldilocks.Compose.TipsNested`, `Consensus.Goldilocks.Compose.ProposalParentHeld`, `Consensus.Goldilocks.Compose.SourceHeld`, `Consensus.Goldilocks.Compose.DutyHeadsHeld`, `Consensus.Goldilocks.Compose.InterfaceStatements`, `Consensus.Goldilocks.Compose.ComposeInterfaceStatements` |
| C0.1 | CLAIMS C0.1 | three tips on one chain at the node | Compose/AnyAC | `Consensus.Goldilocks.Compose.ThreeTips` |
| C0.2 | CLAIMS C0.2 (both halves) | finalized monotone along reachable configurations, across restarts; a restart keeps `Σ` and `Λ` | Compose/AnyAC | `Consensus.Goldilocks.Compose.FinalizedMonotone`, `Consensus.Goldilocks.Compose.RestartKeepsFG` |
| C0.3 | CLAIMS C0.3 | honest blocks are accepted (with `NoColl` on the tree with the block) | Compose/AnyAC | `Consensus.Goldilocks.Compose.NoCollOn`, `Consensus.Goldilocks.Compose.HonestBlockAccepted` |
| C0.4 | CLAIMS C0.4 | the shape of a tick's cuts | Compose/AnyAC | `Consensus.Goldilocks.Compose.ProposalCuts`, `Consensus.Goldilocks.Compose.UpdateCuts`, `Consensus.Goldilocks.Compose.TickShape`, `Consensus.Goldilocks.Compose.TickOrder` |
| C0.5 (b) | CLAIMS C0.5 (b) (goldilocks#36) | the AC sees only blocks the FG accepted: an `ac_on_block(B)` cut comes right after the FG cut accepting `B`, `B` is not of a future slot, its root is new, its full parent is held, it extends `Σ.F` and `state_transition` passes from the parent's state | Compose/AnyAC | `Consensus.Goldilocks.Compose.ACSeesAcceptedBlocks` |
| C0.5 | CLAIMS C0.5 (a), (b), (c) | every handler's cuts obey the cut law; the AC's states are reachable AC states inside the accepted tree; the FG's states are reachable; the record is a client run; the sources are held; attestations signed only in ticks | Compose/AnyAC | `Consensus.Goldilocks.Compose.ExecIsCutChain`, `Consensus.Goldilocks.Compose.ACStatesReachable`, `Consensus.Goldilocks.Compose.FGStatesReachable`, `Consensus.Goldilocks.Compose.RecordIsClientRun`, `Consensus.Goldilocks.Compose.SourcesHeld`, `Consensus.Goldilocks.Compose.SignedOnlyInTicks` |
| — | the bundles | all of the above | Compose/AnyAC | `Consensus.Goldilocks.Compose.NodeStatements`, `Consensus.Goldilocks.Compose.ComposeNodeStatements` |

Modelling choices:

- **The node is parametric in the AC and the digest.** `NodeAC P := ACInterface P (List (FG.Att P.n))`; the
  digest `dg` and the validator `self` are arguments. `Spec/Node` does not import the SA; `Spec/Run` plugs in
  `goldilocksSA` (decomposition §2 D). The clock is not a field of the node state: every handler takes the time,
  and `Node.Config` carries it with the phase.
- **Cuts are component calls** (decomposition §1.5). Every handler returns its cuts in order; an AC cut carries the
  call, the frame `fg_to_ac(Σ)` recomputed before it, and the emissions (`ACLabel`, shared with `Spec/AC/Trace`);
  `ac_proposal` and `ac_to_fg` are cuts with no emissions and their returned value is used by the node. An FG cut
  carries its observations (`FGLabel`): the block and whether it was accepted, the attestation processed, the
  source and the attestation signed. A refused `fg_on_block` is a cut (a call with no write); a dropped future-slot
  block is no cut (no call). The broadcast of an own object is not a cut: a run observes it as the acceptance (own
  block) or the signing (own attestation).
- **The tick carries the input** (`Node.Event.tick x`): the engine's header input that `mkBlock` writes into the
  proposal's `Block.input` and that no handler reads. Statements over a tick quantify over it (`Step … (.tick x)`);
  `RunTrace.TickAt` hides it (`∃ x`).
- **`Node.Reachable` over-approximates a run.** `Node.Step` enforces composition.tex's order within a time (a
  restart in phase `pre`; the tick at a public time in phase `pre`, leaving `post`; a delivery at a public time
  only in `post`) and the wire checks. Three obligations are left to `Spec/Run`: (i) an awake node ticks at every
  public time; (ii) a restart follows a sleep (no cuts in between) and happens once per wake; (iii) an asleep node
  receives nothing. Signatures are not modelled at the node: unforgeability is a run condition.
- **C0.3** is stated on the intermediate states of the tick (`tickStep … .acTick`, then `acProposal`) and the
  block `mkBlock` makes, with the hypotheses an actual tick step (`Node.Step … .tick`), `Proposes`, genesis's root
  its digest, and `NoCollOn` on the tree with the block for the root-newness clause (and the acceptance, which
  needs it). Its well-formedness clause for the block's attestations (the assertion of `state_transition`)
  covers the node's own attestations, which need an FG client fact (`create_attestation` yields well-formed
  attestations at reachable entry states) that is not yet stated: a proof obligation, flagged in the PR.
- **C0.4** is the shape of a tick's cuts (`TickShape`); the restart/tick/deliveries order is `Node.Step` itself
  (definitional, as the claims file says). "Signed only in ticks" is C0.5 (c). **C0.5 (a)** uses `ACInterface.ReachableAt`
  with `U := Σ.T` (which only grows, so one coherent set serves the whole history) and the frame of the last call
  equal to the current `fg_to_ac(Σ)` (every acceptance is followed at once by `ac_on_block`; attestations do not
  change the frame).
- **C0.5 (b), the AC sees only FG-accepted blocks** (goldilocks#36) is stated on the cuts of every event
  (`ACSeesAcceptedBlocks`): the list shape `… ++ fg (block B true) :: ac ℓ :: …` and the `fg_on_block` conditions at
  the FG state before the accepting cut. "A parent of smaller slot" is not repeated: it is the assertion of
  `state_transition` (`FGParams.stateTransition`), which the statement says passes. "With its slot's proposer" is
  not part of the statement: it is not a node fact (no node check reads the proposer), but the run law
  `LocalRun.proposerCredential` for a delivered block and `Proposes` for the own block (`accept_facts`), by the
  2026-10-31 selected-duty repair (`docs/decisions.md`). A restart passes
  no block (the replay is inside `ac_restart`), so the restart clause is vacuous at the node.

Witnesses in `ConsensusLeanTest/GoldilocksNode.lean`, on `rootAC` (an AC with no state that proposes `fc_root`):
kind (a) `rootAC_requirements`, `init_reachable`, `tick_at_zero`, `proposer_tick`; kind (b)
`reachable_after_tick`.

## Persist

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `4ea71d05` (goldilocks#21, #23–#36; C1.1, F.4, F.5 and the
premises unchanged since `688e287b`). SPEC pin: `shared/composition.tex` at goldilocks `4ea71d05` (§"Model"). Layout: decomposition §2 D (`Run`), §3.1 (the "Run"
row), §4.6, §4.7 (test cases 1–3), §5 (admissibility). Milestone `Persist` covers the spec's own run model
(`Spec/Run`), the run-level composition facts every later milestone reads (F.4, F.5 (run), C0.5's projections), and
C1.1 with its corollary. The run is `Trace (Fin n) (NodeState A) (Cut A)`: labelled cuts are the component calls of
the honest nodes, grouped by top-level event; faulty nodes have no cuts.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | CLAIMS §Model, §Runs; SPEC §Model; decomposition §2 D | the run trace; its vocabulary: calls, restarts, block calls and acceptances, own blocks, signings, attestation and message calls and processing, emissions, sends-or-admissions (AC messages, attestations), the blocks that occur, the honest blocks, the latest wake, the delivery deadline `max(τ, w_y) + Δ'`, "the state at `t`" (before the first cut at a time `≥ t`), an own proposal at its slot's start, the horizon, the outputs at a cut | — | `Consensus.Goldilocks.RunTrace`, `Consensus.Goldilocks.RunTrace.IsCall`, `Consensus.Goldilocks.RunTrace.NoCallBetween`, `Consensus.Goldilocks.RunTrace.RestartAt`, `Consensus.Goldilocks.RunTrace.BlockCallAt`, `Consensus.Goldilocks.RunTrace.AcceptAt`, `Consensus.Goldilocks.RunTrace.OwnBlockAt`, `Consensus.Goldilocks.RunTrace.SignAt`, `Consensus.Goldilocks.RunTrace.AttCallAt`, `Consensus.Goldilocks.RunTrace.ProcessAttAt`, `Consensus.Goldilocks.RunTrace.EmitAt`, `Consensus.Goldilocks.RunTrace.MsgCallAt`, `Consensus.Goldilocks.RunTrace.ProcessMsgAt`, `Consensus.Goldilocks.RunTrace.SendOrAdmitAt`, `Consensus.Goldilocks.RunTrace.SendOrAdmitAttAt`, `Consensus.Goldilocks.RunTrace.Occurs`, `Consensus.Goldilocks.RunTrace.HonestBlocks`, `Consensus.Goldilocks.RunTrace.lastWake`, `Consensus.Goldilocks.RunTrace.deadline`, `Consensus.Goldilocks.RunTrace.FirstCutFrom`, `Consensus.Goldilocks.RunTrace.ProposesAt`, `Consensus.Goldilocks.RunTrace.InHorizon`, `Consensus.Goldilocks.RunTrace.finalizedAt`, `Consensus.Goldilocks.RunTrace.confirmedAt`, `Consensus.Goldilocks.RunTrace.headAt` |
| C0.4, C0.5 | CLAIMS §Runs; decomposition §2 D (groups) | a top-level event's cuts as a group of consecutive cuts with the handler's labels in order; membership; a tick group; the phase an event runs in | — | `Consensus.Goldilocks.RunTrace.GroupAt`, `Consensus.Goldilocks.RunTrace.InGroup`, `Consensus.Goldilocks.RunTrace.TickAt`, `Consensus.Goldilocks.Node.Event.phase` |
| — | CLAIMS §Runs (admissibility); SPEC §Model; decomposition §5 | **the run law**: initial state, every cut in a group obeying the cut law, wire checks, time order from `0`, finiteness per bounded interval, restart < tick < delivery at one time, an awake node ticks exactly once at every public time, called only while awake, first call after a sleep is a restart and a wake is a restart (sleep = no cuts, wake = restart cut), the awake clamp past the last cut, unforgeability (own blocks, attestations, AC messages via the signer map `sg`) | — | `Consensus.Goldilocks.Node.LocalRun` |
| Premises | CLAIMS §Premises (`Sync[a,b]`, `GST(g)`, `Sleepy`, `Healthy(g)`; `h_t` awake and joined) | joined at `t`; `h_t`; `f < h_t`; delivery within the deadline (messages, blocks, acceptances, attestations); `Sync` on a window with an effective send time, with acceptance relay; `Sync[a, b]`; `GST(g)`; `Sleepy`; `Healthy(g)` | — | `Consensus.Goldilocks.RunTrace.JoinedAt`, `Consensus.Goldilocks.RunTrace.honestAwakeJoined`, `Consensus.Goldilocks.RunTrace.FaultBound`, `Consensus.Goldilocks.RunTrace.MsgDeliveredBy`, `Consensus.Goldilocks.RunTrace.BlockDeliveredBy`, `Consensus.Goldilocks.RunTrace.BlockAcceptedBy`, `Consensus.Goldilocks.RunTrace.AttDeliveredBy`, `Consensus.Goldilocks.RunTrace.SyncOn`, `Consensus.Goldilocks.RunTrace.SyncRun`, `Consensus.Goldilocks.RunTrace.GSTRun`, `Consensus.Goldilocks.RunTrace.SleepyRun`, `Consensus.Goldilocks.RunTrace.HealthyRun` |
| — | SPEC §Composition; CLAIMS §Runs (carried votes) | the Goldilocks node (the node with the SA at the FG payload); its traces; a Goldilocks run (`LocalRun` with the vote's validator as signer, plus carried-vote unforgeability and the genesis root the digest of its content, so that C1.1 reaches the FG trace through `FGProjection`) | — | `Consensus.Goldilocks.goldilocksNode`, `Consensus.Goldilocks.GoldilocksTrace`, `Consensus.Goldilocks.GoldilocksRun` |
| C0.5 | decomposition §2 D (pointwise projection) | the AC and FG labels of a cut; the AC projection (an `ACTrace` over the `𝒜` parts); the FG projection (an `FGTrace` over the `(Σ, Λ)` parts) | — | `Consensus.Goldilocks.RunTrace.acLabel`, `Consensus.Goldilocks.RunTrace.fgLabel`, `Consensus.Goldilocks.RunTrace.projAC`, `Consensus.Goldilocks.RunTrace.projFG` |
| NoColl | CLAIMS §Premises (`NoColl`) | `NoCollOn` on the objects of the run: the blocks that occur in it and genesis (held from `Store.init`, not necessarily the object of a block call; the claims' `NoColl` is over all objects and C0.3 takes it, consensus-lean#73) | Persist | `Consensus.Goldilocks.Compose.NoCollRun` |
| F.5 (run) | CLAIMS F.5 (run) | the order facts (by time; restart < tick < delivery at one time; positions inside a tick; a send before its receipts); every run has them | Persist | `Consensus.Goldilocks.Compose.RunOrder`, `Consensus.Goldilocks.Compose.EventOrder` |
| F.4 | CLAIMS F.4 (D4) | awake on `[max(0, t − c − 1), t]` with `c + 1 ≥ 8Δ` gives awake and joined at `t`, for `t ≥ 0` (the interval is empty for `t < 0`; consensus-lean#73) | Persist | `Consensus.Goldilocks.Compose.ReadyImpliesJoined` |
| C0.5 | CLAIMS C0.5 (last sentence) | the AC projection is an `ACLocalRun` (with `U` the honest blocks; for an AC with requirements 1–5, since the own block's `ac_on_block` needs `ac_valid_payload`, consensus-lean#73); the FG projection is an `FGLocalRun` at `A.genesisPayload` (with the requirements and the genesis root, the premises of C0.3: the own block is accepted in its tick, so `own_first` holds; consensus-lean#73); the Goldilocks run's AC projection is an `SA.ACRun`; the states at the start of every event are `Node.Reachable`; `Sync` projects to `SyncAC`; joining and `h_t` project | Persist | `Consensus.Goldilocks.Compose.ACProjection`, `Consensus.Goldilocks.Compose.FGProjection`, `Consensus.Goldilocks.Compose.GoldilocksACProjection`, `Consensus.Goldilocks.Compose.GroupStatesReachable`, `Consensus.Goldilocks.Compose.SyncProjection`, `Consensus.Goldilocks.Compose.JoinedProjection`, `Consensus.Goldilocks.Compose.RunStatements` |
| C1.1 | CLAIMS C1.1 (premises), G1.10 ("The scope of C1.1") | the honest votes of a slot; the excluded entries 𝓔 (conflict with `B`, strictly extend an honest `Σ.F` at `t_s`); `Clean(s, m, B)` with (K0) caches, (K1) row cut `K1_𝓔` by `Store.namers` on the FG projection at `t_{s+1} + Δ`, (K2) height lead; the premises (writer honest and joined, a fast lock whose **stored** block (after the move back) is `B`, `Sync[t_s, t_m + Δ]`, `Carry`, half-committee, later `Carry`, `f < h_t` at honest vote times, `NoColl`, `Clean`) | Persist | `Consensus.Goldilocks.Compose.honestVotes`, `Consensus.Goldilocks.Compose.excludedEntries`, `Consensus.Goldilocks.Compose.Clean`, `Consensus.Goldilocks.Compose.StoredFastLockAt`, `Consensus.Goldilocks.Compose.PersistPremises` |
| C1.1 | CLAIMS C1.1 (conclusion), G1.10 (a)–(c) at C1.1's scope | G1.10's conclusion at the scope of C1.1, spelled out at a node for `(B, s, T)`: (a) justified roots on accepted chains compatible with `B`, (b) the height bound at the deepest common ancestor, (c) caches compatible at every cut in `[t_s, T + Δ)` and after the own proposal at `T + Δ`; the conclusion for a slot `s'`: (iii) the cut at `T = t_{s'} + Δ`, (i) viability at every honest vote, (ii) every honest vote extends `B` | Persist | `Consensus.Goldilocks.Compose.CutScopeAt`, `Consensus.Goldilocks.Compose.PersistAt` |
| C1.1 | CLAIMS C1.1 | **honest fast confirmations persist**; the corollary "recent source, next vote" | Persist | `Consensus.Goldilocks.Compose.HonestFastConfirmationsPersist`, `Consensus.Goldilocks.Compose.RecentSourceNextVote`, `Consensus.Goldilocks.Compose.PersistStatements` |

Modelling choices:

- **Cuts are component calls, grouped by top-level event.** The run records a tick, a delivery or a restart of an
  honest node as consecutive cuts with one `event` id, positions `0, 1, …`, and exactly the handler's cuts
  (`GroupAt`); a dropped future-slot block makes no cuts, so it is not an event. C0.4's order inside a tick is the
  position; the FG store's part 2 (`FGLocalRun`, #67) encodes the same order through FG calls, independent of `pos`.
- **The three `Node.Reachable` obligations are closed by `LocalRun`**: (i) `ticks_at_public` (an awake honest node
  ticks exactly once at every public time); (ii) `restart_after_sleep`/`wake_is_restart` (the first call after a
  gap in `awake` is a restart, and a restart is a wake: once per wake); (iii) `called_only_awake` (an asleep node
  has no cuts, so it receives nothing). **The awake clamp**: no honest node is awake after the run's last cut
  (`InHorizon`), the obligation recorded on workbench#5 for `ACLocalRun.restart_at_wake`. A consequence: `Healthy(g)`
  (awake on `[max(g, 0), ∞)`) forces an infinite run, and so does `Sleepy` (`f < h_t` at every slot's times needs
  `h_t > 0` forever); finite prefixes satisfy `Sync[a, b]` and `GST(g)` but neither regime. This is the intended
  reading (runs are `Nat`-indexed traces of the protocol running for ever, a tick at every public time); the kind
  (a) witness `periodicRun_localRun` with `periodicRun_healthy`/`periodicRun_sleepy` (`ConsensusLeanTest/GoldilocksRun.lean`)
  is an infinite periodic `Node.LocalRun` on which both regimes hold, so neither is vacuous against the clamp.
- **`GST(g)`'s "as if sent at `g`"** is read for the deadline only: an object sent at `τ < g` has deadline
  `max(g, w_y) + Δ'`, and its delivery lower bound stays `τ` (it may be delivered before `g`). Posted on goldilocks#7
  as a wording clarification for the claims.
- **Admissibility** (claims §"Runs"): unforgeability is a run law, not a node fact. The AC interface has no signer,
  so the signer of an AC message is a run parameter `sg`; `GoldilocksRun` fixes it as the vote's validator and adds
  carried-vote unforgeability (votes in a block's payload), which the generic node cannot state. The slot-key law
  on delivered blocks is the run law `LocalRun.proposerCredential`: a block delivered to an honest node names its
  slot's proposer, faulty proposers included (composition.tex §"Blocks": `B.proposer`'s slot key signs `B`; the
  paper's `state_transition` proposer assertion is not in the model's `state_transition`, `docs/decisions.md`
  2026-10-31). `SA.HonestObjects.proposer` (frame blocks) follows from it through the projection.
- **`Δ_F` is a parameter** of `SyncOn`/`SyncRun`/…, not a field of `Params`; its positivity `0 < Δ_F` (no order
  with `Δ`, two-bound network 2026-11-02) is a field of `SyncOn` (`deltaF`), so every premise built on it has it. `Sync` carries the acceptance-relay clause
  (`relay`), the own proposal as a send (`block`: accepted or own), and admissions from payloads (`SendOrAdmitAt`,
  mirroring `ACTrace.SendOrAdmit`). `GST(g)` is `SyncOn` on every time with `eff τ = max τ g`: only the deadline
  moves to `max(τ, g)`; the lower bound of the delivery interval stays the real send time `τ`. Its acceptance relay
  covers only acceptances at `τ ≥ g` (`SyncOn`'s relay window `Wr`, consensus-lean#96): `GST(g)` re-delivers old
  objects but does not make them accepted (a block refused for a missing parent is not delivered again), so pre-`g`
  acceptance catch-up is the regime premise `Catch(κ)`, as in the claims.
- **Integer time.** The run keeps `Time = Int` (the claims take continuous time): "processed at a time in
  `[τ, deadline)`" is over integer times, and F.4's bridge reads "awake at `u`" as awake throughout `(u − 1, u]`.
- **"The state of `y` at `t`"** is `y`'s state before the first cut of the run at a time `≥ t` (`FirstCutFrom`),
  which is also its state at the end of time `t − 1` when `y` has no cut at `t`. G1.10 (c)'s "on `[t_s, T + Δ)`"
  (`CutScopeAt.caches`) covers the cuts in the interval and its end, the state before the first cut at `T + Δ`.
- **`JoinedProjection`** relates the run's `JoinedAt` to the SA's `joined` on the state before a cut at `t`, except
  at a restart cut: a restart sets `restart_time` only in its post-state.
- **The corollary's `ac_to_fg` node is the lock writer `x`**: "`ac_to_fg` returns `B` … from a fast lock of slot
  `j`" is read at the node that holds that lock, the one whose lock C1.1's premises are about (confirmation of this
  reading in the claims requested from the spec orb on goldilocks#7; transcribed as read meanwhile).
- **C1.1's (iii)** is spelled out (`CutScopeAt`) rather than cited from FGStore: #67's `QuorumFreeEntries` is G1.10's
  core, not the C1.1 scope with its excluded-entry set. When FGStore states G1.10 at that scope, `CutScopeAt` should
  become its instance; the own-proposal clause (`caches_own`) is kept for fidelity to G1.10 (a)–(c) even where it is
  vacuous at `T = t_{s'} + Δ`.
- **AC-side notions over the AC projection**: votes, `Carry`, fast locks, `ac_to_fg`, viability at a vote are
  `SA.*` over `tr.projAC`; the run premises stay the run's, with `JoinedProjection`/`SyncProjection` bridging them
  to the AC projection's. The FG row cut is `Store.namers` over `tr.projFG`.

Witnesses in `ConsensusLeanTest/GoldilocksRun.lean`: on `rootAC`, kind (a) `oneTickRun_localRun` (the hypothesis
`Node.LocalRun` is satisfiable: one tick at time `0`, the two AC cuts `tickCuts_eq`); on `idleAC` (`rootAC` with
`ac_proposal = ⊥`), kind (a) `periodicRun_localRun`, `periodicRun_healthy`, `periodicRun_sleepy` (an infinite
periodic `Node.LocalRun`, a tick at every time, on which `Healthy(0)` and `Sleepy` hold: the regime premises are
satisfiable together with the awake clamp). The regime witness is over an AC that never proposes, not over
`GoldilocksRun`; a `Sleepy`/`Healthy` run of the SA itself is left to the Healing/Regimes milestone.

## Service

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `4ea71d05`, §"Available chain, after C1.1" (unchanged since
`688e287b`). Layout:
decomposition §3.1 (the "Run" row). Over the Goldilocks run under `Sleepy` and `NoColl` (the claims say only
"under `Sleepy`"; `NoColl` enters through their use of C1.1 and is made explicit). C1.2 (claims at goldilocks `6703bf05`) is
stated in `Statements/Healing/Outcome` (milestone Healing, its premises are the healing regime); C1.3 is in
`Statements/Healing/Recovery`.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| A1.6 | CLAIMS A1.6 | the update of a slot ran with no restart since; A1.6's condition at a cut (awake, joined, updated for `slot(t) − 2`); the record `𝒜.latest_confirmed` as a block of the frame's tree; **head extends the record**: the head extends the record in the frame, `ac_confirmed` is the record, and across served cuts the record extends | Service | `Consensus.Goldilocks.Compose.UpdatedNoRestart`, `Consensus.Goldilocks.Compose.ServedAt`, `Consensus.Goldilocks.Compose.RecordAt`, `Consensus.Goldilocks.Compose.HeadExtendsRecord` |
| A1.7 | CLAIMS A1.7 | **inclusion**: an honest proposal of slot `s` by a joined proposer is in the confirmed tip of every honest node awake and joined at `t ≥ t_s + 6Δ`, awake and joined at `t_s + 6Δ`, with no restart in `(t_s + 6Δ, t]`, that has run the update of slot `s` before the cut with no restart since (`UpdatedNoRestart`; at the boundary `t = t_s + 6Δ` the state before the tick's first cut predates that update, consensus-lean#77); with the genesis root its digest, as C0.3 (consensus-lean#73) | Service | `Consensus.Goldilocks.Compose.Inclusion`, `Consensus.Goldilocks.Compose.ServiceStatements` |
| C1.2 | CLAIMS C1.2 (goldilocks `6703bf05`, #37) | **AC outcome service**: under the healing regime after the reset (`HSShared`, `Catch(2Δ)`, `Prop⁺`, `a_z`), an entry whose block is an honest ready proposal from `R_z`, high (and with a high predecessor when bound), with retained ready inclusion, with `𝓕 = ⌈(6Δ + Δ_F)/(4Δ)⌉` and `δ_t ≥ 𝓕 + k_F`, gets by the end of its window a literal good window (`Store.GoodWindow` on the FG projection) or an accepted early justification (finalizing the predecessor when bound), its carrier relayed within `Δ` in both branches; an unbound entry is justified by then (stated in `Statements/Healing/Outcome`, next to its proof, since its premises are the healing regime) | Healing | `Consensus.Goldilocks.Compose.RunEntry`, `Consensus.Goldilocks.Compose.EarlyOutcome`, `Consensus.Goldilocks.Compose.OutcomeService` |

Modelling choices:

- **"At `t`" is at a cut of the node at time `t`**, with the state before the cut (`ac_head`/`ac_confirmed` take
  that cut's time). A1.6's "while both conditions hold" is "at every cut of the node from `i` to `i'`"; the record
  monotonicity is stated inside the honest blocks of the run, with the later record read as a block of the frame's
  tree (`RecordAt`), as the head clause.
- **A1.7's "has not restarted since `t_s + 6Δ`"** is "no restart cut in `(t_s + 6Δ, t]`" (a restart at `t_s + 6Δ`
  itself is excluded by `JoinedAt y (t_s + 6Δ)`, whose restarts are at or before `t_s`), together with `UpdatedNoRestart tr y i s`: the
  update of slot `s` (the AC tick at `t_s + 6Δ`) ran at a cut before `i` with no restart since. Without it the
  statement fails at `t = t_s + 6Δ`, at the cuts of that tick before the update (consensus-lean#77).

## Healing

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `48aca059` (draft 8, goldilocks#34; §"Healing: top-level
statements" and §"Healing: phase service" unchanged since `30ace044` apart from the H.2 (run) status (#36) and HR.3's evidence (#37, #40)). Layout: the run-level healing nodes HR.1–HR.4
are over the Goldilocks run (`Spec/Run`, `GoldilocksRun`), HR.2 over FG traces (`FGLocalRun`), in
`Statements/Healing/Run`, with H.2 (run), H.3 and H.4; H.1, its corollary and H.2, over driven AC traces of the SA, are
in `Statements/Healing/AC`. HS.1–HS.5 are not transcribed as separate statements yet: HS.0 (`Settle(Δ)`) and
HS.5's `Producer(A)` enter as conclusions (a), (b) of HR.3.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | CLAIMS HR.1 | "after all events at `t`" (the state before the first cut at a time `> t`); `c_z = t_{slot(ḡ)+3}`; `H_z`, the greatest honest `Σ.h_max` after all events at `c_z`; the reset `a_z`, the first time an honest validator signs an attestation of height `H_z + 1`; the honest accepted entries of heights `≥ H_z + 1` | Healing | `Consensus.Goldilocks.Healing.FirstCutAfter`, `Consensus.Goldilocks.Healing.cutZ`, `Consensus.Goldilocks.Healing.HZ`, `Consensus.Goldilocks.Healing.IsReset`, `Consensus.Goldilocks.Healing.HighEntries` |
| Premises | CLAIMS §"Healing: top-level statements" (the two premises), §"Healing: phase service" (shared premises, constants) | `Catch(κ)` over a run; no honest restart after `t`; `Prop⁺(G_p)` (honest joined proposal at a slot start in every `[τ, τ + G_p]`, `τ ≥ ḡ`, with its slot-`(s−1)` support references held by every honest node at `t_s + Δ`); the HS shared premises (`NoColl`, the genesis root, `Healthy(g)`, no restart after `ḡ`, `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`); `D`, `C`, `A` with `G = G_p` | Healing | `Consensus.Goldilocks.Healing.CatchRun`, `Consensus.Goldilocks.Healing.NoRestartAfter`, `Consensus.Goldilocks.Healing.ReadyProposal`, `Consensus.Goldilocks.Healing.PropPlus`, `Consensus.Goldilocks.Healing.HSShared`, `Consensus.Goldilocks.Healing.D_HS`, `Consensus.Goldilocks.Healing.C_HS`, `Consensus.Goldilocks.Healing.A_HS` |
| HR.2, HS | CLAIMS HR.2 (b), §"Healing: phase service" (phases, settled) | the effective phase over an FG trace at a cut: the frontier (greatest honest `Σ.h_max`), a justification at a height on an honest accepted chain, a contest against `J`, the three cases with their rank and top `J`, the phase `(m, c)`, a phase change; the evidence of a phase held by a store; **settled at `w`** (late enough, all joined, evidence held, pre-GST catch-up complete) | Healing | `Consensus.Goldilocks.Healing.FrontierAt`, `Consensus.Goldilocks.Healing.JustifiedAt`, `Consensus.Goldilocks.Healing.ContestAt`, `Consensus.Goldilocks.Healing.PhaseCase`, `Consensus.Goldilocks.Healing.PhaseCase.rank`, `Consensus.Goldilocks.Healing.PhaseCase.topJ`, `Consensus.Goldilocks.Healing.PhaseAt`, `Consensus.Goldilocks.Healing.PhaseChanged`, `Consensus.Goldilocks.Healing.HoldsEvidence`, `Consensus.Goldilocks.Healing.SettledAt` |
| HR.4 | CLAIMS HR.4 | a high origin (a fast-lock write at an honest joined node, stored block of state height `≥ H_z + 1`); (R1)–(R4) for the reset `a` | Healing | `Consensus.Goldilocks.Healing.HighOrigin`, `Consensus.Goldilocks.Healing.RetentionAt` |
| HR.1 | CLAIMS HR.1 (uses A1.5, G1.10 (K1)) | **cut and reset**: `c_z ≤ ḡ + 12Δ`; (a) rows up to `c_z` have height `≤ H_z`, sources from `c_z` on come from fast locks written after `ḡ`; (b) a chain of height `≥ H_z + 2` carries an honest row of height `H_z + 1`; (c) at the reset `a`: `a > c_z`, no high row before `a`, frontier `≤ H_z + 1` at the FG update of the ticks at `a`, rows at `a` of height `≤ H_z + 1`, K1's first clause at `T₀ = a − Δ` by `Store.namers`, rows at `a` in `(T₀, T]` | Healing | `Consensus.Goldilocks.Healing.CutAndReset` |
| HR.2 | CLAIMS HR.2 | **phase count**: over an `FGLocalRun` with `f < 2q − n`, (a) one justified entry per height, (b) the phase moves only forward with one `J` while `m` is fixed, at most two changes per `m` | Healing | `Consensus.Goldilocks.Healing.PhaseCount` |
| HR.3 | CLAIMS HR.3 (with HS.0, HS.5) | **reset existence**: (a) `c_z > ḡ + 8Δ` and `Settle(Δ)` from every `u ≥ c_z`; (b) `Producer(A)` from every settled `w`; (c) `a_z` exists, `a_z ≤ c_z + 6(Δ + A_HS) ≤ ḡ + 24Δ + 12C_HS`, with the closed forms | Healing | `Consensus.Goldilocks.Healing.ResetExistence` |
| HR.4 | CLAIMS HR.4 | **height-scoped retention**: (R1)–(R4) for every reset `a` | Healing | `Consensus.Goldilocks.Healing.HeightScopedRetention`, `Consensus.Goldilocks.Healing.HealingRunStatements` |
| — | CLAIMS §"Healing: top-level statements" (notation, driven AC traces, the two premises) | `ḡ`, `Θ = 4(k + 1)Δ`; `Healthy(g)` and `Catch(κ)` over an AC trace; trivial frames; an honest proposal of slot `p` (the block made from `ac_proposal`: parent the returned duty head, #83); a **driven** AC trace (assigned proposer, slot order, held parent, no future slot, honest slot = honest proposal; tick and proposal order of C0.4, including Driven (b)'s "before any object received at `t_s`": `proposal_first`, every AC message or block call of the proposer at its `ac_proposal`'s time comes after it, consensus-lean#105); `Prop(G_p)` | Healing | `Consensus.Goldilocks.SA.gbar`, `Consensus.Goldilocks.SA.Θ`, `Consensus.Goldilocks.SA.HealthyAC`, `Consensus.Goldilocks.SA.CatchAC`, `Consensus.Goldilocks.SA.TrivialFrames`, `Consensus.Goldilocks.SA.HonestProposal`, `Consensus.Goldilocks.SA.Driven`, `Consensus.Goldilocks.SA.PropAC` |
| H.1 | CLAIMS H.1 and corollary | **AC healing, standalone**: over driven traces with trivial frames, (i) an honest proposal with `t_p ≥ ḡ + 2Θ + 8Δ` gets every honest vote of its slot, (ii) it is in every honest confirmed tip from `t_p + 6Δ`; corollary under `Prop(G_p)` | Healing | `Consensus.Goldilocks.SA.ACHealingStandalone`, `Consensus.Goldilocks.SA.ACHealingStandaloneCorollary` |
| H.2 | CLAIMS §"Healing: top-level statements" (protected blocks, `Inv`, `Geo`), H.2 | a slow lock write (the lock block of `update_confirmation`, not the fast test's `D`); the protected pairs `𝒫(t₀)` (P1)–(P3); `Inv(t₀)`; `Geo(P)`; **AC inclusion**: under `Inv(t₀)`, (i) `Geo(P)` gives unanimity, (ii) unanimity gives inclusion from `t_p + 6Δ` | Healing | `Consensus.Goldilocks.SA.SlowLockAt`, `Consensus.Goldilocks.SA.Protected`, `Consensus.Goldilocks.SA.Inv`, `Consensus.Goldilocks.SA.Geo`, `Consensus.Goldilocks.SA.ACInclusion`, `Consensus.Goldilocks.SA.HealingACStatements` |
| H.2 (run) | CLAIMS H.2 (run) (uses C0.4, C0.5 (b)) | unanimity, honest proposal and inclusion over the AC projection; **AC inclusion in runs**: the projection is driven with `Healthy(g)`, `Catch(2Δ)`, and H.2's conclusions hold for the run | Healing | `Consensus.Goldilocks.Healing.Unanimous`, `Consensus.Goldilocks.Healing.HonestProposalRun`, `Consensus.Goldilocks.Healing.IncludedFrom`, `Consensus.Goldilocks.Healing.RunInclusion` |
| H.3 | CLAIMS H.3 | one settled effective phase for a proposal and its votes; the bridge `Inv(a_z + T_b)` + `Geo` in settled phases; **FG non-interference**: some `T_b ≥ 0` depending on `(n, Δ, Δ_F, k, δ_t)` only, with (a) `a_z ≤ ḡ + 24Δ + 12C_HS`, (b) (R1)–(R4), (c) the bridge | Healing | `Consensus.Goldilocks.Healing.InSettledPhase`, `Consensus.Goldilocks.Healing.BridgeAt`, `Consensus.Goldilocks.Healing.NonInterference` |
| H.4 | CLAIMS H.4 | `T_heal`; **available healing, assembled** (conditional on the bridge): (i) unanimous honest proposals after `T_heal` included, (ii) under `(U_B)`, (iii) under `(U_all)`, with the closed form of `T_heal` | Healing | `Consensus.Goldilocks.Healing.T_heal`, `Consensus.Goldilocks.Healing.AvailableHealing` |
| HS | CLAIMS §"Healing: phase service" (shared definitions) | the phase floor `ℓ` (`m` in a contest, `m − 1` otherwise); a block allowed in the effective phase geometry; the phase constant over a range of cuts (before the phase end `e`); the entry of a source's chain at a height; `a` and `r` from `w`; settled at `w` in a phase; a vote that extends `B` with `B` viable at it; a stored slow lock | Healing | `Consensus.Goldilocks.Healing.phaseFloor`, `Consensus.Goldilocks.Healing.EffAllowed`, `Consensus.Goldilocks.Healing.PhaseOn`, `Consensus.Goldilocks.Healing.EntryOf`, `Consensus.Goldilocks.Healing.slotA`, `Consensus.Goldilocks.Healing.rTime`, `Consensus.Goldilocks.Healing.SettledIn`, `Consensus.Goldilocks.Healing.VoteKeeps`, `Consensus.Goldilocks.Healing.StoredSlowLockAt` |
| HS.1 | CLAIMS HS.1 | **viable-witness retention**: a block allowed in the effective phase geometry is extended by every later honest `Σ.F` before `e`, stays in frame trees and allowed (or below `fc_root`), and its ancestors stay viable or below `fc_root`, also in the voter block tree when it is there | Healing | `Consensus.Goldilocks.Healing.ViableWitnessRetention` |
| HS.2 | CLAIMS HS.2 | **clean-lock transfer and drain**: fast locks of label `≥ a` and slow locks with `j − k + 1 ≥ a` (stored blocks) transfer to the next votes (with `Carry` for fast) and later votes unless below `fc_root`; live locks from `r` are clean; honest proposals from `r` follow every earlier-label live lock | Healing | `Consensus.Goldilocks.Healing.CleanLockDrain` |
| HS.3 | CLAIMS HS.3 | **frozen-tree agreement**: an honest ready proposal in a stable phase, with relay from the previous freeze and the lock premise, gets every honest vote of its slot with its ancestry retained; after `r` (settled, `Prop⁺`) without the lock premise, and later votes and proposal parents extend it | Healing | `Consensus.Goldilocks.Healing.FrozenTreeAgreement` |
| HS.4 | CLAIMS HS.4 | **common path and actual-report acquisition**: the phase ends by `w + D` or a unanimous honest proposal `W` at height `h ∈ {ℓ, m}` with every honest validator holding a source with its entry or a matching row by `v = t_s + 6Δ`, later votes and parents extending `W`; the client subclaim (P1/P2) | Healing | `Consensus.Goldilocks.Healing.CommonPathAcquisition`, `Consensus.Goldilocks.Healing.PhaseServiceStatements` |
| — | CLAIMS §"O.1" (draft 9: `Rec`, `UPat`, constants) | `⌈x/4Δ⌉` in slots; `b₀`, `L_old`, `r_old`, `M*`, `Z`, `T_rec`, `R_*`; the recovery predicate `Rec(t₀)` ((a), (c): C1.1's `Clean(s, m, B)` for every honest fast confirmation written after `t₀` and every `m > s`; (b): compatible honest sources after `t₀`, clean records at the first source of an entry entered after `t₀`); the pattern regime `UPat(W, M)` (with C1.2's `c_F`, `k_F`); C1.2's premises with `UPat` and `M ≥ M*` | Healing | `Consensus.Goldilocks.Healing.slotsCeil`, `Consensus.Goldilocks.Healing.acqSlots`, `Consensus.Goldilocks.Healing.L_old`, `Consensus.Goldilocks.Healing.oldSlots`, `Consensus.Goldilocks.Healing.Mstar`, `Consensus.Goldilocks.Healing.Zreset`, `Consensus.Goldilocks.Healing.T_rec`, `Consensus.Goldilocks.Healing.Rstar`, `Consensus.Goldilocks.Healing.Rec`, `Consensus.Goldilocks.Healing.UPat`, `Consensus.Goldilocks.Healing.PatternPremises` |
| O.1 (node) | CLAIMS node O.1 (draft 9; reviewed conditional assembly, workbench#27) | **recovery under a bounded uniform pattern**: `Rec(ḡ + T_rec)`, and high honest `Σ.F` from `T_F = ḡ + T_rec − 12Δ` (not O.1's target) | Healing | `Consensus.Goldilocks.Healing.PatternRecovery` |
| C1.3 | CLAIMS C1.3 (draft 9) | **recurring finalizing coverage**: from `R_*`, an honest proposal released in `[t, t + 4Δ(W + 1 + M)]` is ⪯ every honest `Σ.F` from `t + 4Δ(W + 1 + M) + Δ` | Healing | `Consensus.Goldilocks.Healing.FinalizingCoverage` |
| HR.5 | CLAIMS HR.5 (G1.9 (b) after the reset) | **cache acceptance after the reset**: an honest acceptance after `a_z` of a block whose `σ.F` is high puts it under `Σ.F` | Healing | `Consensus.Goldilocks.Healing.CacheAcceptanceAfterReset`, `Consensus.Goldilocks.Healing.RecoveryStatements` |

Modelling choices:

- **HR.2 is over FG traces, not runs.** The claims make it an FG store node over the FG component trace, and the
  phase reads only the honest `Σ`, which an `FGTrace` carries with the records, unforgeability and serialized
  clients of `FGLocalRun`; it sits with G1.4 (`Store.FinalizedSafety`), whose `f < 2q − n` it shares. Runs reach
  it through `Compose.FGProjection`; HR.3 reads the same phase on `tr.projFG`.
- **The effective phase is global**: frontier, justifications and contests are read on the blocks that some honest
  node has accepted by the cut (`σ` read at the holder), not on one node's `Σ.F`, `Σ.J` or local allowedness. So
  HR.2's "an advance of an honest `Σ.F` below `m` changes no phase" holds by definition, and HR.3's "advances of
  `Σ.F` below the frontier do not count" too. "Justified at `m − 1`" is `σ.h_j = m − 1` at some honest accepted
  block (every justification is the latest one of the block that makes it). "At most two changes per `m`" counts
  consecutive cuts with frontier `m` whose phases differ (`encard`, so an infinite count is not `0`).
- **Times.** "At `t`" is the state before the first cut at a time `≥ t` (`FirstCutFrom`), "after all events at `t`"
  the state before the first cut at a time `> t` (`FirstCutAfter`). `H_z` reads the latter at `c_z`. HS.0's
  "phase at `u`" is after all events at `u` and "settled at `w`" at `w`; HR.3 (b)'s "by `w + A`" is after all events
  at `w + A`. `HZ` is an `sSup`: under `Healthy(g)` the run is infinite, so the first cut after `c_z` exists.
- **`a_z`** is the least signing time of an honest attestation of height `H_z + 1`; it is a public time because
  honest signing happens only in ticks (a run law), so "first public time" is not repeated in `IsReset`.
- **HR.1 (a), sources**: A1.5's "the block of a fast lock written after `ḡ`" is: `C` is the block of a live fast lock
  of the node at the `ac_to_fg` call, of label `j`, and some fast-lock write of label `j` at that node after `ḡ`
  selected a descendant of `C` (locks move only back, A0.4 (c)).
- **HR.1 (c)**: K1's first clause is stated for every `𝓔` of honest accepted entries of heights `≥ H_z + 1`;
  "every row signed at `a` lies in `(T₀, T]`" is stated for every `T ≥ a`.
- **HR.4's stored block** is the selected block after the move back of `add_locks` (`viable_ancestor` in the
  writing call's frame), as C1.1's "stored block after the move back"; (R2) is read after every cut of an honest
  node at a time `≥ a` (its states from its tick at `a` on), for the origins written at that cut or earlier. (R1)'s
  "so these entries lie on one chain" is a consequence and not stated.
- **`Prop⁺(G_p)`**: "ready" and "support references accepted at every honest voter before its deadline" are read as
  `vote_ready`'s condition on the slot-`(s−1)` support entries (a block of slot `≤ s − 1` with that root) held by
  every honest node at `t_s + Δ`, the vote deadline.
- **HS parameter bounds**: of "the protocol's parameter bounds", `k ≥ 2` is in `SAParams` and `0 < Δ_F` in `SyncOn`;
  `δ_t ≥ x + 𝓕 + k_F` (with `x, k_F ≥ 0`, which `Params` does not carry) enters `HSShared` as its consequence
  `4Δδ_t ≥ 6Δ + Δ_F`. `R ≥ 𝓕` has no counterpart (the model attests in every tick).
- **Slots against `r_AC`, `s_AC`**: "`j ≥ r_AC(t₀)`" (the least slot with `t_r ≥ t₀ + 4Δ`) is `t_j ≥ t₀ + 4Δ`, and
  "`j − k + 1 ≥ r_AC(t₀)`" is `t_{j−k+1} ≥ t₀ + 4Δ` over integer slots; "`p ≥ s_AC(t₀)`" is `t_p ≥ t₀ + 2Θ + 8Δ`
  (slot times are increasing, so these are equivalent and no least slot is named).
- **`Inv`, `Geo`**: `filtered(Φ, Φ.tree)` is `Φ.viableTree Φ.tree` and `Φ.allowed` is `Φ.viableHeads`; the vote
  clause of `Inv` is viability in the voter block tree at every emission of the call. `Geo(P)` is read at every `ac_proposal` call of the
  proposer at `t_p`.
- **H.3 (c), H.4**: "a function of the parameters only" is a function of `(n, Δ, Δ_F, k, δ_t)` chosen before
  the run (`K_W = 2` is fixed; `k_F` and `x` are not model parameters), so not of `G_p` or the proposer schedule.
  H.4 is stated for any reset `a` and any `T_b ≥ 0` for which the bridge holds on the run, so it does not depend on
  the choice in H.3. "Lie in one effective phase in which every honest node is settled" is `InSettledPhase`: the run is
  settled (with `κ = 2Δ`) at some `w ≤ t_p` and the phase is constant on every cut from `w` through `t_p` and the
  last honest slot-`p` vote.
- **"`B ⪯ fc_root`" is block order** (consensus-lean#78), in `Inv` (inside `U`), HR.4 (R3), and C1.1's (K2) and (i)
  (inside `tr.HonestBlocks H`), not ancestry inside the frame tree (`Φ.Anc`, as in `SA.ViableAtVote`): once an
  honest `Σ.F` passes `B`, `B` leaves the frame tree and the frame reading fails. `tr.HonestBlocks H` holds every
  block of an honest node's accepted tree, faulty proposals included, so it contains the voter's `fc_root` (in its
  own `Σ.tree`) and `B`'s chain.
- **Genesis root** (consensus-lean#73): `HSShared` and H.2 (run) take `genesis.RootOk dg`, as C0.3 and A1.7 do. Without
  it an honest proposal whose digest is the genesis root is refused by every FG, so driven-trace clause (b) (H.2 (run)),
  the reset's existence (HR.3, H.3 (a)) and C1.2's window proposal can fail. HR.1, HR.2 and HR.4 conclude nothing about
  the acceptance of honest proposals and do not take it.
- **Confirmed tip**: "in every honest confirmed tip at every `t ≥ t₁`" (H.2 (run), H.4) is `IncludedFrom`:
  `ac_confirmed` after every AC call of an honest node at a time `≥ t₁`, with that call's frame. FG-only cuts
  (attestations) are not read separately; H.4's proof is H.2 (run) (ii), which the claims state the same way.
- **H.2 (run)** states both the bridge to H.2's premises (driven, `Healthy`, `Catch` on the projection) and the
  run conclusion, so that its proof is the bridge plus H.2 with `GoldilocksACProjection`.
- **HS.1–HS.4** (`Statements/Healing/Service`): "before the phase end `e`" is `PhaseOn` from the cut that fixes the
  phase (for HS.2–HS.4 the first cut at `w`); "label `j ≥ a`" is `t_j ≥ w + 4Δ`. Stored blocks (after the move back)
  for the fast and slow locks of HS.2, as in C1.1 and HR.4. "Follows every effective live earlier-label lock" (HS.2
  (3), HS.3's premise) is read at each honest slot-`s` vote: every live lock (`liveLocks`, moved back) of a label `< s`
  of the voter is below the proposal or at or below the voter's `fc_root`; so HS.2 (3) gives HS.3's premise. `Carry`
  in HS.2 (1), (2) is for the retained counted heads; HS.3 (a) and (b) both assume the run settled at `w` in the
  phase (`SettledIn`, as the claims' "HS.2–HS.5 assume that the run is settled at w"; #86 had it in (b) only), i.e. when `B` is not at or below the voter's `fc_root`. HS.3's
  "stable effective phase geometry on the compared events" is the phase constant from a cut at or before the previous
  freeze `t_{s−1} + 3Δ` (the voters' pre-freeze trees are compared) through every slot-`s` vote. HS.3 (a) also assumes that
  each voter starts at or below the proposer's unlocked anchor (every live lock of a label `< s` of the proposer after
  its `ac_proposal` at `t_s` is at or below a live lock block of the voter or its `fc_root`): a lock only the proposer
  holds otherwise starts the proposal walk below where lock-free voters stop (consensus-lean#100; claims HS.3,
  goldilocks#49). (b) needs no such premise: HS.2 puts every voter above every clean origin from `r`. HS.4's source "with
  entry `E`" has state height `h` (`fg_attest` signs at the source's own height), so a higher suppressing source does
  not count; it is current: returned in `[t_s, v]`, extending `W` and allowed in the phase geometry, so the client
  subclaim (b) applies to it (phase-service.md §5: every candidate at the update extends the fresh proposal, and a
  suppressing earlier report "occurred after P's creation, not in the archival prefix"; consensus-lean#88). HS.3's "acceptance relay from the previous freeze" is `t_{s−1} + 3Δ ≥ ḡ` (relay holds
  from `ḡ` under `Healthy`). HS.4's "by `v`" is at a cut at a time `≤ v`. HS.0 and HS.5's `Producer(A)` are HR.3
  (a), (b); HS.5's other conclusions (PhaseService, continuation, row delivery, consumption) are not transcribed yet.
- **Recovery** (`Statements/Healing/Recovery`): `UPat` is the regime node O.1 is proved under, not O.1's target, which
  stays open (claims §"O.1", Status). `Rec` (a) and (c) are C1.1's `Clean(s, m, B)` for every `m > s`, at every honest
  fast confirmation written after `t₀` by a joined node (`StoredFastLockAt`, of any label: a regular write of label
  `s` happens at `t_s + 6Δ`). `Rec` (b)'s served entry is read through the compatibility of the honest sources after
  `t₀` (part of `Rec`): an entry entered after `t₀` (slot start `> t₀`) is the entry at its height of such a source's
  chain. C1.3 is stated here (not in `Compose/Service`) because it shares `UPat` and the constants with node O.1, with
  its "accepted block whose state finalizes a block extending `P`". `W ≥ 1` is a premise (`PatternPremises`). `Rec`
  (b) covers every entry entered after `t₀` at a post-`t₀` honest source's height; it is the claims' served entry when
  the earliest honest source reaching `h` is after `t₀`. **Checked against node O.1's proof** (healing orb,
  2026-10-30, against §27 and workbench#27 `o1-section27-review.md` §4): for any such entry `E` the caller's cached
  high `F₀` at a call in `[T_F, t₀)` satisfies `F₀ ⪯ C` and `E ⪯ C`, and `E ⪯ F₀` is excluded (`t_{E.slot} > t₀`, no
  future blocks), so `F₀ ≺ E` and `h ≥ H_z + 1`; actual-source stored-origin provenance and whole-run HR.4 identify
  `E` with any earlier recorded root at `h`, so §16's record argument applies without asking that the earliest honest
  source reaching `h` be after `t₀`. An earlier pre-`c_z` source has height `≤ H_z` by `H_z`'s and the store's `h_max`
  monotonicity (not HR.1 (a), which bounds signed rows only). So the broader quantifier is covered under the
  conditional O.1 assembly and its imports; no narrowing is needed. `M*`'s ceilings are integer ceilings of slots of
  `4Δ`.
- **Witnesses** (`ConsensusLeanTest/GoldilocksHealing`): kind (a) for HR.2's premises and the phase vocabulary, and
  for `Catch` and `NoRestartAfter` with the run laws, and for `Healthy(0)` with `Catch` and `NoRestartAfter` on the
  infinite periodic `idleAC` run; arithmetic checks of `C_HS`, HR.3's bound and `T_heal`. No witness over Goldilocks
  traces for `HSShared`, `PropPlus` or the run statements (HR.1, HR.3, HR.4, H.2 (run), H.3, H.4), and none over
  driven SA traces for H.1/H.2: they need an infinite live run of the Goldilocks SA (a follow-up).

## Regimes

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `c6653258`, §"L2: regime theorems (skeleton)". Layout: the
run-level forms of the `GoldilocksTarget` rows, over the Goldilocks run (`GoldilocksRun`; `Compose.NoCollRun` only
where the target row allows the collision escape); the Refinement milestone carries them to the model system. R.7 and R.8 (no regime premise) are in
`Statements/Regimes/Always`; R.1 and R.2 (`Sleepy`) in `Statements/Regimes/Sleepy`; R.3 (healed, at a heal point
`T ≥ T_heal`) in `Statements/Regimes/Healed`; R.5 (`Outage`) in `Statements/Regimes/Outage`; R.6 (`Weak`) in
`Statements/Regimes/Weak`; R.4 (final, at a heal point `T ≥ T_heal`, `T ≥ ḡ + T_rec`, under `UPat(W, M)`) in
`Statements/Regimes/Final`.

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | CLAIMS R.7 (G1.5's binding), R.8 (`outputValid`) | the attestations on the chain of a block of a node's tree; a valid output (in the tree, chain linked to genesis, each non-genesis block with its digest as root, accepted by the node, with its slot's proposer and an earlier parent) | Regimes | `Consensus.Goldilocks.Regimes.ChainAtts`, `Consensus.Goldilocks.Regimes.ValidOutput` |
| R.8 | CLAIMS R.8 (uses C0.1, C0.2, F.2, F.3) | **`nested`**: finalized ⪯ confirmed ⪯ head at every honest cut; **`finalMonotone`**: the honest finalized tip moves only to descendants, across restarts; **`outputValid`**: the finalized and confirmed outputs are valid outputs of the node's tree | Regimes | `Consensus.Goldilocks.Regimes.OutputsNested`, `Consensus.Goldilocks.Regimes.FinalizedMonotone`, `Consensus.Goldilocks.Regimes.OutputsValid` |
| — | CLAIMS R.1, R.2 (the target's `Ready`, `gc`, `gProg`) | a read point, a point between a node's events, and the first cut after a time; the catch-up `18Δ` in the protocol's `Δ` (at the Refinement's `Δp = Δe + 1` it is `18Δe + 18`, not the target's `gc = 18Δe`); ready at `t` (honest, awake on `[max(0, t − c − 1), t]`); the confirmed read after all events at `t`; an honest proposal by a proposer ready at its release; one honest ready proposer in every window of `k` consecutive slots whose first slot starts after `a` and whose last slot starts by `b`; ready-reader safety (agreement and monotonicity) on the cuts of `[t₀, t₁]` | Regimes | `Consensus.Goldilocks.Regimes.CutAfter`, `Consensus.Goldilocks.Regimes.ReadPoint`, `Consensus.Goldilocks.Regimes.Boundary`, `Consensus.Goldilocks.Regimes.catchUp`, `Consensus.Goldilocks.Regimes.ReadyAt`, `Consensus.Goldilocks.Regimes.readAfter`, `Consensus.Goldilocks.Regimes.ReadyProposalAt`, `Consensus.Goldilocks.Regimes.ProposerRecurrence`, `Consensus.Goldilocks.Regimes.ReadySafeOn` |
| R.1 | CLAIMS R.1 (uses A1.2–A1.4, A1.6, C1.1, F.4) | **`sleepySafe`**: under `Sleepy`, ready-reader safety of the confirmed output on every cut; **`confirmed_safe_sleepy_prefix`**: `Sync[0, b − Δ]` (sends in `[0, b − Δ]`, not the model's `SyncUntil b`; see the modelling choices) and `f < h_t` at the slot points up to `b` give it on the cuts up to `b` | Regimes | `Consensus.Goldilocks.Regimes.SleepySafe`, `Consensus.Goldilocks.Regimes.SleepySafePrefix` |
| R.2 | CLAIMS R.2 (uses A1.7, F.4) | **`includeSleepy`**: honest ready proposals are in every ready confirmed read from `τ + 6Δ`; **`growSleepy`**: with one honest ready proposer per `k` slots, a new common confirmed entry by `t + (4k + 6)Δ`, above every ready read at `t` | Regimes | `Consensus.Goldilocks.Regimes.IncludeSleepy`, `Consensus.Goldilocks.Regimes.GrowSleepy`, `Consensus.Goldilocks.Regimes.SleepyStatements` |
| — | CLAIMS R.3 (heal point D1), H.4 (ii), (iii), H.3 (c) | `(U_all)` and `(U_B)` from `T` (H.4's open premises); the healing premises of R.3 at a heal point `T` (HS shared premises, `Catch(2Δ)`, `Prop⁺`, the reset, H.3 (c)'s bridge as a named hypothesis, `T ≥ T_heal`) | Regimes | `Consensus.Goldilocks.Regimes.UnanimousFrom`, `Consensus.Goldilocks.Regimes.UnanimousWithin`, `Consensus.Goldilocks.Regimes.HealedPremises` |
| R.3 | CLAIMS R.3 (uses R.1, R.2, C1.1, H.4) | at a heal point `T ≥ T_heal` (not the target's `gHeal`): **`healedSafe`** (ready-reader safety from `T`); **`includeHealed`** (under `(U_all)`); **`growHealed`** (under `(U_B)` with `B = 4kΔ` and the recurrence from `gReady`); cross-node ancestry dropped by owner (#104) | Regimes | `Consensus.Goldilocks.Regimes.HealedSafe`, `Consensus.Goldilocks.Regimes.IncludeHealed`, `Consensus.Goldilocks.Regimes.GrowHealed`, `Consensus.Goldilocks.Regimes.HealedStatements` |
| — | CLAIMS §"Premises" (`Outage(T, b₀, b₁)`), R.5; fgsa-protocol.tex "Outage continuation under (V)" | honest and recently awake; η-sleepy participation at `t` (`θ = ½`); more than half of all ready at `t`; the resilience reader; the outage times with the arming lag `(4k − 4)Δ` and (V) with `L = (4k − 2)Δ`; **`Outage`** over the run | Regimes | `Consensus.Goldilocks.Regimes.RecentlyAwake`, `Consensus.Goldilocks.Regimes.EtaSleepyAt`, `Consensus.Goldilocks.Regimes.ReadyOfAllAt`, `Consensus.Goldilocks.Regimes.ResilienceReader`, `Consensus.Goldilocks.Regimes.OutageWindowTimes`, `Consensus.Goldilocks.Regimes.OutageRun` |
| R.5 | CLAIMS R.5 (uses A1.2, A1.3, C1.1; (V)) | **`persists`**: under `Outage`, a ready read at `T` is an ancestor of every resilience reader's confirmed read from `b₀`; **`outageWindow`**: the same up to `b₁ − 1` with no premise after `b₀`; **`outage_final_compatible`**: compatible with every resilience reader's finalized read from `b₀` | Regimes | `Consensus.Goldilocks.Regimes.OutagePersists`, `Consensus.Goldilocks.Regimes.OutageWindow`, `Consensus.Goldilocks.Regimes.OutageFinalCompatible`, `Consensus.Goldilocks.Regimes.OutageStatements` |
| — | CLAIMS §"Premises" (`Weak`), R.6 | the ready-proposer premise on `[ḡ, T]`; **`Weak`** with the healing premises cut at the heal point `T ≥ T_heal` | Regimes | `Consensus.Goldilocks.Regimes.PropPlusUntil`, `Consensus.Goldilocks.Regimes.WeakPremises` |
| R.6 | CLAIMS R.6 (uses R.1–R.3) | at a heal point `T ≥ T_heal`: **`weakSafe`**, **`weakInclude`** (from `T + 8Δ`), **`weakGrow`** (recurrence from `T`); cross-node ancestry dropped by owner (#104) | Regimes | `Consensus.Goldilocks.Regimes.WeakSafe`, `Consensus.Goldilocks.Regimes.WeakInclude`, `Consensus.Goldilocks.Regimes.WeakGrow`, `Consensus.Goldilocks.Regimes.WeakStatements` |
| — | CLAIMS R.4 (heal point D1), node O.1, C1.3 | the final deadline `D_fin = 4Δ(W + 1 + M) + 2Δ` (C1.3's coverage deadline for the coverage requested at `t + Δ`); the premises of R.4 at a heal point `T`: R.3's `HealedPremises` (`T ≥ T_heal`), node O.1's and C1.3's `PatternPremises` (`UPat(W, M)`, `M ≥ M*`) and `T ≥ ḡ + T_rec` | Regimes | `Consensus.Goldilocks.Regimes.D_fin`, `Consensus.Goldilocks.Regimes.FinalPremises` |
| R.4 | CLAIMS R.4 (uses C1.3, G1.9, R.3, O.1's open target; here node O.1's regime) | at a heal point `T` (not the target's `gHealFin`/`finalCut`), deadline `D_fin` (not `W_W(gf)`): **`liveDC`** (an honest ready proposal released after `t`, a new finalized entry at `t + D_fin` above the ready confirmed reads at `t`; `finalRecur` is it without the proposal, `finalFirst` is `finalRecur` at `t = T`); **block form of `healthyLive` (final) / `finalized_txLive`** (a ready proposal released in `[t + Δ, t + Δ + 4Δ(W + 1 + M)]`, in every ready finalized read from `t + D_fin` on) | Regimes | `Consensus.Goldilocks.Regimes.LiveDC`, `Consensus.Goldilocks.Regimes.FinalInclude`, `Consensus.Goldilocks.Regimes.FinalStatements` |
| R.7 | CLAIMS R.7 (uses G1.3–G1.5) | **`finalAccountable`**: conflicting honest finalized tips convict `≥ 2q − n` validators from the attestations on two chains the readers hold; **`nonFraming`**: an honest validator signs no slashable pair; **`finalized_safe_below_third`**: with `f < 2q − n`, honest finalized tips never conflict | Regimes | `Consensus.Goldilocks.Regimes.FinalAccountable`, `Consensus.Goldilocks.Regimes.NonFraming`, `Consensus.Goldilocks.Regimes.FinalizedSafe`, `Consensus.Goldilocks.Regimes.AlwaysStatements` |

Modelling choices:

- **Reads** (R.1, R.2): a read is the confirmed output at a read point `(j, t)` (the state before cut `j` is the state
  at `t`), evaluated at `t` (`readAfter`): this covers the reads before each cut (`t = time j`, `confirmedAt`) and the
  read after all events at `t` (`CutAfter`, the model's end-of-time cut), so R.1 and R.2 speak of the same reads; "from
  `τ + 6Δ`" includes the update tick at `τ + 6Δ` (consensus-lean#77). `Ready` is the model's: honest and awake on
  `[max(0, t − c − 1), t]` with `c = 18Δ`. `Sleepy`'s `f < h_t` is read at the slot points (`SleepyRun`); the prefix
  form takes `Sync[0, b − Δ]` (`SyncRun H ΔF 0 (b − Δ)`) and those points up to `b`. That premise is not the
  model's `SyncUntil b` (sends with deadline `≤ b`), in three ways: it windows the **send** time and owes each
  delivery against the recipient's deadline `max(τ, w_y) + Δ'` (`Δ'` the object's class delay) at every later call, so it constrains the run after
  `b`; **late wakers**: a node that wakes at `w > b` must still process the window's sends by `w + Δ'`; and the
  deadlines **differ by class** (attestations `Δ_F`, the other objects `Δ`): for `Δ_F > Δ`, attestations sent in
  `(b − Δ_F, b − Δ]` have deadline `τ + Δ_F > b`, so the premise can require their processing after `b`, even by
  nodes awake throughout, and for `Δ_F < Δ`, some
  attestations due by `b` (those sent in `(b − Δ, b − Δ_F]`) are not covered. The row is proved as stated; this
  records what its premise assumes, not a counterexample (the finite form the Refinement uses is
  `sleepy_safe_finite`). `ProposerRecurrence` is over the windows of `k` consecutive slots whose first slot starts
  after `a` and whose last slot starts by `b` (the target's `(t, t + 4kΔ]`), and
  `GrowSleepy` takes it up to its read time only (the target's `gProg … 0 horizon`). `confirmed_txLive_sleepy` is not stated over the run (no
  transactions there): the Refinement derives it from `IncludeSleepy`.
- **Reads between AC calls** (checked 2026-10-30, consensus-lean#91). The confirmed output reads the AC state and
  the frame `fg_to_ac(Σ)`, and the frame reads only `Σ.T`, `Σ.F`, `Σ.J`, `h_max`, `h_j` and `σ`. Of the FG cuts,
  `fg_on_attestation` changes only the pool, `fg_attest` only the record and the pool, and a refused `fg_on_block`
  nothing; the only frame-changing FG cut, an accepted `fg_on_block`, is followed in the same event by its
  `ac_on_block` (`Node.onBlock`, `proposeBlock`). So **at a point between two events of a node** (`Boundary`; every
  `CutAfter` point is one) its AC state and frame are those after its last AC call, and the read differs from that
  call's read only through the time argument, whose thresholds are public times, at which an awake node ticks.
  Hence `IncludeSleepy`, `IncludeHealed` and `GrowSleepy` (reads after all events) are **not refuted** by FG-only
  events; their proofs need that lemma (a read after all events is the read after the last AC call, at the last
  public time), not a new argument about the protocol. **Inside an event**, after an accepted `fg_on_block` and
  before its `ac_on_block`, the frame already has the new block (and possibly a higher `F` or floor) while the AC
  has not processed it; no argument covers that state and the model never reads it (a model cut is a whole event),
  so `ReadySafeOn` is restricted to `Boundary` read points (a statement correction of #89, #90).
- **R.3's heal point** is a parameter `T ≥ T_heal` (H.4), not the target's `gHeal = max(g, 0) + (29 + B_H^F(k))Δ`:
  R.3 at `gHeal` stays open (docs/decisions.md, "Goldilocks instance", 2026-10-30). H.4's open premises are named
  hypotheses: H.3 (c)'s `BridgeAt` (in `HealedPremises`), unanimity from `T` for `includeHealed` and within `4kΔ`
  windows for `growHealed` (the `(U_all)`/`(U_B)` forms, used through H.4 (i) per proposal). Premises the target
  lacks: `Catch(2Δ)` and `Prop⁺(G_p)` (bridges B1–B3 of the claims' premises table), and `HSShared`'s parameter bound
  `6Δ + Δ_F ≤ 4Δδ_t` and genesis root. Open proof items (not premises): `RecRet` (`healedSafe`); the confirmed tip
  across FG-only frame changes between AC calls (`includeHealed` reads after all events, H.4 concludes at AC calls).
  `healthyLive` and `confirmed_txLive_healed` are derived in the Refinement from
  `includeHealed` (no transactions in the run).
- **Cross-node ancestry is dropped** (owner decision, consensus-lean#104): Baseline's `crossNest` and
  `weakCrossNest`, R.3's `CrossNest` and R.6's `WeakCrossNest` are removed, not restated with a lag.
  Cross-node compatibility follows from `HealedSafe`/`WeakSafe` and R.8's `OutputsNested` (C0.1):
  `F_x ⪯ C_x`, and compatible `C_x`, `C_y`, imply compatible `F_x`, `C_y`. Lagged ancestry is not stated.
  An honest proposer finalizes by accepting its own block inside its tick, and the other nodes receive that block up
  to `Δ` later. Evidence is the scripted grid (sa-fg-model `48a21ba`, `runs/crossnest-shape-grid.json`; replays
  n10 f3 s388 and n13 f4 s427 past `T_heal`, `Δ_F ∈ {Δ, 2Δ}`, carrier delay 0, one unit, latest legal): the
  same-instant form fails (94 / 189 read checks at the latest carrier time), with 0 failures of (1) same-instant
  compatibility and of (2) ancestry from `Δ` later; each reader extends the new `Σ.F` from its acceptance of the
  carrier, at most `Δ − 1` unit after `x`, and `updateFinality`'s gates never blocked. The 582 random n10/n13 sweep
  runs never reach the shape (it needs the boosted set chosen exactly), so they are not evidence for (2).
  This bounded evidence is not a proof of lagged ancestry and does not retain it as a target obligation.
- **R.5 (`Outage`)**: the claims replace the target's budget `b₁ − b₀ ≤ min(η, 4·lockK − 5)Δ` by (V),
  `b₁ − b₀ + ((b₀ − 6Δ) mod 4Δ) ≤ (4k − 2)Δ` (fgsa-protocol.tex: the old budget does not imply continuation after
  `b₁`), with the target's `lockK` read as the SA's `k` (D1) and the arming lag `(4·lockK − 4)Δ` kept. For `b₀` a
  multiple of `Δ` the target's budget implies (V) (the `mod` term is then `≤ 3Δ`); for other `b₀` the Refinement
  must relate them (open). `outageWindow` (the interval-only P1) takes `b₁ − b₀ ≤ (4k − 2)Δ` instead of (V), which
  the target's budget implies. Synchrony "before `b₀`" is `Consensus.Goldilocks.RunTrace.SyncBefore`:
  recipient protocol deadlines (including the latest wake) at most `b₀`, not the send window
  `Sync[0, b₀ − Δ]`, which would still require service after later wakes during the outage. The
  protocol deadline itself is cut off, not its last admissible integer processing time; the
  participation is the target's as of 2026-11-01: η-sleepy at every time (`θ = ½`, `η = eta·Δ`) and more than half
  ready at `b₀`. The target changed on 2026-11-02 (slow arming only: lag `4·lockK + 6`, no majority premise, the
  no-sleep window and cohort count, ready readers from `b₁ + 9Δ`; `docs/decisions.md`); the node-level R.5 is parked
  on the old premise.
- **R.6 (`Weak`)**: the heal point is `T ≥ T_heal`, as for R.3, and the healing premises are cut at `T`
  (`WeakPremises`: honest awake on `[ḡ, T]`, ready honest more than faulty from `T`, the ready-proposer premise on
  `[ḡ, T]`, plus R.3's); `weakInclude` and `weakGrow` also take H.4's open unanimity premises, as R.3 does. Its proof
  needs H.4 and R.3 in a form that uses `Healthy` and the ready-proposer premise only up to `T` (open; H.4 is stated
  under `Healthy(g)` and `Prop⁺(G_p)` on the whole run).
- **R.4 (final)**: the heal point is a parameter `T` with `T ≥ T_heal` (R.3's, for the confirmed reads that the new
  finalized entry must extend) and `T ≥ ḡ + T_rec` (node O.1's, so `Rec(T)` holds and C1.3 covers every window from
  `T`, since `R_* ≤ ḡ + T_rec`); the one deadline `D_fin` is C1.3's coverage requested at `t + Δ` (so the proposal is
  released after `t`, and after a transaction submitted at `t` has reached a ready proposer). **Premise the target
  lacks: `UPat(W, M)` with `M ≥ M*`** (and C1.2's `c_F`, `k_F`), the regime node O.1 is proved under, in place of the
  contract's finality recurrence `gProg .final gf`; plus R.3's (`Catch(2Δ)`, `Prop⁺`, the `δ_t` bound, the genesis
  root, H.3 (c)'s bridge). R.4 under the contract's premise needs O.1's target (open, claims §"O.1"); R.4 at the
  target's numbers (`gHealFin`, `finalCut`, `W_W(gf)`) stays open (docs/decisions.md). No unanimity premise: the rows
  cover one honest proposal per C1.3 window. `finalFirst` and `finalRecur` are not stated apart (with one deadline
  they are `LiveDC`'s consequences). The finalized read after all events at `t'` is covered because C1.3 concludes at
  every honest call from its deadline and an awake honest node calls again after `t'` (its state between calls is
  that of the next call). The transaction rows are the Refinement's, from `FinalInclude`.
- **Network model vs the spec's premises** (consensus-lean#92, #107): the owner chose delivery-time relay in
  the generic engine and protocol delay `Δ_p = Δ_e + 1`. The engine's inclusive delivery bound (`≤`) becomes
  the spec's strict processing deadline (`<`) with this one-unit slack; it absorbs only the endpoint, not
  relay latency. The spec treats admission as an instantaneous send. The model's persistent-relay variants
  still break R.1 when relay waits for an awake tick or is one unit late, so buffering across sleep or adding
  relay slack is not the chosen repair. `SyncOn` and `SyncAC` stay unchanged. The Refinement transport from
  `PSync`/`SyncUntil` to `GSTRun`/`SyncRun` remains to be proved with delivery-time relay and the chosen delay;
  this decision does not establish `PSync ⇒ GSTRun` at `Δ_p = Δ_e`.
- **Conflict** is incompatibility inside the honest blocks of the run (`tr.HonestBlocks H`), as in G1.4 and C1.1.
- **`finalAccountable`** reads "conflicting honest reads convict from their own views" (G1.5: "among the attestations
  included on the chains held by the two readers, taken together") as: some block of each reader's tree at the cut
  of its read, whose chains' attestations together hold a slashable pair for each convicted validator. The fraction
  is G1.3's `2q − n` (`≥ n/3`, G1.1); the contract's `α` is set by the Refinement.
- **`NoColl`**: R.8 and `nonFraming` are `HoldsAlways` rows (no collision escape), so they take no `NoColl` and read
  ancestry in the node's own tree; `finalAccountable` and `finalized_safe_below_third` take it.
- **`nonFraming`** is stated on honest signings. The target row itself follows from the model's `sysOf_nonFraming`; the
  run row serves the simulation (the engine's slashing guard is then a no-op).
- **`outputValid`**: the model's `Linked`/`PosIncreasing`/`Provenant` read as the output's chain in the node's tree
  linked to genesis with each block's root its digest (`RootOk`, for `Linked`), slots increasing, and each block
  accepted by the node with the slot's proposer (seen in a proposal role, for `Provenant`).
- **Witnesses** (`ConsensusLeanTest/GoldilocksWitness`, #69): the one-validator tick run (`n = 1`, `f = 0`, `Δ = 1`,
  awake and ticking at every time) is a `GoldilocksRun` (kind (a), `tickRun_goldilocksRun`) with `Sync` for every
  window, `Healthy(g)`, `Catch(κ)` and the HS shared premises (kind (a)), with a ready proposal at every slot `≥ 1`
  (`tickRun_readyProposal`) and `Prop⁺(G_p)` for `G_p ≥ 4Δ` (`tickRun_propPlus`). `HealedPremises`, `PatternPremises`
  and `FinalPremises` hold outright (`healedPremises_tickRun`, `patternPremises_tickRun`, `finalPremises_tickRun` in
  `GoldilocksWitnessRun`, W3; the run computed tick by tick in `GoldilocksWitnessChain`, `GoldilocksWitnessTicks`):
  the reset is `a_z = t_{slot(ḡ)+4}` (`tickRun_isReset`), H.3 (c)'s bridge holds with `Inv(t₀)` for every `t₀` and
  `Geo` required of no proposal, since each own block raises the frontier between its proposal and its votes, so no
  proposal lies in one settled effective phase (`not_inSettledPhase`; the witness does not exercise `Geo`, which fails
  on this run), and `UPat(1, M)` with its retained inclusion (`tickRun_upat`). `n = 1` shows the premises consistent,
  not met with faults (a faulty witness is a follow-up). R.7 and R.8 have no premise beyond the run laws (and `NoColl`, `f < 2q − n` where
  stated).

## Refinement

CLAIMS pin: `goldilocks-claims.tex` at goldilocks main `4ea71d05` (the Refinement row of the module table: "G1.5; the
engine simulates the node (C0.4 kept)"). SPEC pin: `shared/composition.tex` at goldilocks `4ea71d05` (§"Blocks",
§"Model"). Layout: decomposition §2 E (`Refinement`), §4.8. The milestone writes the Goldilocks node as a generic
`ChainShape` (`Refinement/Defs`) so that the engine (`Spec/Model/Run`) runs it and the generic L1 theorems apply, and
states that every valid engine run is simulated by a run of the spec's node (`Spec/Run`), with the evidence binding
G1.5. Goldilocks' `Params` needs `1 ≤ n`; the family keeps that dependence out of its types (`FamilyState`).

| Node | Reference | Definition | Milestone | Lean name |
|---|---|---|---|---|
| — | SPEC §Blocks (the wire format); decomposition §2 E | the output identifiers and schema (`confirmed` serves available and stable, `finalized` final); the `n`-independent wire forms of an attestation and a vote (the validator index as a number) with their encodings and decodings; a header's protocol data (attestations, votes, support votes) and its decoding; the signed bodies (a vote, an attestation) and the unsigned relay wrapper; the wire objects (no committee kinds) | — | `Consensus.Goldilocks.Refinement.Out`, `Consensus.Goldilocks.Refinement.schema`, `Consensus.Goldilocks.Refinement.WireAtt`, `Consensus.Goldilocks.Refinement.WireVote`, `Consensus.Goldilocks.Refinement.Info`, `Consensus.Goldilocks.Refinement.encodeAtt`, `Consensus.Goldilocks.Refinement.decodeAtt`, `Consensus.Goldilocks.Refinement.encodeVote`, `Consensus.Goldilocks.Refinement.decodeVote`, `Consensus.Goldilocks.Refinement.encodeInfo`, `Consensus.Goldilocks.Refinement.decodeInfo`, `Consensus.Goldilocks.Refinement.Body`, `Consensus.Goldilocks.Refinement.Wire` |
| — | SPEC §Blocks (signatures: the slot key signs a block, a validator its votes and attestations); CLAIMS G1.5 (`conflicts`) | the canonical objects: a vote and an attestation signed by their validator in the `.poll` role, a block's header signed by its proposer in its slot's proposer role **carrying** the canonical objects of its payload (`payloadObjs`), so that the engine can release blocks that carry them and a reader's view contains the evidence; the slashing rule `conflicts` (E1/E2 on two canonical attestation objects); the decoders of canonical objects (a received object is processed only in canonical form, anything else dropped) and the node event a received object stands for | — | `Consensus.Goldilocks.Refinement.voteObj`, `Consensus.Goldilocks.Refinement.attObj`, `Consensus.Goldilocks.Refinement.payloadObjs`, `Consensus.Goldilocks.Refinement.blockObj`, `Consensus.Goldilocks.Refinement.conflicts`, `Consensus.Goldilocks.Refinement.decodeBlock`, `Consensus.Goldilocks.Refinement.decodeVoteObj`, `Consensus.Goldilocks.Refinement.decodeAttObj`, `Consensus.Goldilocks.Refinement.canonEvent`, `Consensus.Goldilocks.Refinement.delivered` |
| F.3 | SPEC §Blocks (the root is the digest of the content); CLAIMS §Premises (`NoColl`) | the digest from the engine's hash with the genesis root `g`: genesis (no parent) has root `g`, any other block's root is the hash of its header, whose parent reference is `.root` for `g` and `.digest r` otherwise (so a header naming genesis by digest is dropped and every processed block is `RootOk` by construction); the digest of a header among those the engine passed; a block's header; the block of a header with its digest | — | `Consensus.Goldilocks.Refinement.parentRef`, `Consensus.Goldilocks.Refinement.parentRoot`, `Consensus.Goldilocks.Refinement.dgOf`, `Consensus.Goldilocks.Refinement.rootOf`, `Consensus.Goldilocks.Refinement.headerOf`, `Consensus.Goldilocks.Refinement.blockOf` |
| C0.4 | CLAIMS C0.4 (the steps at a public time); SPEC §Model (the engine) | **the shape**: slots of `4Δ_p`, the proposer chosen by the run at each slot (`.sized 1`; `runProposer` names it), everyone in the poll role, no committee kinds, the step order `[poll, poll, pollPropose, propose, poll, poll]` (two polls release the bodies queued since the last tick, so a proposal carries only released objects; the poll proposal step is the node's tick `ac_on_tick` at the public times, a duty so that it runs only awake; the slot proposal is `ac_proposal` with the own `on_block` on release; the first trailing poll runs the FG update `ac_to_fg` then `attest`, the trailing polls drain the tick's vote and attestation); the shape's state (own key, node state `(Σ, 𝒜, Λ)`, the clock, the outbox, the relay queue, the FG update due); emissions as bodies; a handler's result applied; relay queueing; processing a received object and a delivery; recording an own released object; the node's tick; the slot proposal; the FG update; a poll step; the chain of headers to a block; the output chains (`finalized` is `Σ.F`, `confirmed` is `ac_confirmed`); a restart (`durable` is the identity, so everything is durable and the queued bodies are kept; the paper's durable set, CLAIMS §Objects "Durable" (D4: Λ, Σ, the locks and the latest confirmation), is `restore ∘ durable`, through `ac_restart`); the shape | — | `Consensus.Goldilocks.Refinement.skeleton`, `Consensus.Goldilocks.Refinement.State`, `Consensus.Goldilocks.Refinement.emitted`, `Consensus.Goldilocks.Refinement.apply`, `Consensus.Goldilocks.Refinement.relayIf`, `Consensus.Goldilocks.Refinement.processOne`, `Consensus.Goldilocks.Refinement.process`, `Consensus.Goldilocks.Refinement.recordOwn`, `Consensus.Goldilocks.Refinement.nodeTick`, `Consensus.Goldilocks.Refinement.propose`, `Consensus.Goldilocks.Refinement.fgUpdate`, `Consensus.Goldilocks.Refinement.poll`, `Consensus.Goldilocks.Refinement.chainTo`, `Consensus.Goldilocks.Refinement.outOf`, `Consensus.Goldilocks.Refinement.restore`, `Consensus.Goldilocks.Refinement.goldilocksShape` |
| — | SPEC §Parameters; decomposition §2 E | the setup (the parameters not fixed by `pub`: the genesis root, `δ_t`, `k ≥ 2`, the replay order); the SA parameters at `pub` with `n ≥ 1`; the family's state (a Goldilocks state at every proof of `1 ≤ n`); **the family** | — | `Consensus.Goldilocks.Refinement.Setup`, `Consensus.Goldilocks.Refinement.Setup.params`, `Consensus.Goldilocks.SA.SAParams.pub`, `Consensus.Goldilocks.Refinement.Blk`, `Consensus.Goldilocks.Refinement.FamilyState`, `Consensus.Goldilocks.Refinement.family` |
| C0.4 | CLAIMS §Refinement ("the engine simulates the node (C0.4 kept)") | the vocabulary of the simulation: the honest keys of a run; the node's digest in a run; the shape's state at an engine cut; the time of the node's last tick or restart; an object released at its emission time (`ReleasedFrom`, including delivery-time votes); an admitted object relayed in a wrapper at that exact admission time (`RelayedFrom`, even at the horizon, without a future-awake escape); the node cuts of a delivery (`DeliverSeq`: one group per canonical object, none for a dropped one or for a canonical one whose handler makes no cut, a future-slot block) | — | `Consensus.Goldilocks.Refinement.honestKeys`, `Consensus.Goldilocks.Refinement.digestOf`, `Consensus.Goldilocks.Refinement.stateAt`, `Consensus.Goldilocks.Refinement.lastClock`, `Consensus.Goldilocks.Refinement.ReleasedFrom`, `Consensus.Goldilocks.Refinement.RelayedFrom`, `Consensus.Goldilocks.Refinement.DeliverSeq` |
| C0.4 | CLAIMS §Refinement; C0.4; F.5 (run) | **the engine simulates the node**: a `GoldilocksRun` at the engine's digest for the honest keys and a monotone cut map `ι` (from `0`) with: the node state inside the shape's state agrees at every engine cut; the clock is the last tick or restart; a tick at a public time is the node's tick with the engine's input (the encoded mempool), one group, a tick at a non-public time has no cut; a delivery is the groups of its canonical objects in order; a restart is a restart group; every labelled node cut is in an engine event's range; awake agrees up to the spec's horizon clamp; own blocks released at their proposal time, votes and attestations from their emission, admitted blocks, votes and attestations relayed; every valid run (`ExecutionValid`) has one | Refinement | `Consensus.Goldilocks.Refinement.Simulates`, `Consensus.Goldilocks.Refinement.EngineSimulatesNode` |
| — | CLAIMS §Outputs | the chain trace reads the shape's outputs of the node state at the shape's clock | Refinement | `Consensus.Goldilocks.Refinement.ReadIsOut` |
| NoColl | CLAIMS §Premises (`NoColl`); F.3 | tagged roots make `GenesisFresh` unconditional; **`NoColl` transport**: a valid engine run with no observed hash collision gives `NoCollRun` over its canonical trace, not arbitrary simulation witnesses; the engine run and provenance suppliers it uses are proved (no `sorry` remains under `Refinement`) | Refinement | `Consensus.Goldilocks.Refinement.GenesisFresh`, `Consensus.Goldilocks.Refinement.NoCollTransport` |
| G1.5 | CLAIMS G1.5 (targets `nonFraming`, `finalized_accountable`) | (a) `conflicts` holds exactly of the canonical objects of two `slashable` attestations; (b) every attestation included on an honest finalized read is in the reader's view as its canonical object; (c) in a valid run with no observed collision, two honest finalized reads are compatible or at least `2q − n` validators are slashable on the two views together (the run-level G1.3; the evidence is the two whole views, as in the generic L0 `convicts`, so (c) is weaker than G1.5, which takes the attestations included on the two chains; a chain-restricted form would be a separate statement); `nonFraming` is the generic `System.NonFraming` of the compiled family (Lemmas `sysOf_nonFraming`); the bundle | Refinement | `Consensus.Goldilocks.Refinement.ConflictsIff`, `Consensus.Goldilocks.Refinement.EvidenceInView`, `Consensus.Goldilocks.Refinement.FinalizedAccountable`, `Consensus.Goldilocks.Refinement.RefinementStatements` |
| — | CLAIMS §Refinement (the acceptance endpoint) | **Goldilocks Accepted**, the concrete endpoint: for every setup and every assumption set (a row ratio `r ≥ 1` and the timeout `3·cF r ≤ δ_t`, `cF r = ⌈(r + 6)/4⌉`), the family is `Accepted` at the contract `acceptanceContract A (accepted_coefficients S A)` (standard thresholds; row ratio `r` (healthy: `ΔF ≤ r·Δ`); arming lag `8k + 12`, outage budget `4k − 6`, `η = 0`, no-sleep margin `max 38 (8k + 16)`, recovery delay `18`; final progress the window `[0, c, 2c, 3c]`, `c = cF r`, one proposer otherwise; catch-up `max 37 (8k + 4)`, heal `max 37 (8k + 4) + 128k + 112δ_t + 160X + 187` at every capability, latency `8X + 12` (available, stable) and `8(X + 3·cF r) + 2` (final)) | Accepted | `Consensus.Goldilocks.Refinement.finalWindow`, `Consensus.Goldilocks.Refinement.AcceptanceAssumptions`, `Consensus.Goldilocks.Refinement.AcceptanceCoefficients`, `Consensus.Goldilocks.Refinement.acceptanceContract`, `Consensus.Goldilocks.Refinement.accepted_coefficients`, `Consensus.Goldilocks.Refinement.AcceptedEndpoint` |

Modelling choices (`docs/decisions.md` §"Goldilocks instance", the Refinement entries):

- **The wire format and the digest are the refinement's.** composition.tex fixes the signatures and that the root is
  the digest of the content, not an encoding; the refinement chooses an `n`-independent encoding (the family fixes
  one body type for every parameter set), canonical objects, and a digest from the engine's hash with the genesis
  root as a parameter (the engine hashes only headers, so genesis, which has none, keeps its root; a header naming
  genesis by digest is dropped, so `RootOk` holds of every processed block by construction).
- **Blocks carry their payload's objects.** The engine releases an object only if it has seen everything it
  carries, and a reader's view is the closure of what it saw; carrying the canonical attestation and vote objects
  makes G1.5 (b) hold (the evidence is in the view) and lets a node carry on votes and attestations it saw.
- **The node's tick is a duty, not the clock.** The engine's `clock` runs while asleep and only keeps the time; the
  spec's tick runs only awake (`tick_of_awake`), so it is the poll proposal step at the public times. The release
  of queued bodies is the shape's own, through poll steps; the two leading polls make a proposal carry only
  released objects (the spec has no release step).
- **Not stated: the network premises' transport.** The engine's `Delivers` bounds a receipt by `max(a, g) + Δ`
  (`≤`) where the spec requires processing strictly before `max(τ, w_y) + Δ'`, and reads an admission as an
  instantaneous send (`SendOrAdmitAt`). The owner decision in consensus-lean#107 is delivery-time relay in the
  generic engine and `Δ_p = Δ_e + 1`: only the inclusive-to-strict endpoint consumes the extra unit, never
  relay delay. The transport `PSync`/`SyncUntil` → `GSTRun`/`SyncRun` is still a proof obligation under that
  choice; `SyncOn` and `SyncAC` are unchanged. The earlier next-tick `+1/+2` analysis is superseded, not a
  transport theorem.
- **The proposer selection is the run's.** The generic skeleton's proposer selection is per slot
  (`proposerSel : Slot → SelSpec n`, consensus-lean#93); the Goldilocks skeleton sets it to `.sized 1` at every
  slot (consensus-lean#117, ac3e8d5c: the runtime has no proposer schedule), so a valid run selects one proposer
  per slot, named by `runProposer` (kind (a) witness `selValid_proposer`,
  `ConsensusLeanTest/GoldilocksRefinement.lean`; `selValid_exists` shows `SelValid` is satisfiable). The earlier
  hypothesis `SelIs` is gone.
- **The simulating run is built from the engine run.** The proof of `EngineSimulatesNode`
  (`Lemmas/Refinement/`) does not choose the node run existentially: every event of an honest node is replayed
  through `Node.exec` on the node state the engine holds before it, and the handler's cuts with their post-states
  are the trace's cuts (`simTrace`); the cut map counts the cuts of the earlier events (`cutMap`). The trace's awake
  function is the environment's clamped to `[0, ∞)` and to the trace's horizon, so `awake_to` and
  `awake_in_horizon` hold by construction. The steps are named theorems, all proved: the shape's pure facts (`Shape`:
  the decoders invert the canonical objects, `conflicts` is E1/E2, `protects` passes blocks and votes), the engine
  side (`Steps`: the node state across each event, the clock, at most two bodies pending at a tick, a proposal
  carries only released objects, `protects` passes an honest node's own attestation, the digests cover a block's
  header), and one theorem per field of `GoldilocksRun` and `Simulates` over the trace (`Run`); `Simulation`
  assembles them (`engineSimulatesNode`).
- **Not linked: the Baseline target and the refinement family.** `GoldilocksTarget F pp` requires
  `GoldilocksBindings F` (the skeleton is `goldilocksSkeleton`, over `goldilocksSchema`); `family S` has its own
  schema and a skeleton that differs in `Kind`, `pollSel` and `order` (its `proposerSel` is `.sized 1` since #117, so
  it would fit a `.recur` requirement), so no Baseline row is instantiated at the refinement family, and nothing in
  Lemmas or Proofs does so. The milestone statements are stated directly over `compiled (family S)`; whether
  Baseline is restated at the refinement skeleton (and its `.recur` rows through the instance's ready-proposer
  premise) is the first-slice re-review's decision (consensus-lean#10, #38).

## Exclusions

What the model leaves out, and why. Generic exclusions (static adversary, equal weights, one `Δ`, no
responsiveness claim, no transaction validity, …) are in README "Scope". For the baseline, the sheet's module
docstring (`ConsensusLean/Instances/Goldilocks/Statements/Baseline.lean`) lists the intended properties not yet stated
(§3), those stated weaker than intended, and the migration obligations. Known differences between the baseline
and SPEC (issue #38): lock lifetime and outage budget, FG attestations after every tick instead of once per
round, and the loose-BJ bounds (`K_W = 2`, general `Δ_F`). The first slice replaces this paragraph with one row
per exclusion: what is left out, why, and which claim it affects.

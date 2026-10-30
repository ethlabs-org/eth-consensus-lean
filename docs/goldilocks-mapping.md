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

Nothing cited yet; the milestone's statements PR fills this section.

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

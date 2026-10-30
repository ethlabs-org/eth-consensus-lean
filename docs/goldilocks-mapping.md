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

## Exclusions

What the model leaves out, and why. Generic exclusions (static adversary, equal weights, one `Δ`, no
responsiveness claim, no transaction validity, …) are in README "Scope". For the baseline, the sheet's module
docstring (`ConsensusLean/Instances/Goldilocks/Statements/Baseline.lean`) lists the intended properties not yet stated
(§3), those stated weaker than intended, and the migration obligations. Known differences between the baseline
and SPEC (issue #38): lock lifetime and outage budget, FG attestations after every tick instead of once per
round, and the loose-BJ bounds (`K_W = 2`, general `Δ_F`). The first slice replaces this paragraph with one row
per exclusion: what is left out, why, and which claim it affects.

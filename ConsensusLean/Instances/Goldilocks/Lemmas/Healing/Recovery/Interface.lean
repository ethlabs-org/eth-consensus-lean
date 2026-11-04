module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Goldilocks Recovery: shared duty and coverage proof obligations

These `Prop` structures fix the obligations without assuming proofs or introducing `sorry`.
Implementations belong in separate Recovery modules; none of the structures is an
extra premise of the public Recovery statements.

* The C1.2 lane supplies `ReadyProposalReportSupply` and the existing exact
  `Compose.OutcomeService`. A higher report is not yet an `EarlyOutcome`: excluding an early
  timeout, extracting the actual justification and proving the predecessor gate and strict
  carrier acceptance remain obligations of that lane. No stronger timeout is assumed here.
* The C1.3 lane supplies `PatternCoverageSupply`: acquisition, retained old-entry crossing,
  service of the new entry and its actual successor, and propagation to honest caches. The
  witness keeps the acquired proposal's high height, which public `FinalizingCoverage` omits.
* The O.1 lane supplies `Rec` from permanent high finality (`rec_of_high_finality`). Its
  internal R1–R5 split is late stored-write highness (including vetoed writes), historical K0/K1
  and frozen-domain K2, source compatibility, new ancestral-entry highness, and record equality.
  No source-height or earliest-global-source restriction may replace `Rec.records`. Catch-up is
  not needed by this lane's interface.

The shared seam is high finalized caches at honest pre-call states. At `t = Rstar`, the
coverage deadline is `gbar g + T_rec - 12Δ`; O.1 then uses the unchanged `12Δ` margin.
There is no Healing-to-Refinement import. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- Every honest pre-call finalized cache is above the pre-reset height bound from `T` on. -/
structure HighFinalityFrom (g T : Time) : Prop where
  at_call : ∀ y ∈ H, ∀ k, tr.IsCall y k → T ≤ tr.time k →
    HZ tr H g + 1 ≤ ((tr.state y k).fg.σ (tr.state y k).fg.F.root).h

/-- Actual report coverage of a post-drain ready proposal, with the same disjunction as
`report_cover_of_compatible_floors` but without its unproved `hcuts` input. Historical reports
are allowed: the deadline is inclusive and there is deliberately no lower time bound. -/
structure ReadyProposalReportSupply (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a : Time) : Prop where
  report_cover : ResetPremises tr H proposer dg g ΔF a → CatchRun tr H g (2 * sp.Δ) →
    ∀ (p : Fin sp.n) (k u : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H proposer p k u P → drainTime sp a ≤ sp.ts u →
      (∀ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C) ∨
      ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧
        tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h

/-- Fresh finalizing coverage after a request `t`, retaining the acquired proposal's high
height and permanent high cached finality. `duration` excludes the final relay allowance `Δ`.
The carrier is an actual acceptance, not a delivery or an assumed replay of a refused update. -/
structure HighCoverageAt (g t duration : Time) : Prop where
  witness : ∃ (q : Fin sp.n) (kP : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))),
    q ∈ H ∧ tr.ProposesAt q kP P ∧ t ≤ sp.ts P.slot ∧ sp.ts P.slot ≤ t + duration ∧
    (∃ iP, tr.AcceptAt q iP P ∧
      HZ tr H g + 1 ≤ ((tr.post iP).fg.σ P.root).h) ∧
    (∃ x ∈ H, ∃ kX X, tr.AcceptAt x kX X ∧ ∃ Fx ∈ (tr.post kX).fg.tree,
      Fx.root = ((tr.post kX).fg.σ X.root).F ∧ Anc (tr.HonestBlocks H) P Fx) ∧
    ∀ y ∈ H, ∀ k, tr.IsCall y k → t + duration + sp.Δ ≤ tr.time k →
      Anc (tr.HonestBlocks H) P (tr.state y k).fg.F
  high_finality : HighFinalityFrom tr H g (t + duration + sp.Δ)

/-- Lane A's bounded coverage obligation under exactly the public pattern premises. The
four-anchor stronger timeout regime is not substituted for `cF + kF ≤ δt`. -/
structure PatternCoverageSupply (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF Gp : Time)
    (W M cF kF : Nat) : Prop where
  coverage : GoldilocksRun proposer dg H tr →
    PatternPremises tr H proposer dg g ΔF Gp W M cF kF →
    ∀ t, Rstar sp g ΔF Gp ≤ t →
      HighCoverageAt tr H g t (4 * sp.Δ * ((W : Time) + 1 + M))

end Consensus.Goldilocks.Healing.Recovery

end

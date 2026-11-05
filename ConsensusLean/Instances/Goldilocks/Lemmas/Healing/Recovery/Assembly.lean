module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.FromHighFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: assemble the public statements from high coverage

The coverage proof supplies the fresh proposal, actual finalizing carrier and permanent high
cached finality. C1.3 forgets the proposal's high-height witness; O.1 applies that coverage at
`Rstar`, then uses recovery from high finality with the unchanged `12Δ` margin. HR.5 is already
proved independently. The coverage supplier is an explicit argument, not an added axiom. -/

namespace Consensus.Goldilocks.Healing

/-- The recovery statements of milestone Healing (HR.5, node O.1, C1.3): proof packaging, since
`Challenge` states each field on its own. -/
structure RecoveryStatements : Prop where
  cacheAcceptance : CacheAcceptanceAfterReset
  patternRecovery : PatternRecovery
  finalizingCoverage : FinalizingCoverage

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

/-- The strengthened coverage supplier discharges all three public Recovery statements.
The supplier remains an explicit proof input until the coverage proof is complete. -/
theorem recovery_statements_of_coverage
    (hcoverage : ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (proposer : Nat → Fin sp.n)
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time) (W M cF kF : Nat),
      PatternCoverageSupply tr H proposer dg g ΔF Gp W M cF kF) :
    RecoveryStatements := by
  refine ⟨cache_acceptance_after_reset, ?_, ?_⟩
  · intro sp ro proposer dg H tr g ΔF Gp W M cF kF hrun hp
    have hc := (hcoverage sp ro proposer dg H tr g ΔF Gp W M cF kF).coverage
      hrun hp (Rstar sp g ΔF Gp) le_rfl
    obtain ⟨a, hr, -, -⟩ := pattern_reset hrun hp
    let T := Rstar sp g ΔF Gp + 4 * sp.Δ * ((W : Time) + 1 + M) + sp.Δ
    have hΔ := sp.toParams.hΔ
    have hk : (0 : Time) ≤ sp.k := Nat.cast_nonneg _
    have hδ : (0 : Time) ≤ sp.toParams.δt := Nat.cast_nonneg _
    have hGp := pattern_Gp_nonneg hp
    have hΔF := hp.shared.healthy.1.deltaF
    have hZ : 0 ≤ Zreset sp ΔF Gp := by
      simp only [Zreset, C_HS, D_HS]
      nlinarith
    have hwindow : 0 ≤ 4 * sp.Δ * ((W : Time) + 1 + M) := by positivity
    have hgT : gbar g ≤ T := by
      dsimp only [T, Rstar]
      nlinarith
    have htime : T + 12 * sp.Δ = gbar g + T_rec sp ΔF Gp W M := by
      dsimp only [T, Rstar, T_rec]
      ring
    refine ⟨?_, fun y hy k hcall hlate => ?_⟩
    · rw [← htime]
      exact rec_of_high_finality hr hgT hp.shared.noRestart hc.high_finality
    · apply hc.high_finality.at_call y hy k hcall
      change T ≤ tr.time k
      linarith
  · intro sp ro proposer dg H tr g ΔF Gp W M cF kF hrun hp t ht
    have hc := (hcoverage sp ro proposer dg H tr g ΔF Gp W M cF kF).coverage hrun hp t ht
    obtain ⟨q, kP, P, hq, hprop, hlo, hhi, -, hcarrier, hcache⟩ := hc.witness
    exact ⟨q, kP, P, hq, hprop, hlo, hhi, hcarrier, hcache⟩

end Consensus.Goldilocks.Healing.Recovery

end

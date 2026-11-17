module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Attest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Persist: a slot-timing fact of C1.1's induction

`not_proposesAt_mid`: no proposal is made at `t_{s'} + 2Δ`, the midpoint between two slot
starts. The induction of C1.1 that read it is retired with C1.1. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder goldilocksSA Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

variable {tr H}
variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {ΔF : Time} {x : Fin sp.n}
  {i₀ s m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
  {proposer : Nat → Fin sp.n}

/-- No proposal is processed at `t_{s'} + 2Δ`: slots start at multiples of `4Δ`. -/
theorem not_proposesAt_mid {y : Fin sp.n} {k : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))}
    {s' : Nat} (hX : tr.ProposesAt y k X) (hk : tr.time k = sp.ts s' + sp.Δ + sp.Δ) : False := by
  have h₁ := hX.2.2
  rw [sp.slotTime_eq] at h₁
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  unfold SA.SAParams.ts at hk
  have e : 4 * sp.Δ * (X.slot : Int) = 4 * sp.Δ * s' + sp.Δ + sp.Δ := h₁.symm.trans hk
  have h₂ : sp.Δ * (4 * (X.slot : Int) - 4 * s' - 2) = 0 := by
    ring_nf
    ring_nf at e
    linarith
  rcases mul_eq_zero.mp h₂ with h | h
  · exact hΔ.ne' h
  · have h' : 4 * (X.slot : Int) - 4 * (s' : Int) - 2 = 0 := h
    omega

end Consensus.Goldilocks.Compose

end

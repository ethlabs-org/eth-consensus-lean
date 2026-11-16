module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.SleepyLayer1
import ConsensusLean.Lemmas.Problem.Facts.Regimes
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Independent retention-window transports

Earlier retention charges keep more ready validators and fewer faulty validators.
Population and committee windows are transported separately.
-/

namespace Consensus.Goldilocks.Generic.SleepyLayer1

private theorem count_mono {V : Type} {R R' F F' : Finset V} {θ : ℚ}
    (h : θ * ((R.card + F.card : Nat) : ℚ) < R.card)
    (hr : R ⊆ R') (hf : F' ⊆ F) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * ((R'.card + F'.card : Nat) : ℚ) < R'.card := by
  have hrq : (R.card : ℚ) ≤ R'.card := by exact_mod_cast Finset.card_le_card hr
  have hfq : (F'.card : ℚ) ≤ F.card := by exact_mod_cast Finset.card_le_card hf
  have hm := mul_le_mul_of_nonneg_left hfq h0
  have hd := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hrq)
  push_cast at h ⊢
  linarith

private theorem ready_subset {V : Type} [Fintype V]
    (p : EnvPoint V) {e d c c' t : Time} (hd : d ≤ e) (hc : c' ≤ c) :
    (p.retain e).readyAt c t ⊆ (p.retain d).readyAt c' t := by
  intro v hv
  simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  refine ⟨fun hf => hv.1 (p.faultyAt_mono hd hf), fun u hu hut => hv.2 u ?_ hut⟩
  exact le_trans (max_le_max_left 0 (by linarith)) hu

open Shape Blocks

variable {P : Params} {A : NodeAC P}
  {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

theorem committee_transport (M : RunMap rho payload)
    (C : ACCorrectLocal A M.signer) : CommitteeTransport M C := by
  intro p b c W _ hc hW h0 h1 h t d ht htd hdb hne
  have hcount := h t ht (htd.trans (hdb.trans (min_le_left _ _))) hne
  simp only [le_refl, ↓reduceIte] at hcount
  apply count_mono hcount
    (Finset.inter_subset_inter
      (ready_subset p (by rw [← hW]; exact hdb.trans (min_le_right _ _)) hc)
      (Finset.Subset.refl _))
    (Finset.inter_subset_inter (p.faultyAt_mono (by rw [← hW]; exact hdb.trans (min_le_right _ _)))
      (Finset.Subset.refl _)) h0 h1

theorem population_transport (M : RunMap rho payload)
    (C : ACCorrectLocal A M.signer) : PopulationTransport M C := by
  intro p b c W _ hc hW h0 h1 h t d ht htd hdb
  have hcount := h t ht (htd.trans (hdb.trans (min_le_left _ _)))
  have he : d ≤ p.lookAhead W t := by rw [← hW]; exact hdb.trans (min_le_right _ _)
  change C.θ * (((p.retain (p.lookAhead W t)).readyAt c t).card +
    (p.faultyAt (p.lookAhead W t)).card : ℚ) < _ at hcount
  change C.θ * (((p.retain d).readyAt C.catchUp t).card + (p.faultyAt d).card : ℚ) < _
  have hr := ready_subset p (t := t) he hc
  have hf := p.faultyAt_mono he
  have hm := count_mono (R := (p.retain (p.lookAhead W t)).readyAt c t)
    (R' := (p.retain d).readyAt C.catchUp t)
    (F := p.faultyAt (p.lookAhead W t)) (F' := p.faultyAt d)
    (by simpa only [Nat.cast_add] using hcount) hr hf h0 h1
  simpa only [Nat.cast_add] using hm

end Consensus.Goldilocks.Generic.SleepyLayer1

end

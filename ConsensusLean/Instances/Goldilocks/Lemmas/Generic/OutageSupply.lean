module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage participation from `System.Outage`

`OutageTransport.participation_of_outage`: for every shape family, a valid run in `Outage`
satisfies the `participation` conjunct of `OutageTransport` at its own point and selected
population: the population and look-back committee η-sleepy clauses with the outage catch-up
`max cDur (η·ΔAC − 1)` and the contract's independent look-aheads and participation
threshold. These are the participation premises of L9 (`OutageReadPoint.protection`).

`OutageTransport.participation_local`: the same clauses at the fixed local outage catch-up
`max C.catchUp (C.outageEta − 1)` and the local look-aheads, exactly as L9 consumes them. A longer
catch-up only removes ready validators, so the advertised counts at `max cDur (η·ΔAC − 1)` transport
down along `OutageRecoveryBinding.catchUp : C.catchUp + 1 ≤ cDur`. -/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E}

/-- `System.Outage` gives the `participation` conjunct of `OutageTransport` at the run's own
point and selected population. -/
theorem OutageTransport.participation_of_outage (K : Contract ProgressReq) :
    rho.ExecutionValid → ∀ T b₀ b₁,
    (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
    rho.point.EtaSleepyOn K.params.θ ((K.params.η : Time) * E.ΔAC)
      (max ((Sys F V).cDur K ⟨E, rho⟩) ((K.params.η : Time) * E.ΔAC - 1))
      ((Sys F V).aheadDur K ⟨E, rho⟩) 0 rho.point.horizon ∧
    ∀ δ, 0 ≤ δ → δ ≤ (K.params.η : Time) * E.ΔAC →
      rho.point.CommitteeSleepyOn
        (fun t => (shapeProgress F V).selected E ((shapeProgress F V).ext ⟨E, rho⟩)
          (max 0 (t - δ)))
        K.params.θ ((K.params.η : Time) * E.ΔAC)
        (max ((Sys F V).cDur K ⟨E, rho⟩) ((K.params.η : Time) * E.ΔAC - 1))
        ((Sys F V).committeeAheadDur K ⟨E, rho⟩) 0 rho.point.horizon := by
  intro _ T b₀ b₁ h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- A longer catch-up only removes ready validators. -/
private theorem readyAt_subset {W : Type} [Fintype W] (p : EnvPoint W) {c c' t : Time}
    (h : c ≤ c') : p.readyAt c' t ⊆ p.readyAt c t := by
  classical
  intro v hv
  simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact ⟨hv.1, fun u hu hut => hv.2 u ((max_le_max le_rfl (by linarith)).trans hu) hut⟩

/-- A count `θ · (r + f) < r` survives a larger ready count. The count itself forces `θ < 1`. -/
private theorem sum_count_mono {θ : ℚ} {r r' f : Nat} (hr : r ≤ r')
    (h : θ * ((r : ℚ) + f) < r) : θ * ((r' : ℚ) + f) < r' := by
  have hrq : (r : ℚ) ≤ r' := by exact_mod_cast hr
  have hr0 : (0 : ℚ) ≤ r := by positivity
  have hf0 : (0 : ℚ) ≤ f := by positivity
  have hθ : θ ≤ 1 := by
    by_contra hθ
    nlinarith
  nlinarith

/-- A count `θ · |R ∪ X| < |R|` survives a larger ready set. The count itself forces `θ < 1`;
a negative `θ` makes the larger count immediate. -/
private theorem union_count_mono {W : Type} [DecidableEq W] {θ : ℚ} {R R' X : Finset W}
    (hR : R ⊆ R') (h : θ * ((R ∪ X).card : ℚ) < R.card) :
    θ * ((R' ∪ X).card : ℚ) < R'.card := by
  have h1 : (R' ∪ X).card ≤ (R ∪ X).card + (R' \ R).card :=
    (Finset.card_le_card fun v hv => by
      simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢
      tauto).trans (Finset.card_union_le _ _)
  have h2 : ((R' \ R).card : ℚ) + R.card = R'.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hR
  have h1q : ((R' ∪ X).card : ℚ) ≤ (R ∪ X).card + (R' \ R).card := by exact_mod_cast h1
  have h3 : (R.card : ℚ) ≤ (R ∪ X).card := by
    exact_mod_cast Finset.card_le_card Finset.subset_union_left
  have h4 : ((R ∪ X).card : ℚ) ≤ (R' ∪ X).card := by
    exact_mod_cast Finset.card_le_card (Finset.union_subset_union hR le_rfl)
  have hd : (0 : ℚ) ≤ (R' \ R).card := by positivity
  have hR0 : (0 : ℚ) ≤ R.card := by positivity
  rcases le_or_gt 0 θ with h0 | h0
  · have hθ : θ ≤ 1 := by
      by_contra hθ
      nlinarith
    have := mul_le_mul_of_nonneg_left h1q h0
    have := mul_le_mul_of_nonneg_right hθ hd
    linarith
  · nlinarith

/-- η-sleepy population counts transport to a shorter catch-up. -/
private theorem etaSleepyOn_catchUp_mono {W : Type} [Fintype W] [DecidableEq W]
    {p : EnvPoint W} {η c c' L a b : Time} {θ : ℚ} (hc : c ≤ c')
    (h : p.EtaSleepyOn θ η c' L a b) : p.EtaSleepyOn θ η c L a b := by
  intro t hat htb
  have ht := h t hat htb
  have hR := readyAt_subset (p.retain (p.lookAhead L t)) (t := t) hc
  unfold EnvPoint.EtaReadyAbove at ht ⊢
  split_ifs at ht ⊢
  · exact sum_count_mono (Finset.card_le_card hR) ht
  · rw [Finset.union_assoc] at ht ⊢
    exact union_count_mono hR ht

/-- Committee η-sleepy counts transport to a shorter catch-up. -/
private theorem committeeSleepyOn_catchUp_mono {W : Type} [Fintype W] [DecidableEq W]
    {p : EnvPoint W} {K : Time → Finset W} {η c c' L a b : Time} {θ : ℚ} (hc : c ≤ c')
    (h : p.CommitteeSleepyOn K θ η c' L a b) :
    p.CommitteeSleepyOn K θ η c L a b := by
  intro t hat htb hK
  have ht := h t hat htb hK
  have hR := readyAt_subset (p.retain (p.lookAhead L t)) (t := t) hc
  have hRK := Finset.inter_subset_inter hR (Finset.Subset.refl (K t))
  dsimp only at ht ⊢
  split_ifs at ht ⊢
  · push_cast at ht ⊢
    exact sum_count_mono (Finset.card_le_card hRK) ht
  · rw [Finset.union_assoc, Finset.union_inter_distrib_right] at ht ⊢
    exact union_count_mono hRK ht

/-- The outage participation of L9 at the fixed local outage catch-up and look-aheads, from the
advertised clauses of `OutageTransport` and the policy matching of `OutageRecoveryBinding`, at
every participation threshold: each advertised count itself forces `θ < 1`. -/
theorem OutageTransport.participation_local {P : Params} {A : NodeAC P}
    {payload : A.Blk → Set Nat} {M : RunMap rho payload} {D : OutagePolicy M}
    {K : Contract ProgressReq} {fgHold : Time} {C : ACCorrectLocal A M.signer fgHold}
    (hT : OutageTransport M D K) (hB : OutageRecoveryBinding M K C) (hv : rho.ExecutionValid)
    {T b₀ b₁ : Time}
    (h : (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩) :
    D.point.EtaSleepyOn C.θ C.outageEta (max C.catchUp (C.outageEta - 1)) C.look 0
        D.point.horizon ∧
      ∀ δ, 0 ≤ δ → δ ≤ C.outageEta →
        D.point.CommitteeSleepyOn (fun t => M.committee (max 0 (t - δ))) C.θ C.outageEta
          (max C.catchUp (C.outageEta - 1)) C.committeeLook 0 D.point.horizon := by
  obtain ⟨hp, hc⟩ := hT.participation hv T b₀ b₁ h
  rw [← hB.eta, ← hB.threshold, ← hB.look] at hp
  rw [← hB.eta, ← hB.threshold, ← hB.committeeLook] at hc
  have hcu : max C.catchUp (C.outageEta - 1) ≤
      max ((Sys F V).cDur K ⟨E, rho⟩) (C.outageEta - 1) :=
    max_le_max (by linarith [hB.catchUp]) le_rfl
  exact ⟨etaSleepyOn_catchUp_mono hcu hp, fun δ hδ hδη =>
    committeeSleepyOn_catchUp_mono hcu (hc δ hδ hδη)⟩

end Consensus.Goldilocks.Generic

end

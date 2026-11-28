module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The hand-over regime (generic facts)

Facts about `System.Handover` that the continuation proof reads: a hand-over at or after the
horizon is the healthy regime (`Handover.healthy`); full participation on `[max g 0, T]` extends
the sleepy budget at `T` back to `ready g` (`Handover.sleepyOn_from_ready`), and with the
cross-boundary committee bound the committee budget too
(`Handover.committeeSleepyOn_from_ready`). -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] {p : EnvPoint V}

/-- On a retained view, the ready validators and the retained faults are disjoint. -/
private theorem card_readyAt_retain_add_le (c t D : Time) :
    ((p.retain D).readyAt c t).card + (p.faultyAt D).card ≤ Fintype.card V := by
  classical
  have hdis : Disjoint ((p.retain D).readyAt c t) (p.faultyAt D) := by
    refine Finset.disjoint_left.mpr fun v hv hf => ?_
    unfold readyAt at hv
    exact (Finset.mem_filter.mp hv).2.1 hf
  rw [← Finset.card_union_of_disjoint hdis]
  exact Finset.card_le_univ _

/-- On a retained view, a validator compromised by the retention time `D` only after the ready
window of `t` (`t ≤ D`), and awake whenever honest on that window, is ready at `t`: so the ready
validators and the retained faults make up all validators. -/
private theorem card_readyAt_retain_add_eq {c t D : Time} (htD : t ≤ D)
    (haw : ∀ v u, max 0 (t - c - 1) ≤ u → u ≤ t → p.HonestAt v u → p.env.awake v u = true) :
    ((p.retain D).readyAt c t).card + (p.faultyAt D).card = Fintype.card V := by
  classical
  refine le_antisymm (card_readyAt_retain_add_le c t D) ?_
  have hsub : Finset.univ \ p.faultyAt D ⊆ (p.retain D).readyAt c t := by
    intro v hv
    have hvD : v ∉ p.faultyAt D := (Finset.mem_sdiff.mp hv).2
    unfold readyAt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD,
      fun u hu ht => haw v u hu ht fun hf => hvD (p.faultyAt_mono (ht.trans htD) hf)⟩
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (p.faultyAt D))
  rw [Finset.card_univ] at hc
  have := Finset.card_le_card hsub
  omega

end EnvPoint

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog : Type} {X : External S}

omit [Fintype V] [DecidableEq V] in
/-- The sleepy look-ahead is a nonnegative duration. -/
private theorem aheadDur_nonneg (K : Contract Prog) (r : S.Run) : 0 ≤ S.aheadDur K r :=
  mul_nonneg (Nat.cast_nonneg _) (S.pt r).env.ΔAC_pos.le

/-- A hand-over at or after the horizon is the healthy regime: faults only grow, so the fault
bounds at `T` (of the population and of the selected committees) bound the faults at the
horizon, and the awake window and the selection window `[max g 0, horizon]` lie in
`[max g 0, T]`. -/
theorem Handover.healthy {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover X K g T r) (hT : (S.pt r).horizon ≤ T) : S.Healthy X K g r := by
  obtain ⟨hnet, ⟨hf, haw⟩, hΔ, -, -, hK, -⟩ := h
  refine ⟨hnet, ⟨lt_of_le_of_lt ?_ hf, fun v t hg ht => haw v t hg (ht.trans hT)⟩, hΔ,
    fun t ht htb hne => lt_of_le_of_lt ?_ (hK t ht (htb.trans hT) hne)⟩
  · exact_mod_cast Finset.card_le_card ((S.pt r).faultyAt_mono hT)
  · exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_inter_right ((S.pt r).faultyAt_mono hT))

/-- Full participation on `[max g 0, T]` extends the sleepy budget at `T` back to `ready g`. At
`t ∈ [ready g, T)` every validator not compromised by the look-ahead of `t` is honest, hence
awake, on the ready window of `t`, which lies in `[max g 0, T]`: so the ready validators and the
retained faults make up all validators at `t`. At `T` they make up at most all validators, the
faults at the look-ahead of `t` are at most those at the look-ahead of `T`, and `θ ≤ 1`. -/
theorem Handover.sleepyOn_from_ready {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover X K g T r) (hT : T ≤ (S.pt r).horizon) (hθ : K.params.θ ≤ 1) :
    (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) (S.ready K g r)
      (S.pt r).horizon := by
  obtain ⟨-, ⟨-, haw⟩, -, hsl, -⟩ := h
  intro t ht htb
  rcases le_or_gt T t with hTt | htT
  · exact hsl t hTt htb
  have hW := aheadDur_nonneg (S := S) K r
  have ht' : max g 0 + S.cDur K r + 1 ≤ t := ht
  have hDt : t ≤ (S.pt r).lookAhead (S.aheadDur K r) t :=
    le_min (le_add_of_nonneg_right hW) htb
  have hDtT : (S.pt r).lookAhead (S.aheadDur K r) t ≤ (S.pt r).lookAhead (S.aheadDur K r) T :=
    min_le_min_right _ (by linarith only [htT])
  have heq := EnvPoint.card_readyAt_retain_add_eq (c := S.cDur K r) hDt fun v u hu hut hv =>
    haw v u (by linarith only [ht', hu, le_max_right 0 (t - S.cDur K r - 1)])
      (hut.trans htT.le) hv
  have hle := EnvPoint.card_readyAt_retain_add_le (p := S.pt r) (S.cDur K r) T
    ((S.pt r).lookAhead (S.aheadDur K r) T)
  have hF := Finset.card_le_card ((S.pt r).faultyAt_mono hDtT)
  have hT' := hsl T le_rfl hT
  unfold EnvPoint.ReadyAbove EnvPoint.faultCount at hT' ⊢
  set Rt := ((S.pt r).retain ((S.pt r).lookAhead (S.aheadDur K r) t)).readyAt (S.cDur K r) t
  set RT := ((S.pt r).retain ((S.pt r).lookAhead (S.aheadDur K r) T)).readyAt (S.cDur K r) T
  set Ft := (S.pt r).faultyAt ((S.pt r).lookAhead (S.aheadDur K r) t)
  set FT := (S.pt r).faultyAt ((S.pt r).lookAhead (S.aheadDur K r) T)
  change K.params.θ * ((RT.card : ℚ) + FT.card) < RT.card at hT'
  change K.params.θ * ((Rt.card : ℚ) + Ft.card) < Rt.card
  have heq' : (Rt.card : ℚ) + Ft.card = Fintype.card V := by exact_mod_cast heq
  have hle' : (RT.card : ℚ) + FT.card ≤ Fintype.card V := by exact_mod_cast hle
  have hF' : (Ft.card : ℚ) ≤ FT.card := by exact_mod_cast hF
  have hslack := mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr hle')
  rw [heq']
  linarith

/-- **Committee sleepy participation from `ready g`.** Full participation on `[max g 0, T]`
extends the committee budget at `T` back to `ready g`, at `θ ≤ ½` and a committee look-ahead of
at most `6ΔAC`. At `t ∈ [ready g, T)` every member of the committee selected at `t` that is not
compromised by the look-ahead of `t` is honest, hence awake, on the ready window of `t`, which
lies in `[max g 0, T]`: so the ready members and the retained faulty members make up the
committee, and the faulty ones are fewer than half of it by the cross-boundary bound at `u = t`,
charged at `min (t + 6ΔAC) horizon`, at or after the look-ahead. -/
theorem Handover.committeeSleepyOn_from_ready {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover X K g T r) (hθ : K.params.θ ≤ 1 / 2)
    (hW : S.committeeAheadDur K r ≤ 6 * (S.pt r).env.ΔAC) :
    (S.pt r).CommitteeSleepyOn (X.selected (S.pt r).env (X.ext r)) K.params.θ 0 (S.cDur K r)
      (S.committeeAheadDur K r) (S.ready K g r) (S.pt r).horizon := by
  classical
  obtain ⟨-, ⟨-, haw⟩, -, -, -, -, hsl, hcross⟩ := h
  intro t ht htb hne
  rcases le_or_gt T t with hTt | htT
  · exact hsl t hTt htb hne
  set p := S.pt r
  set C := X.selected p.env (X.ext r) t
  set L := p.lookAhead (S.committeeAheadDur K r) t
  have hc0 : 0 ≤ S.cDur K r := mul_nonneg (Nat.cast_nonneg _) p.env.ΔAC_pos.le
  have hW0 : 0 ≤ S.committeeAheadDur K r := mul_nonneg (Nat.cast_nonneg _) p.env.ΔAC_pos.le
  have ht' : max g 0 + S.cDur K r + 1 ≤ t := ht
  have htL : t ≤ L := le_min (le_add_of_nonneg_right hW0) htb
  -- the ready members are the members not compromised by `L`
  have hR : (p.retain L).readyAt (S.cDur K r) t ∩ C = C \ p.faultyAt L := by
    ext v
    simp only [EnvPoint.readyAt, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hv, -⟩, hvC⟩
      exact ⟨hvC, hv⟩
    · rintro ⟨hvC, hv⟩
      refine ⟨⟨hv, fun u hu hut => haw v u ?_ (hut.trans htT.le) fun hf =>
        hv (p.faultyAt_mono (hut.trans htL) hf)⟩, hvC⟩
      linarith only [ht', hu, le_max_right 0 (t - S.cDur K r - 1)]
  -- the faulty members by `L` are fewer than half of the committee
  have hF : 2 * (p.faultyAt L ∩ C).card < C.card := by
    have hLM : L ≤ min (t + 6 * p.env.ΔAC) p.horizon :=
      min_le_min_right _ (by linarith only [hW])
    refine lt_of_le_of_lt ?_ (hcross t (by linarith only [ht', hc0]) (le_min htT.le htb) hne)
    exact Nat.mul_le_mul_left 2 (Finset.card_le_card
      (Finset.inter_subset_inter_right (p.faultyAt_mono hLM)))
  have hsplit := Finset.card_sdiff_add_card_inter C (p.faultyAt L)
  rw [Finset.inter_comm C (p.faultyAt L)] at hsplit
  change (if (0 : Time) ≤ 0 then _ else _)
  simp only [le_refl, ↓reduceIte]
  change K.params.θ * ((((p.retain L).readyAt (S.cDur K r) t ∩ C).card +
    (p.faultyAt L ∩ C).card : Nat) : ℚ) < (((p.retain L).readyAt (S.cDur K r) t ∩ C).card : ℚ)
  rw [hR]
  have hlt : ((p.faultyAt L ∩ C).card : ℚ) < ((C \ p.faultyAt L).card : ℚ) := by
    exact_mod_cast (by omega : (p.faultyAt L ∩ C).card < (C \ p.faultyAt L).card)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hθ (by positivity :
    (0 : ℚ) ≤ ((C \ p.faultyAt L).card : ℚ) + ((p.faultyAt L ∩ C).card : ℚ))]

end System

end Consensus

end

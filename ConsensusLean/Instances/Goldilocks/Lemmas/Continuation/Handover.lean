module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The hand-over regime (generic facts)

Facts about `System.Handover` that the continuation proof reads: a hand-over at or after the
horizon is the healthy regime (`Handover.healthy`); full participation on `[max g 0, T]` extends
the sleepy budget at `T` back to `ready g` (`Handover.sleepyOn_from_ready`); at `θ = ½` and
`β ≤ ½`, fewer than half of the validators are compromised at every time up to the horizon
(`Handover.two_faults_lt`). -/

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

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog : Type}

omit [Fintype V] [DecidableEq V] in
/-- The sleepy look-ahead is a nonnegative duration. -/
private theorem aheadDur_nonneg (K : Contract Prog) (r : S.Run) : 0 ≤ S.aheadDur K r :=
  mul_nonneg (Nat.cast_nonneg _) (S.pt r).env.ΔAC_pos.le

omit [DecidableEq V] in
/-- A hand-over at or after the horizon is the healthy regime: faults only grow, so the fault
bound at `T` bounds the faults at the horizon, and the awake window `[max g 0, horizon]` lies in
`[max g 0, T]`. -/
theorem Handover.healthy {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover K g T r) (hT : (S.pt r).horizon ≤ T) : S.Healthy K g r := by
  obtain ⟨hnet, ⟨hf, haw⟩, hΔ, -, -⟩ := h
  unfold System.Healthy
  refine ⟨hnet, ⟨lt_of_le_of_lt ?_ hf, fun v t hg ht => haw v t hg (ht.trans hT)⟩, hΔ⟩
  exact_mod_cast Finset.card_le_card ((S.pt r).faultyAt_mono hT)

omit [DecidableEq V] in
/-- Full participation on `[max g 0, T]` extends the sleepy budget at `T` back to `ready g`. At
`t ∈ [ready g, T)` every validator not compromised by the look-ahead of `t` is honest, hence
awake, on the ready window of `t`, which lies in `[max g 0, T]`: so the ready validators and the
retained faults make up all validators at `t`. At `T` they make up at most all validators, the
faults at the look-ahead of `t` are at most those at the look-ahead of `T`, and `θ ≤ 1`. -/
theorem Handover.sleepyOn_from_ready {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover K g T r) (hT : T ≤ (S.pt r).horizon) (hθ : K.params.θ ≤ 1) :
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

omit [DecidableEq V] in
/-- At `θ = ½` and `β ≤ ½`, fewer than half of the validators are compromised at every time up to
the horizon: up to `T` by the healthy fault bound (faults only grow), after `T` because the faults
charged by the sleepy budget are fewer than the ready validators, which they are disjoint from. -/
theorem Handover.two_faults_lt {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover K g T r) (hθ : K.params.θ = 1 / 2) (hβ : K.params.β ≤ 1 / 2) :
    ∀ d, d ≤ (S.pt r).horizon → 2 * (S.pt r).faultCount d < Fintype.card V := by
  obtain ⟨-, ⟨hf, -⟩, -, hsl, -⟩ := h
  intro d hd
  rcases le_or_gt d T with hdT | hTd
  · have hdT' : ((S.pt r).faultCount d : ℚ) ≤ (S.pt r).faultCount T := by
      exact_mod_cast Finset.card_le_card ((S.pt r).faultyAt_mono hdT)
    have hβn : K.params.β * Fintype.card V ≤ 1 / 2 * Fintype.card V :=
      mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg _)
    have : (2 * (S.pt r).faultCount d : ℚ) < Fintype.card V := by linarith only [hdT', hf, hβn]
    exact_mod_cast this
  · have hD : d ≤ (S.pt r).lookAhead (S.aheadDur K r) d :=
      le_min (le_add_of_nonneg_right (aheadDur_nonneg K r)) hd
    have hle := EnvPoint.card_readyAt_retain_add_le (p := S.pt r) (S.cDur K r) d
      ((S.pt r).lookAhead (S.aheadDur K r) d)
    have hF := Finset.card_le_card ((S.pt r).faultyAt_mono hD)
    have hs := hsl d hTd.le hd
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount at hs
    rw [hθ] at hs
    unfold EnvPoint.faultCount
    set R := ((S.pt r).retain ((S.pt r).lookAhead (S.aheadDur K r) d)).readyAt (S.cDur K r) d
    set F := (S.pt r).faultyAt ((S.pt r).lookAhead (S.aheadDur K r) d)
    change 1 / 2 * ((R.card : ℚ) + F.card) < R.card at hs
    have hRF : F.card < R.card := by
      have : (F.card : ℚ) < R.card := by linarith only [hs]
      exact_mod_cast this
    omega

end System

end Consensus

end

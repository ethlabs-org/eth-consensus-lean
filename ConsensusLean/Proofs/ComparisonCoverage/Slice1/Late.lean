module
public import ConsensusLean.Comparison.HealCoverage
public import ConsensusLean.Proofs.ComparisonCoverage.Witness
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the late witness point

The late witness point `latePoint A T₁ u H`: `ΔAC = ΔFG = 2`, every validator asleep before `T₁`
and awake from `T₁` on, the validators of `A` compromised from the start, horizon `H`,
transaction `42` submitted to `u` at time `T₁`. Nobody releases anything before `T₁`, so a run at
this point has no honest content before `T₁` (the split witness starts its incident at an honest
first release, which must come after the forgeries planned before the incident).

* `latePoint_ready`: an honest validator is ready with catch-up `c` from `T₁ + c + 1` on.
* `latePoint_notAwakeHonest`: on an incident starting at or after `T₁`, the validators that cannot
  vote are exactly `A`.
* `latePoint_honestAwakeAfter`: everyone honest is awake from `b₁ ≥ T₁` on.
* `latePoint_holds`: a fitting progress requirement admitting `|A|` compromised validators holds on
  every window starting at `T₁ + c + 1` (key `1` honest).
* `latePoint_safeActive`, `latePoint_txLiveActive`: the claims are active given room before the
  horizon. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf)

variable {V : Type} [DecidableEq V]

/-- The late witness point. -/
def latePoint (A : Finset V) (T₁ : Time) (u : V) (H : Time) : EnvPoint V :=
  ⟨⟨2, two_pos, 2, two_pos, fun _ t => decide (T₁ ≤ t)⟩, fun _ => A, monotone_const, H,
    fun v t => if v = u ∧ t = T₁ then [42] else []⟩

section Point

variable (A : Finset V) (T₁ : Time) (u : V) (H : Time)

@[simp] theorem latePoint_ΔAC : (latePoint A T₁ u H).env.ΔAC = 2 := by rfl

@[simp] theorem latePoint_ΔFG : (latePoint A T₁ u H).env.ΔFG = 2 := by rfl

/-- The public parameters of the late point's environment. -/
theorem latePoint_pubOf [Fintype V] :
    pubOf (latePoint A T₁ u H).env = ⟨Fintype.card V, 2, two_pos, 2, two_pos⟩ := by rfl

theorem latePoint_awake (v : V) (t : Time) :
    (latePoint A T₁ u H).env.awake v t = decide (T₁ ≤ t) := by rfl

@[simp] theorem latePoint_faultyAt (t : Time) : (latePoint A T₁ u H).faultyAt t = A := by rfl

theorem latePoint_faultCount (t : Time) : (latePoint A T₁ u H).faultCount t = A.card := by rfl

@[simp] theorem latePoint_horizon : (latePoint A T₁ u H).horizon = H := by rfl

theorem latePoint_submit (v : V) (t : Time) :
    (latePoint A T₁ u H).submit v t = if v = u ∧ t = T₁ then [42] else [] := by rfl

/-- The late point with another horizon. -/
theorem latePoint_withHorizon (H' : Time) :
    ({ latePoint A T₁ u H with horizon := H' } : EnvPoint V) = latePoint A T₁ u H' := by rfl

/-- The late point's environment does not depend on the horizon. -/
theorem latePoint_env (H' : Time) : (latePoint A T₁ u H).env = (latePoint A T₁ u H').env := by
  rfl

variable {A T₁ u H}

theorem latePoint_honest {v : V} (hv : v ∉ A) (t : Time) : (latePoint A T₁ u H).HonestAt v t :=
  hv

theorem latePoint_awake_of_ge {t : Time} (ht : T₁ ≤ t) (v : V) :
    (latePoint A T₁ u H).env.awake v t = true := by
  rw [latePoint_awake, decide_eq_true_iff]
  exact ht

theorem le_of_latePoint_awake {v : V} {t : Time}
    (h : (latePoint A T₁ u H).env.awake v t = true) : T₁ ≤ t := by
  rw [latePoint_awake, decide_eq_true_iff] at h
  exact h

/-- An honest validator is ready with catch-up `c` from `T₁ + c + 1` on. -/
theorem latePoint_ready {v : V} (hv : v ∉ A) {c t : Time} (ht : T₁ + c + 1 ≤ t) :
    (latePoint A T₁ u H).Ready c v t :=
  ⟨hv, fun t' ht' _ => latePoint_awake_of_ge (by
    have := le_max_right 0 (t - c - 1)
    dsimp only [Time] at *
    omega) v⟩

/-- Everyone honest is awake from `max b₁ 0` on, for `T₁ ≤ b₁`. -/
theorem latePoint_honestAwakeAfter {b₁ : Time} (hb : T₁ ≤ b₁) :
    ∀ v t, max b₁ 0 ≤ t → t ≤ (latePoint A T₁ u H).horizon →
      (latePoint A T₁ u H).HonestAt v t →
      (latePoint A T₁ u H).env.awake v t = true :=
  fun v _ ht _ _ => latePoint_awake_of_ge (hb.trans ((le_max_left _ _).trans ht)) v

/-- From `T₁ + c + 1` on, at most `|A|` validators are not ready. -/
theorem latePoint_readyAt_card [Fintype V] {c t : Time} (ht : T₁ + c + 1 ≤ t) :
    Fintype.card V ≤ ((latePoint A T₁ u H).readyAt c t).card + A.card := by
  classical
  have hsub : Finset.univ \ A ⊆ (latePoint A T₁ u H).readyAt c t := by
    intro v hv
    unfold EnvPoint.readyAt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      latePoint_ready (Finset.mem_sdiff.mp hv).2 ht⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter Finset.univ A
  rw [Finset.univ_inter, Finset.card_univ] at h2
  omega

omit [DecidableEq V] in
private theorem mem_notAwakeHonest_iff' [Fintype V] [DecidableEq V] {S : System V} {r : S.Run}
    {b₀ b₁ : Time} {v : V} :
    v ∈ notAwakeHonest S b₀ b₁ r ↔ v ∈ (S.pt r).faultyAt (S.pt r).horizon ∨
      (max b₀ 0 < b₁ ∧ ∀ t, max b₀ 0 ≤ t → t < b₁ →
        (S.pt r).HonestAt v t ∧ (S.pt r).env.awake v t = false) := by
  classical
  simp only [notAwakeHonest, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The validators that cannot vote** at a run of the late point, on an incident starting at or
after `T₁`: exactly `A`. -/
theorem latePoint_notAwakeHonest [Fintype V] {S : System V} {r : S.Run} {b₀ b₁ : Time}
    (hp : S.pt r = latePoint A T₁ u H) (hb : T₁ ≤ b₀) :
    (notAwakeHonest S b₀ b₁ r).card = A.card := by
  congr 1
  ext v
  rw [mem_notAwakeHonest_iff', hp, latePoint_faultyAt]
  refine ⟨fun h => h.elim id fun ⟨hlt, h⟩ => ?_, Or.inl⟩
  have := (h (max b₀ 0) le_rfl hlt).2
  rw [latePoint_awake_of_ge (hb.trans (le_max_left _ _))] at this
  exact absurd this (by decide)

end Point

/-! ## Progress and active claims -/

variable [Fintype V] {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- A fitting progress requirement that admits `|A|` compromised validators holds on every window
starting at `T₁ + c + 1` of the late point, under every selection that agrees with the extremal one
on the proposer roles, when key `1` is honest. -/
theorem latePoint_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (key : Fin (Fintype.card V) ≃ V) (h2 : 2 ≤ Fintype.card V) {A : Finset V}
    {T₁ : Time} {u : V} {H : Time} {p : EnvPoint V} (hp : p = latePoint A T₁ u H)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ s, sel (.proposer s) = extremalSel F p.env (.proposer s))
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (hA : AdmitsFaults (K.progress cap i) A.card) (h1 : key ⟨1, by omega⟩ ∉ A)
    {c s : Time} (hs : T₁ + c + 1 ≤ s) (e : Time) :
    shapeHolds F (K.progress cap i) c s e p (key, sel) := by
  subst hp
  have hfit := hf cap i (pubOf (latePoint A T₁ u H).env)
  revert hfit hA
  cases K.progress cap i with
  | recur ρ =>
    intro _ hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    change PatternRecurrence _ _ (fun s => sel (.proposer s)) _ _ _ _ _
    rw [funext hsel]
    intro t ht _ _
    have hSL := (F (pubOf (latePoint A T₁ u H).env)).skel.grid.slotLen_pos
    obtain ⟨sl, hs₁, hs₂⟩ := (F (pubOf (latePoint A T₁ u H).env)).skel.grid.exists_slot_in_window
      (le_trans (le_max_right _ _) ht) (k := (ρ.gap : Nat)) ρ.gap.pos
    refine ⟨sl, hs₁, hs₂, fun j _ => ?_⟩
    have hmem := extremalSel_proposer_mem F hfit h2 (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    refine ⟨latePoint_ready h1 ?_, latePoint_honest h1 _⟩
    rw [TimeGrid.slotTime_add]
    have h0 : (0 : Time) ≤ (j : Time) * (F (pubOf (latePoint A T₁ u H).env)).skel.grid.slotLen :=
      mul_nonneg (by positivity) hSL.le
    have := le_max_left s 0
    linarith
  | notReadyAtMost m =>
    intro hA _ t ht _ _
    have : T₁ + c + 1 ≤ t := hs.trans ((le_max_left _ _).trans ht)
    exact le_trans (latePoint_readyAt_card this) (Nat.add_le_add_left hA _)

omit [Fintype V] in
/-- Safety is active after `t₀` at the late point, given room before the horizon. -/
theorem latePoint_safeActive {A : Finset V} {T₁ : Time} {u : V} {H : Time} {v w : V}
    (hv : v ∉ A) (hw : w ∉ A) (hne : v ≠ w) (c t₀ : Time) (hH : t₀ + 2 ≤ H)
    (hc : T₁ + c + 2 ≤ H) : SafeActive c t₀ (latePoint A T₁ u H) :=
  ⟨v, w, H - 1, H, hne, by linarith, by linarith, le_rfl,
    latePoint_ready hv (by linarith), latePoint_ready hw (by linarith),
    latePoint_ready hv (by linarith)⟩

omit [Fintype V] in
/-- Liveness is active from `start` at the late point: transaction `42`, submitted to the honest
`u` at `T₁`, is owed to an honest `w ≠ u` ready at the horizon. -/
theorem latePoint_txLiveActive {A : Finset V} {T₁ : Time} {u : V} {H : Time} {w : V}
    (hu : u ∉ A) (hw : w ∉ A) (hne : w ≠ u) (hT : 0 ≤ T₁) (c start D : Time)
    (hH : max T₁ start + 2 + D ≤ H) (hc : T₁ + c + 1 ≤ H) :
    (latePoint A T₁ u H).TxLiveActive c start D := by
  refine ⟨42, T₁, H, u, w, hT, latePoint_honest hu T₁, latePoint_awake_of_ge le_rfl u,
    ?_, hne, ?_, ?_, le_rfl, latePoint_ready hw hc⟩
  · simp [latePoint_submit]
  · intro τ
    simp [latePoint_submit, hne]
  · simpa only [latePoint_ΔAC] using hH

end Consensus.Comparison

end

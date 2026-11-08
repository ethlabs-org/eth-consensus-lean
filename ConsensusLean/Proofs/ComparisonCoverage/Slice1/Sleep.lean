module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Point
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the sleepy late witness point

The point `sleepPoint A Sl T₁ b₀ b₁ u Ts H`: `ΔAC = ΔFG = 2`, every validator asleep before `T₁`,
the sleepers `Sl` also asleep on `[b₀, b₁)`, the validators of `A` compromised from the start,
horizon `H`, transaction `42` submitted to `u` at time `Ts`. With `Sl = ∅` it is the late point of
`Late` with a late submission.

* `sleepPoint_ready`, `sleepPoint_ready_of_ge`: a validator neither compromised nor a sleeper is
  ready from `T₁ + c + 1` on; every honest validator from `b₁ + c + 1` on (for `T₁ ≤ b₁`).
* `sleepPoint_notAwakeHonest`: on the incident `[b₀, b₁)` with `T₁ ≤ b₀ < b₁` and disjoint `A`,
  `Sl`, the validators that cannot vote are exactly `A ∪ Sl`.
* `sleepPoint_holds`, `sleepPoint_safeActive`, `sleepPoint_txLiveActive`: progress and the claims
  after the incident. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf)

variable {V : Type} [DecidableEq V]

/-- The sleepy late witness point. -/
def sleepPoint (A Sl : Finset V) (T₁ b₀ b₁ : Time) (u : V) (Ts H : Time) : EnvPoint V :=
  ⟨⟨2, two_pos, 2, two_pos, fun v t => decide (T₁ ≤ t) && sleepAwake Sl b₀ b₁ v t⟩,
    fun _ => A, monotone_const, H, fun v t => if v = u ∧ t = Ts then [42] else []⟩

section Point

variable (A Sl : Finset V) (T₁ b₀ b₁ : Time) (u : V) (Ts H : Time)

theorem sleepPoint_eq : sleepPoint A Sl T₁ b₀ b₁ u Ts H =
    ⟨⟨2, two_pos, 2, two_pos, fun v t => decide (T₁ ≤ t) && sleepAwake Sl b₀ b₁ v t⟩,
      fun _ => A, monotone_const, H, fun v t => if v = u ∧ t = Ts then [42] else []⟩ := by rfl

@[simp] theorem sleepPoint_ΔAC : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.ΔAC = 2 := by rfl

@[simp] theorem sleepPoint_ΔFG : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.ΔFG = 2 := by rfl

@[simp] theorem sleepPoint_faultyAt (t : Time) : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).faultyAt t = A :=
  by rfl

theorem sleepPoint_faultCount (t : Time) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).faultCount t = A.card := by rfl

@[simp] theorem sleepPoint_horizon : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).horizon = H := by rfl

theorem sleepPoint_submit (v : V) (t : Time) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).submit v t = if v = u ∧ t = Ts then [42] else [] := by rfl

theorem sleepPoint_awake_eq_true {v : V} {t : Time} :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.awake v t = true ↔
      T₁ ≤ t ∧ ¬ (v ∈ Sl ∧ b₀ ≤ t ∧ t < b₁) := by
  change (decide (T₁ ≤ t) && sleepAwake Sl b₀ b₁ v t) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_iff, sleepAwake_eq_true]

variable {A Sl T₁ b₀ b₁ u Ts H}

theorem sleepPoint_honest {v : V} (hv : v ∉ A) (t : Time) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).HonestAt v t := hv

/-- A validator that is not a sleeper is awake from `T₁` on. -/
theorem sleepPoint_awake {v : V} (hs : v ∉ Sl) {t : Time} (ht : T₁ ≤ t) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.awake v t = true :=
  (sleepPoint_awake_eq_true ..).mpr ⟨ht, fun h => hs h.1⟩

/-- Everyone is awake from `max T₁ b₁` on. -/
theorem sleepPoint_awake_of_ge {t : Time} (h1 : T₁ ≤ t) (h2 : b₁ ≤ t) (v : V) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.awake v t = true :=
  (sleepPoint_awake_eq_true ..).mpr ⟨h1, fun h => absurd h.2.2 (not_lt.mpr h2)⟩

theorem le_of_sleepPoint_awake {v : V} {t : Time}
    (h : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.awake v t = true) : T₁ ≤ t :=
  ((sleepPoint_awake_eq_true ..).mp h).1

/-- A validator neither compromised nor a sleeper is ready from `T₁ + c + 1` on. -/
theorem sleepPoint_ready {v : V} (hv : v ∉ A) (hs : v ∉ Sl) {c t : Time} (ht : T₁ + c + 1 ≤ t) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).Ready c v t :=
  ⟨hv, fun t' ht' _ => sleepPoint_awake hs (by
    have := le_max_right 0 (t - c - 1)
    dsimp only [Time] at *
    omega)⟩

/-- An honest validator is ready from `b₁ + c + 1` on, for `T₁ ≤ b₁`. -/
theorem sleepPoint_ready_of_ge {v : V} (hv : v ∉ A) (hT : T₁ ≤ b₁) {c t : Time}
    (ht : b₁ + c + 1 ≤ t) : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).Ready c v t :=
  ⟨hv, fun t' ht' _ => sleepPoint_awake_of_ge
    (by have := le_max_right 0 (t - c - 1); dsimp only [Time] at *; omega)
    (by have := le_max_right 0 (t - c - 1); dsimp only [Time] at *; omega) v⟩

/-- Everyone honest is awake from `max b₁ 0` on, for `T₁ ≤ b₁`. -/
theorem sleepPoint_honestAwakeAfter (hT : T₁ ≤ b₁) :
    ∀ v t, max b₁ 0 ≤ t → t ≤ (sleepPoint A Sl T₁ b₀ b₁ u Ts H).horizon →
      (sleepPoint A Sl T₁ b₀ b₁ u Ts H).HonestAt v t →
      (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.awake v t = true :=
  fun v _ ht _ _ => sleepPoint_awake_of_ge (hT.trans ((le_max_left _ _).trans ht))
    ((le_max_left _ _).trans ht) v

/-- From `b₁ + c + 1` on, at most `|A|` validators are not ready (for `T₁ ≤ b₁`). -/
theorem sleepPoint_readyAt_card [Fintype V] (hT : T₁ ≤ b₁) {c t : Time} (ht : b₁ + c + 1 ≤ t) :
    Fintype.card V ≤ ((sleepPoint A Sl T₁ b₀ b₁ u Ts H).readyAt c t).card + A.card := by
  classical
  have hsub : Finset.univ \ A ⊆ (sleepPoint A Sl T₁ b₀ b₁ u Ts H).readyAt c t := by
    intro v hv
    unfold EnvPoint.readyAt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      sleepPoint_ready_of_ge (Finset.mem_sdiff.mp hv).2 hT ht⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter Finset.univ A
  rw [Finset.univ_inter, Finset.card_univ] at h2
  omega

omit [DecidableEq V] in
private theorem mem_notAwakeHonest_iff'' [Fintype V] [DecidableEq V] {S : System V} {r : S.Run}
    {b₀ b₁ : Time} {v : V} :
    v ∈ notAwakeHonest S b₀ b₁ r ↔ v ∈ (S.pt r).faultyAt (S.pt r).horizon ∨
      (max b₀ 0 < b₁ ∧ ∀ t, max b₀ 0 ≤ t → t < b₁ →
        (S.pt r).HonestAt v t ∧ (S.pt r).env.awake v t = false) := by
  classical
  simp only [notAwakeHonest, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The validators that cannot vote** at a run of the sleepy late point, on its incident
`[b₀, b₁)` with `T₁ ≤ b₀ < b₁` and disjoint `A`, `Sl`: exactly `A ∪ Sl`. -/
theorem sleepPoint_notAwakeHonest [Fintype V] {S : System V} {r : S.Run}
    (hp : S.pt r = sleepPoint A Sl T₁ b₀ b₁ u Ts H) (hb₀ : 0 ≤ b₀) (hT : T₁ ≤ b₀) (hb : b₀ < b₁)
    (hd : Disjoint A Sl) : (notAwakeHonest S b₀ b₁ r).card = A.card + Sl.card := by
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext v
  rw [mem_notAwakeHonest_iff'', hp, Finset.mem_union, sleepPoint_faultyAt, max_eq_left hb₀]
  constructor
  · rintro (ha | ⟨-, h⟩)
    · exact Or.inl ha
    · right
      by_contra hs
      have := (h b₀ le_rfl hb).2
      rw [sleepPoint_awake hs hT] at this
      exact absurd this (by decide)
  · rintro (ha | hs)
    · exact Or.inl ha
    · refine Or.inr ⟨hb, fun t ht htb => ⟨fun ha => Finset.disjoint_left.mp hd ha hs, ?_⟩⟩
      cases h : (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env.awake v t
      · rfl
      · exact absurd ⟨hs, ht, htb⟩ ((sleepPoint_awake_eq_true ..).mp h).2

end Point

/-! ## Progress and active claims -/

variable [Fintype V] {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- A fitting progress requirement that admits `|A|` compromised validators holds on every window
starting at `b₁ + c + 1` of the sleepy late point (for `T₁ ≤ b₁`), under every selection that
agrees with the extremal one on the proposer roles, when key `1` is honest. -/
theorem sleepPoint_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (key : Fin (Fintype.card V) ≃ V) (h2 : 2 ≤ Fintype.card V) {A Sl : Finset V}
    {T₁ b₀ b₁ : Time} {u : V} {Ts H : Time} {p : EnvPoint V}
    (hp : p = sleepPoint A Sl T₁ b₀ b₁ u Ts H)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ s, sel (.proposer s) = extremalSel F p.env (.proposer s))
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (hA : AdmitsFaults (K.progress cap i) A.card) (h1 : key ⟨1, by omega⟩ ∉ A) (hT : T₁ ≤ b₁)
    {c s : Time} (hs : b₁ + c + 1 ≤ s) (e : Time) :
    shapeHolds F (K.progress cap i) c s e p (key, sel) := by
  subst hp
  have hfit := hf cap i (pubOf (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env)
  revert hfit hA
  cases K.progress cap i with
  | recur ρ =>
    intro _ hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    change PatternRecurrence _ _ (fun s => sel (.proposer s)) _ _ _ _ _
    rw [funext hsel]
    intro t ht _ _
    have hSL := (F (pubOf (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env)).skel.grid.slotLen_pos
    obtain ⟨sl, hs₁, hs₂⟩ :=
      (F (pubOf (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env)).skel.grid.exists_slot_in_window
        (le_trans (le_max_right _ _) ht) (k := (ρ.gap : Nat)) ρ.gap.pos
    refine ⟨sl, hs₁, hs₂, fun j _ => ?_⟩
    have hmem := extremalSel_proposer_mem F hfit h2 (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    refine ⟨sleepPoint_ready_of_ge h1 hT ?_, sleepPoint_honest h1 _⟩
    rw [TimeGrid.slotTime_add]
    have h0 : (0 : Time) ≤
        (j : Time) * (F (pubOf (sleepPoint A Sl T₁ b₀ b₁ u Ts H).env)).skel.grid.slotLen :=
      mul_nonneg (by positivity) hSL.le
    have := le_max_left s 0
    linarith
  | notReadyAtMost m =>
    intro hA _ t ht _ _
    have : b₁ + c + 1 ≤ t := hs.trans ((le_max_left _ _).trans ht)
    exact le_trans (sleepPoint_readyAt_card hT this) (Nat.add_le_add_left hA _)

omit [Fintype V] in
/-- Safety is active after `t₀` at the sleepy late point, given room before the horizon. -/
theorem sleepPoint_safeActive {A Sl : Finset V} {T₁ b₀ b₁ : Time} {u : V} {Ts H : Time}
    {v w : V} (hv : v ∉ A) (hw : w ∉ A) (hne : v ≠ w) (hT : T₁ ≤ b₁) (c t₀ : Time)
    (hH : t₀ + 2 ≤ H) (hc : b₁ + c + 2 ≤ H) :
    SafeActive c t₀ (sleepPoint A Sl T₁ b₀ b₁ u Ts H) :=
  ⟨v, w, H - 1, H, hne, by linarith, by linarith, le_rfl,
    sleepPoint_ready_of_ge hv hT (by linarith), sleepPoint_ready_of_ge hw hT (by linarith),
    sleepPoint_ready_of_ge hv hT (by linarith)⟩

omit [Fintype V] in
/-- Liveness is active from `start` at the sleepy late point: transaction `42`, submitted to the
honest `u` at `Ts ≥ max T₁ b₁`, is owed to an honest `w ≠ u` ready at the horizon. -/
theorem sleepPoint_txLiveActive {A Sl : Finset V} {T₁ b₀ b₁ : Time} {u : V} {Ts H : Time}
    {w : V} (hu : u ∉ A) (hw : w ∉ A) (hne : w ≠ u) (hT : T₁ ≤ b₁) (hTs : b₁ ≤ Ts)
    (hTs0 : 0 ≤ Ts) (c start D : Time) (hH : max Ts start + 2 + D ≤ H) (hc : b₁ + c + 1 ≤ H) :
    (sleepPoint A Sl T₁ b₀ b₁ u Ts H).TxLiveActive c start D := by
  refine ⟨42, Ts, H, u, w, hTs0, sleepPoint_honest hu Ts,
    sleepPoint_awake_of_ge (hT.trans hTs) hTs u, ?_, hne, ?_, ?_, le_rfl,
    sleepPoint_ready_of_ge hw hT hc⟩
  · simp [sleepPoint_submit]
  · intro τ
    simp [sleepPoint_submit, hne]
  · simpa only [sleepPoint_ΔAC] using hH

end Consensus.Comparison

end

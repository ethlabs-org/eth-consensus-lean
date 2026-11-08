module
public import ConsensusLean.Comparison.HealCoverage
public import ConsensusLean.Proofs.ComparisonCoverage.Witness
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the witness point

The witness point `cov1Point A Sl b₀ b₁ u H`: `ΔAC = ΔFG = 2`, the validators of `A` compromised
from the start, the validators of `Sl` asleep on `[b₀, b₁)` and awake otherwise, everyone else awake
at every time, horizon `H`, transaction `42` submitted to `u` at time `0`.

* `cov1Point_ready`: a validator neither compromised nor a sleeper is ready at every time with
  every catch-up; a sleeper is ready from `b₁ + c + 1` on.
* `cov1Point_notAwakeHonest`: with `0 ≤ b₀ < b₁`, the validators that cannot vote during the
  incident are exactly `A ∪ Sl`; with no sleepers, exactly `A`.
* `cov1Point_honestAwakeAfter`: everyone honest is awake from `b₁` on.
* `cov1Point_holds`: a fitting progress requirement admitting `|A|` compromised validators holds on
  every window starting at `b₁ + c + 1` (key `1` honest and not a sleeper), under any selection that
  agrees with the extremal one on the proposer roles.
* `cov1Point_safeActive`, `cov1Point_txLiveActive`: the claims are active for every catch-up. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf)

variable {V : Type} [DecidableEq V]

/-- The awake profile of the witness: the sleepers `Sl` are asleep on `[b₀, b₁)`, everyone is awake
otherwise. -/
def sleepAwake (Sl : Finset V) (b₀ b₁ : Time) (v : V) (t : Time) : Bool :=
  !(decide (v ∈ Sl) && decide (b₀ ≤ t) && decide (t < b₁))

theorem sleepAwake_eq_true {Sl : Finset V} {b₀ b₁ : Time} {v : V} {t : Time} :
    sleepAwake Sl b₀ b₁ v t = true ↔ ¬ (v ∈ Sl ∧ b₀ ≤ t ∧ t < b₁) := by
  unfold sleepAwake
  by_cases h1 : v ∈ Sl <;> by_cases h2 : b₀ ≤ t <;> by_cases h3 : t < b₁ <;> simp [h1, h2, h3]

/-- The Slice 1 coverage witness point. -/
def cov1Point (A Sl : Finset V) (b₀ b₁ : Time) (u : V) (H : Time) : EnvPoint V :=
  ⟨⟨2, two_pos, 2, two_pos, sleepAwake Sl b₀ b₁⟩, fun _ => A, monotone_const, H,
    fun v t => if v = u ∧ t = 0 then [42] else []⟩

section Point

variable (A Sl : Finset V) (b₀ b₁ : Time) (u : V) (H : Time)

@[simp] theorem cov1Point_ΔAC : (cov1Point A Sl b₀ b₁ u H).env.ΔAC = 2 := by rfl

/-- The public parameters of the witness point's environment. -/
theorem cov1Point_pubOf [Fintype V] :
    pubOf (cov1Point A Sl b₀ b₁ u H).env = ⟨Fintype.card V, 2, two_pos, 2, two_pos⟩ := by rfl

@[simp] theorem cov1Point_ΔFG : (cov1Point A Sl b₀ b₁ u H).env.ΔFG = 2 := by rfl

theorem cov1Point_awake (v : V) (t : Time) :
    (cov1Point A Sl b₀ b₁ u H).env.awake v t = sleepAwake Sl b₀ b₁ v t := by rfl

@[simp] theorem cov1Point_faultyAt (t : Time) : (cov1Point A Sl b₀ b₁ u H).faultyAt t = A := by
  rfl

theorem cov1Point_faultCount (t : Time) : (cov1Point A Sl b₀ b₁ u H).faultCount t = A.card := by
  rfl

@[simp] theorem cov1Point_horizon : (cov1Point A Sl b₀ b₁ u H).horizon = H := by rfl

theorem cov1Point_submit (v : V) (t : Time) :
    (cov1Point A Sl b₀ b₁ u H).submit v t = if v = u ∧ t = 0 then [42] else [] := by rfl

variable {A Sl b₀ b₁ u H}

theorem cov1Point_honest {v : V} (hv : v ∉ A) (t : Time) :
    (cov1Point A Sl b₀ b₁ u H).HonestAt v t := hv

/-- A validator that is not a sleeper is awake at every time. -/
theorem cov1Point_awake_of_not_sleeper {v : V} (hv : v ∉ Sl) (t : Time) :
    (cov1Point A Sl b₀ b₁ u H).env.awake v t = true := by
  rw [cov1Point_awake, sleepAwake_eq_true]
  exact fun h => hv h.1

/-- Every validator is awake from `b₁` on. -/
theorem cov1Point_awake_of_ge {t : Time} (ht : b₁ ≤ t) (v : V) :
    (cov1Point A Sl b₀ b₁ u H).env.awake v t = true := by
  rw [cov1Point_awake, sleepAwake_eq_true]
  exact fun h => absurd h.2.2 (not_lt.mpr ht)

/-- A validator neither compromised nor a sleeper is ready at every time with every catch-up. -/
theorem cov1Point_ready {v : V} (hv : v ∉ A) (hs : v ∉ Sl) (c t : Time) :
    (cov1Point A Sl b₀ b₁ u H).Ready c v t :=
  ⟨hv, fun t' _ _ => cov1Point_awake_of_not_sleeper hs t'⟩

/-- An honest validator is ready from `b₁ + c + 1` on. -/
theorem cov1Point_ready_of_ge {v : V} (hv : v ∉ A) {c t : Time} (ht : b₁ + c + 1 ≤ t) :
    (cov1Point A Sl b₀ b₁ u H).Ready c v t :=
  ⟨hv, fun t' ht' _ => cov1Point_awake_of_ge (by
    have := le_max_right 0 (t - c - 1)
    dsimp only [Time] at *
    omega) v⟩

/-- Everyone honest is awake from `max b₁ 0` on. -/
theorem cov1Point_honestAwakeAfter :
    ∀ v t, max b₁ 0 ≤ t → t ≤ (cov1Point A Sl b₀ b₁ u H).horizon →
      (cov1Point A Sl b₀ b₁ u H).HonestAt v t →
      (cov1Point A Sl b₀ b₁ u H).env.awake v t = true :=
  fun v _ ht _ _ => cov1Point_awake_of_ge ((le_max_left _ _).trans ht) v

/-- From `b₁ + c + 1` on, at most `|A|` validators are not ready. -/
theorem cov1Point_readyAt_card [Fintype V] {c t : Time} (ht : b₁ + c + 1 ≤ t) :
    Fintype.card V ≤ ((cov1Point A Sl b₀ b₁ u H).readyAt c t).card + A.card := by
  classical
  have hsub : Finset.univ \ A ⊆ (cov1Point A Sl b₀ b₁ u H).readyAt c t := by
    intro v hv
    unfold EnvPoint.readyAt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      cov1Point_ready_of_ge (Finset.mem_sdiff.mp hv).2 ht⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter Finset.univ A
  rw [Finset.univ_inter, Finset.card_univ] at h2
  omega

omit [DecidableEq V] in
private theorem mem_notAwakeHonest_iff [Fintype V] [DecidableEq V] {S : System V} {r : S.Run}
    {b₀ b₁ : Time} {v : V} :
    v ∈ notAwakeHonest S b₀ b₁ r ↔ v ∈ (S.pt r).faultyAt (S.pt r).horizon ∨
      (max b₀ 0 < b₁ ∧ ∀ t, max b₀ 0 ≤ t → t < b₁ →
        (S.pt r).HonestAt v t ∧ (S.pt r).env.awake v t = false) := by
  classical
  simp only [notAwakeHonest, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The validators that cannot vote** at a run of the witness point with `0 ≤ b₀ < b₁` and
disjoint `A`, `Sl`: exactly `A ∪ Sl`. -/
theorem cov1Point_notAwakeHonest [Fintype V] {S : System V} {r : S.Run}
    (hp : S.pt r = cov1Point A Sl b₀ b₁ u H) (hb₀ : 0 ≤ b₀) (hb : b₀ < b₁) (hd : Disjoint A Sl) :
    (notAwakeHonest S b₀ b₁ r).card = A.card + Sl.card := by
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext v
  rw [mem_notAwakeHonest_iff, hp, Finset.mem_union, cov1Point_faultyAt, max_eq_left hb₀]
  constructor
  · rintro (ha | ⟨-, h⟩)
    · exact Or.inl ha
    · right
      by_contra hs
      have := (h b₀ le_rfl hb).2
      rw [cov1Point_awake_of_not_sleeper hs] at this
      exact absurd this (by decide)
  · rintro (ha | hs)
    · exact Or.inl ha
    · refine Or.inr ⟨hb, fun t ht htb => ⟨fun ha => Finset.disjoint_left.mp hd ha hs, ?_⟩⟩
      rw [cov1Point_awake]
      cases h : sleepAwake Sl b₀ b₁ v t
      · rfl
      · exact absurd ⟨hs, ht, htb⟩ (sleepAwake_eq_true.mp h)

/-- **The validators that cannot vote** at a run of the witness point without sleepers: exactly
`A`. -/
theorem cov1Point_notAwakeHonest_empty [Fintype V] {S : System V} {r : S.Run}
    (hp : S.pt r = cov1Point A ∅ b₀ b₁ u H) :
    (notAwakeHonest S b₀ b₁ r).card = A.card := by
  congr 1
  ext v
  rw [mem_notAwakeHonest_iff, hp, cov1Point_faultyAt]
  refine ⟨fun h => h.elim id fun ⟨hlt, h⟩ => ?_, Or.inl⟩
  have := (h (max b₀ 0) le_rfl hlt).2
  rw [cov1Point_awake_of_not_sleeper (Finset.notMem_empty v)] at this
  exact absurd this (by decide)

end Point

/-! ## Progress and active claims -/

variable [Fintype V] {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- A fitting progress requirement that admits `|A|` compromised validators holds on every window
starting at `b₁ + c + 1` of the witness point, under every selection that agrees with the extremal
one on the proposer roles, when key `1` is neither compromised nor a sleeper. -/
theorem cov1Point_holds (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (key : Fin (Fintype.card V) ≃ V) (h2 : 2 ≤ Fintype.card V) {A Sl : Finset V}
    {b₀ b₁ : Time} {u : V} {H : Time} {p : EnvPoint V} (hp : p = cov1Point A Sl b₀ b₁ u H)
    (sel : (protoOf (compiled F) p.env).Role → Finset (Fin (Fintype.card V)))
    (hsel : ∀ s, sel (.proposer s) = extremalSel F p.env (.proposer s))
    (hf : ProgressFits K F) (cap : Capability) (i : K.Idx)
    (hA : AdmitsFaults (K.progress cap i) A.card) (h1 : key ⟨1, by omega⟩ ∉ A)
    (h1s : key ⟨1, by omega⟩ ∉ Sl) {c s : Time} (hs : b₁ + c + 1 ≤ s) (e : Time) :
    shapeHolds F (K.progress cap i) c s e p (key, sel) := by
  subst hp
  have hfit := hf cap i (pubOf (cov1Point A Sl b₀ b₁ u H).env)
  revert hfit hA
  cases K.progress cap i with
  | recur ρ =>
    intro _ hfit
    change ∀ s, (F _).skel.proposerSel s = .sized 1 at hfit
    change PatternRecurrence _ _ (fun s => sel (.proposer s)) _ _ _ _ _
    rw [funext hsel]
    apply patternRecurrence_of_all
    intro sl j _
    have hmem := extremalSel_proposer_mem F hfit h2 (sl + j)
    refine ⟨⟨⟨1, by omega⟩, (hmem _).mpr rfl⟩, fun k hk => ?_⟩
    have hk1 : k = ⟨1, by omega⟩ := Fin.ext ((hmem k).mp hk)
    subst hk1
    exact ⟨cov1Point_ready h1 h1s _ _, cov1Point_honest h1 _⟩
  | notReadyAtMost m =>
    intro hA _ t ht _ _
    have : b₁ + c + 1 ≤ t := hs.trans ((le_max_left _ _).trans ht)
    exact le_trans (cov1Point_readyAt_card this) (Nat.add_le_add_left hA _)

omit [Fintype V] in
/-- Safety is active after `t₀` at the witness point, for every catch-up. -/
theorem cov1Point_safeActive {A Sl : Finset V} {b₀ b₁ : Time} {u : V} {H : Time} {v w : V}
    (hv : v ∉ A) (hvs : v ∉ Sl) (hw : w ∉ A) (hws : w ∉ Sl) (hne : v ≠ w) (c t₀ : Time)
    (hH : t₀ + 2 ≤ H) : SafeActive c t₀ (cov1Point A Sl b₀ b₁ u H) :=
  ⟨v, w, t₀ + 1, t₀ + 2, hne, lt_add_one t₀, by linarith, hH,
    cov1Point_ready hv hvs _ _, cov1Point_ready hw hws _ _, cov1Point_ready hv hvs _ _⟩

omit [Fintype V] in
/-- Liveness is active from `start` at the witness point, for every catch-up. -/
theorem cov1Point_txLiveActive {A Sl : Finset V} {b₀ b₁ : Time} {u : V} {H : Time} {w : V}
    (hu : u ∉ A) (hus : u ∉ Sl) (hw : w ∉ A) (hws : w ∉ Sl) (hne : w ≠ u) (c start D : Time)
    (hH : max 0 start + 2 + D ≤ H) : (cov1Point A Sl b₀ b₁ u H).TxLiveActive c start D := by
  refine ⟨42, 0, H, u, w, le_rfl, cov1Point_honest hu 0, cov1Point_awake_of_not_sleeper hus 0,
    ?_, hne, ?_, ?_, le_rfl, cov1Point_ready hw hws c H⟩
  · simp [cov1Point_submit]
  · intro τ
    simp [cov1Point_submit, hne]
  · simpa only [cov1Point_ΔAC] using hH

end Consensus.Comparison

end

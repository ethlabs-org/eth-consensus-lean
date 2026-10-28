module
public import ConsensusProblem
public import Mathlib.Tactic
@[expose] public section

/-! # Tests of the L0 definition of a good protocol

* Vacuous systems are not good (review Astra B3):
  `false_progress_not_good` (a progress reader that never holds violates
  `Realizable` for `|V| ≥ 5`), `empty_valid_not_good` (no valid run violates
  `Adequate.covers` as soon as one well-formed point has admissible external
  data), `excuse_true_not_good` (an excuse on every run, likewise).
* `prefix_sync_then_async` (review Opus B1): a log synchronous for deadlines up
  to `b = 1` whose later honest send is never received. It meets the premises
  of `Good.sleepySafe_prefix` at `b = 1` (`SyncUntil 1`, sleepy on `[0, 1]`)
  but is not partially synchronous with GST `0`, so the full-run sleepy
  regime (and `DAClaims.sleepySafe`) does not apply.
* `healthy_rotating_sleeper` (review Astra B5): four honest validators, one of
  them asleep at each time in turn. More than ⅔ are honest and awake at every
  time (`HealthyFrom ⅔ 0`), while with catch-up `3` nobody is ready from time
  `3` on: the healthy regime counts awake validators, readiness restricts only
  readers and progress. -/

namespace Consensus.Shape.Tests.Good

section Vacuous

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract' S.schema Prog}

/-- A progress reader that never holds: not good (for `|V| ≥ 5`). -/
theorem false_progress_not_good (hX : ∀ π c s e p x, ¬ X.holds π c s e p x)
    (h5 : 5 ≤ Fintype.card V) : ¬ Good S X K := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  obtain ⟨r, -, -, -, hp, -⟩ := (h.realizable h5).sleepy .available i 1 one_pos
  exact hX _ _ _ _ _ _ hp

omit [Fintype V] [DecidableEq V] in
/-- No valid run: not adequate, as soon as some well-formed point has
admissible external data. -/
theorem empty_valid_not_adequate (hS : ∀ r, ¬ S.Valid r)
    (hX : ∃ (p : EnvPoint V) (e : X.Ext p.env), p.WellFormed ∧ X.Admits p.env e) :
    ¬ S.Adequate X := by
  rintro ⟨hc, -⟩
  obtain ⟨p, e, hp, he⟩ := hX
  obtain ⟨r, hv, -⟩ := hc p hp e he 0
  exact hS r hv

/-- No valid run: not good. -/
theorem empty_valid_not_good (hS : ∀ r, ¬ S.Valid r)
    (hX : ∃ (p : EnvPoint V) (e : X.Ext p.env), p.WellFormed ∧ X.Admits p.env e) :
    ¬ Good S X K :=
  fun h => empty_valid_not_adequate hS hX h.adequate

/-- An excuse on every run: not good. -/
theorem excuse_true_not_good (hS : ∀ r, S.Excuse r)
    (hX : ∃ (p : EnvPoint V) (e : X.Ext p.env), p.WellFormed ∧ X.Admits p.env e) :
    ¬ Good S X K := by
  rintro ⟨-, ⟨hc, -⟩, -⟩
  obtain ⟨p, e, hp, he⟩ := hX
  obtain ⟨r, -, hne, -⟩ := hc p hp e he 0
  exact hne (hS r)

end Vacuous

section Prefix

/-- Two honest, always-awake validators, `Δ = 1`, horizon `3`, no
submissions. -/
def prefixPoint : EnvPoint (Fin 2) :=
  ⟨⟨1, by decide, 0, fun _ _ => true⟩, Finset.univ, 3, fun _ _ => []⟩

/-- Validator `0` sends at `2`; nobody ever receives anything. -/
def prefixLog : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 2, fun _ _ _ => False, fun _ _ => []⟩

theorem prefixPoint_readyAt (c t : Time) : prefixPoint.readyAt c t = Finset.univ := by
  classical
  unfold EnvPoint.readyAt
  apply Finset.filter_true_of_mem
  intro v _
  exact ⟨Finset.mem_univ _, fun _ _ _ => rfl⟩

theorem prefixPoint_faulty : prefixPoint.faulty = ∅ := by
  unfold EnvPoint.faulty prefixPoint; simp

/-- A log synchronous up to `1` and silent after: the premises of
`Good.sleepySafe_prefix` at `b = 1` hold (for every `θ ≤ ½` and catch-up), the
full-run sleepy regime does not (for every contract numbers). -/
theorem prefix_sync_then_async :
    prefixLog.SyncUntil prefixPoint 1 ∧
      (∀ θ c, θ ≤ 1 / 2 → prefixPoint.SleepyOn θ c 0 1) ∧
      ¬ prefixLog.PSync prefixPoint 0 ∧
      ∀ {Idx : Type} (P : Params Idx), ¬ Regime.Sleepy P prefixPoint prefixLog := by
  have hnp : ¬ prefixLog.PSync prefixPoint 0 := by
    intro h
    obtain ⟨t', ht', hs, -⟩ := h.msgs 0 (Finset.mem_univ _) () 2 ⟨rfl, rfl⟩ 1 (Finset.mem_univ _)
      (by decide) (by decide) rfl
    rcases hs with ⟨h1, -⟩ | h1
    · exact absurd h1 (by decide)
    · exact h1
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hnp, fun P h => hnp h.1⟩
  · rintro v - m t ⟨-, rfl⟩ w - hc - -
    exact absurd hc (by decide)
  · rintro v - m t ⟨-, rfl⟩ w - a ha hc - -
    have h2 : ∀ a : Int, 2 < a → ¬ a + 1 ≤ 1 := by intro a h; omega
    exact absurd hc (h2 a ha)
  · intro u _ x τ _ _ hx
    exact absurd hx (by simp [prefixPoint])
  · intro θ c hθ t _ _
    apply EnvPoint.ReadyAbove.mono _ _ hθ
    unfold EnvPoint.ReadyAbove
    rw [prefixPoint_readyAt, prefixPoint_faulty]
    norm_num

end Prefix

section Rotating

/-- Four honest validators; at time `t`, validator `t mod 4` sleeps. `Δ = 1`,
horizon `10`. -/
def rotPoint : EnvPoint (Fin 4) :=
  ⟨⟨1, by decide, 0, fun v t => decide (t % 4 ≠ ((v : Nat) : Int))⟩, Finset.univ, 10,
    fun _ _ => []⟩

theorem rotPoint_awake_card (t : Int) : (rotPoint.awakeAt t).card = 3 := by
  classical
  have hm : 0 ≤ t % 4 ∧ t % 4 < 4 :=
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  have hk : ∃ k : Fin 4, t % 4 = ((k : Nat) : Int) :=
    ⟨⟨(t % 4).toNat, by omega⟩, by simp only; omega⟩
  obtain ⟨k, hk⟩ := hk
  have : rotPoint.awakeAt t = Finset.univ.erase k := by
    ext v
    simp only [EnvPoint.awakeAt, rotPoint, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, decide_eq_true_eq, ne_eq, and_true, hk]
    constructor
    · intro h hv; exact h (by rw [hv])
    · intro h hv; exact h (Fin.ext (by exact_mod_cast hv.symm))
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]
  rfl

/-- Healthy at ⅔ from time `0` (three of four awake at every time), while
with catch-up `3` nobody is ready from time `3` on. -/
theorem healthy_rotating_sleeper :
    rotPoint.HealthyFrom (2 / 3) 0 ∧ ∀ t, 3 ≤ t → rotPoint.readyAt 3 t = ∅ := by
  refine ⟨fun t _ _ => ?_, fun t ht => ?_⟩
  · unfold EnvPoint.AwakeOfAll
    rw [rotPoint_awake_card]
    norm_num
  · classical
    unfold EnvPoint.readyAt
    apply Finset.filter_false_of_mem
    rintro v - ⟨-, hA⟩
    have hv : (v : Nat) < 4 := v.isLt
    have a1 : ∀ t v : Int, 3 ≤ t → 0 ≤ v → v < 4 → max 0 (t - 3 - 1) ≤ t - (t - v) % 4 := by
      intros; omega
    have a2 : ∀ t v : Int, 0 ≤ v → v < 4 → t - (t - v) % 4 ≤ t := by intros; omega
    have a3 : ∀ t v : Int, 0 ≤ v → v < 4 → (t - (t - v) % 4) % 4 = v := by intros; omega
    have hv0 : (0 : Int) ≤ ((v : Nat) : Int) := by positivity
    have hv4 : ((v : Nat) : Int) < 4 := by exact_mod_cast hv
    have hu := hA (t - (t - ((v : Nat) : Int)) % 4) (a1 t _ ht hv0 hv4) (a2 t _ hv0 hv4)
    simp only [rotPoint, decide_eq_true_eq] at hu
    exact hu (a3 t _ hv0 hv4)

end Rotating

end Consensus.Shape.Tests.Good

end

module
public import ConsensusProblem
public import Mathlib.Tactic
@[expose] public section

/-! # Tests of the L0 definition of a good protocol

* Vacuous systems are not good (review Astra B3):
  `false_progress_not_good` (a progress reader that never holds violates
  `Realizable` for `|V| ≥ 5`), `no_admissible_not_good` (no admissible
  external data, e.g. `Admits := False`, violates `Adequate.admits`),
  `empty_valid_not_good` (no valid run violates `Adequate.covers`),
  `excuse_true_not_good` (an excuse on every run, likewise).
* `prefix_sync_then_async` (review Opus B1): a log synchronous for deadlines up
  to `b = 1` whose later honest send is never received. It meets the premises
  of `Good.sleepySafe_prefix` at `b = 1` (`SyncUntil 1`, sleepy on `[0, 1]`)
  but is not partially synchronous with GST `0`, so the full-run sleepy
  regime (and `DAClaims.sleepySafe`) does not apply.
* `healthy_rotating_sleeper` (review Astra B5, iteration 6 stage 4 B2): four
  honest validators, one of them asleep at each time in turn. More than ⅔ are
  honest and awake at every time, but no validator is awake throughout, so the
  healthy regime (one fixed set awake throughout, no churn) is **rejected**;
  with catch-up `3` nobody is ready from time `3` on.
* `eta_sleepy_history_sensitive` (stage 4 B1): the same rotation with
  catch-up `0` is plain ½-sleepy at every time, but not ½-η-sleepy with
  look-back `2` (at time `4` two validators are ready, all four were ready in
  `[2, 4]`): the outage regime's participation is history-sensitive.
* `stable_alias_final_sleepy_live` (override 3): a schema that aliases stable
  to final must make the final output live in the sleepy regime. -/

namespace Consensus.Shape.Tests.Good

section Vacuous

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract S.schema Prog}

/-- A progress reader that never holds: not good (for `|V| ≥ 5`). -/
theorem false_progress_not_good (hX : ∀ π c s e p x, ¬ X.holds π c s e p x)
    (h5 : 5 ≤ Fintype.card V) : ¬ Good S X K := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  obtain ⟨r, -, -, -, hp, -⟩ := (h.realizable h5).sleepy .available i 1 one_pos
  exact hX _ _ _ _ _ _ hp

/-- A well-formed point: `Δ = 1`, GST `0`, everybody awake, nobody honest,
horizon `0`, no submissions. -/
def trivPoint (V : Type) : EnvPoint V :=
  ⟨⟨1, by decide, fun _ _ => true⟩, ∅, 0, fun _ _ => []⟩

omit [Fintype V] [DecidableEq V] in
/-- No admissible external data (e.g. `Admits := False`): not adequate. -/
theorem no_admissible_not_adequate (hX : ∀ E e, ¬ X.Admits E e) : ¬ S.Adequate X := by
  intro h
  obtain ⟨e, he⟩ := h.admits (trivPoint V).env
  exact hX _ e he

/-- No admissible external data: not good. -/
theorem no_admissible_not_good (hX : ∀ E e, ¬ X.Admits E e) : ¬ Good S X K :=
  fun h => no_admissible_not_adequate hX h.adequate

omit [Fintype V] [DecidableEq V] in
/-- No valid run: not adequate. -/
theorem empty_valid_not_adequate (hS : ∀ r, ¬ S.Valid r) : ¬ S.Adequate X := by
  intro h
  obtain ⟨e, he⟩ := h.admits (trivPoint V).env
  obtain ⟨r, hv, -⟩ := h.covers (trivPoint V) le_rfl e he 0
  exact hS r hv

/-- No valid run: not good. -/
theorem empty_valid_not_good (hS : ∀ r, ¬ S.Valid r) : ¬ Good S X K :=
  fun h => empty_valid_not_adequate hS h.adequate

/-- An excuse on every run: not good. -/
theorem excuse_true_not_good (hS : ∀ r, S.Excuse r) : ¬ Good S X K := by
  intro h
  obtain ⟨e, he⟩ := h.adequate.admits (trivPoint V).env
  obtain ⟨r, -, hne, -⟩ := h.adequate.covers (trivPoint V) le_rfl e he 0
  exact hne (hS r)

end Vacuous

section Prefix

/-- Two honest, always-awake validators, `Δ = 1`, horizon `3`, no
submissions. -/
def prefixPoint : EnvPoint (Fin 2) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ, 3, fun _ _ => []⟩

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
  ⟨⟨1, by decide, fun v t => decide (t % 4 ≠ ((v : Nat) : Int))⟩, Finset.univ, 10,
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

/-- More than ⅔ honest and awake at every time, yet not healthy from `0`: every
validator sleeps at some time in `[0, 10]`, so no fixed set stays awake (no
churn allowed). With catch-up `3` nobody is ready from time `3` on. -/
theorem healthy_rotating_sleeper :
    (∀ t, rotPoint.AwakeOfAll (2 / 3) t) ∧ ¬ rotPoint.HealthyFrom (2 / 3) 0 ∧
      ∀ t, 3 ≤ t → rotPoint.readyAt 3 t = ∅ := by
  refine ⟨fun t => ?_, ?_, fun t ht => ?_⟩
  · unfold EnvPoint.AwakeOfAll
    rw [rotPoint_awake_card]
    norm_num
  · rintro ⟨H, -, hc, ha⟩
    have hne : H.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℚ) < H.card := lt_of_le_of_lt (by positivity) hc
      exact_mod_cast this
    obtain ⟨v, hv⟩ := hne
    have hv4 : (v : Nat) < 4 := v.isLt
    have hu := ha v hv ((v : Nat) : Int) (by simp) (by change _ ≤ (10 : Int); omega)
    simp [rotPoint] at hu
    exact hu (Int.emod_eq_of_lt (by positivity) (by omega))
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

theorem rotPoint_faulty : rotPoint.faulty = ∅ := by
  unfold EnvPoint.faulty rotPoint; simp

/-- The rotation with catch-up `0` is plain ½-sleepy on `[0, 10]` (some
validator is ready at every time), but not ½-η-sleepy with look-back `2`: at
time `4` only validators `1` and `2` are ready, while all four were ready at
some time in `[2, 4]`. -/
theorem eta_sleepy_history_sensitive :
    rotPoint.SleepyOn (1 / 2) 0 0 10 ∧ ¬ rotPoint.EtaSleepyOn (1 / 2) 2 0 0 10 := by
  classical
  refine ⟨fun t ht0 _ => ?_, fun h => ?_⟩
  · have hne : (rotPoint.readyAt 0 t).Nonempty := by
      refine ⟨⟨((t + 1) % 4).toNat, by omega⟩, ?_⟩
      unfold EnvPoint.readyAt
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, fun u h1 h2 => ?_⟩
      simp only [rotPoint, decide_eq_true_eq, ne_eq]
      dsimp only [Time] at *
      omega
    have hc : (0 : ℚ) < (rotPoint.readyAt 0 t).card := by exact_mod_cast hne.card_pos
    unfold EnvPoint.ReadyAbove
    rw [rotPoint_faulty, Finset.card_empty]
    push_cast
    linarith
  · have h4 := h 4 (by norm_num) (by norm_num)
    unfold EnvPoint.EtaReadyAbove at h4
    have hin : rotPoint.readyIn 0 (4 - 2) 4 ∪ rotPoint.faulty = Finset.univ := by
      rw [rotPoint_faulty, Finset.union_empty]
      apply Finset.eq_univ_of_forall
      intro v
      unfold EnvPoint.readyIn
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      fin_cases v
      · exact ⟨2, by norm_num, by norm_num, Finset.mem_univ _, fun u h1 h2 => by
          simp only [rotPoint, decide_eq_true_eq, ne_eq]; simp at h1 ⊢
          dsimp only [Time] at *; omega⟩
      · exact ⟨4, by norm_num, le_rfl, Finset.mem_univ _, fun u h1 h2 => by
          simp only [rotPoint, decide_eq_true_eq, ne_eq]; simp at h1 ⊢
          dsimp only [Time] at *; omega⟩
      · exact ⟨4, by norm_num, le_rfl, Finset.mem_univ _, fun u h1 h2 => by
          simp only [rotPoint, decide_eq_true_eq, ne_eq]; simp at h1 ⊢
          dsimp only [Time] at *; omega⟩
      · exact ⟨2, by norm_num, by norm_num, Finset.mem_univ _, fun u h1 h2 => by
          simp only [rotPoint, decide_eq_true_eq, ne_eq]; simp at h1 ⊢
          dsimp only [Time] at *; omega⟩
    have hat : rotPoint.readyAt 0 4 ⊆ {1, 2} := by
      intro v hv
      unfold EnvPoint.readyAt at hv
      obtain ⟨-, -, hA⟩ := Finset.mem_filter.mp hv
      have h3 := hA 3 (by norm_num) (by norm_num)
      have h4' := hA 4 (by norm_num) le_rfl
      simp only [rotPoint, decide_eq_true_eq, ne_eq] at h3 h4'
      fin_cases v <;> simp_all
    have hcard : (rotPoint.readyAt 0 4).card ≤ 2 :=
      (Finset.card_le_card hat).trans (by decide)
    rw [hin, Finset.card_univ, Fintype.card_fin] at h4
    have : ((rotPoint.readyAt 0 4).card : ℚ) ≤ 2 := by exact_mod_cast hcard
    norm_num at h4
    linarith

end Rotating

section Alias

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract S.schema Prog}

/-- Stable aliased to final (override 3): if a good system's stable and final
outputs are the same identifier, the final output is live in the sleepy
regime. So a schema with `stable := final` is good only if its final output is
sleepy-live. -/
theorem stable_alias_final_sleepy_live (h : Good S X K) {g : S.schema.Id}
    (hs : S.schema.output .stable = some g) (_hf : S.schema.output .final = some g)
    (i : K.Idx) :
    S.Holds (fun r => S.Sleepy K r ∧ S.prog X K .stable i 0 (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g 0 (S.lat K .stable i r)) :=
  (h.behaviour.da .stable g (Or.inr rfl) hs).sleepyLive i

end Alias

end Consensus.Shape.Tests.Good

end

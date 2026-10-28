module
public import ConsensusProblem
public import ConsensusShapeTests.Regimes
public import Mathlib.Tactic
@[expose] public section

/-! # Tests of the L0 definition of a good protocol

* Submission-dependent censoring progress is rejected by `submit_irrel`.
* Vacuous systems are not good:
  `false_progress_not_good` (a progress reader that never holds violates
  `Realizable` for `|V| ≥ 5`), `no_admissible_not_good` (no admissible
  external data, e.g. `Admits := False`, violates `Adequate.admits`),
  `empty_valid_not_good` (no valid run violates `Adequate.covers`),
  `excuse_true_not_good` (an excuse on every run, likewise).
* `prefix_sync_then_async`: a log synchronous for deadlines up
  to `b = 1` whose later honest send is never received. It meets the premises
  of `Good.sleepySafe_prefix` at `b = 1` (`SyncUntil 1`, sleepy on `[0, 1]`)
  but is not partially synchronous with GST `0`, so the full-run sleepy
  regime (and `DAClaims.sleepySafe`) does not apply.
* `healthy_rotating_sleeper`: four
  honest validators, one of them asleep at each time in turn. More than ⅔ are
  honest and awake at every time, but no validator is awake throughout, so the
  healthy regime (one fixed set awake throughout, no churn) is **rejected**;
  with catch-up `3` nobody is ready from time `3` on.
* `eta_sleepy_history_sensitive`: the same rotation with
  catch-up `0` is plain ½-sleepy at every time, but not ½-η-sleepy with
  look-back `2` (at time `4` two validators are ready, all four were awake in
  `[2, 4]`): the outage regime's participation is history-sensitive. It meets
  the awake-count form, so the contract's form is the stronger premise.
* `eta_sleepy_counts_brief`: honest validators awake only
  briefly (never ready) count against η-sleepy participation in the look-back
  window, as in the awake-count form.
* `eta_sleepy_startup`: no participation history before time
  `0`; honest validators asleep throughout do not count at startup.
* `stable_alias_final_sleepy_live` (override 3): a schema that aliases stable
  to final must make the final output live in the sleepy regime. -/

namespace Consensus.EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- More than fraction `φ` of all validators are honest and awake at `t`
(moved from L0: only this documentation test uses it). -/
def AwakeOfAll (φ : ℚ) (t : Time) : Prop :=
  φ * Fintype.card V < ((p.awakeAt t).card : ℚ)

omit [DecidableEq V] in
/-- A smaller fraction of all validators honest and awake is weaker. -/
theorem AwakeOfAll.mono {φ φ' : ℚ} {t : Time} (h : p.AwakeOfAll φ' t) (hle : φ ≤ φ') :
    p.AwakeOfAll φ t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

variable {p}

omit [DecidableEq V] in
/-- Healthy on `[max g 0, b]` gives more than `φ·n` honest and awake at every
time in it. -/
theorem HealthyOn.awakeOfAll {φ : ℚ} {g b t : Time} (h : p.HealthyOn φ g b)
    (ht : max g 0 ≤ t) (htb : t ≤ b) : p.AwakeOfAll φ t := by
  classical
  obtain ⟨H, hH, hc, ha⟩ := h
  have hsub : H ⊆ p.awakeAt t := by
    intro v hv
    unfold awakeAt
    exact Finset.mem_filter.mpr ⟨hH hv, ha v hv t ht htb⟩
  have : (H.card : ℚ) ≤ (p.awakeAt t).card := by exact_mod_cast Finset.card_le_card hsub
  unfold AwakeOfAll
  linarith

end Consensus.EnvPoint

namespace Consensus.Shape.Tests.Good

section Vacuous

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract S.schema Prog}

omit [Fintype V] [DecidableEq V] in
/-- A reader cannot gate progress on every submission being transaction `42`. -/
theorem censoring_progress_rejected (v : V) (π : Prog) (c s e : Time)
    (p : EnvPoint V) (x : X.Ext p.env)
    (h : ∀ σ : V → Time → List Tx,
      X.holds π c s e {p with submit := σ} x ↔
        ∀ v t y, y ∈ σ v t → y = 42) : False := by
  have hempty := (h (fun _ _ => [])).mpr (by simp)
  have hfull := X.submit_irrel (fun _ _ => [43]) hempty
  have hall := (h (fun _ _ => [43])).mp hfull
  have := hall v 0 43 (by simp)
  norm_num at this

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
time `4` only validators `1` and `2` are ready, while all four were awake at
some time in `[2, 4]`. It does meet the awake-count form (three of four awake
at every time): the contract's ready-numerator form is the stronger premise. -/
theorem eta_sleepy_history_sensitive :
    rotPoint.SleepyOn (1 / 2) 0 0 10 ∧ ¬ rotPoint.EtaSleepyOn (1 / 2) 2 0 0 10 ∧
      ∀ t, (1 / 2 : ℚ) * ((rotPoint.awakeIn (max 0 (t - 2)) t ∪ rotPoint.faulty).card : ℚ) <
        (rotPoint.awakeAt t).card := by
  classical
  refine ⟨fun t ht0 _ => ?_, fun h => ?_, fun t => ?_⟩
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
    rw [EnvPoint.EtaReadyAbove,
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (2 : Time) ≤ 0 by norm_num))] at h4
    have hin : rotPoint.readyAt 0 4 ∪ rotPoint.awakeIn (max 0 (4 - 2)) 4 ∪ rotPoint.faulty =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      unfold EnvPoint.awakeIn
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      fin_cases v
      · exact ⟨2, by norm_num, by norm_num, by decide⟩
      · exact ⟨2, by norm_num, by norm_num, by decide⟩
      · exact ⟨3, by norm_num, by norm_num, by decide⟩
      · exact ⟨2, by norm_num, by norm_num, by decide⟩
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
  · rw [rotPoint_awake_card]
    have : ((rotPoint.awakeIn (max 0 (t - 2)) t ∪ rotPoint.faulty).card : ℚ) ≤ 4 := by
      have := Finset.card_le_univ (rotPoint.awakeIn (max 0 (t - 2)) t ∪ rotPoint.faulty)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    push_cast
    linarith

end Rotating

section EtaHistory

/-- Ten validators, `0` faulty, `1`–`3` honest and always awake, `4`–`9`
honest and awake only at time `0`. `Δ = 1`, horizon `10`. -/
def briefPoint : EnvPoint (Fin 10) :=
  ⟨⟨1, by decide, fun v t => decide ((v : Nat) ≤ 3 ∨ t = 0)⟩, Finset.univ.erase 0, 10,
    fun _ _ => []⟩

theorem briefPoint_faulty : briefPoint.faulty = {0} := by
  unfold EnvPoint.faulty briefPoint; ext v; simp

theorem briefPoint_readyAt : briefPoint.readyAt 0 1 = {1, 2, 3} := by
  classical
  ext v
  simp only [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, briefPoint,
    Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, -, hA⟩
    have h1 := hA 1 (by norm_num) le_rfl
    have h3 : (v : Nat) ≤ 3 := by
      rcases h1 with h | h
      · exact h
      · norm_num at h
    clear hA h1
    fin_cases v <;> simp_all
  · intro hv
    refine ⟨?_, ?_, fun u _ _ => ?_⟩ <;> fin_cases v <;> simp_all

/-- Briefly awake participants count: validators `4`–`9`
are awake only at `0`, so at time `1` they are not ready. With catch-up `0` the
run is plain ½-sleepy at `1` (`½·(3 + 1) < 3`), but not ½-η-sleepy with
look-back `2`: the window `[0, 1]` sees nine honest validators awake
(`½·10 ≮ 3`). This matches the awake-count form, which also fails here. -/
theorem eta_sleepy_counts_brief :
    briefPoint.ReadyAbove (1 / 2) 0 1 ∧ ¬ briefPoint.EtaReadyAbove (1 / 2) 2 0 1 := by
  classical
  refine ⟨?_, fun h => ?_⟩
  · unfold EnvPoint.ReadyAbove
    rw [briefPoint_readyAt, briefPoint_faulty]
    norm_num
  · rw [EnvPoint.EtaReadyAbove,
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (2 : Time) ≤ 0 by norm_num))] at h
    have hin : briefPoint.readyAt 0 1 ∪ briefPoint.awakeIn (max 0 (1 - 2)) 1 ∪
        briefPoint.faulty = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      by_cases h0 : v = 0
      · exact Finset.mem_union_right _ (by rw [briefPoint_faulty, h0]; simp)
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        simp only [EnvPoint.awakeIn, briefPoint, Finset.mem_filter, Finset.mem_erase,
          Finset.mem_univ, and_true, decide_eq_true_eq]
        exact ⟨h0, 0, by norm_num, by norm_num, Or.inr rfl⟩
    rw [hin, briefPoint_readyAt, Finset.card_univ, Fintype.card_fin] at h
    norm_num at h

/-- Seven validators, `0` faulty, `1`–`2` honest and always awake, `3`–`6`
honest and always asleep. `Δ = 1`, horizon `10`. -/
def startPoint : EnvPoint (Fin 7) :=
  ⟨⟨1, by decide, fun v _ => decide ((v : Nat) ≤ 2)⟩, Finset.univ.erase 0, 10,
    fun _ _ => []⟩

theorem startPoint_faulty : startPoint.faulty = {0} := by
  unfold EnvPoint.faulty startPoint; ext v; simp

theorem startPoint_readyAt {t : Time} (ht : 0 ≤ t) : startPoint.readyAt 0 t = {1, 2} := by
  classical
  ext v
  constructor
  · intro hv
    unfold EnvPoint.readyAt at hv
    obtain ⟨hh, -, hA⟩ := Finset.mem_filter.mp hv
    have h1 := hA t (max_le ht (by linarith)) le_rfl
    simp only [startPoint, decide_eq_true_eq] at h1
    simp only [startPoint, Finset.mem_erase, Finset.mem_univ, and_true] at hh
    clear hA hv
    fin_cases v <;> simp_all
  · simp only [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, startPoint,
      Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, decide_eq_true_eq]
    intro hv
    refine ⟨?_, ?_, fun u _ _ => ?_⟩ <;> fin_cases v <;> simp_all

theorem startPoint_awakeIn (a b : Time) : startPoint.awakeIn a b ⊆ {1, 2} := by
  classical
  intro v hv
  simp only [EnvPoint.awakeIn, startPoint, Finset.mem_filter, Finset.mem_erase,
    Finset.mem_univ, and_true, decide_eq_true_eq] at hv
  obtain ⟨h0, -, -, -, h2⟩ := hv
  fin_cases v <;> simp_all

/-- No participation history before time `0`: honest
validators `3`–`6` sleep throughout, and the run is ½-η-sleepy on `[0, 10]`
for every look-back, startup included (`½·3 < 2`). Readiness at negative
times (vacuous) would have counted all seven validators at the start. -/
theorem eta_sleepy_startup (η : Time) : startPoint.EtaSleepyOn (1 / 2) η 0 0 10 := by
  classical
  intro t ht _
  unfold EnvPoint.EtaReadyAbove
  split_ifs
  · unfold EnvPoint.ReadyAbove
    rw [startPoint_readyAt ht, startPoint_faulty]
    norm_num
  · have hsub : startPoint.readyAt 0 t ∪ startPoint.awakeIn (max 0 (t - η)) t ∪
        startPoint.faulty ⊆ {0, 1, 2} := by
      rw [startPoint_readyAt ht, startPoint_faulty]
      intro v hv
      simp only [Finset.mem_union] at hv
      rcases hv with (hv | hv) | hv
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢; tauto
      · have := startPoint_awakeIn _ _ hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢; tauto
    have hc : ((startPoint.readyAt 0 t ∪ startPoint.awakeIn (max 0 (t - η)) t ∪
        startPoint.faulty).card : ℚ) ≤ 3 := by
      have := (Finset.card_le_card hsub).trans (Finset.card_le_three)
      exact_mod_cast this
    have hr : ((startPoint.readyAt 0 t).card : ℚ) = 2 := by rw [startPoint_readyAt ht]; rfl
    rw [hr]
    linarith

end EtaHistory

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

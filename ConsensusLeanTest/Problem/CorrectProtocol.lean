module
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import ConsensusLean.Spec.Problem.Profile
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
public import ConsensusLeanTest.Problem.Regimes
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Tests of the L0 definition of a correct protocol

* Submission-dependent censoring progress is rejected by `submit_irrel`.
* Vacuous systems are not good:
  `false_progress_not_correct` (a progress reader that never holds violates
  `Realizable` for `|V| ≥ 5`), `no_admissible_not_correct` (no admissible
  external data, e.g. `Admits := False`, violates `Adequate.admits`),
  `empty_valid_not_correct` (no valid run violates `Adequate.covers`),
  `excuse_true_not_correct` (an excuse on every run, likewise).
* `prefix_sync_then_async`: a log synchronous for deadlines up
  to `b = 1` whose later honest send is never received. It meets the premises
  of `CorrectProtocol.sleepySafe_prefix` at `b = 1` (`SyncUntil 1`, sleepy on `[0, 1]`)
  but is not partially synchronous with GST `0`, so the full-run sleepy
  regime (and `Behaviour.sleepySafe`) does not apply.
* `healthy_rotating_sleeper`: four
  honest validators, one of them asleep at each time in turn. More than ⅔ are
  honest and awake at every time, but no validator is awake throughout, so the
  healthy regime (full participation: every honest validator awake
  throughout) is **rejected** at every fault bound;
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
  to final must make the final output live in the sleepy regime.
* Profiles (`Profile.Matches`): `profile_matches_controls` (three distinct outputs, one output
  aliasing all three, final only with unadvertised identifiers, available and stable aliased);
  `profile_exact_rejections` (rejection: the match is exact, not a lower bound or an upper bound);
  `profile_unique` (at most one profile matches); `profile_matches_serves` (every profile serves
  a ledger); `profile_not_exhaustive` (an available-only and a final-and-available schema serve a
  ledger and match no profile). -/

namespace Consensus.EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- More than fraction `φ` of all validators are honest and awake at `t`
(moved from L0: only this documentation test uses it). -/
def AwakeOfAll (φ : ℚ) (t : Time) : Prop :=
  φ * Fintype.card V < ((p.awakeAt t).card : ℚ)

/-- A smaller fraction of all validators honest and awake is weaker. -/
theorem AwakeOfAll.mono {φ φ' : ℚ} {t : Time} (h : p.AwakeOfAll φ' t) (hle : φ ≤ φ') :
    p.AwakeOfAll φ t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

variable {p}

/-- Healthy at fault bound `β` on `[max g 0, b]` gives more than `(1 − β)·n`
honest and awake at every time in it (every honest validator is awake). -/
theorem HealthyOn.awakeOfAll {β : ℚ} {g b t : Time} (h : p.HealthyOn β g b)
    (ht : max g 0 ≤ t) (htb : t ≤ b) : p.AwakeOfAll (1 - β) t := by
  classical
  obtain ⟨hc, ha⟩ := h
  have hsub : p.honestAt b ⊆ p.awakeAt t := by
    intro v hv
    unfold awakeAt
    have hh : p.HonestAt v t := fun h => (Finset.mem_sdiff.mp hv).2 (p.faultyAt_mono htb h)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩,
      ha v t ht htb hh⟩
  have : ((p.honestAt b).card : ℚ) ≤ (p.awakeAt t).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hsum : (p.faultyAt b).card + (p.honestAt b).card = Fintype.card V := by
    unfold honestAt
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ (p.faultyAt b)
    omega
  have hsum' : ((p.faultyAt b).card : ℚ) + (p.honestAt b).card = Fintype.card V := by
    exact_mod_cast hsum
  unfold faultCount at hc
  unfold AwakeOfAll
  linarith

end Consensus.EnvPoint

namespace Consensus.Shape.Tests.CorrectProtocol

section Vacuous

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

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
theorem false_progress_not_correct (hX : ∀ π c s e p x, ¬ X.holds π c s e p x)
    (h5 : 5 ≤ Fintype.card V) :
    ¬ CorrectProtocolOn S X K (fun p => p.ConstantFaults) := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  obtain ⟨r, -, -, hp, -⟩ := (h.realizable h5).sleepy .available i 2 2 (by norm_num)
    (by norm_num)
  exact hX _ _ _ _ _ _ hp

/-- A well-formed point: `Δ = 1`, GST `0`, everybody honest and awake,
horizon `0`, no submissions. -/
def trivPoint (V : Type) : EnvPoint V :=
  ⟨⟨1, by decide, 1, by decide, fun _ _ => true⟩, fun _ => ∅,
    monotone_const, 0, fun _ _ => []⟩

omit [Fintype V] [DecidableEq V] in
/-- No admissible external data (e.g. `Admits := False`): not adequate. -/
theorem no_admissible_not_adequate (hX : ∀ E e, ¬ X.Admits E e) : ¬ S.Adequate X := by
  intro h
  obtain ⟨e, he⟩ := h.admits (trivPoint V).env
  exact hX _ e he

/-- No admissible external data: not good. -/
theorem no_admissible_not_correct (hX : ∀ E e, ¬ X.Admits E e) : ¬ CorrectProtocol S X K :=
  fun h => no_admissible_not_adequate hX h.adequate

omit [Fintype V] [DecidableEq V] in
/-- No valid run: not adequate. -/
theorem empty_valid_not_adequate (hS : ∀ r, ¬ S.Valid r) : ¬ S.Adequate X := by
  intro h
  obtain ⟨e, he⟩ := h.admits (trivPoint V).env
  obtain ⟨r, hv, -⟩ := h.covers (trivPoint V) le_rfl e he 0
  exact hS r hv

/-- No valid run: not good. -/
theorem empty_valid_not_correct (hS : ∀ r, ¬ S.Valid r) : ¬ CorrectProtocol S X K :=
  fun h => empty_valid_not_adequate hS h.adequate

/-- An excuse on every run: not good. -/
theorem excuse_true_not_correct (hS : ∀ r, S.Excuse r) : ¬ CorrectProtocol S X K := by
  intro h
  obtain ⟨e, he⟩ := h.adequate.admits (trivPoint V).env
  obtain ⟨r, -, hne, -⟩ := h.adequate.covers (trivPoint V) le_rfl e he 0
  exact hne (hS r)

end Vacuous

section Prefix

/-- Two honest, always-awake validators, `Δ = 2` (deadlines `a + 1`), horizon `3`, no
submissions. -/
def prefixPoint : EnvPoint (Fin 2) :=
  ⟨⟨2, by decide, 2, by decide, fun _ _ => true⟩, fun _ => ∅,
    monotone_const, 3, fun _ _ => []⟩

/-- Validator `0` sends at `2`; nobody ever receives anything. -/
def prefixLog : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 2, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩

theorem prefixPoint_readyAt (c t : Time) : prefixPoint.readyAt c t = Finset.univ := by
  classical
  unfold EnvPoint.readyAt
  apply Finset.filter_true_of_mem
  intro v _
  exact ⟨by simp [EnvPoint.HonestAt, prefixPoint], fun _ _ _ => rfl⟩

theorem prefixPoint_faulty (t : Time) : prefixPoint.faultyAt t = ∅ := rfl

/-- A log synchronous up to `1` and silent after: the premises of
`CorrectProtocol.sleepySafe_prefix` at `b = 1` hold (for every `θ ≤ ½` and catch-up), the
full-run sleepy regime does not (for every contract numbers). -/
theorem prefix_sync_then_async :
    prefixLog.SyncUntil prefixPoint 1 ∧
      (∀ θ c W, θ ≤ 1 / 2 → prefixPoint.SleepyOn θ c W 0 1) ∧
      ¬ prefixLog.PSync prefixPoint 0 ∧
      ∀ {Idx : Type} (P : Params Idx),
        ¬ (prefixLog.PSync prefixPoint 0 ∧
          prefixPoint.SleepyOn P.θ ((P.catchUp : Time) * prefixPoint.env.ΔAC)
            ((P.ahead : Time) * prefixPoint.env.ΔAC) 0
            prefixPoint.horizon) := by
  have hnp : ¬ prefixLog.PSync prefixPoint 0 := by
    intro h
    obtain ⟨t', ht', hs, -⟩ := h.msgs 0 () 2 ⟨rfl, rfl⟩
      (by simp [EnvPoint.HonestAt, prefixPoint]) id 1
      2 le_rfl (by decide) (by decide) (by simp [EnvPoint.HonestAt, prefixPoint])
      (fun _ _ _ => rfl)
    rcases hs with ⟨h1, -⟩ | h1
    · exact absurd h1 (by decide)
    · exact h1
  refine ⟨⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩, ?_, hnp, fun P h => hnp h.1⟩
  · rintro v m t ⟨-, rfl⟩ - - w a ha hc - - -
    have h2 : ∀ a : Int, 2 ≤ a → ¬ a + 2 - 1 ≤ 1 := by intro a h; omega
    exact absurd hc (h2 a ha)
  · intro u x τ _ _ _ hx
    exact absurd hx (by simp [prefixPoint])
  · intro θ c W hθ t _ _
    change prefixPoint.ReadyAbove θ c t
    apply EnvPoint.ReadyAbove.mono _ _ hθ
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [prefixPoint_readyAt, prefixPoint_faulty]
    norm_num

end Prefix

section Rotating

/-- Four honest validators; at time `t`, validator `t mod 4` sleeps. `Δ = 1`,
horizon `10`. -/
def rotPoint : EnvPoint (Fin 4) :=
  ⟨⟨1, by decide, 1, by decide, fun v t => decide (t % 4 ≠ ((v : Nat) : Int))⟩,
    fun _ => ∅, monotone_const, 10,
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
    simp only [EnvPoint.awakeAt, EnvPoint.honestAt, rotPoint, Finset.sdiff_empty,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, decide_eq_true_eq, ne_eq, and_true, hk]
    constructor
    · intro h hv; exact h (by rw [hv])
    · intro h hv; exact h (Fin.ext (by exact_mod_cast hv.symm))
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]
  rfl

/-- More than ⅔ honest and awake at every time, yet not healthy from `0` at
any fault bound: validator `0` sleeps at time `0` (the healthy regime is full
participation). With catch-up `3` nobody is ready from time `3` on. -/
theorem healthy_rotating_sleeper :
    (∀ t, rotPoint.AwakeOfAll (2 / 3) t) ∧ (∀ β, ¬ rotPoint.HealthyOn β 0 rotPoint.horizon) ∧
      ∀ t, 3 ≤ t → rotPoint.readyAt 3 t = ∅ := by
  refine ⟨fun t => ?_, ?_, fun t ht => ?_⟩
  · unfold EnvPoint.AwakeOfAll
    rw [rotPoint_awake_card]
    norm_num
  · intro β h
    have hu := h.2 0 0 (by simp) (by change _ ≤ (10 : Int); omega)
      (by simp [EnvPoint.HonestAt, rotPoint])
    simp [rotPoint] at hu
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

theorem rotPoint_faulty (t : Time) : rotPoint.faultyAt t = ∅ := rfl

/-- The rotation with catch-up `0` is plain ½-sleepy on `[0, 10]` (some
validator is ready at every time), but not ½-η-sleepy with look-back `2`: at
time `4` only validators `1` and `2` are ready, while all four were awake at
some time in `[2, 4]`. It does meet the awake-count form (three of four awake
at every time): the contract's ready-numerator form is the stronger premise. -/
theorem eta_sleepy_history_sensitive :
    rotPoint.SleepyOn (1 / 2) 0 0 0 10 ∧ ¬ rotPoint.EtaSleepyOn (1 / 2) 2 0 0 0 10 ∧
      ∀ t, (1 / 2 : ℚ) * ((rotPoint.awakeIn (max 0 (t - 2)) t ∪ rotPoint.faultyAt t).card : ℚ) <
        (rotPoint.awakeAt t).card := by
  classical
  refine ⟨fun t ht0 _ => ?_, fun h => ?_, fun t => ?_⟩
  · change rotPoint.ReadyAbove (1 / 2) 0 t
    have hne : (rotPoint.readyAt 0 t).Nonempty := by
      refine ⟨⟨((t + 1) % 4).toNat, by omega⟩, ?_⟩
      unfold EnvPoint.readyAt
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simp [EnvPoint.HonestAt, rotPoint], fun u h1 h2 => ?_⟩
      simp only [rotPoint, decide_eq_true_eq, ne_eq]
      dsimp only [Time] at *
      omega
    have hc : (0 : ℚ) < (rotPoint.readyAt 0 t).card := by exact_mod_cast hne.card_pos
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [rotPoint_faulty, Finset.card_empty]
    push_cast
    linarith
  · have h4 := h 4 (by norm_num) (by norm_num)
    change rotPoint.EtaReadyAbove (1 / 2) 2 0 4 at h4
    rw [EnvPoint.EtaReadyAbove,
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (2 : Time) ≤ 0 by norm_num))] at h4
    have hin : rotPoint.readyAt 0 4 ∪ rotPoint.awakeIn (max 0 (4 - 2)) 4 ∪ rotPoint.faultyAt 4 =
        Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      unfold EnvPoint.awakeIn
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      fin_cases v
      · exact ⟨2, by norm_num, by norm_num, by simp [EnvPoint.HonestAt, rotPoint], by decide⟩
      · exact ⟨2, by norm_num, by norm_num, by simp [EnvPoint.HonestAt, rotPoint], by decide⟩
      · exact ⟨3, by norm_num, by norm_num, by simp [EnvPoint.HonestAt, rotPoint], by decide⟩
      · exact ⟨2, by norm_num, by norm_num, by simp [EnvPoint.HonestAt, rotPoint], by decide⟩
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
    have : ((rotPoint.awakeIn (max 0 (t - 2)) t ∪ rotPoint.faultyAt t).card : ℚ) ≤ 4 := by
      have := Finset.card_le_univ (rotPoint.awakeIn (max 0 (t - 2)) t ∪ rotPoint.faultyAt t)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    push_cast
    linarith

end Rotating

section EtaHistory

/-- Ten validators, `0` faulty, `1`–`3` honest and always awake, `4`–`9`
honest and awake only at time `0`. `Δ = 1`, horizon `10`. -/
def briefPoint : EnvPoint (Fin 10) :=
  ⟨⟨1, by decide, 1, by decide, fun v t => decide ((v : Nat) ≤ 3 ∨ t = 0)⟩,
    fun _ => {0}, monotone_const, 10,
    fun _ _ => []⟩

theorem briefPoint_faulty (t : Time) : briefPoint.faultyAt t = {0} := rfl

theorem briefPoint_readyAt : briefPoint.readyAt 0 1 = {1, 2, 3} := by
  classical
  ext v
  simp only [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, briefPoint,
    EnvPoint.HonestAt, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, hA⟩
    have h1 := hA 1 (by norm_num) le_rfl
    have h3 : (v : Nat) ≤ 3 := by
      rcases h1 with h | h
      · exact h
      · norm_num at h
    clear hA h1
    fin_cases v <;> norm_num at *
  · intro hv
    refine ⟨?_, fun u _ _ => ?_⟩ <;> fin_cases v <;> norm_num at *

/-- Briefly awake participants count: validators `4`–`9`
are awake only at `0`, so at time `1` they are not ready. With catch-up `0` the
run is plain ½-sleepy at `1` (`½·(3 + 1) < 3`), but not ½-η-sleepy with
look-back `2`: the window `[0, 1]` sees nine honest validators awake
(`½·10 ≮ 3`). This matches the awake-count form, which also fails here. -/
theorem eta_sleepy_counts_brief :
    briefPoint.ReadyAbove (1 / 2) 0 1 ∧ ¬ briefPoint.EtaReadyAbove (1 / 2) 2 0 1 := by
  classical
  refine ⟨?_, fun h => ?_⟩
  · unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [briefPoint_readyAt, briefPoint_faulty]
    norm_num
  · rw [EnvPoint.EtaReadyAbove,
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (2 : Time) ≤ 0 by norm_num))] at h
    have hin : briefPoint.readyAt 0 1 ∪ briefPoint.awakeIn (max 0 (1 - 2)) 1 ∪
        briefPoint.faultyAt 1 = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      by_cases h0 : v = 0
      · exact Finset.mem_union_right _ (by rw [briefPoint_faulty, h0]; simp)
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        simp only [EnvPoint.awakeIn, briefPoint, EnvPoint.HonestAt, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_singleton, decide_eq_true_eq]
        exact ⟨0, by norm_num, by norm_num, h0, Or.inr rfl⟩
    rw [hin, briefPoint_readyAt, Finset.card_univ, Fintype.card_fin] at h
    norm_num at h

/-- Seven validators, `0` faulty, `1`–`2` honest and always awake, `3`–`6`
honest and always asleep. `Δ = 1`, horizon `10`. -/
def startPoint : EnvPoint (Fin 7) :=
  ⟨⟨1, by decide, 1, by decide, fun v _ => decide ((v : Nat) ≤ 2)⟩,
    fun _ => {0}, monotone_const, 10,
    fun _ _ => []⟩

theorem startPoint_faulty (t : Time) : startPoint.faultyAt t = {0} := rfl

theorem startPoint_readyAt {t : Time} (ht : 0 ≤ t) : startPoint.readyAt 0 t = {1, 2} := by
  classical
  ext v
  constructor
  · intro hv
    unfold EnvPoint.readyAt at hv
    obtain ⟨-, hh, hA⟩ := Finset.mem_filter.mp hv
    have h1 := hA t (max_le ht (by linarith)) le_rfl
    simp only [startPoint, decide_eq_true_eq] at h1
    simp only [EnvPoint.HonestAt, startPoint, Finset.mem_singleton] at hh
    clear hA hv
    fin_cases v <;> norm_num at *
  · simp only [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, startPoint,
      EnvPoint.HonestAt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, decide_eq_true_eq]
    intro hv
    refine ⟨?_, fun u _ _ => ?_⟩ <;> fin_cases v <;> norm_num at *

theorem startPoint_awakeIn (a b : Time) : startPoint.awakeIn a b ⊆ {1, 2} := by
  classical
  intro v hv
  simp only [EnvPoint.awakeIn, startPoint, EnvPoint.HonestAt, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton, decide_eq_true_eq] at hv
  obtain ⟨_, _, _, h0, h2⟩ := hv
  fin_cases v <;> simp_all

/-- No participation history before time `0`: honest
validators `3`–`6` sleep throughout, and the run is ½-η-sleepy on `[0, 10]`
for every look-back, startup included (`½·3 < 2`). Readiness at negative
times (vacuous) would have counted all seven validators at the start. -/
theorem eta_sleepy_startup (η : Time) : startPoint.EtaSleepyOn (1 / 2) η 0 0 0 10 := by
  classical
  intro t ht _
  change startPoint.EtaReadyAbove (1 / 2) η 0 t
  unfold EnvPoint.EtaReadyAbove
  split_ifs
  · unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [startPoint_readyAt ht, startPoint_faulty]
    norm_num
  · have hsub : startPoint.readyAt 0 t ∪ startPoint.awakeIn (max 0 (t - η)) t ∪
        startPoint.faultyAt t ⊆ {0, 1, 2} := by
      rw [startPoint_readyAt ht, startPoint_faulty]
      intro v hv
      simp only [Finset.mem_union] at hv
      rcases hv with (hv | hv) | hv
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢; tauto
      · have := startPoint_awakeIn _ _ hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢; tauto
    have hc : ((startPoint.readyAt 0 t ∪ startPoint.awakeIn (max 0 (t - η)) t ∪
        startPoint.faultyAt t).card : ℚ) ≤ 3 := by
      have := (Finset.card_le_card hsub).trans (Finset.card_le_three)
      exact_mod_cast this
    have hr : ((startPoint.readyAt 0 t).card : ℚ) = 2 := by rw [startPoint_readyAt ht]; rfl
    rw [hr]
    linarith

end EtaHistory

section Alias

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

/-- Stable aliased to final (override 3): if a good system's stable and final
outputs are the same identifier, the final output is live in the sleepy
regime. So a schema with `stable := final` is good only if its final output is
sleepy-live. -/
theorem stable_alias_final_sleepy_live (h : CorrectProtocol S X K) {g : S.schema.Id}
    (hs : S.schema.output .stable = some g) (_hf : S.schema.output .final = some g)
    (i : K.Idx) :
    S.Holds (fun r => S.Sleepy K r ∧ S.prog X K .stable i 0 (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g 0 (S.lat K .stable i r)) :=
  h.behaviour.sleepyLive .stable g (Or.inr rfl) hs i

end Alias

section Profiles

/-- Three distinct outputs, one per capability. -/
def schemaThree : OutputSchema :=
  ⟨Fin 3, fun | .final => some 0 | .stable => some 1 | .available => some 2⟩

/-- One output serving all three capabilities. -/
def schemaOne : OutputSchema := ⟨Unit, fun _ => some ()⟩

/-- Final only, with two identifiers that serve no capability. -/
def schemaFinalOnly : OutputSchema := ⟨Fin 3, fun | .final => some 0 | _ => none⟩

/-- Available and stable aliased to one output, no final. -/
def schemaAvailStable : OutputSchema := ⟨Unit, fun | .final => none | _ => some ()⟩

/-- Available only. -/
def schemaAvailOnly : OutputSchema := ⟨Unit, fun | .available => some () | _ => none⟩

/-- Final and available, no stable. -/
def schemaFinalAvail : OutputSchema :=
  ⟨Fin 2, fun | .final => some 0 | .available => some 1 | .stable => none⟩

/-- Positive controls: each profile matches its schemas, with distinct or aliased outputs and with
identifiers that serve no capability. -/
theorem profile_matches_controls :
    Profile.ebbAndFlow.Matches schemaThree ∧ Profile.ebbAndFlow.Matches schemaOne ∧
      Profile.bft.Matches schemaFinalOnly ∧ Profile.available.Matches schemaAvailStable :=
  ⟨fun cap => by cases cap <;> rfl, fun cap => by cases cap <;> rfl,
    fun cap => by cases cap <;> rfl, fun cap => by cases cap <;> rfl⟩

/-- Rejection: the match is exact. An all-three schema is neither BFT nor available (not a lower
bound), a final-only schema is not Ebb-and-Flow or available, and an available-and-stable schema
is not Ebb-and-Flow or BFT (not an upper bound). -/
theorem profile_exact_rejections :
    ¬ Profile.bft.Matches schemaThree ∧ ¬ Profile.available.Matches schemaThree ∧
      ¬ Profile.ebbAndFlow.Matches schemaFinalOnly ∧ ¬ Profile.available.Matches schemaFinalOnly ∧
      ¬ Profile.ebbAndFlow.Matches schemaAvailStable ∧ ¬ Profile.bft.Matches schemaAvailStable :=
  ⟨fun h => absurd (h .stable) (by decide), fun h => absurd (h .final) (by decide),
    fun h => absurd (h .stable) (by decide), fun h => absurd (h .final) (by decide),
    fun h => absurd (h .final) (by decide), fun h => absurd (h .final) (by decide)⟩

/-- At most one profile matches a schema. -/
theorem profile_unique {p q : Profile} {O : OutputSchema} (hp : p.Matches O)
    (hq : q.Matches O) : p = q := by
  cases p <;> cases q <;> first
    | rfl
    | exact absurd ((hp .final).symm.trans (hq .final)) (by decide)
    | exact absurd ((hp .stable).symm.trans (hq .stable)) (by decide)

/-- Every profile serves a ledger: a schema matching it provides a final or an available output. -/
theorem profile_matches_serves {p : Profile} {O : OutputSchema} (h : p.Matches O) : O.Serves := by
  unfold OutputSchema.Serves
  cases p
  · exact Or.inl (by rw [h .final]; rfl)
  · exact Or.inl (by rw [h .final]; rfl)
  · exact Or.inr (by rw [h .available]; rfl)

/-- The profiles are not exhaustive: an available-only and a final-and-available schema serve a
ledger and match no profile. -/
theorem profile_not_exhaustive :
    schemaAvailOnly.Serves ∧ schemaFinalAvail.Serves ∧
      ∀ p : Profile, ¬ p.Matches schemaAvailOnly ∧ ¬ p.Matches schemaFinalAvail := by
  refine ⟨Or.inr rfl, Or.inl rfl, fun p => ?_⟩
  cases p
  · exact ⟨fun h => absurd (h .final) (by decide), fun h => absurd (h .stable) (by decide)⟩
  · exact ⟨fun h => absurd (h .final) (by decide), fun h => absurd (h .available) (by decide)⟩
  · exact ⟨fun h => absurd (h .stable) (by decide), fun h => absurd (h .final) (by decide)⟩

end Profiles

end Consensus.Shape.Tests.CorrectProtocol

end

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLeanTest.Problem.Growth
public import ConsensusLeanTest.Problem.Regimes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Tests of the continuation side property

* Vacuous systems do not continue, for `|V| ≥ 5`, through `Continues.realizable`:
  `empty_valid_not_continues` (no valid run), `excuse_true_not_continues` (an excuse on every
  run), `false_progress_not_continues` (a progress reader that never holds).
* `handover_of_full_selection`: at full selection the population hand-over supplies the three
  committee conjuncts, given `β ≤ βK`, `β ≤ ½`, `θ ≥ ½`, equal population and committee
  look-aheads, and a population look-ahead of at least `5ΔAC`. The cross-boundary bound at a
  charge time up to `T` comes from the fault bound at `T`; past `T` from the sleepy budget at
  `min (T + ΔAC) horizon`, which is the horizon itself when `T + ΔAC` passes it; with `T` past
  the horizon every charge time is at most `T`.
* `handover_witness`: the hand-over regime and the corruption growth of `realizable` are jointly
  satisfiable. Five validators, all awake, none compromised before `5` and `{0, 1}` from `5` on,
  a silent network, no evidence that convicts, every validator selected: the run hands over at
  `T = 4` after GST `0`, and by `κ = 5` at least fraction `β` (`⅓`) of the validators are
  compromised. -/

namespace Consensus.Shape.Tests.Continuation

section Vacuous

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

/-- No valid run: does not continue (for `|V| ≥ 5`). -/
theorem empty_valid_not_continues (hS : ∀ r, ¬ S.Valid r) (h5 : 5 ≤ Fintype.card V) :
    ¬ Continues S X K := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  have hd : (2 : Time) ≤ (K.params.fgDelay : Time) * 2 :=
    le_mul_of_one_le_left (by norm_num) (by exact_mod_cast K.params.fgDelay.pos)
  obtain ⟨r, -, -, hv, -⟩ := h.realizable h5 .available i 2 2 0 (.inl rfl) (by norm_num)
    (by norm_num) hd le_rfl
  exact hS r hv

/-- An excuse on every run: does not continue (for `|V| ≥ 5`). -/
theorem excuse_true_not_continues (hS : ∀ r, S.Excuse r) (h5 : 5 ≤ Fintype.card V) :
    ¬ Continues S X K := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  have hd : (2 : Time) ≤ (K.params.fgDelay : Time) * 2 :=
    le_mul_of_one_le_left (by norm_num) (by exact_mod_cast K.params.fgDelay.pos)
  obtain ⟨r, -, -, -, hne, -⟩ := h.realizable h5 .available i 2 2 0 (.inl rfl) (by norm_num)
    (by norm_num) hd le_rfl
  exact hne (hS r)

/-- A progress reader that never holds: does not continue (for `|V| ≥ 5`). -/
theorem false_progress_not_continues (hX : ∀ π c s e p x, ¬ X.holds π c s e p x)
    (h5 : 5 ≤ Fintype.card V) : ¬ Continues S X K := by
  intro h
  obtain ⟨i⟩ := K.idx_nonempty
  have hd : (2 : Time) ≤ (K.params.fgDelay : Time) * 2 :=
    le_mul_of_one_le_left (by norm_num) (by exact_mod_cast K.params.fgDelay.pos)
  obtain ⟨r, -, -, -, -, -, -, -, -, hp, -⟩ := h.realizable h5 .available i 2 2 0 (.inl rfl)
    (by norm_num) (by norm_num) hd le_rfl
  exact hX _ _ _ _ _ _ hp

end Vacuous


section FullSelection

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}

/-- **Full-selection specialisation**: when every validator is selected at every time, the
population hand-over (partial synchrony, health up to `T`, the FG delay bound, sleepy
participation from `T`, conviction below `α`) supplies the committee conjuncts of `Handover`. -/
theorem handover_of_full_selection (X : External S) (K : Contract Prog) {g T : Time} {r : S.Run}
    (hX : ∀ t, X.selected (S.pt r).env (X.ext r) t = Finset.univ)
    (hβ : K.params.β ≤ K.params.βK) (hβ2 : K.params.β ≤ 1 / 2) (hθ : 1 / 2 ≤ K.params.θ)
    (hW : S.committeeAheadDur K r = S.aheadDur K r)
    (h5 : 5 * (S.pt r).env.ΔAC ≤ S.aheadDur K r)
    (h : (S.log r).PSync (S.pt r) g ∧ (S.pt r).HealthyOn K.params.β g T ∧
      (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC ∧
      (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) T (S.pt r).horizon ∧
      S.ConvictedBelow K r) :
    S.Handover X K g T r := by
  classical
  obtain ⟨hps, hhe, hfg, hsl, hcb⟩ := h
  set p := S.pt r
  have hn : (0 : ℚ) ≤ Fintype.card V := Nat.cast_nonneg _
  -- fewer than half compromised by `T`
  have hT2 : ∀ d, d ≤ T → 2 * (p.faultyAt d).card < Fintype.card V := by
    intro d hd
    have h1 : ((p.faultyAt d).card : ℚ) < 1 / 2 * Fintype.card V :=
      lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card (p.faultyAt_mono hd))
        (hhe.1.trans_le (mul_le_mul_of_nonneg_right hβ2 hn))
    have h2 : (2 * (p.faultyAt d).card : ℚ) < Fintype.card V := by linarith
    exact_mod_cast h2
  -- fewer than half compromised by the look-ahead of a time of the sleepy window
  have hS2 : ∀ t, T ≤ t → t ≤ p.horizon →
      2 * (p.faultyAt (p.lookAhead (S.aheadDur K r) t)).card < Fintype.card V := by
    intro t ht htb
    set d := p.lookAhead (S.aheadDur K r) t
    have hA := hsl t ht htb
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount at hA
    have hsub : (p.retain d).readyAt (S.cDur K r) t ⊆ Finset.univ \ p.faultyAt d := by
      intro v hv
      simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv.1⟩
    have hR := Finset.card_le_card hsub
    rw [Finset.card_univ_sdiff] at hR
    change K.params.θ * (((p.retain d).readyAt (S.cDur K r) t).card + (p.faultyAt d).card : ℚ) <
      _ at hA
    have hR' : (((p.retain d).readyAt (S.cDur K r) t).card : ℚ) ≤
        Fintype.card V - (p.faultyAt d).card := by
      have := Finset.card_le_univ (p.faultyAt d)
      rw [le_sub_iff_add_le]
      exact_mod_cast (by omega : ((p.retain d).readyAt (S.cDur K r) t).card +
        (p.faultyAt d).card ≤ Fintype.card V)
    have hpos : (0 : ℚ) ≤ ((p.retain d).readyAt (S.cDur K r) t).card + (p.faultyAt d).card := by
      positivity
    have hlt : ((p.faultyAt d).card : ℚ) < ((p.retain d).readyAt (S.cDur K r) t).card := by
      nlinarith [mul_le_mul_of_nonneg_right hθ hpos]
    have h2 : (2 * (p.faultyAt d).card : ℚ) < Fintype.card V := by linarith
    exact_mod_cast h2
  refine ⟨hps, hhe, hfg, hsl, hcb, ?_, ?_, ?_⟩
  · intro t _ _ hne
    rw [hX] at hne ⊢
    rw [Finset.inter_univ, Finset.card_univ]
    exact lt_of_lt_of_le hhe.1 (mul_le_mul_of_nonneg_right hβ hn)
  · intro t ht htb _
    rw [hX, hW]
    have hA := hsl t ht htb
    simpa only [le_refl, ↓reduceIte, Finset.inter_univ, EnvPoint.ReadyAbove, EnvPoint.faultCount,
      Nat.cast_add] using hA
  · intro u hu huT _ _
    change 2 * (_ ∩ X.selected (S.pt r).env (X.ext r) u).card <
      (X.selected (S.pt r).env (X.ext r) u).card
    rw [hX, Finset.inter_univ, Finset.card_univ]
    set m := min (u + 6 * p.env.ΔAC) p.horizon
    have huT' : u ≤ T := huT.trans (min_le_left _ _)
    rcases le_or_gt m T with hmT | hmT
    · exact hT2 m hmT
    · have hTh : T < p.horizon := hmT.trans_le (min_le_right _ _)
      have hΔ := p.env.ΔAC_pos
      set t := min (T + p.env.ΔAC) p.horizon
      have htT : T ≤ t := le_min (by linarith) hTh.le
      have htb : t ≤ p.horizon := min_le_right _ _
      have hmd : m ≤ p.lookAhead (S.aheadDur K r) t := by
        unfold EnvPoint.lookAhead
        rcases le_total (T + p.env.ΔAC) p.horizon with h1 | h1
        · rw [show t = T + p.env.ΔAC from min_eq_left h1]
          exact min_le_min_right _ (by linarith)
        · rw [show t = p.horizon from min_eq_right h1]
          exact le_min ((min_le_right _ _).trans (le_add_of_nonneg_right ((by positivity :
            (0 : Time) ≤ 5 * p.env.ΔAC).trans h5))) (min_le_right _ _)
      exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Finset.card_le_card (p.faultyAt_mono hmd)))
        (hS2 t htT htb)

end FullSelection

section Witness

/-- Five validators, all awake, `Δ = 1`; none compromised before `5`, `{0, 1}` from `5` on;
horizon `10`, no submissions (`Tests.Growth.point` with every validator awake). -/
def handoverPoint : EnvPoint (Fin 5) :=
  { Tests.Growth.point with env := ⟨1, by decide, 1, by decide, fun _ _ => true⟩ }

/-- One run on `handoverPoint`: an empty log, empty views, no conviction, no excuse. -/
def handoverSys : System (Fin 5) where
  schema := ⟨Unit, fun _ => some ()⟩
  Run := Unit
  trace _ := ⟨handoverPoint, 0, fun _ => 0, fun _ _ _ => []⟩
  Valid _ := True
  Obs := Unit
  log _ := Regimes.silentLog (Fin 5) Unit
  view _ _ _ := ∅
  convicts _ _ _ := False
  Excuse _ := False

/-- Every validator selected at every time. -/
def handoverX : External handoverSys where
  Ext _ := Unit
  ext _ := ()
  Admits _ _ := True
  selected _ _ _ := Finset.univ

/-- The standard thresholds (`θ = ½`, `β = α = ⅓`, FG delay bound `1`, look-ahead `0`),
lag `2`, budget `3` (`Regimes.P23`), one index. -/
def handoverK : Contract Unit where
  Idx := Unit
  idx_nonempty := ⟨()⟩
  params := Regimes.P23
  progress _ _ := ()

/-- On the view retained through `d`, the ready validators are the honest ones. -/
theorem handoverPoint_readyAt (d c t : Time) :
    (handoverPoint.retain d).readyAt c t = if 5 ≤ d then {2, 3, 4} else Finset.univ := by
  classical
  ext v
  fin_cases v <;> by_cases hd : 5 ≤ d <;>
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt, EnvPoint.retain,
      EnvPoint.AwakeOnClosed, handoverPoint, Tests.Growth.point, hd]

/-- Half-sleepy participation holds on every retained view: five ready against none
compromised, or three ready against two. -/
theorem handoverPoint_readyAbove (d c t : Time) :
    (handoverPoint.retain d).ReadyAbove (1 / 2) c t := by
  rw [EnvPoint.ReadyAbove, handoverPoint_readyAt]
  by_cases hd : 5 ≤ d <;>
    simp [hd, EnvPoint.faultCount, EnvPoint.retain, handoverPoint, Tests.Growth.point] <;>
    norm_num

/-- The hand-over regime and the corruption growth are jointly satisfiable, and safety is active
after the growth: the run hands over at `T = 4` after GST `0`, at or after the heal point (`0` for
this contract); by `κ = 5 ≤ horizon` at least fraction `β` of the five validators are compromised;
and validators `2` and `3` are ready at `6`, validator `2` again at `7` (`SafeActive` after `κ`). -/
theorem handover_witness :
    ∃ g T κ : Time, g ≤ T ∧ T < κ ∧ κ ≤ (handoverSys.pt ()).horizon ∧
      handoverSys.Handover handoverX handoverK g T () ∧
      handoverSys.heal handoverK .available () g () ≤ T ∧
      handoverK.params.β * 5 ≤ ((handoverSys.pt ()).faultCount κ : ℚ) ∧
      SafeActive (handoverSys.cDur handoverK ()) κ (handoverSys.pt ()) := by
  refine ⟨0, 4, 5, by decide, by decide, by decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Regimes.silentLog_delivers _ (fun _ _ => rfl) _ _ _
  · refine ⟨?_, fun _ _ _ _ _ => rfl⟩
    change ((handoverPoint.faultyAt 4).card : ℚ) < 1 / 3 * Fintype.card (Fin 5)
    norm_num [handoverPoint, Tests.Growth.point]
  · decide
  · exact fun t _ _ => handoverPoint_readyAbove _ _ _
  · intro u v i j _ _ _ _
    have he : convicted (handoverSys.convicts ()) (handoverSys.view () u i ∪
        handoverSys.view () v j) = ∅ := by
      classical
      rw [convicted]
      exact Finset.filter_false_of_mem fun _ _ h => h
    rw [he]
    change ((∅ : Finset (Fin 5)).card : ℚ) < 1 / 3 * Fintype.card (Fin 5)
    norm_num
  · intro t _ _ _
    change ((handoverPoint.faultyAt 4 ∩ Finset.univ).card : ℚ) <
      1 / 2 * (Finset.univ : Finset (Fin 5)).card
    norm_num [handoverPoint, Tests.Growth.point]
  · intro t _ _ _
    change (if (0 : Time) ≤ 0 then _ else _)
    simp only [le_refl, ↓reduceIte]
    change (1 / 2 : ℚ) * ((((handoverPoint.retain _).readyAt _ t ∩ Finset.univ).card +
      ((handoverPoint.retain _).faultyAt t ∩ Finset.univ).card : Nat) : ℚ) <
      (((handoverPoint.retain _).readyAt _ t ∩ Finset.univ).card : ℚ)
    rw [handoverPoint_readyAt]
    split_ifs with hd <;>
      simp [hd, EnvPoint.retain, handoverPoint, Tests.Growth.point] <;> norm_num
  · intro u _ _ _ _
    change 2 * (handoverPoint.faultyAt _ ∩ Finset.univ).card < (Finset.univ : Finset (Fin 5)).card
    simp only [handoverPoint, Tests.Growth.point]
    split_ifs <;> decide
  · change max (0 : Time) 0 + ((0 : Nat) : Time) * 1 ≤ 4
    norm_num
  · change (1 / 3 : ℚ) * 5 ≤ ((handoverPoint.faultyAt 5).card : ℚ)
    norm_num [handoverPoint, Tests.Growth.point]
  · have hready : ∀ v : Fin 5, 2 ≤ v.val → ∀ t : Time, handoverPoint.Ready 1 v t := by
      intro v hv t
      refine ⟨?_, fun _ _ _ => rfl⟩
      simp only [EnvPoint.HonestAt, handoverPoint, Tests.Growth.point]
      split_ifs
      · fin_cases v <;> simp_all
      · exact Finset.notMem_empty _
    refine ⟨2, 3, 6, 7, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
      exact hready _ (by decide) _

end Witness

end Consensus.Shape.Tests.Continuation

end

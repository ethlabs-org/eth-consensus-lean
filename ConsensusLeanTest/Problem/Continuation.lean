module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLeanTest.Problem.Growth
public import ConsensusLeanTest.Problem.Regimes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
@[expose] public section

/-! # Tests of the continuation side property

* Vacuous systems do not continue, for `|V| ≥ 5`, through `Continues.realizable`:
  `empty_valid_not_continues` (no valid run), `excuse_true_not_continues` (an excuse on every
  run), `false_progress_not_continues` (a progress reader that never holds).
* `handover_witness`: the hand-over regime and the corruption growth of `realizable` are jointly
  satisfiable. Five validators, all awake, none compromised before `5` and `{0, 1}` from `5` on,
  a silent network, no evidence that convicts: the run hands over at `T = 4` after GST `0`, and
  by `κ = 5` at least fraction `β` (`⅓`) of the validators are compromised. -/

namespace Consensus.Shape.Tests.Continuation

section Vacuous

variable {V : Type} [Fintype V] {Prog : Type} {S : System V}
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
      handoverSys.Handover handoverK g T () ∧ handoverSys.heal handoverK .available () g () ≤ T ∧
      handoverK.params.β * 5 ≤ ((handoverSys.pt ()).faultCount κ : ℚ) ∧
      SafeActive (handoverSys.cDur handoverK ()) κ (handoverSys.pt ()) := by
  refine ⟨0, 4, 5, by decide, by decide, by decide, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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

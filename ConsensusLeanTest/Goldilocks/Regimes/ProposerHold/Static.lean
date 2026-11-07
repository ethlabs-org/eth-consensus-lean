module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHold.Engine
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Read
public import ConsensusLean.Lemmas.Model.Constant
import all ConsensusLean.Lemmas.Model.Retain
@[expose] public section

/-! # The proposer-hold counterexample: the retained run

`rhoc := (rho S).retain 41` drops the events of keys `0` and `1` and makes them faulty from the
start. It is a valid run with constant faults, synchronous up to the horizon, without a hash
collision, and with three ready validators against two faulty ones at every time: the proved
constant-fault Sleepy machinery applies to its node trace (`simTrace`) with the honest keys
`2, 3, 4`, and gives the record invariant up to `41` (`rhoc_invariant`). Its reads are the full
run's for the kept nodes (`read_rhoc`). -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks Simulation
open Consensus.Model (pubOf)

variable (S : Setup)

/-- **The retained run** at the horizon. -/
noncomputable abbrev rhoc : Model.Run (compiled (goldilocks S)) env := (rho S).retain 41

variable {S}

theorem rhoc_valid : (rhoc S).ExecutionValid :=
  Model.Run.retain_valid (rho_valid S) (by rw [rho_horizon])

theorem rhoc_const : (rhoc S).point.ConstantFaults := Model.Run.retain_constant

theorem rhoc_faultyAt (t : Time) : (rhoc S).faultyAt t = {0, 1} := by
  change (rho S).faultyAt 41 = _
  rw [rho_faultyAt, faulty_of_ge (by norm_num)]

theorem rhoc_horizon : (rhoc S).horizon = 41 := (rho_horizon S)

theorem rhoc_key : (rhoc S).key = Equiv.refl _ := rho_key S

theorem rhoc_not_hashCollision : ¬ (rhoc S).HashCollision :=
  Model.Run.retain_not_hashCollision (rho_valid S) (by rw [rho_horizon]) (rho_not_hashCollision S)

theorem rhoc_sync : (rhoc S).log.SyncUntil (rhoc S).point 41 := by
  have h := (rho_psync S).syncUntil_zero ((rho S).log_sendsFromZero (rho_valid S)) 41
  exact Model.Run.retain_delivers (rho_valid S) (by rw [rho_horizon])
    (fun a => by change a ≤ a + 3 - 1; dsimp only [Time]; omega) h

/-- The kept nodes are `2, 3, 4`. -/
theorem rhoc_honest (v : Fin 5) : v ∉ (rhoc S).faultyAt 0 ↔ v ≠ 0 ∧ v ≠ 1 := by
  rw [rhoc_faultyAt]; simp

variable (S) in
/-- The honest keys of the retained run. -/
abbrev H : Set (Fin (Fintype.card (Fin 5))) := honestKeys S (rhoc S)

theorem mem_H (y : Fin (Fintype.card (Fin 5))) : y ∈ H S ↔ y.val ≠ 0 ∧ y.val ≠ 1 := by
  rw [mem_honestKeys_iff, rhoc_faultyAt, rhoc_key]
  change (⟨y.val, by simpa using y.isLt⟩ : Fin 5) ∉ ({0, 1} : Finset (Fin 5)) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨fun h => h0 (Fin.ext h), fun h => h1 (Fin.ext h)⟩
  · rintro ⟨h0, h1⟩; exact ⟨fun h => h0 (congrArg Fin.val h), fun h => h1 (congrArg Fin.val h)⟩

/-- On the retained point, the ready validators are `2, 3, 4` at every time. -/
theorem rhoc_readyAt (c t : Time) : (rhoc S).point.readyAt c t = {2, 3, 4} := by
  unfold EnvPoint.readyAt
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, EnvPoint.Ready, EnvPoint.HonestAt,
    EnvPoint.AwakeOnClosed, Model.Run.point, rhoc_faultyAt, env, implies_true, and_true]
  revert v
  decide

/-- Sleepy participation on the retained point: three ready against two faulty. -/
theorem rhoc_sleepyOn (c W : Time) : (rhoc S).point.SleepyOn (1 / 2) c W 0 41 := by
  rw [EnvPoint.sleepyOn_iff rhoc_const]
  intro t _ _
  unfold EnvPoint.ReadyAbove
  rw [rhoc_readyAt]
  simp only [EnvPoint.faultCount, Model.Run.point, rhoc_faultyAt]
  norm_num

/-! ### The constant-fault machinery on the retained run -/

variable (S) in
/-- The node trace of the retained run. -/
noncomputable abbrev tr : GoldilocksTrace (S.params (pubOf env) one_le_card) (S.ro _) :=
  simTrace S (rhoc S) one_le_card

theorem rhoc_run : GoldilocksRun (runProposer S (rhoc S) one_le_card) (digestOf S (rhoc S)) (H S)
    (tr S) :=
  simTrace_goldilocksRun S (rhoc S) one_le_card rhoc_const rhoc_valid

theorem rhoc_noColl : Compose.NoCollRun (digestOf S (rhoc S)) (tr S) :=
  noCollRun_simTrace S (rhoc S) one_le_card rhoc_const rhoc_valid rhoc_not_hashCollision

theorem rhoc_service :
    Compose.SleepyServiceBefore (tr S) (H S) (S.params (pubOf env) one_le_card).Δ 41 :=
  Obligations.sleepyServiceBefore_of_syncUntil S (rhoc S) one_le_card rhoc_const rhoc_valid rhoc_noColl
    (by rw [rhoc_horizon]) rhoc_sync

theorem rhoc_faultBound : ∀ s : Nat, ∀ d ∈ ({0, (S.params (pubOf env) one_le_card).Δ,
    2 * (S.params (pubOf env) one_le_card).Δ} : Set Time),
    (S.params (pubOf env) one_le_card).ts s + d ≤ 41 →
    (tr S).FaultBound (H S) ((S.params (pubOf env) one_le_card).ts s + d) :=
  Obligations.sleepy_faultBound S (rhoc S) one_le_card rhoc_const rhoc_valid (W := 0)
    (by rw [rhoc_horizon]) (rhoc_sleepyOn _ _)

/-- **The Sleepy record invariant up to the horizon** on the retained run. -/
theorem rhoc_invariant : Compose.SleepyInvariantUpTo (tr S) (H S) 41 :=
  Compose.sleepy_invariant_before rhoc_run rhoc_noColl (by norm_num) rhoc_service rhoc_faultBound

end Consensus.Goldilocks.Test.ProposerHold

end

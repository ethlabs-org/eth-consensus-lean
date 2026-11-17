module
public import ConsensusLeanTest.Goldilocks.Regimes.ProposerHoldRun.Engine
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction
public import ConsensusLean.Lemmas.Model.Constant
import all ConsensusLean.Lemmas.Model.Retain
@[expose] public section

/-! # The proposer-hold counterexample: the retained run

`rhoc := (rho S).retain 41` drops the events of keys `0` and `1` and makes them faulty from the
start. It is a valid run with constant faults, synchronous up to the horizon, without a hash
collision, and with three ready validators against two faulty ones at every time. Its honest
keys at every time are `2, 3, 4` (`Hg`, `mem_Hg`), so the growing-fault Sleepy machinery applies
to its node trace (`simTrace`): the run (`rhoc_runAt`), the finite service (`rhoc_serviceAt`), the
count shapes at the full committee (`rhoc_boundsAt`, `rhoc_factsAt`, `rhoc_cboundsAt`) and the
record invariant up to `41` (`rhoc_invariantAt`). Its reads are the full run's for the kept nodes
(`read_rhoc`). -/

namespace Consensus.Goldilocks.Test.ProposerHold
open AsChainShape Shape Blocks Simulation
open Consensus.Model (pubOf)

variable (S : Setup)

/-- **The retained run** at the horizon. -/
noncomputable abbrev rhoc : Model.Run (compiled (goldilocks { S with vote := stock })) env :=
  (rho S).retain 41

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
abbrev H : Set (Fin (Fintype.card (Fin 5))) := honestKeys { S with vote := stock } (rhoc S)

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
noncomputable abbrev tr : GoldilocksTrace
    (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card) (S.ro _) :=
  simTrace { S with vote := stock } (rhoc S) one_le_card

theorem rhoc_run : GoldilocksRun (runProposer { S with vote := stock } (rhoc S) one_le_card)
    (digestOf { S with vote := stock } (rhoc S)) (H S)
    (tr S) :=
  Simulation.Test.goldilocksRun_of_at S (rhoc S) one_le_card rhoc_const rhoc_valid

theorem rhoc_noColl : Compose.NoCollRun (digestOf { S with vote := stock } (rhoc S)) (tr S) := by
  rw [tr, ← simTraceAt_eq]
  exact noCollRun_simTraceAt _ (rhoc S) one_le_card rhoc_valid rhoc_not_hashCollision

variable (S) in
/-- The time-indexed honest keys of the retained run: the keys `2, 3, 4` at every time. -/
abbrev Hg : Time → Set (Fin (Fintype.card (Fin 5))) :=
  honestKeysAt { S with vote := stock } (rhoc S)

theorem mem_Hg {y : Fin (Fintype.card (Fin 5))} {t : Time} : y ∈ Hg S t ↔ y ∈ H S := by
  rw [mem_honestKeysAt_iff, mem_honestKeys_iff, rhoc_faultyAt, rhoc_faultyAt]

/-- The honest blocks of the time-indexed reading are honest blocks of the kept keys. -/
theorem honestBlocksAt_sub : (tr S).HonestBlocksAt (Hg S) ⊆ (tr S).HonestBlocks (H S) :=
  fun _ ⟨y, i, _, _, _, hy, hB⟩ => ⟨y, mem_Hg.mp hy, i, hB⟩

/-! ### The growing-fault machinery on the retained run -/

theorem rhoc_runAt :
    Consensus.Goldilocks.Growing.GoldilocksRun
      (runProposer { S with vote := stock } (rhoc S) one_le_card)
      (digestOf { S with vote := stock } (rhoc S)) (Hg S) (tr S) := by
  have h := simTraceAt_goldilocksRun { S with vote := stock } (rhoc S) one_le_card rhoc_valid
  rw [simTraceAt_eq] at h
  exact h

theorem rhoc_serviceAt :
    Compose.Growing.SleepyServiceBefore (tr S) (Hg S)
      (({ S with vote := AsChainShape.stock } : Setup).params (pubOf env) one_le_card).Δ 41 := by
  have h := sleepyServiceBefore_of_syncUntil_at { S with vote := stock } (rhoc S)
    one_le_card rhoc_valid (by rw [simTraceAt_eq]; exact rhoc_noColl) (by rw [rhoc_horizon])
    rhoc_sync
  rw [simTraceAt_eq] at h
  exact h

theorem rhoc_boundsAt : Compose.Growing.SleepyBoundsFrom (tr S) (Hg S) 0 41 := by
  have h := Obligations.Growing.sleepy_bounds_at { S with vote := stock } (rhoc S) one_le_card
    rhoc_valid (a := 0) (σ₀ := 0) (by rw [rhoc_horizon]) (rhoc_sleepyOn _ _)
    (by change (0 : Time) ≤ 4 * 3 * ((0 : Nat) : Int) + 3; norm_num) (by norm_num)
  rw [simTraceAt_eq] at h
  exact h

theorem rhoc_factsAt :
    Compose.Growing.CommitteeFacts (tr S) (Hg S) (SA.CommitteeDict.full (Fintype.card (Fin 5))) :=
  Compose.Growing.CommitteeFacts.of_full rhoc_runAt rhoc_noColl rfl

theorem rhoc_cboundsAt : Compose.Growing.CommitteeBoundsFrom (tr S) (Hg S)
    (SA.CommitteeDict.full (Fintype.card (Fin 5))) 0 41 :=
  Compose.Growing.CommitteeBoundsFrom.of_full rhoc_runAt rhoc_boundsAt

/-- **The Sleepy record invariant up to the horizon** on the retained run, under growing faults. -/
theorem rhoc_invariantAt : Compose.Growing.SleepyInvariantUpTo (tr S) (Hg S) 41 :=
  Compose.Growing.sleepy_invariant_at rhoc_runAt rhoc_noColl rhoc_factsAt (by norm_num)
    rhoc_serviceAt rhoc_boundsAt rhoc_cboundsAt

end Consensus.Goldilocks.Test.ProposerHold

end

module
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope -- shake: keep (test environment)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.HealingOpeningSupport
open AvailableChain.SimplexFG Gen.Pure

abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def env : Generic.Env (Fin 1) :=
  ⟨1, by decide, 5, by decide, fun _ t => decide (t < 1 ∨ 5 ≤ t)⟩

def run : V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := {0}
  horizon := 10
  events := [.tick 0 0, .restart 0 5, .tick 0 5, .tick 0 6, .tick 0 7,
    .tick 0 8, .tick 0 9, .tick 0 10]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- The wake is before the vote at the same time. Each scheduled tick is awake. -/
theorem fgp_schedule : V2.D.ScheduleWellFormed env run ∧
    V2.D.SleepWellFormed env run ∧ V2.D.RestartsAtWakes env run := by
  refine ⟨⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    simp [run] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    simp [run] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v t ht
    simp [run] at ht
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact ⟨0, by decide⟩ | exact ⟨5, by decide⟩ | exact ⟨6, by decide⟩ |
        exact ⟨7, by decide⟩ | exact ⟨8, by decide⟩ | exact ⟨9, by decide⟩ |
        exact ⟨10, by decide⟩
  · intro v hv t _ ht hh ha
    have hv0 : v = 0 := Finset.mem_singleton.mp hv
    subst v
    change 0 ≤ t at ht
    change t ≤ 10 at hh
    simp [env] at ha
    simp [run]
    dsimp [Time] at *
    omega
  · intro v t ht
    simp [run] at ht
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro v o t ht
    simp [run] at ht
  · intro v t ht
    simp [run] at ht
    rcases ht with ⟨rfl, rfl⟩
    decide
  · intro v hv t ht hh hw
    have hv0 : v = 0 := Finset.mem_singleton.mp hv
    subst v
    have ht5 : t = 5 := by
      simp [V2.D.Wakes, env] at hw
      dsimp [Time] at *
      omega
    subst t
    simp [run]
  · intro v t ht
    simp [run] at ht
    rcases ht with ⟨rfl, rfl⟩
    exact ⟨by decide, by unfold V2.D.Wakes; decide⟩

/-- Empty delivery leaves all delivery and signature obligations satisfied. -/
theorem fgp_valid : V2.D.ExecutionValid env run := by
  refine { toScheduleWellFormed := fgp_schedule.1
           toSleepWellFormed := fgp_schedule.2.1
           toDeliveryWellFormed := ?_
           toUnforgeableSignatures := ?_ }
  · refine ⟨?_, ?_, ?_⟩ <;> intro i v o t hi <;>
      have hm := List.mem_of_getElem? hi <;> simp [run] at hm
  · refine ⟨?_, ?_⟩
    · intro v o t hp
      obtain ⟨i, hi⟩ := hp
      have hm := List.mem_of_getElem? hi
      simp [run] at hm
    · intro v o t hp
      obtain ⟨i, hi⟩ := hp
      have hm := List.mem_of_getElem? hi
      simp [run] at hm

/-- All selected voters wake at v_1 = 5. Awake does not imply joinedness or support. -/
theorem wake_at_vote :
    env.awake 0 (SA.voteTime p.toParams 1) = true ∧
    joinedNow p ((fgsa p unitCodec).clock
      (run.stateBefore env 2 0) (SA.voteTime p.toParams 1)).st = false ∧
    ¬ env.t_GST ≤ slotStartZ p ((1 : Slot) - (1 : Int)) ∧
    ¬ enabledGateAt p unitCodec env run 7 0 1 ∧
    SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p unitCodec env run 7 0)
        (SA.gateTime p.toParams 1))) 1 .genesis = 0 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide, ?_, by decide +kernel⟩
  intro h
  have hr : (storeAt p unitCodec env run 7 0).restartTime = some 5 := by decide +kernel
  have hb := h.2
  change (match (storeAt p unitCodec env run 7 0).restartTime with
    | none => True | some w => w ≤ slotStartZ p (1 : Int)) at hb
  rw [hr] at hb
  exact (by decide : ¬ (5 : Time) ≤ slotStartZ p (1 : Int)) hb

/-- No selected honest voter is joined; the scoped HEAD condition is vacuous. -/
theorem no_joined_voter : joinedHonest p env run (SA.voteTime p.toParams 1) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro y hy
  have hy0 : y = 0 := Finset.mem_singleton.mp hy
  subst y
  change ¬ joinedAt p env run 0 1 5
  intro h
  have hr := h.2.2 5 (by decide) (by decide) (by simp [run])
  exact (by decide : ¬ (5 : Time) ≤ slotStartZ p ((1 : Slot) - (1 : Int))) hr

/-- The awake vote tick emits no HEAD because its duty guard is false. -/
theorem no_head_emission : run.emitsAt env 2 = [] := by decide +kernel

/-- HEAD coverage of genesis cannot replace the missing join cutoff. -/
theorem genesis_coverage :
    ∀ z ∈ run.honest, ∀ K, headAtLabel p unitCodec env run z 1 = some K →
      Block.Preceq .genesis K := by
  intro z hz K hK
  have hz0 : z = 0 := Finset.mem_singleton.mp hz
  subst z
  have hgen : headAtLabel p unitCodec env run 0 1 = some .genesis := by decide +kernel
  have he : K = .genesis := Option.some.inj (hK.symm.trans hgen)
  rw [he]
  exact Gen.Pure.block_preceq_refl .genesis

end AvailableChain.FGSA.Run.Tests.HealingOpeningSupport

#print axioms AvailableChain.FGSA.Run.Tests.HealingOpeningSupport.fgp_valid
#print axioms AvailableChain.FGSA.Run.Tests.HealingOpeningSupport.fgp_schedule
#print axioms AvailableChain.FGSA.Run.Tests.HealingOpeningSupport.wake_at_vote
#print axioms AvailableChain.FGSA.Run.Tests.HealingOpeningSupport.genesis_coverage

#print axioms AvailableChain.FGSA.Run.Tests.HealingOpeningSupport.no_joined_voter

#print axioms AvailableChain.FGSA.Run.Tests.HealingOpeningSupport.no_head_emission

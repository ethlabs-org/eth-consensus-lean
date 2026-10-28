module
public import AvailableChainContractTests.Leaks

@[expose] public section
namespace AvailableChain.Contract.Tests
open AvailableChain.Generic

def env4 : Env (Fin 4) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩

def controls : Constants := {
  slotTicks := 1, catchUp := 1, η := 2, D_c := 1, D_s := 2, D_f := 1
  armingLag := 1, fastArmingLag := 1, budget := 2
  θ := 1 / 2, θrec := 1 / 2, recoveryFull := true
  growth := ⟨1, 1⟩, stableGrowth := ⟨2, 1⟩, recovery := ⟨1, 1⟩
  finStart := ⟨1, 1⟩, finDelay := ⟨1, 1⟩ }

theorem controls_valid : controls.Valid := by
  constructor <;> norm_num [controls]

def seat4 {F : Family} : (protoOf F env4).Label → Fin (Fintype.card (Fin 4)) ≃ Fin 4 :=
  fun _ => Equiv.refl _

def run4 (es : List (Event (Fin 4) (protoOf (family false false false) env4).Object)) :
    Run (family false false false) env4 :=
  mkRun Finset.univ 20 seat4 (fun _ => 0) (fun _ _ => 0) goodHash es

theorem run4_no_hashCollision (es : List (Event (Fin 4)
    (protoOf (family false false false) env4).Object)) :
    ¬ (run4 es).HashCollision :=
  Run.not_hashCollision_of_injective ⟨goodHash_injective, goodHash_nonzero⟩

theorem positive_controls : ∃ es,
    let r := run4 es
    r.Sleepy controls 0 ∧ r.StableSleepy controls 0 ∧ r.Fast controls 0 ∧
    r.LiveSleepy controls 0 1 ∧ r.Outage controls 2 4 6 ∧
    r.FastOutage controls 2 4 6 ∧ r.Recovery controls 1 ∧ r.Finality controls 1 ∧
    (∃ t : Time, 0 ≤ t ∧ t + (1 : Time) *
      (protoOf (family false false false) env4).slotLen ≤ r.horizon) ∧
    (∃ s, 0 < (protoOf (family false false false) env4).proposalTime s ∧
      r.ReadyProposer controls s ∧
      (protoOf (family false false false) env4).proposalTime s + (controls.D_c : Time) * env4.Δ ≤ r.horizon ∧
      (r.readyAt controls ((protoOf (family false false false) env4).proposalTime s + (controls.D_c : Time) * env4.Δ)).Nonempty) ∧
    (env4.t_GST + (controls.finStart.eval 1 : Time) * env4.Δ + (controls.finDelay.eval 1 : Time) * env4.Δ ≤ r.horizon ∧
      (r.readyAt controls (env4.t_GST + (controls.finStart.eval 1 : Time) * env4.Δ + (controls.finDelay.eval 1 : Time) * env4.Δ)).Nonempty) ∧
    (∃ t, (2 : Time) < 4 ∧ 4 ≤ t ∧ t < 6 ∧ t ≤ r.horizon ∧
      ∃ w ∈ r.honest, AwakeOnClosed env4 w (4 - (controls.catchUp : Time) * env4.Δ - 1) t) := by
  obtain ⟨es, valid, sync, healthy⟩ := canonical_run (family false false false) (Fin 4) env4 Finset.univ 20
    (by decide) seat4 (fun _ => 0) (fun _ _ => 0) goodHash
  let r := run4 es
  have ready : ∀ t, r.readyAt controls t = Finset.univ := by
    intro t
    ext v
    simp [Run.readyAt, Run.Ready, AwakeOnClosed, r, run4, mkRun, env4]
  have rp : ∀ s, r.ReadyProposer controls s := by
    intro s
    simp [Run.ReadyProposer, Run.Ready, AwakeOnClosed, r, run4, mkRun, env4]
  have faulty : r.faulty = ∅ := by simp [Run.faulty, r, run4, mkRun]
  have awake : ∀ t, r.awakeIn (t - (controls.η : Time) * env4.Δ) t = Finset.univ := by
    intro t
    ext v
    simp only [Run.awakeIn, r, run4, mkRun, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => ⟨t, by simp [controls, env4], le_rfl, rfl⟩⟩
  have majority : ∀ t, r.ReadyMajority controls t := by
    intro t
    simp [Run.ReadyMajority, ready, faulty]
  have eta : ∀ t, r.EtaSleepy controls t := by
    intro t
    unfold Run.EtaSleepy
    rw [awake t, faulty, ready t]
    norm_num [controls]
  have full : r.FullParticipation 0 := by simp [Run.FullParticipation, env4]
  have recur : r.Recurrence controls 0 1 := by
    intro t ht hh
    have ht1 : 0 ≤ t + 1 := Int.add_nonneg ht (by decide)
    refine ⟨(t + 1).toNat, ?_, ?_, rp _⟩
    · simp [Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env4, Int.toNat_of_nonneg ht1]
    · simp [Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env4, Int.toNat_of_nonneg ht1]
  have sleepy : r.Sleepy controls 0 := ⟨valid, sync, rfl, rfl, fun t _ _ => majority t⟩
  have outage : r.Outage controls 2 4 6 := by
    refine ⟨valid, healthy 4, ?_, ?_, ?_, fun t _ _ => majority t, fun t _ _ => eta t⟩ <;>
      norm_num [controls, env4, r, run4, mkRun]
  have recovery : r.Recovery controls 1 := by
    refine ⟨valid, sync, ?_, ?_, ?_, recur, ?_⟩
    · intro t _ _
      rw [ready t, faulty]
      norm_num [controls]
    · intro _; exact full
    · simp [Wakes, env4]
    · norm_num [controls, Affine.eval, env4, r, run4, mkRun]
  refine ⟨es, sleepy, ⟨sleepy, fun t _ _ => eta t⟩, ⟨sleepy, full, ?_⟩,
    ⟨sleepy, recur⟩, outage, ⟨outage, ?_⟩, recovery, ⟨recovery, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · change r.BelowQuarter
    simp [Run.BelowQuarter, faulty]
  · intro t _ _
    change (4 + 1) / 2 ≤ (r.readyAt controls t).card
    simp [ready]
  · change r.BelowOneThird
    simp [Run.BelowOneThird, faulty]
  · intro t _ _
    change 2 * Fintype.card (Fin 4) < 3 * (r.readyAt controls t).card
    simp [ready]
  · refine ⟨0, le_rfl, ?_⟩
    norm_num [Protocol.slotLen, protoOf, family, pubOf, env4, r, run4, mkRun]
  · refine ⟨1, ?_, rp 1, ?_, ?_⟩
    · norm_num [Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env4]
    · norm_num [Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env4, controls, r, run4, mkRun]
    · rw [ready]; simp
  · constructor
    · norm_num [controls, Affine.eval, env4, r, run4, mkRun]
    · rw [ready]; simp
  · refine ⟨4, by decide, le_rfl, by decide, ?_, 0, ?_, ?_⟩
    · simp [r, run4, mkRun]
    · simp [r, run4, mkRun]
    · simp [AwakeOnClosed, env4]

end AvailableChain.Contract.Tests
end

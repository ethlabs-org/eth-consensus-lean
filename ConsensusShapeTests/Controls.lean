module
public import ConsensusShapeTests.Leaks

@[expose] public section
namespace Consensus.Shape.Tests
open Model
open Run

def env4 : Env (Fin 4) := ⟨1, by decide, 0, fun _ _ => true⟩

def controls : Constants := {
  slotTicks := 1, catchUp := 1, η := 2, D_c := 1, D_s := 2, D_f := 1
  armingLag := 1, fastArmingLag := 1, budget := 2
  θ := 1 / 2, θrec := 1 / 2, recoveryFull := true
  recGrowth := ⟨1, 1⟩, growth := ⟨1, 1⟩, stableGrowth := ⟨2, 1⟩, recovery := ⟨1, 1⟩
  finStart := ⟨1, 1⟩, finDelay := ⟨1, 1⟩ }

theorem controls_valid : controls.Valid := by
  constructor <;> norm_num [controls]

def seat4 {F : Family} : (ℓ : (Model.protoOf (compiled F) env4).Label) →
    Fin ((Model.protoOf (compiled F) env4).seats ℓ) ↪ Fin 4
  | .inl _ => ⟨fun i => i, fun _ _ h => h⟩
  | .inr _ => ⟨fun _ => 0, fun a b _ => by
      change Fin 1 at a b
      exact Subsingleton.elim a b⟩

def submissions4 (_ : Fin 4) (t : Time) : List Tx := if t = 0 then [42] else []

def run4 (es : List (Event (Fin 4) (Model.protoOf (compiled (family false false false)) env4).Object)) :=
  Model.mkRun (F := compiled (family false false false)) (E := env4)
    Finset.univ 20 seat4 submissions4 goodHash es

theorem run4_no_hashCollision (es : List (Event (Fin 4)
    (Model.protoOf (compiled (family false false false)) env4).Object)) :
    ¬ (run4 es).HashCollision :=
  Model.Run.not_hashCollision_of_injective ⟨goodHash_injective, goodHash_nonzero⟩

theorem positive_controls : ∃ es,
    let r := run4 es
    Sleepy r controls ∧ StableSleepy r controls ∧ Fast r controls ∧
    LiveSleepy r controls 1 ∧ Outage r controls 2 4 6 ∧
    FastOutage r controls 2 4 6 ∧ Recovery r controls 1 ∧ Finality r controls 1 ∧
    r.point.SubmittedToAll 42 0 ∧
    (∀ d ∈ [controls.D_c, controls.D_s, controls.D_f, controls.growth.eval 1,
      controls.stableGrowth.eval 1, controls.recovery.eval 1,
      controls.recovery.eval 1 + controls.recGrowth.eval 1,
      controls.finStart.eval 1 + controls.finDelay.eval 1],
      (d : Time) * env4.Δ ≤ r.horizon ∧
      r.point.Ready (controls.catchUp * env4.Δ) 0 ((d : Time) * env4.Δ)) ∧
    (∃ t : Time, 0 ≤ t ∧ t + (1 : Time) *
      (protoOf (family false false false) env4).slotLen ≤ r.horizon) ∧
    (∃ s, 0 < (protoOf (family false false false) env4).proposalTime s ∧
      ReadyProposer r (controls.catchUp * env4.Δ) s ∧
      (protoOf (family false false false) env4).proposalTime s + (controls.D_c : Time) * env4.Δ ≤ r.horizon ∧
      (r.point.readyAt (controls.catchUp * env4.Δ) ((protoOf (family false false false) env4).proposalTime s + (controls.D_c : Time) * env4.Δ)).Nonempty) ∧
    (env4.gst + (controls.finStart.eval 1 : Time) * env4.Δ + (controls.finDelay.eval 1 : Time) * env4.Δ ≤ r.horizon ∧
      (r.point.readyAt (controls.catchUp * env4.Δ) (env4.gst + (controls.finStart.eval 1 : Time) * env4.Δ + (controls.finDelay.eval 1 : Time) * env4.Δ)).Nonempty) ∧
    (∃ t, (2 : Time) < 4 ∧ 4 ≤ t ∧ t < 6 ∧ t ≤ r.horizon ∧
      ∃ w ∈ r.honest, (run4 es).point.AwakeOnClosed w (4 - (controls.catchUp : Time) * env4.Δ - 1) t) := by
  obtain ⟨es, valid, sync, healthy⟩ := Model.canonical_run (compiled (family false false false)) (Fin 4) env4 Finset.univ 20
    (by decide) seat4 submissions4 goodHash
  let r := run4 es
  have ready : ∀ t, r.point.readyAt (controls.catchUp * env4.Δ) t = Finset.univ := by
    intro t
    ext v
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, r, run4, Model.mkRun, Model.Run.point, env4]
  have rp : ∀ s, ReadyProposer r (controls.catchUp * env4.Δ) s := by
    intro s
    simp [Run.ReadyProposer, EnvPoint.Ready, EnvPoint.AwakeOnClosed, r, run4, Model.mkRun, Model.Run.point, env4]
  have faulty : r.point.faulty = ∅ := by simp [EnvPoint.faulty, r, run4, Model.mkRun, Model.Run.point]
  have awake : ∀ t, r.point.awakeIn (t - (controls.η : Time) * env4.Δ) t = Finset.univ := by
    intro t
    ext v
    simp only [EnvPoint.awakeIn, Finset.mem_filter]
    change (v ∈ r.point.honest ∧ ∃ u, t - (controls.η : Time) * env4.Δ ≤ u ∧
      u ≤ t ∧ env4.awake v u = true) ↔ v ∈ Finset.univ
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      exact ⟨Finset.mem_univ _, t, by norm_num [controls, env4], le_rfl, rfl⟩
  have majority : ∀ t, r.point.ReadyMajority (controls.catchUp * env4.Δ) t := by
    intro t
    simp [EnvPoint.ReadyMajority, ready, faulty]
  have eta : ∀ t, r.point.EtaSleepy (controls.catchUp * env4.Δ) controls.θ (controls.η * env4.Δ) t := by
    intro t
    unfold EnvPoint.EtaSleepy
    rw [awake t, faulty, ready t]
    norm_num [controls]
  have full : r.point.FullParticipation 0 := by intro v hv t ht hh; rfl
  have recur : Recurrence r (controls.catchUp * env4.Δ) 0 1 := by
    intro t ht hh
    have ht1 : 0 ≤ t + 1 := Int.add_nonneg ht (by decide)
    refine ⟨(t + 1).toNat, ?_, ?_, rp _⟩
    · simp [ShapeProtocol.proposalTime, ShapeProtocol.slotLen, protoOf, family, Model.pubOf, env4, Int.toNat_of_nonneg ht1]
    · simp [ShapeProtocol.proposalTime, ShapeProtocol.slotLen, protoOf, family, Model.pubOf, env4, Int.toNat_of_nonneg ht1]
  have sleepy : Sleepy r controls := ⟨valid, sync, rfl, fun t _ _ => majority t⟩
  have outage : Outage r controls 2 4 6 := by
    refine ⟨valid, healthy 4, ?_, ?_, ?_, fun t _ _ => majority t, fun t _ _ => eta t⟩ <;>
      norm_num [controls, env4, r, run4, Model.mkRun, Model.Run.point]
  have recovery : Recovery r controls 1 := by
    refine ⟨valid, sync, ?_, ?_, ?_, recur, ?_⟩
    · intro t _ _
      rw [ready t, faulty]
      norm_num [controls]
    · intro _; exact full
    · simp [Wakes, env4]
    · norm_num [controls, Affine.eval, env4, r, run4, Model.mkRun, Model.Run.point]
  refine ⟨es, sleepy, ⟨sleepy, fun t _ _ => eta t⟩, ⟨sleepy, full, ?_⟩,
    ⟨sleepy, recur⟩, outage, ⟨outage, ?_⟩, recovery, ⟨recovery, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change r.point.BelowQuarter
    simp [EnvPoint.BelowQuarter, faulty]
  · intro t _ _
    change (4 + 1) / 2 ≤ (r.point.readyAt (controls.catchUp * env4.Δ) t).card
    simp [ready]
  · change r.point.BelowOneThird
    simp [EnvPoint.BelowOneThird, faulty]
  · intro t _ _
    change 2 * Fintype.card (Fin 4) < 3 * (r.point.readyAt (controls.catchUp * env4.Δ) t).card
    simp [ready]
  · intro v _; exact ⟨0, le_rfl, le_rfl, by simp [r, run4, Model.mkRun, Model.Run.point, submissions4]⟩
  · simp [controls, Affine.eval, r, run4, Model.mkRun, Model.Run.point,
      EnvPoint.Ready, EnvPoint.AwakeOnClosed, env4]
  · refine ⟨0, le_rfl, ?_⟩
    norm_num [ShapeProtocol.slotLen, protoOf, family, Model.pubOf, env4, r, run4, Model.mkRun, Model.Run.point]
  · refine ⟨1, ?_, rp 1, ?_, ?_⟩
    · norm_num [ShapeProtocol.proposalTime, ShapeProtocol.slotLen, protoOf, family, Model.pubOf, env4]
    · norm_num [ShapeProtocol.proposalTime, ShapeProtocol.slotLen, protoOf, family, Model.pubOf, env4, controls, r, run4, Model.mkRun, Model.Run.point]
    · rw [ready]; simp
  · constructor
    · norm_num [controls, Affine.eval, env4, r, run4, Model.mkRun, Model.Run.point]
    · rw [ready]; simp
  · refine ⟨4, by decide, le_rfl, by decide, ?_, 0, ?_, ?_⟩
    · simp [r, run4, Model.mkRun, Model.Run.point]
    · simp [r, run4, Model.mkRun, Model.Run.point]
    · intro u hu ht; rfl

end Consensus.Shape.Tests
end

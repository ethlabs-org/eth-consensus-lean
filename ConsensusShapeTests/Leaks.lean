module
public import Mathlib.Tactic
public import ConsensusShape.Refinement
public import ConsensusModelProofs.Canonical
public import ConsensusModelProofs.Lift
@[expose] public section
namespace Consensus.Shape.Tests
open Model
open Run

def env : Env (Fin 1) := ⟨1, by decide, 0, fun _ _ => true⟩

def family (proposal vote bad : Bool) : Family := fun _ => {
  State := Unit, Label := Unit, Duty := Time, Body := Unit, Durable := Unit
  decLabel := inferInstance, decBody := inferInstance
  slotTicks := 1, slotTicks_pos := by decide
  init := (), clock := fun s _ => s
  propose := fun _ _ => if proposal then some (0, 0, []) else none
  label := fun _ => (), actTime := id
  duties := fun t => [t]
  duties_spec := by simp
  duties_nodup := by simp
  act := fun _ _ => if vote then some ((), []) else none
  gossip := fun _ _ => []
  process := fun s _ _ => s, recordOwn := fun s _ _ => s
  durable := id, restore := fun s _ => s
  confirmed := fun _ => if bad then [⟨0, 1, 7, 7⟩] else []
  stable := fun _ => [], finalized := fun _ => []
  conflicts := fun _ _ => vote }

def seat {F : Family} : (ℓ : (Model.protoOf (compiled F) env).Label) →
    Fin ((Model.protoOf (compiled F) env).seats ℓ) ↪ Fin 1 :=
  fun ℓ => ⟨fun _ => 0, fun a b _ => by
    cases ℓ <;> change Fin 1 at a b <;> exact Subsingleton.elim a b⟩

def goodHash (h : Header) : Nat := Encodable.encode h + 1

theorem goodHash_injective : Function.Injective goodHash := by
  intro a b he
  exact Encodable.encode_injective (Nat.add_right_cancel he)

theorem goodHash_nonzero (h : Header) : goodHash h ≠ 0 := Nat.succ_ne_zero _

def run {F : Family} (relay : Fin 1 → Time → List Tx) (h : Time)
    (es : List (Event (Fin 1) (Model.protoOf (compiled F) env).Object)) :=
  Model.mkRun (F := compiled F) (E := env) Finset.univ h seat (fun _ _ => []) relay goodHash es

theorem run_no_collision {F : Family} (relay : Fin 1 → Time → List Tx) (h : Time)
    (es : List (Event (Fin 1) (Model.protoOf (compiled F) env).Object)) :
    ¬ (run relay h es).HashCollision :=
  Model.Run.not_hashCollision_of_injective ⟨goodHash_injective, goodHash_nonzero⟩

theorem ready {F : Family} (relay : Fin 1 → Time → List Tx) (h : Time)
    (es : List (Event (Fin 1) (Model.protoOf (compiled F) env).Object))
    (c t : Time) (v : Fin 1) : (run relay h es).point.Ready c v t := by
  have : v = 0 := Subsingleton.elim _ _
  simp [this, EnvPoint.Ready, EnvPoint.AwakeOnClosed, run, Model.mkRun, Model.Run.point, env]

theorem majority {F : Family} (relay : Fin 1 → Time → List Tx) (h : Time)
    (es : List (Event (Fin 1) (Model.protoOf (compiled F) env).Object)) (c t : Time) :
    (run relay h es).point.ReadyMajority c t := by
  classical
  have hr : (run relay h es).point.readyAt c t = Finset.univ := by
    ext v
    simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ]
    exact ⟨fun _ => trivial, fun _ => ⟨Finset.mem_univ v, ready relay h es c t v⟩⟩
  unfold EnvPoint.ReadyMajority
  rw [hr]
  norm_num [EnvPoint.faulty, run, Model.mkRun, Model.Run.point]

/-- Reserved digest zero makes even one observed item an escaped run. -/
theorem hash_escape_needed {V : Type} [Fintype V] [DecidableEq V]
    {F : Model.Family} {E : Env V} (r : Model.Run F E)
    (hz : r.hash = fun _ => 0) (observed : ∃ x, r.ObservedItem x) :
    r.HashCollision := by
  obtain ⟨x, hx⟩ := observed
  exact Or.inr ⟨x, hx, by rw [hz]⟩

theorem empty_outputs (proposal : Bool) : ∀ A, A.WellFormed → ∀ C, ¬ ShapeClaims (family proposal false false) A C := by
  intro A hA C claims
  let H : Time := 1 + (C.D_c : Time)
  obtain ⟨relay, es, valid, sync, _⟩ := Model.canonical_run (compiled (family proposal false false))
    (Fin 1) env Finset.univ H (by dsimp [H]; positivity) seat (fun _ _ => []) goodHash
  let r := run relay H es
  have sleepy : Sleepy r A := ⟨valid, sync, rfl, by
    intro t _ _
    have hr : (r.point.readyAt ((A.catchUp : Time) * env.Δ) t).card = 1 := by
      have := majority relay H es ((A.catchUp : Time) * env.Δ) t
      have hu := Finset.card_le_univ (r.point.readyAt ((A.catchUp : Time) * env.Δ) t)
      unfold EnvPoint.ReadyMajority at this
      change r.point.faulty.card < (r.point.readyAt ((A.catchUp : Time) * env.Δ) t).card at this
      simp only [Fintype.card_fin] at hu
      omega
    have hf : r.point.faulty = ∅ := by simp [EnvPoint.faulty, r, run, Model.mkRun, Model.Run.point]
    unfold EnvPoint.ReadyAbove
    rw [hr, hf]
    simpa using hA.sleepy_upper⟩
  have inc := (claims.confirmedIncluded (Fin 1) env r sleepy).resolve_right (run_no_collision relay H es)
  obtain ⟨h, _, inside⟩ := inc 1 (by norm_num [ShapeProtocol.proposalTime, ShapeProtocol.slotLen, protoOf, family, Model.pubOf, env]) (ready relay H es _ _ _)
    (by simp [H, ShapeProtocol.proposalTime, ShapeProtocol.slotLen, protoOf, family,
      Model.pubOf, env, r, run, Model.mkRun])
  have hin := inside 0 (ready relay H es _ _ _)
  change h ∈ [] at hin
  cases hin

theorem silent : ∀ A, A.WellFormed → ∀ C, ¬ ShapeClaims (family false false false) A C := empty_outputs false
theorem proposeButGenesis : ∀ A, A.WellFormed → ∀ C, ¬ ShapeClaims (family true false false) A C := empty_outputs true

theorem fabricated : ∀ A C, ¬ ShapeClaims (family false false true) A C := by
  intro A C claims
  obtain ⟨relay, es, valid, _, _⟩ := Model.canonical_run (compiled (family false false true))
    (Fin 1) env Finset.univ 2 (by decide) seat (fun _ _ => []) goodHash
  let r := run relay 2 es
  have hv := (claims.outputValid (Fin 1) env r valid).1 0
    (by simp [r, run, Model.mkRun]) 0 (Nat.zero_le _)
  have hm : (⟨0, 1, 7, 7⟩ : Header) ∈ readChainIdx r (protoOf (family false false true) env).confirmed 0 0 := by
    simp [readChainIdx, protoOf, family]
  obtain ⟨_, cs, hcs⟩ := hv.2.2 _ hm
  obtain ⟨k, _, hk, _⟩ := hcs
  omega

theorem conflictsTrue : ∀ A C, ¬ ShapeClaims (family false true false) A C := by
  intro A C claims
  obtain ⟨relay, es, valid, _, _⟩ := Model.canonical_run (compiled (family false true false))
    (Fin 1) env Finset.univ 0 (by decide) seat (fun _ _ => []) goodHash
  let r := run relay 0 es
  have ht : Event.tick (0 : Fin 1) 0 ∈ r.events :=
    valid.tick_total 0 (Finset.mem_univ _) 0 ⟨0, rfl⟩ (le_refl _) rfl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
  let o : (Model.protoOf (compiled (family false true false)) env).Object :=
    .mk (.signed (.inl ()) ⟨0, by decide⟩) (.data ()) []
  have rel : r.releases 0 o 0 := by
    refine ⟨i, hi, ?_⟩
    rw [Model.Run.releasesAt, hi]
    have hc : r.candidates
        ((Model.protoOf (compiled (family false true false)) env).clock
          (r.stateBefore i 0).st 0 (Model.mempool r.inbox 0 0)) 0 0 = [o] := by
      rfl
    unfold Model.Run.tick
    dsimp only []
    rw [ite_eq_left (show env.awake 0 0 = true from rfl), hc]
    change o ∈ [o]
    exact List.mem_cons_self
  have obs : o ∈ r.Observed := by
    obtain ⟨j, hj, hr⟩ := rel
    exact ⟨0, Finset.mem_univ _, j, o, (List.getElem?_eq_some_iff.mp hj).1,
      Or.inl ⟨0, hj, hr⟩, Model.Obj.Contains.refl _⟩
  have slash : r.Slashable r.Observed 0 :=
    ⟨o, obs, o, obs, rfl, rfl, rfl⟩
  exact claims.honestNeverSlashed (Fin 1) env r valid 0 (Finset.mem_univ _) slash

end Consensus.Shape.Tests
end

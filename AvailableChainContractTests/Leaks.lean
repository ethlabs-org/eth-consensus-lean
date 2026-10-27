module
public import Mathlib.Tactic
public import AvailableChainContractProofs.Canonical

@[expose] public section

namespace AvailableChain.Contract.Tests
open AvailableChain.Generic

def env : Env (Fin 1) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩

def family (proposal vote bad : Bool) : Family := fun _ => {
  State := Unit, Label := Unit, Duty := Time, Body := Unit, Durable := Unit
  decLabel := inferInstance, decBody := inferInstance
  slotTicks := 1, slotTicks_pos := by decide
  init := (), clock := fun s _ => s
  propose := fun _ _ => if proposal then some (.genesis, 0, []) else none
  label := fun _ => (), actTime := id
  duties := fun t => [t]
  duties_spec := by simp
  duties_nodup := by simp
  act := fun _ _ => if vote then some ((), []) else none
  gossip := fun _ _ => []
  process := fun s _ => s, recordOwn := fun s _ => s
  durable := id, restore := fun s _ => s
  confirmed := fun _ => if bad then .node .genesis 1 7 7 else .genesis
  stable := fun _ => .genesis, finalized := fun _ => .genesis
  conflicts := fun _ _ => vote }

def seat {F : Family} : (protoOf F env).Label → Fin (Fintype.card (Fin 1)) ≃ Fin 1 :=
  fun _ => Equiv.refl _

def run {F : Family} (h : Time) (es : List (Event (Fin 1) (protoOf F env).Object)) : Run F env :=
  mkRun Finset.univ h seat (fun _ => 0) (fun _ _ => 0) es

theorem ready {F : Family} (h : Time) (es : List (Event (Fin 1) (protoOf F env).Object))
    (C : Constants) (v : Fin 1) (t : Time) : (run h es).Ready C v t := by
  have : v = 0 := Subsingleton.elim _ _
  simp [Run.Ready, run, mkRun, AwakeOnClosed, env, this]

theorem majority {F : Family} (h : Time) (es : List (Event (Fin 1) (protoOf F env).Object))
    (C : Constants) (t : Time) : (run h es).ReadyMajority C t := by
  classical
  simp [Run.ReadyMajority, Run.faulty, Run.readyAt, run, mkRun, Run.Ready,
    AwakeOnClosed, env]
  exact ⟨0, by simp⟩

theorem ready_nonempty {F : Family} (h : Time)
    (es : List (Event (Fin 1) (protoOf F env).Object)) (C : Constants) (t : Time) :
    ((run h es).readyAt C t).Nonempty := by
  classical
  exact ⟨0, by simpa [Run.readyAt, run, mkRun, Run.Ready, AwakeOnClosed, env]⟩

theorem recurrence (h : Time) (es : List (Event (Fin 1) (protoOf (family false false false) env).Object))
    (C : Constants) : (run h es).Recurrence C 0 1 := by
  intro t ht hh
  have ht1 : 0 ≤ t + 1 := Int.add_nonneg ht (by decide)
  refine ⟨(t + 1).toNat, ?_, ?_, ?_⟩
  · simp [Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env, Int.toNat_of_nonneg ht1]
  · simp [Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env, Int.toNat_of_nonneg ht1]
  · exact ready h es C _ _

theorem silent_cond (canonical : CanonicalRun) : ∀ C, ¬ Claims (family false false false) C := by
  intro C claims
  let H : Time := 1 + (C.D_c : Time)
  obtain ⟨es, valid, sync, _⟩ := canonical (family false false false) (Fin 1) env Finset.univ H (by dsimp [H]; positivity) seat (fun _ => 0) (fun _ _ => 0)
  let r := run H es
  have sleepy : r.Sleepy C 0 := ⟨valid, sync, rfl, rfl, fun t _ _ => majority H es C t⟩
  have inc := claims.confirmedIncluded (Fin 1) env r 0 sleepy
  have hp := inc 1 (by decide) (ready H es C _ _) (by simp [H, Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env, r, run, mkRun])
  obtain ⟨B, ⟨_, cs, i, hi, hm⟩, _⟩ := hp
  rw [Run.releasesAt, hi] at hm
  have hs : (protoOf (family false false false) env).slotAt?
      ((protoOf (family false false false) env).proposalTime 1) = some 1 :=
    (Protocol.slotAt?_eq_some _).mpr rfl
  simp [Run.tick, Run.candidates, hs, family, protoOf, env, releaseAll] at hm
  split at hm <;> cases hm

theorem proposeButGenesis_cond (canonical : CanonicalRun) : ∀ C, ¬ Claims (family true false false) C := by
  intro C claims
  let H : Time := 1 + (C.D_c : Time)
  obtain ⟨es, valid, sync, _⟩ := canonical (family true false false) (Fin 1) env Finset.univ H
    (by dsimp [H]; positivity) seat (fun _ => 0) (fun _ _ => 0)
  let r := run H es
  have sleepy : r.Sleepy C 0 := ⟨valid, sync, rfl, rfl, fun t _ _ => majority H es C t⟩
  have inc := claims.confirmedIncluded (Fin 1) env r 0 sleepy
  obtain ⟨B, ⟨_, cs, i, hi, hm⟩, inside⟩ := inc 1 (by decide) (ready H es C _ _)
    (by simp [H, Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env, r, run, mkRun])
  have hin := inside 0 (ready H es C _ _)
  have hb : B = .genesis := by
    simpa [Run.readOut, family, protoOf, CBlock.Preceq, CBlock.chain] using hin
  subst B
  rw [Run.releasesAt, hi] at hm
  simp [Run.tick, Run.candidates, family, protoOf, env] at hm
  split at hm
  · split at hm <;> cases hm <;> rename_i h <;> cases h
  · cases hm

theorem conflictsTrue_cond (canonical : CanonicalRun) : ∀ C, ¬ Claims (family false true false) C := by
  intro C claims
  obtain ⟨es, valid, _, _⟩ := canonical (family false true false) (Fin 1) env Finset.univ 0
    (by decide) seat (fun _ => 0) (fun _ _ => 0)
  let r := run 0 es
  have ht : Event.tick (0 : Fin 1) 0 ∈ r.events :=
    valid.tick_total 0 (by simp [r, run, mkRun]) 0 ⟨0, by simp⟩ (by simp [r, run, mkRun]) rfl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
  let o : (protoOf (family false true false) env).Object := .mk (.vote () ((r.seat ()).symm 0)) (.data ()) []
  have rel : r.releases 0 o 0 := by
    refine ⟨i, hi, ?_⟩
    rw [Run.releasesAt, hi]
    simp [Run.tick, Run.candidates, family, protoOf, env, Protocol.slotAt?,
      Protocol.slotLen, pubOf, releaseAll, Obj.carried, o, r, run, mkRun, seat]
    exact List.mem_cons_self
  have obs : o ∈ r.Observed := by
    obtain ⟨j, hj, hr⟩ := rel
    exact ⟨0, by simp [r, run, mkRun], j, o, (List.getElem?_eq_some_iff.mp hj).1,
      Or.inl ⟨0, hj, hr⟩, Obj.Contains.refl _⟩
  have slash : r.Slashable r.Observed 0 := ⟨o, obs, o, obs, by simp [o, Run.holder, Obj.auth], by simp [o, Run.holder, Obj.auth], rfl⟩
  exact claims.honestNeverSlashed (Fin 1) env r valid 0 (by simp [r, run, mkRun]) slash

theorem fabricated_never_proposes (h : Time)
    (es : List (Event (Fin 1) (protoOf (family false false true) env).Object))
    (s : Slot) (B : CBlock) : ¬ (run h es).HonestProposal s B := by
  rintro ⟨_, cs, i, hi, hm⟩
  rw [Run.releasesAt, hi] at hm
  simp [Run.tick, Run.candidates, family, protoOf, env] at hm
  split at hm <;> cases hm

theorem fabricated_cond (canonical : CanonicalRun) : ∀ C, ¬ Claims (family false false true) C := by
  intro C claims
  obtain ⟨es, valid, _, _⟩ := canonical (family false false true) (Fin 1) env Finset.univ 2
    (by decide) seat (fun _ => 0) (fun _ _ => 0)
  let r := run 2 es
  have norelease : ∀ i t cs, r.events[i]? = some (Event.tick 0 t) →
      (Obj.mk (.proposer 1) (.prop (.node .genesis 1 7 7)) cs : (protoOf (family false false true) env).Object) ∉ r.releasesAt i := by
    intro i t cs hi hm
    rw [Run.releasesAt, hi] at hm
    simp [Run.tick, Run.candidates, family, protoOf, env] at hm
    split at hm <;> cases hm
  have noview : ∀ i cs, (Obj.mk (.proposer 1) (.prop (.node .genesis 1 7 7)) cs :
      (protoOf (family false false true) env).Object) ∉ r.ViewIdx 0 i := by
    intro i cs hv
    obtain ⟨k, o, hk, he, hc⟩ := hv
    rcases he with ⟨t, ht, hr⟩ | ⟨t, ht⟩
    · rw [Run.releasesAt, ht] at hr
      simp [Run.tick, Run.candidates, family, protoOf, env] at hr
      split at hr <;> cases hr
    · obtain ⟨j, t', hj, ht', hr⟩ := valid.unforgeable k 0 o t ht _ hc 0
        (by simp [r, run, mkRun]) (by simp [Run.holder, r, run, mkRun, Obj.auth])
      exact norelease j t' cs ht' hr
  have ht : Event.tick (0 : Fin 1) 1 ∈ r.events :=
    valid.tick_total 0 (by simp [r, run, mkRun]) 1 ⟨1, by simp [env]⟩
      (by simp [r, run, mkRun]) rfl
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
  have hlen : i + 1 ≤ r.events.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  have htime : (protoOf (family false false true) env).proposalTime 1 ≤ r.cutTime (i + 1) := by
    unfold Run.cutTime
    simp only [Nat.add_comm, Nat.zero_add] at *
    rw [hi]
    simp [Event.time, Protocol.proposalTime, Protocol.slotLen, protoOf, family, pubOf, env]
  have hv := (claims.outputValid (Fin 1) env r valid).1 0 (by simp [r, run, mkRun])
    (i + 1) (.node .genesis 1 7 7) hlen
    (by simp [Run.readIdx, protoOf, family, CBlock.Preceq, CBlock.chain]) (by decide)
  obtain ⟨_, _, cs, hcs⟩ := hv
  exact noview _ cs hcs

theorem silent : ∀ C, ¬ Claims (family false false false) C := silent_cond canonical_run
theorem proposeButGenesis : ∀ C, ¬ Claims (family true false false) C :=
  proposeButGenesis_cond canonical_run
theorem conflictsTrue : ∀ C, ¬ Claims (family false true false) C := conflictsTrue_cond canonical_run
theorem fabricated : ∀ C, ¬ Claims (family false false true) C := fabricated_cond canonical_run

end AvailableChain.Contract.Tests
end

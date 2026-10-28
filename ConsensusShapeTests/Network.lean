module
public import ConsensusShapeTests.Model
public import Mathlib.Tactic
@[expose] public section

/-! # Network tests (L0 delivery, L1 faithfulness)

* `endpoint_waker` (review B1 scenario): `Δ = 2`, GST `0`; validator 1 is
  asleep at `0` and `1` and awake from `2`. An honest send at `0` must be held
  by validator 1 at `2 = max 0 0 + Δ`, because it is awake *at* the deadline
  (Francesco's rule). The earlier model rule (awake throughout `[a, dl a)`)
  did not require it. `endpoint_waker_silent`: a log in which validator 1
  never receives the message is not partially synchronous.
* `receipt_at_deadline`: receipt exactly at `t + Δ` meets `PSync 0`
  ("received by that time").
* `held_restart`: a receipt before a wake is held until the wake, not after.
* `psync_mono_instance`: a later GST is weaker (`PSync.mono`).
* `faithful_relayedRun`: on the model test run, the system's log is the
  engine's (`sysOf_log_faithful`): inbox and sends. -/

namespace Consensus.Shape.Tests.Network
open Consensus

/-- `Δ = 2`; validator 0 always awake, validator 1 asleep before time `2`. -/
def envW : Env (Fin 2) := ⟨2, by decide, 0, fun v t => decide (v = 0 ∨ 2 ≤ t)⟩

/-- Both honest, horizon `5`, no submissions. -/
def ptW : EnvPoint (Fin 2) := ⟨envW, Finset.univ, 5, fun _ _ => []⟩

/-- Validator 0 sends one message at `0`; receipts as given. -/
def logW (recv : Fin 2 → Unit → Time → Prop) : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, recv, fun _ _ => []⟩

/-- Francesco's rule at the endpoint: validator 1, asleep at `0`–`1` and awake
at the deadline `2`, must hold the message sent at `0`. -/
theorem endpoint_waker (recv : Fin 2 → Unit → Time → Prop) (h : (logW recv).PSync ptW 0) :
    (logW recv).Held ptW 1 () 2 :=
  h.msgs 0 (Finset.mem_univ _) () 0 le_rfl ⟨rfl, rfl⟩ 1 (Finset.mem_univ _) (by decide)
    (by decide) (by decide)

/-- A log in which validator 1 never receives the message violates `PSync 0`. -/
theorem endpoint_waker_silent : ¬ (logW fun _ _ _ => False).PSync ptW 0 := by
  intro h
  obtain ⟨t', -, hs, -⟩ := endpoint_waker _ h
  rcases hs with ⟨h1, -⟩ | hs
  · exact absurd h1 (by decide)
  · exact hs

/-- The log with validator 1 receiving the message exactly at `0 + Δ = 2`. -/
def recvAt2 : Fin 2 → Unit → Time → Prop := fun w _ t => w = 1 ∧ t = 2

theorem held0 (d : Time) (hd : 0 ≤ d) : (logW recvAt2).Held ptW 0 () d := by
  refine ⟨0, hd, Or.inl ⟨rfl, rfl⟩, fun u _ _ hwk => ?_⟩
  have := hwk.2
  simp [ptW, envW] at this

theorem held1 (d : Time) (hd : 2 ≤ d) : (logW recvAt2).Held ptW 1 () d := by
  refine ⟨2, hd, Or.inr ⟨rfl, rfl⟩, fun u hu _ hwk => ?_⟩
  have := hwk.2
  simp only [ptW, envW, decide_eq_false_iff_not, not_or] at this
  dsimp only [Time] at *
  omega

theorem held_all (w : Fin 2) (d : Time) (hd : 2 ≤ d) : (logW recvAt2).Held ptW w () d := by
  fin_cases w
  · exact held0 d (by dsimp only [Time] at *; omega)
  · exact held1 d hd

/-- Receipt exactly at the deadline `t + Δ` satisfies `PSync 0`. -/
theorem receipt_at_deadline : (logW recvAt2).PSync ptW 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro v - m t - ⟨-, rfl⟩ w - - - -
    exact held_all w _ (by simp [ptW, envW])
  · rintro v - m t - ⟨-, rfl⟩ w - a ha - - -
    refine held_all w _ ?_
    change 2 ≤ max a 0 + 2
    have := le_max_right a 0
    dsimp only [Time] at *
    omega
  · intro u _ x τ _ _ hx
    exact absurd hx (List.not_mem_nil)

/-- A later GST is weaker. -/
theorem psync_mono_instance : (logW recvAt2).PSync ptW 3 :=
  receipt_at_deadline.mono (by decide)

/-- Validator 0 awake at `0`, asleep at `1`, awake again (a wake) at `2`. -/
def envR : Env (Fin 2) := ⟨1, by decide, 0, fun _ t => decide (t ≠ 1)⟩

/-- Validator 0 received one message at `0`. -/
def logR : CommLog (Fin 2) Unit := ⟨fun _ _ _ => False, fun v _ t => v = 0 ∧ t = 0, fun _ _ => []⟩

def ptR : EnvPoint (Fin 2) := ⟨envR, Finset.univ, 5, fun _ _ => []⟩

/-- A receipt is held until the next wake (holding is memory, not
awakeness: validator 0 holds at `1` while asleep) and lost at the wake at `2`. -/
theorem held_restart : logR.Held ptR 0 () 1 ∧ ¬ logR.Held ptR 0 () 2 := by
  refine ⟨⟨0, by decide, Or.inr ⟨rfl, rfl⟩, fun u hu hu1 hwk => ?_⟩, ?_⟩
  · have hu' : u = 1 := by dsimp only [Time] at *; omega
    subst hu'
    have := hwk.1
    simp [ptR, envR] at this
  · rintro ⟨t', -, hs, hn⟩
    rcases hs with hs | ⟨-, rfl⟩
    · exact hs
    · exact hn 2 (by decide) le_rfl ⟨by simp [ptR, envR], by simp [ptR, envR]⟩

open Consensus.Model in
/-- On the model test run the system's log is the engine's communication: the
inbox (with the relayed transaction `42` at time `2`) and the sends. -/
theorem faithful_relayedRun :
    ((sysOf Model.schema Model.family (Fin 2)).log ⟨Model.env, Model.relayedRun⟩).inbox =
      Model.relayedRun.inbox ∧
    42 ∈ ((sysOf Model.schema Model.family (Fin 2)).log ⟨Model.env, Model.relayedRun⟩).inbox 0 2 ∧
    ∀ v o t, ((sysOf Model.schema Model.family (Fin 2)).log ⟨Model.env, Model.relayedRun⟩).sent
      v ⟨Model.env, o⟩ t ↔ Model.relayedRun.releases v o t := by
  have hf := sysOf_log_faithful (O := Model.schema) (F := Model.family) (V := Fin 2)
    ⟨Model.env, Model.relayedRun⟩
  refine ⟨hf.2.2.2, ?_, hf.1⟩
  rw [hf.2.2.2]
  simp [Model.relayedRun, mkRun, Run.inbox]

end Consensus.Shape.Tests.Network

end

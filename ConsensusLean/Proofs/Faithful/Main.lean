module
public import ConsensusLean.Spec.Model.System
public import Mathlib.Tactic
public import ConsensusLean.Spec.Model.Served
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Good
public import ConsensusLean.Lemmas.Model.Protocol

public section

/-! # The log of a compiled system is the engine's communication (L1)

L0 states network conditions on a system's communication log; it cannot check
that the log is the system's real communication. For the model this is proved
once here:

* `sysOf_log_faithful`: the log of `sysOf` is exactly the engine's releases
  (sent), deliveries (received) and inboxes, tagged with the run's
  environment; it carries no other message.
* `Run.held_iff_served`: on a valid run, L0 holding (`CommLog.Held`: no wake
  in `(t', d]`) is the engine's holding (`Run.Served`: no restart in
  `(t', d]`), since restarts are exactly the wakes after time `0`.
* `sysOf_delivers_iff`: L0 delivery for the system's log is L0 delivery for the
  run's log.
* `Run.log_sendsFromZero`: a valid run sends nothing before time `0`.

Boundary: this shows that the log cannot invent sends or receipts and that L0
holding is engine holding. It does not make an arbitrary L0 system honest, and
it does not show that handlers retain or use delivered data (that is the
protocol's business). -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

/-- The log of `sysOf` is the engine's communication. -/
theorem sysOf_log_faithful (r : (sysOf O F V).Run) :
    (∀ v o t, ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t) ∧
    (∀ v o t, ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t) ∧
    (∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩) ∧
    ((sysOf O F V).log r).inbox = r.2.inbox := by
  obtain ⟨E, rho⟩ := r
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro v o t
    constructor
    · rintro ⟨o', he, h⟩
      cases he
      exact h
    · intro h
      exact ⟨o, rfl, h⟩
  · intro v o t
    constructor
    · rintro ⟨o', he, h⟩
      cases he
      exact h
    · intro h
      exact ⟨o, rfl, h⟩
  · rintro v m t (⟨o, he, -⟩ | ⟨o, he, -⟩) <;> exact ⟨o, he⟩

/-- The environment point of a system run is the run's point. -/
theorem sysOf_point (rho : Run F E) :
    ((sysOf O F V).trace ⟨E, rho⟩).point = rho.point := rfl

/-- Holding in the system's log is holding in the run's log. -/
theorem sysOf_held_iff (rho : Run F E) (w : V) (o : (protoOf F E).Object) (d : Time) :
    CommLog.Held rho.point ((sysOf O F V).log ⟨E, rho⟩) w ⟨E, o⟩ d ↔
      CommLog.Held rho.point rho.log w o d := by
  have hf := sysOf_log_faithful (O := O) (F := F) (V := V) ⟨E, rho⟩
  constructor
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, ?_, hn⟩
    rcases hs with hs | hs
    · exact Or.inl ((hf.1 w o t').mp hs)
    · exact Or.inr ((hf.2.1 w o t').mp hs)
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, ?_, hn⟩
    rcases hs with hs | hs
    · exact Or.inl ((hf.1 w o t').mpr hs)
    · exact Or.inr ((hf.2.1 w o t').mpr hs)

/-- Delivery of `sysOf` is delivery of the run's log. -/
theorem sysOf_delivers_iff (rho : Run F E) (dl : Time → Time) (cut : Time) :
    CommLog.Delivers ((sysOf O F V).trace ⟨E, rho⟩).point ((sysOf O F V).log ⟨E, rho⟩) dl cut ↔
      CommLog.Delivers rho.point rho.log dl cut := by
  rw [sysOf_point]
  constructor
  · intro h
    refine ⟨?_, h.txs⟩
    intro v hv o t hs w hw a hta hc hh ha
    exact (sysOf_held_iff rho w o _).mp (h.msgs v hv ⟨E, o⟩ t ⟨o, rfl, hs⟩ w hw a hta hc hh ha)
  · intro h
    refine ⟨?_, h.txs⟩
    rintro v hv m t ⟨o, rfl, hs⟩ w hw a hta hc hh ha
    exact (sysOf_held_iff rho w o _).mpr (h.msgs v hv o t hs w hw a hta hc hh ha)

namespace Run

/-- On a valid run, L0 holding is the engine's holding: restarts of an honest
node are exactly its wakes in `(0, horizon]`. -/
theorem held_iff_served (rho : Run F E) (hv : rho.ExecutionValid) {w : V}
    (hw : w ∈ rho.honest) (o : (protoOf F E).Object) {d : Time} (hd : d ≤ rho.horizon) :
    CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d := by
  constructor
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, hs, ?_⟩
    rintro u hu ⟨h₁, h₂⟩
    exact hn u h₁ h₂ (hv.restart_at_wake w u hu).2
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, hs, ?_⟩
    intro u h₁ h₂ hwk
    have ht0 : 0 ≤ t' := by
      rcases hs with ⟨i, hi, -⟩ | ⟨i, hi⟩
      · exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1
      · exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1
    exact hn u (hv.wake_restart w hw u (lt_of_le_of_lt ht0 h₁) (le_trans h₂ hd) hwk) ⟨h₁, h₂⟩

/-- On a valid run no send happens before time `0` (event times are in
`[0, horizon]`), so the L0 convenience `CommLog.PSync.syncUntil_zero` applies. -/
theorem log_sendsFromZero (rho : Run F E) (hv : rho.ExecutionValid) :
    CommLog.SendsFromZero rho.point rho.log := by
  rw [CommLog.sendsFromZero_iff]
  rintro v - o t ⟨i, hi, -⟩
  exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1

end Run

end Consensus.Model

end

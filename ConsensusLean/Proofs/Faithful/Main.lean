module
public import ConsensusLean.Lemmas.Model.SysLog
public import ConsensusLean.Spec.Model.Served

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

The supporting log characterisations (`sysOf_sent_iff`, `sysOf_recv_iff`,
`sysOf_held_iff`, `sysOf_delivers_iff`, `Run.log_sendsFromZero`) are in
`Lemmas/Model/SysLog.lean`, so other layers use them without importing this
milestone.

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
    ((sysOf O F V).log r).inbox = r.2.inbox :=
  ⟨sysOf_sent_iff r, sysOf_recv_iff r, sysOf_log_tagged r, rfl⟩

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
      rcases hs with ⟨i, hi | ⟨_, hi⟩, -⟩ | ⟨i, hi⟩ <;>
        exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1
    exact hn u (hv.wake_restart w hw u (lt_of_le_of_lt ht0 h₁) (le_trans h₂ hd) hwk) ⟨h₁, h₂⟩

end Run

end Consensus.Model

end

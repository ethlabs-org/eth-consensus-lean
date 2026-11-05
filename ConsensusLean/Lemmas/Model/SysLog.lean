module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Problem.DerivedFacts

public section

/-! # The log of a compiled system, read through the engine (L1 support)

Characterisations of `sysOf`'s communication log that the milestones use:
sends and receipts are exactly the engine's releases and receipts, tagged
with the run's environment (`sysOf_sent_iff`, `sysOf_recv_iff`,
`sysOf_log_tagged`); its message class is the protocol's (`sysOf_log_fgAtt`); holding and delivery
of the system's log are those of the run's log (`sysOf_held_iff`,
`sysOf_delivers_iff`); and a valid run sends
nothing before time `0` (`Run.log_sendsFromZero`). The Faithful milestone
(`Proofs/Faithful/Main.lean`) assembles `sysOf_log_faithful` from them. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

/-- A send of the system's log is an engine release, tagged with the run's environment. -/
theorem sysOf_sent_iff (r : (sysOf O F V).Run) (v : V) (o : (protoOf F r.1).Object) (t : Time) :
    ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t := by
  obtain ⟨E, rho⟩ := r
  constructor
  · rintro ⟨o', he, h⟩
    cases he
    exact h
  · intro h
    exact ⟨o, rfl, h⟩

/-- A receipt of the system's log is an engine receipt, tagged with the run's environment. -/
theorem sysOf_recv_iff (r : (sysOf O F V).Run) (v : V) (o : (protoOf F r.1).Object) (t : Time) :
    ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t := by
  obtain ⟨E, rho⟩ := r
  constructor
  · rintro ⟨o', he, h⟩
    cases he
    exact h
  · intro h
    exact ⟨o, rfl, h⟩

/-- Every message the system's log sends or receives carries the run's environment. -/
theorem sysOf_log_tagged (r : (sysOf O F V).Run) :
    ∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩ := by
  obtain ⟨E, rho⟩ := r
  rintro v m t (⟨o, he, -⟩ | ⟨o, he, -⟩) <;> exact ⟨o, he⟩

/-- The environment point of a system run is the run's point. -/
theorem sysOf_point (rho : Run F E) :
    ((sysOf O F V).trace ⟨E, rho⟩).point = rho.point := rfl

/-- Holding in the system's log is holding in the run's log. -/
theorem sysOf_held_iff (rho : Run F E) (w : V) (o : (protoOf F E).Object) (d : Time) :
    CommLog.Held rho.point ((sysOf O F V).log ⟨E, rho⟩) w ⟨E, o⟩ d ↔
      CommLog.Held rho.point rho.log w o d := by
  constructor
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, ?_, hn⟩
    rcases hs with hs | hs
    · exact Or.inl ((sysOf_sent_iff ⟨E, rho⟩ w o t').mp hs)
    · exact Or.inr ((sysOf_recv_iff ⟨E, rho⟩ w o t').mp hs)
  · rintro ⟨t', ht, hs, hn⟩
    refine ⟨t', ht, ?_, hn⟩
    rcases hs with hs | hs
    · exact Or.inl ((sysOf_sent_iff ⟨E, rho⟩ w o t').mpr hs)
    · exact Or.inr ((sysOf_recv_iff ⟨E, rho⟩ w o t').mpr hs)

/-- The message class of the system's log is the protocol's: a tagged object is an attestation
exactly when the protocol classifies it as one (`Model.Protocol.isFGAtt`). -/
theorem sysOf_log_fgAtt (rho : Run F E) (o : (protoOf F E).Object) :
    ((sysOf O F V).log ⟨E, rho⟩).fgAtt ⟨E, o⟩ ↔ (protoOf F E).isFGAtt o := by
  constructor
  · rintro ⟨o', he, h⟩
    cases he
    exact h
  · intro h
    exact ⟨o, rfl, h⟩

/-- Delivery of `sysOf` is delivery of the run's log. -/
theorem sysOf_delivers_iff (rho : Run F E) (dl dlF : Time → Time) (cut : Time) :
    CommLog.Delivers ((sysOf O F V).trace ⟨E, rho⟩).point ((sysOf O F V).log ⟨E, rho⟩) dl dlF
        cut ↔
      CommLog.Delivers rho.point rho.log dl dlF cut := by
  rw [sysOf_point]
  constructor
  · intro h
    refine ⟨?_, ?_, h.txs⟩
    · intro v hv o t hs hr w hw a hta hc hh ha
      exact (sysOf_held_iff rho w o _).mp (h.msgs v hv ⟨E, o⟩ t ⟨o, rfl, hs⟩
        (fun h' => hr ((sysOf_log_fgAtt rho o).mp h')) w hw a hta hc hh ha)
    · intro v hv o t hs hr w hw a hta hc hh ha
      exact (sysOf_held_iff rho w o _).mp (h.fgAtts v hv ⟨E, o⟩ t ⟨o, rfl, hs⟩
        ((sysOf_log_fgAtt rho o).mpr hr) w hw a hta hc hh ha)
  · intro h
    refine ⟨?_, ?_, h.txs⟩
    · rintro v hv m t ⟨o, rfl, hs⟩ hr w hw a hta hc hh ha
      exact (sysOf_held_iff rho w o _).mpr (h.msgs v hv o t hs
        (fun h' => hr ((sysOf_log_fgAtt rho o).mpr h')) w hw a hta hc hh ha)
    · rintro v hv m t ⟨o, rfl, hs⟩ hr w hw a hta hc hh ha
      exact (sysOf_held_iff rho w o _).mpr (h.fgAtts v hv o t hs
        ((sysOf_log_fgAtt rho o).mp hr) w hw a hta hc hh ha)

/-- On a valid run no send happens before time `0` (event times are in
`[0, horizon]`), so the L0 convenience `CommLog.PSync.syncUntil_zero` applies. -/
theorem Run.log_sendsFromZero (rho : Run F E) (hv : rho.ExecutionValid) :
    CommLog.SendsFromZero rho.point rho.log := by
  rw [CommLog.sendsFromZero_iff]
  rintro v - o t ⟨i, hi | ⟨_, hi⟩, -⟩ <;> exact (hv.in_horizon _ (List.mem_of_getElem? hi)).1

end Consensus.Model

end

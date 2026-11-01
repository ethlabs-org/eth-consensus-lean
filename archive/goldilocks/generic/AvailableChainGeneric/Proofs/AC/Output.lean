module
public import AvailableChainGeneric.Statements.AC.Reads
public import AvailableChainEngineV2.Conditions.Schedule -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V : Type} {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

/-- The three output cases on an interval with no local restart
(aclaws-inputs.md:9–13; GLY C.1 item 2). -/
theorem output_step_of_restartFree (A : ACReads E rho) (laws : ACLaws A)
    (i : Nat) (x : V) (hrf : restartFree rho x i (i + 1)) :
    A.output (i + 1) x = A.output i x ∨ GateWrite A i x ∨ Reconcile A i x := by
  rcases laws.output_step i x with same | gate | reconcile | reset
  · exact Or.inl same
  · exact Or.inr (Or.inl gate)
  · exact Or.inr (Or.inr reconcile)
  · obtain ⟨t, ht, _⟩ := reset
    exact (hrf i t (Nat.le_refl i) (Nat.lt_succ_self i) ht).elim

/-- Select the observations at the unique scheduled tick for each label and
node, then transfer the gate law (step4b-plan.md, S4b-02; Reads.lean:252–259). -/
theorem gateWrite_of_scheduleWellFormed_statement :
    GateWriteOfScheduleWellFormedStatement := by
  classical
  unfold GateWriteOfScheduleWellFormedStatement
  intro V In P E rho A laws schedule
  let tickIndex (s : Slot) (x : V) : Nat :=
    if h : ∃ i : Nat, rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) then
      h.choose
    else 0
  have tickIndex_eq (i : Nat) (s : Slot) (x : V)
      (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s))) :
      tickIndex s x = i := by
    have hex : ∃ j : Nat, rho.events[j]? = some (.tick x (SA.gateTime A.prm s)) := ⟨i, he⟩
    dsimp only [tickIndex]
    rw [dite_eq_left hex]
    obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.mp hex.choose_spec
    obtain ⟨hi, hie⟩ := List.getElem?_eq_some_iff.mp he
    exact (schedule.nodup.getElem_inj_iff (hi := hj) (hj := hi)).mp (hje.trans hie.symm)
  let raw (s : Slot) (x : V) := A.raw (tickIndex s x) s x
  let fast (s : Slot) (x : V) := A.fast (tickIndex s x) s x
  refine ⟨raw, fast, ?_⟩
  intro i s x he
  have hraw : A.raw i s x = raw s x := by
    dsimp only [raw]
    rw [tickIndex_eq i s x he]
  have hfast : A.fast i s x = fast s x := by
    dsimp only [fast]
    rw [tickIndex_eq i s x he]
  have gate := laws.gate_write i s x he
  refine ⟨hraw, hfast, {
    view_output := gate.view_output
    view_leases := gate.view_leases
    view_now := gate.view_now
    anchor_eq := gate.anchor_eq
    raw_eq := hraw.symm.trans gate.raw_eq
    saved_other := gate.saved_other
    saved := gate.saved
    fresh := ?_
    effects := ?_ }⟩
  · intro hfresh
    exact (gate.fresh hfresh).trans (congrArg some hraw)
  · rcases gate.effects with skip | run
    · exact Or.inl ⟨skip.1, skip.2.1, skip.2.2.1, hfast.symm.trans skip.2.2.2⟩
    · refine Or.inr { empty := ?_, veto := ?_, accept := ?_ }
      · intro hempty
        obtain ⟨hout, hleases, hfast'⟩ := run.empty (hraw.trans hempty)
        exact ⟨hout, hleases, hfast.symm.trans hfast'⟩
      · intro h hsome hveto
        obtain ⟨hout, hleases, hfast'⟩ := run.veto h (hraw.trans hsome) hveto
        exact ⟨hout, hleases, hfast.symm.trans hfast'⟩
      · intro h hsome haccept
        obtain ⟨hout, hleases, hfast'⟩ := run.accept h (hraw.trans hsome) haccept
        exact ⟨hout, hleases, hfast.symm.trans hfast'⟩

/-- The slot-only gate observations under a well-formed schedule (S4b-02). -/
theorem gateWrite_of_scheduleWellFormed :
    ∀ {V In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}
      (A : ACReads E rho), ACLaws A → ScheduleWellFormed E rho →
      ∃ (raw : Slot → V → Option Block) (fast : Slot → V → List Block),
        ∀ i s x, rho.events[i]? = some (.tick x (SA.gateTime A.prm s)) →
          A.raw i s x = raw s x ∧ A.fast i s x = fast s x ∧
            GateWriteAtSpec
              ({ A with raw := fun _ => raw, fast := fun _ => fast } : ACReads E rho) i s x :=
  gateWrite_of_scheduleWellFormed_statement

end AvailableChain.Gen.AC

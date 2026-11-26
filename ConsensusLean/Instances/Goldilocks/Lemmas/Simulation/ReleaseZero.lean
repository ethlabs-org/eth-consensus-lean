module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AdmitsAtTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps

public section

/-! # Goldilocks Simulation: the stock release schedule

At the stock schedule (`release ≡ true`) no state ever holds an attestation
(`held_nil_of_release`), so every batch poll is the one of the node without a release schedule
(`pollBatch_of_held_nil`), and the own attestations a tick admits to the pool are only the one
its FG update signs and releases at once (`admitsAt_tick_of_release`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V} [DecidableEq V] (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **At the stock schedule nothing is ever held**: the FG update releases what it signs, so no
step adds to the held queue. -/
theorem held_nil_of_release (hR : S.release (pubOf E) = fun _ _ => true) (v : V) :
    ∀ i, (stateAt S rho hn v i).held = []
  | 0 => by rw [stateAt_zero]; exact init_held (fun _ _ => true) (fun _ _ => true) _ _ _
  | i + 1 => by
    have ih := held_nil_of_release hR v i
    have hpoll : ∀ (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) t, st.held = [] →
        (pollBatch st t (S.release (pubOf E))).1.held = [] := fun st t h => by
      rw [hR]; exact pollBatch_held_stock st t h
    match he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_tick S rho hn w he]
          refine tick_pres S rho hn (fun st => st.held = [])
            (fun st o hs h => (recordOwn_held st o hs).trans h)
            (fun st s h => (propose_held st s).trans h)
            (fun st h => (nodeTick_held st).trans h) hpoll w _ t ?_
          rw [stateAt_eq] at ih
          exact ih
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_deliver S rho hn w he]
          refine deliver_pres S rho hn (fun st => st.held = []) hpoll
            (fun st _ _ hs h => (recordOwn_held st _ hs).trans h) w _ o t ?_
          rw [stateAt_eq] at ih
          exact (process_held _ _ _).trans ih
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          rw [stateAt_restart S rho hn w he, restore_held]
          exact ih
      · rw [state_of_other S rho hn v i e he hne]
        exact ih

/-- At the stock schedule nothing is held before a tick's first trailing poll either. -/
theorem beforeTrailing_held_nil (hR : S.release (pubOf E) = fun _ _ => true) (v : V) (i : Nat)
    (t : Time) : (shapeOf S hn (beforeTrailing S rho v i t)).held = [] := by
  have hpoll : ∀ (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) t, st.held = [] →
      (pollBatch st t (S.release (pubOf E))).1.held = [] := fun st t h => by
    rw [hR]; exact pollBatch_held_stock st t h
  have hpres := runDuties_pres S rho hn (fun st => st.held = [])
    (fun st o hs h => (recordOwn_held st o hs).trans h) (fun st s h => (propose_held st s).trans h)
    (fun st h => (nodeTick_held st).trans h) hpoll v
  rw [beforeTrailing_eq]
  refine hpres _ _ (hpres _ _ ?_)
  have := held_nil_of_release S rho hn hR v i
  rw [stateAt_eq] at this
  exact this

/-- **At the stock schedule a tick admits only the attestation its FG update signs**: the first
trailing poll flushes nothing, since nothing is held. -/
theorem admitsAt_tick_of_release (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    admitsAt S rho hn v i ⊆ (fgSigned (shapeOf S hn (beforeTrailing S rho v i t))).toList := by
  intro a ha
  have hX := beforeTrailing_held_nil S rho hn hR v i t
  rcases List.mem_append.1 (mem_admitsAt_rel_tick S rho hn hv he ha) with h | h
  · rw [pollFlush_eq, hX] at h
    split at h <;> cases h
  · split at h
    · exact h
    · cases h

/-- **At the stock schedule a tick admits exactly the attestation its FG update signs, when it is
not already in the pool** (`on_attestation` appends only new attestations). -/
theorem admitsAt_tick_of_release_eq (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    admitsAt S rho hn v i =
      (if (shapeOf S hn (beforeTrailing S rho v i t)).fgDue then
        fgSigned (shapeOf S hn (beforeTrailing S rho v i t)) else none).toList.filter
        (fun a => a ∉ (stateAt S rho hn v i).node.fg.atts) := by
  have hX := beforeTrailing_held_nil S rho hn hR v i t
  have hlist : pollFlush (shapeOf S hn (beforeTrailing S rho v i t)) (S.release (pubOf E)) ++
      (if ((shapeOf S hn (beforeTrailing S rho v i t)).fgDue &&
          S.release (pubOf E) (shapeOf S hn (beforeTrailing S rho v i t)).self
            (shapeOf S hn (beforeTrailing S rho v i t)).now) = true then
        (fgSigned (shapeOf S hn (beforeTrailing S rho v i t))).toList else []) =
      (if (shapeOf S hn (beforeTrailing S rho v i t)).fgDue then
        fgSigned (shapeOf S hn (beforeTrailing S rho v i t)) else none).toList := by
    rw [pollFlush_eq, hX, hR]
    cases (shapeOf S hn (beforeTrailing S rho v i t)).fgDue <;> simp
  rw [admitsAt_trace, ← node_stateAt_trace]
  refine NodeAsChainShape.CanonicalTrace.Encoding.OpLaws.admitsAt_of_rel_toList
    (traceEncoding_opLaws S hn) (goldilocks_ready S hn) rho hv he _ ?_
  rw [← hlist]
  exact trailing_rel S rho hn

/-- Recording an attestation adds its content to the contents sent. -/
theorem recordAtt_sent {n : Nat} (Λ : FG.Record) (a : FG.Att n) :
    (Λ.recordAtt a).sent = Λ.sent ++ [a.content] := by rfl

end Consensus.Goldilocks.Simulation

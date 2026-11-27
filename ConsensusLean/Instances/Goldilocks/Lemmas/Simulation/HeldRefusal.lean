module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox

public section

/-! # Goldilocks Simulation: the held queue at every engine cut

The engine-level reading of `HeldQueue`'s laws. After the first poll that follows the tick step
(the proposal poll sets `ticked`), an honest node's held queue is non-empty only when its release
schedule refuses release at its own time: at every cut `HeldRefused` holds unless the node's
last event was a restart (`heldRefused_inv`). So the poll of a delivery, which follows a tick at
the same time, flushes nothing, and a delivery releases no attestation (`deliver_not_att`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

section Invariant

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **After the first poll of a tick, a non-empty held queue means the release schedule refuses
release at the node's time.** At every cut an honest node satisfies `HeldRefused` unless its last
event was a restart: a tick ends with a batch poll, which establishes it, and the gossip keeps
it; a delivery keeps the key, the clock and the held queue, then polls. -/
theorem heldRefused_inv (hv : rho.ExecutionValid) (v : V) :
    ∀ i, LastRestart S rho v i ∨ HeldRefused (S.release (pubOf E)) (stateAt S rho hn v i)
  | 0 => by
    rw [stateAt_zero]
    exact Or.inr ((heldRefused_iff _).2 fun h => absurd rfl h)
  | i + 1 => by
    have ih := heldRefused_inv hv v i
    have hext : LastRestart S rho v i → (∀ e, rho.events[i]? = some e → e.node ≠ v) →
        LastRestart S rho v (i + 1) := by
      simp only [lastRestart_eq]
      exact fun h hi => NodeAsChainShape.CanonicalTrace.lastRestart_other rho hi h
    have hkeep : ∀ (st : State (S.params (pubOf E) hn) S.vote) o hs,
        HeldRefused (S.release (pubOf E)) st →
        HeldRefused (S.release (pubOf E)) (recordOwn st o hs) := fun st o hs h =>
      heldRefused_of_held (recordOwn_self _ _ _) (recordOwn_now _ _ _) (recordOwn_held _ _ _) h
    match he : rho.events[i]? with
    | none =>
      rw [stateAt_succ_none S rho hn v he]
      exact ih.imp_left fun h => hext h fun e he' => by rw [he] at he'; cases he'
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick w t =>
          simp only [Model.Event.node] at hne
          subst hne
          have hm := List.mem_of_getElem? he
          rw [stateAt_tick S rho hn w he]
          refine Or.inr ?_
          rw [tick_of_awake S rho w _ t (hv.tick_awake w t hm)]
          apply releaseAll_pres S rho hn _ hkeep
          have hsel := poll_selected S rho hv w
          rw [duties_eq S t (hv.in_horizon _ hm).1, runDuties_fst_append]
          have hpoll : ∀ N : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
              shapeOf S hn (rho.runDuties w N [.poll t.toNat]).1 =
                (pollBatch (shapeOf S hn N) t.toNat (S.release (pubOf E))).1 :=
            fun N => dutyStep_poll S rho hn w N t.toNat hsel
          rw [hpoll]
          refine heldRefused_pollBatch _ _ ?_
          -- after the proposal poll the tick flag is set, and the rest of the duties keep it
          refine (congrArg (fun n => (shapeOf S hn n).ticked) (runDuties_fst_append S rho w
            ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i w).st t
              (Model.mempool rho.inbox w t), (rho.stateBefore i w).seen⟩
            [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
            ((skeleton (pubOf E) S.vote).proposeAt t ++ [.poll t.toNat]))).trans ?_
          rw [← atProposal_eq]
          refine runDuties_pres S rho hn (fun st => st.ticked = true)
            (fun st o hs h => (recordOwn_ticked st o hs).trans h)
            (fun st s h => (propose_ticked st s).trans h) (fun _ _ => rfl)
            (fun st τ h => (pollBatch_ticked st τ).trans h) w _ _ ?_
          rw [atProposal_shape S rho hn w _ t hsel]
        | deliver w o t =>
          simp only [Model.Event.node] at hne
          subst hne
          refine Or.inr ?_
          have h0 : HeldRefused (S.release (pubOf E)) (stateAt S rho hn w i) := by
            rcases ih with h | h
            · exact absurd h (not_lastRestart_deliver S rho hv he)
            · exact h
          rw [stateAt_deliver S rho hn w he]
          refine deliver_pres S rho hn (HeldRefused (S.release (pubOf E)))
            (fun st τ h => heldRefused_pollBatch_of_refused h τ)
            (fun st _ _ hs h => hkeep st _ hs h) w (rho.stateBefore i w) o t ?_
          rw [← stateAt_eq S rho hn w i]
          exact heldRefused_of_held (process_self _ _ _) (process_now _ _ _) (process_held _ _ _)
            h0
        | restart w t =>
          simp only [Model.Event.node] at hne
          subst hne
          refine Or.inl ?_
          rw [lastRestart_eq, NodeAsChainShape.CanonicalTrace.lastRestart_iff]
          exact ⟨i, by omega, t, he, fun l h1 h2 => absurd h2 (by omega)⟩
      · rw [state_of_other S rho hn v i e he hne]
        exact ih.imp_left fun h => hext h fun e' he' => by
          rw [he] at he'; cases he'; exact hne

end Invariant

section DeliveryReleases

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

include hn in
/-- A delivery releases only a queued vote or unsigned gossip, never an attestation. -/
theorem deliver_not_att (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    {o : (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) (a : FG.Att (Fintype.card V)) :
    attObj a ∉ rho.releasesAt i := by
  have hm := List.mem_of_getElem? he
  have ht := (hv.in_horizon _ hm).1
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hpre : OneVote t (stateAt S rho hn v i) := by
    rcases (outbox_inv S rho hn hv v i).2 with h | h
    · exact absurd h (not_lastRestart_deliver S rho hv he)
    · rwa [hnow] at h
  have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o) ht
    (delivered (stateAt S rho hn v i).voteIO (Model.digests rho.hash o) (stateAt S rho hn v i) o)
    (stateAt S rho hn v i) hnow hpre
  intro h
  simp only [Model.Run.releasesAt, he] at h
  unfold Model.Run.deliver at h
  simp only at h
  rcases List.mem_append.mp h with h | h
  · rw [deliverDuties_eq S t ht] at h
    have hrd : ∀ N : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
        (rho.runDuties v N [.poll t.toNat]).2 = (rho.dutyStep v N (.poll t.toNat)).2 :=
      fun _ => rfl
    rw [hrd] at h
    rcases dutyStep_poll_sub S rho hn v _ _ _ h with ⟨b, hb, heq⟩ | ⟨τ, cs, heq⟩ |
      ⟨τ, m, w, -, heq⟩ | ⟨a', ha', -⟩
    case inr.inr.inr =>
      have hr : HeldRefused (S.release (pubOf E))
          (process (stateAt S rho hn v i) o (Model.digests rho.hash o)) := by
        rcases heldRefused_inv S rho hn hv v i with h | h
        · exact absurd h (not_lastRestart_deliver S rho hv he)
        · exact heldRefused_of_held (process_self _ _ _) (process_now _ _ _)
            (process_held _ _ _) h
      change a' ∈ pollFlush (process ((rho.stateBefore i v).st.1 hn) o
        (Model.digests rho.hash o)) (S.release (pubOf E)) at ha'
      rw [← stateAt_eq S rho hn v i, pollFlush_eq_nil hr] at ha'
      cases ha'
    case inr.inl =>
      have hmsg := congrArg Model.Obj.msg heq
      change Model.Msg.data (Body.att (encodeAtt a)) = Model.Msg.data (Body.forward τ) at hmsg
      cases hmsg
    case inr.inr.inl =>
      have hmsg := congrArg Model.Obj.msg heq
      change Model.Msg.data (Body.att (encodeAtt a)) =
        Model.Msg.data (Body.voteForward τ (encodeVote m)) at hmsg
      cases hmsg
    have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
      (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
    change (pollPre (process ((rho.stateBefore i v).st.1 hn) o
      (Model.digests rho.hash o)) (S.release (pubOf E))).outbox.head? =
      some b at hb
    rw [← stateAt_eq S rho hn v i] at hb
    rw [pollPre_eq, hf] at hb
    obtain ⟨w, z, rfl⟩ := ((oneVote_iff _ _).1 hproc).1 b (List.mem_of_mem_head? hb)
    have hmsg := congrArg Model.Obj.msg heq
    simp only [attObj, Model.Obj.msg] at hmsg
    cases hmsg
  · have := gossip_unsigned S rho _ _ _ _ h
    simp [attObj, Model.Obj.auth] at this

end DeliveryReleases

end Consensus.Goldilocks.Simulation

end

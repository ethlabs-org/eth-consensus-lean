module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding

public section

/-! # Reachable forwarding inventory

Runtime queue shape and prefix holdings used to connect block acceptance to publication.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Pending block payloads have the canonical parent/child shape. This says nothing about
whether their guards succeed or whether the parent has already been published. -/
def ForwardQueueCanonical {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) : Prop :=
  ∀ q ∈ st.forwards, ∃ p : Option (Wire sp.n), ∃ B, q.2 = p.toList ++ [blockObj sp B]

/-- Expose only the queue-shape proposition, not the definition body. -/
theorem forwardQueueCanonical_iff {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) :
    ForwardQueueCanonical st ↔
      ∀ q ∈ st.forwards, ∃ p : Option (Wire sp.n), ∃ B,
        q.2 = p.toList ++ [blockObj sp B] := by rfl

/-- Every new acceptance queues one canonical child with its exact optional parent. -/
theorem forwardQueueCanonical_queueAccepted {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (queueAccepted st B) := by
  rw [forwardQueueCanonical_iff] at h ⊢
  intro q hq
  rcases queueAccepted_forward_origin st B q hq with hq | ⟨root, p, _, _, he⟩
  · exact h q hq
  · exact ⟨p, B, congrArg Prod.snd he⟩

/-- The handler's acceptance fold preserves canonical payload shape. -/
theorem forwardQueueCanonical_apply {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) r
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (apply st r) := by
  rw [forwardQueueCanonical_iff] at h ⊢
  intro q hq
  rcases apply_forward_origin st r q hq with hq | ⟨B, p, _, he⟩
  · exact h q hq
  · exact ⟨p, B, congrArg Prod.snd he⟩

/-- Canonical queue payloads become canonical signed forwarding objects. -/
theorem forwardQueueCanonical_pending {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (h : ForwardQueueCanonical st) :
    ∀ o ∈ pendingWrappers st, ∃ t p B, o = forwardObj sp st.self t p B := by
  rw [forwardQueueCanonical_iff] at h
  intro o ho
  rw [pendingWrappers_eq] at ho
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
  obtain ⟨p, B, he⟩ := h q hq
  exact ⟨q.1, p, B, by simp only [he, forwardObj]⟩

private theorem canonical_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact forwardQueueCanonical_apply st _ h
    · exact h
  · exact h

private theorem canonical_processOne {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (processOne hs st o) := by
  unfold processOne
  split
  · unfold relayIf
    dsimp only
    split <;> exact forwardQueueCanonical_apply st _ h
  · exact forwardQueueCanonical_apply st _ h
  · unfold relayIf
    simp only [↓reduceIte]
    exact forwardQueueCanonical_apply st _ h
  · exact h

private theorem canonical_poll {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) t :
    ForwardQueueCanonical (poll st t).1 := by
  rw [forwardQueueCanonical_iff, (poll_wrappers st t).2]
  exact fun q h => False.elim (List.not_mem_nil h)

/-- The actual event-boundary queue always has canonical block payload shape. This
structural invariant needs no execution-validity or publication-success premise. -/
theorem stateAt_forwardQueueCanonical {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) : ∀ i, ForwardQueueCanonical (stateAt S rho hn v i)
  | 0 => by
    rw [forwardQueueCanonical_iff]
    exact fun q h => False.elim (List.not_mem_nil h)
  | i + 1 => by
    have ih := stateAt_forwardQueueCanonical S rho hn v i
    cases he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some ev =>
      by_cases hnode : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_tick S rho hn v he]
          apply tick_pres S rho hn ForwardQueueCanonical canonical_recordOwn
            (fun st s h => by unfold propose; dsimp only; split <;> exact h)
            (fun st h => by
              unfold nodeTick
              split
              · exact forwardQueueCanonical_apply st _ h
              · exact h)
            (fun st t _ => canonical_poll st t)
          exact ih
        | deliver w o t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_deliver S rho hn v he]
          apply deliver_pres S rho hn ForwardQueueCanonical (fun st t _ => canonical_poll st t)
            (fun st m cs hs h => canonical_recordOwn st _ hs h)
          have hf : ∀ xs : List (Wire (Fintype.card V)),
              ∀ st : State (S.params (pubOf E) hn) (S.ro _), ForwardQueueCanonical st →
                ForwardQueueCanonical (xs.foldl (processOne (digests rho.hash o)) st) := by
            intro xs
            induction xs with
            | nil => exact fun _ h => h
            | cons x xs hx => exact fun st h => hx _ (canonical_processOne st x _ h)
          exact hf _ _ ih
        | restart w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_restart S rho hn v he]
          exact ih
      · rw [state_of_other S rho hn v i ev he hnode]; exact ih

end Consensus.Goldilocks.Refinement

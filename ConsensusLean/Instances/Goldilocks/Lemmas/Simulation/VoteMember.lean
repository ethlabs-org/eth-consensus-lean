module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields

public section

/-! # Goldilocks Simulation: own member votes in the outbox

Every handler keeps the node's installed vote permission (`SA.step_mayVote`) and emits only
through the gate (`SA.emits_mayVote`), so every queued vote is an own vote of a slot whose vote
role selects the node (`VoteMember`, `stateAt_voteMember`, `delivery_outbox_vote_member`); every
emission of an AC cut passes the gate of its handler's start state
(`emits_mayVote_of_mem_exec`). -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload SAState)

variable {binding : VoteBinding}

section MemberVotes

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {p : Nat → Bool}

/-- The node's permission is `p`, and every queued vote is an own vote of a slot `p` admits. -/
def VoteMember (p : Nat → Bool) (st : State sp ro binding) : Prop :=
  st.node.ac.mayVote = p ∧
    ∀ m, .vote (encodeVote m) ∈ st.outbox → m.val = st.self ∧ p m.slot = true

/-- `VoteMember p st`: the node's permission is `p`, and every queued vote is an own vote of a
slot `p` admits. -/
theorem VoteMember_iff (st : State sp ro binding) :
    VoteMember p st ↔ st.node.ac.mayVote = p ∧
      ∀ m, .vote (encodeVote m) ∈ st.outbox → m.val = st.self ∧ p m.slot = true := by
  rfl

private theorem emitted_voteMember (self : Fin sp.n) (cs : List (Cut (goldilocksNode sp ro)))
    (h : ∀ ℓ, Cut.ac ℓ ∈ cs → ∀ e ∈ ℓ.emits, e.msg.val = self ∧ p e.msg.slot = true) :
    ∀ m, .vote (encodeVote m) ∈ emitted cs → m.val = self ∧ p m.slot = true := by
  intro m hm
  obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp hm
  cases c with
  | fg c => cases hm
  | ac ℓ =>
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    have heq' := congrArg (decodeVote sp.n) (Body.vote.inj heq)
    simp only [decodeVote_encodeVote, Option.some.injEq] at heq'
    subst m
    exact h ℓ hc e he

private theorem apply_voteMember (st : State sp ro binding) r (h : VoteMember p st)
    (hac : r.1.ac.mayVote = p)
    (he : ∀ m, .vote (encodeVote m) ∈ emitted r.2 → m.val = st.self ∧ p m.slot = true) :
    VoteMember p (apply st r) :=
  ⟨hac, fun m hm => (List.mem_append.mp hm).elim (h.2 m) (he m)⟩

private theorem acCall_voteMember (st : State sp ro binding) (c : (goldilocksNode sp ro).Call)
    (h : VoteMember p st) :
    VoteMember p (apply st ((Node.acCall st.self st.node st.now c).1,
      [(Node.acCall st.self st.node st.now c).2])) :=
  apply_voteMember st _ h
    ((SA.step_mayVote ro st.self st.node.ac (frame st.node) st.now c).trans h.1)
    (emitted_voteMember st.self _ fun ℓ hℓ e he => by
      have hℓ := Cut.ac.inj (List.mem_singleton.mp hℓ)
      subst ℓ
      refine ⟨emits_val st.self st.node.ac (frame st.node) st.now c e he, ?_⟩
      rw [← h.1]
      exact SA.emits_mayVote ro st.self st.node.ac (frame st.node) st.now c e he)

private theorem tick_voteMember (st : State sp ro binding) (h : VoteMember p st) :
    VoteMember p (nodeTick st) := by
  unfold nodeTick
  split
  · exact acCall_voteMember st .tick h
  · exact h

private theorem block_voteMember (st : State sp ro binding) (B : Blk sp) (h : VoteMember p st) :
    VoteMember p (apply st (Node.onBlock st.self st.node st.now B)) := by
  unfold Node.onBlock
  split_ifs
  · exact apply_voteMember st _ h h.1 (fun _ hm => absurd hm (by simp [emitted]))
  · split
    · exact apply_voteMember st _ h h.1 (fun _ hm => absurd hm (by simp [emitted]))
    · exact apply_voteMember st _ h
        ((SA.step_mayVote ro st.self st.node.ac _ st.now (.block B)).trans h.1)
        (emitted_voteMember st.self _ fun ℓ hℓ e he => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
          rcases hℓ with hℓ | hℓ
          · cases hℓ
          · have hℓ := Cut.ac.inj hℓ
            subst ℓ
            refine ⟨emits_val _ _ _ _ _ e he, ?_⟩
            rw [← h.1]
            exact SA.emits_mayVote ro _ _ _ _ _ e he)

private theorem processOne_voteMember hs (st : State sp ro binding) o (h : VoteMember p st) :
    VoteMember p (processOne hs st o) := by
  classical
  unfold processOne
  split
  · dsimp only
    unfold relayIf
    split <;> exact block_voteMember st _ h
  · dsimp only
    exact acCall_voteMember st _ h
  · unfold relayIf
    split <;> simpa only [VoteMember, apply, Node.onAttestation, emitted,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil] using h
  · exact h

theorem process_voteMember (st : State sp ro binding) o hs (h : VoteMember p st) :
    VoteMember p (process st o hs) := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => exact h
  | cons o os ih => exact ih _ (processOne_voteMember hs st o h)

private theorem record_voteMember (st : State sp ro binding) o hs (h : VoteMember p st) :
    VoteMember p (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact block_voteMember st _ h
    · exact h
  · exact h

theorem fgUpdate_voteMember (st : State sp ro binding) (h : VoteMember p st) :
    VoteMember p (fgUpdate st) := by
  have hac : (Node.acToFG st.node st.now).1.ac.mayVote = p :=
    (SA.step_mayVote ro st.self st.node.ac (frame st.node) st.now .toFG).trans h.1
  unfold fgUpdate
  dsimp only
  split
  · exact ⟨hac, h.2⟩
  · split
    · exact ⟨hac, h.2⟩
    · refine ⟨hac, fun m hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact h.2 m hm
      · cases List.mem_singleton.mp hm

private theorem poll_voteMember (st : State sp ro binding) (t : Time) (h : VoteMember p st) :
    VoteMember p (poll st t).1 := by
  have hi : VoteMember p (if st.fgDue then fgUpdate st else st) := by
    split
    · exact fgUpdate_voteMember st h
    · exact h
  unfold poll
  generalize (if st.fgDue then fgUpdate st else st) = pre at hi ⊢
  dsimp only
  split
  · exact hi
  · rename_i b rest he
    exact ⟨hi.1, fun m hm => hi.2 m (by rw [he]; exact List.mem_cons_of_mem _ hm)⟩

private theorem propose_voteMember (st : State sp ro binding) (s : Slot) (h : VoteMember p st) :
    VoteMember p (propose st s).1 := by
  obtain ⟨ho, hs, -⟩ := propose_keeps' st s
  refine ⟨?_, fun m hm => ?_⟩
  · unfold propose
    dsimp only
    split <;>
      exact (SA.step_mayVote ro st.self st.node.ac (frame st.node) st.now .proposal).trans h.1
  · rw [ho] at hm
    rw [hs]
    exact h.2 m hm

private theorem restore_voteMember (k : Fin sp.n) (d : State sp ro binding) (t : Time)
    (hk : d.self = k) (h : VoteMember p d) : VoteMember p (restore k d t) :=
  apply_voteMember { d with self := k, now := t } _
    ⟨h.1, fun m hm => ⟨(h.2 m hm).1.trans hk, (h.2 m hm).2⟩⟩
    ((SA.step_mayVote ro k d.node.ac (frame d.node) t .restart).trans h.1)
    (emitted_voteMember k _ fun ℓ hℓ e he => by
      have hℓ := Cut.ac.inj (List.mem_singleton.mp hℓ)
      subst ℓ
      refine ⟨emits_val k d.node.ac (frame d.node) t .restart e he, ?_⟩
      rw [← h.1]
      exact SA.emits_mayVote ro k d.node.ac (frame d.node) t .restart e he)

/-- Every emission of an AC cut of a handler passes the gate of the handler's
start state: the AC cuts before it keep `mayVote` (`SA.step_mayVote`), FG cuts keep `𝒜`. -/
theorem emits_mayVote_of_mem_exec (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (e : Event (goldilocksNode sp ro)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : Cut.ac ℓ ∈ (exec proposer dg self st t e).2) :
    ∀ m ∈ ℓ.emits, st.ac.mayVote m.msg.slot = true := by
  have key : ∀ {st₀ st' : NodeState (goldilocksNode sp ro)} {cs},
      CutChain self t st₀ cs st' → st₀.ac.mayVote = st.ac.mayVote → Cut.ac ℓ ∈ cs →
        ∀ m ∈ ℓ.emits, st.ac.mayVote m.msg.slot = true := by
    intro st₀ st' cs hc
    induction hc with
    | nil => exact fun _ h => absurd h List.not_mem_nil
    | @cons st₀ st₁ _ c cs hstep _ ih =>
      intro hp hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        obtain ⟨-, he, -, -⟩ := hstep
        intro m hm'
        rw [← hp]
        exact SA.emits_mayVote ro self st₀.ac ℓ.frame t ℓ.call m (by rw [he]; exact hm')
      · refine ih ?_ hm
        rw [← hp]
        cases c with
        | ac ℓ' =>
          obtain ⟨-, he, -, -⟩ := hstep
          have h₁ := SA.step_mayVote ro self st₀.ac ℓ'.frame t ℓ'.call
          rw [he] at h₁
          exact h₁
        | fg f =>
          cases f with
          | block B acc =>
            cases acc
            · rw [hstep.2]
            · rw [hstep.2.2.1]
          | attestation a => rw [hstep.2.1]
          | attest C r =>
            cases r
            · rw [hstep.2]
            · rw [hstep.2.2]
  exact key (Compose.exec_is_cut_chain (P := sp.toParams) (A := goldilocksNode sp ro)
    proposer dg self st t e) rfl h

end MemberVotes

section MemberVotesEngine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Every duty run keeps `VoteMember`. -/
theorem runDuties_voteMember {p : Nat → Bool} (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (ds : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty)
    (h : VoteMember p (shapeOf S hn nd)) :
    VoteMember p (shapeOf S hn (rho.runDuties v nd ds).1) :=
  runDuties_pres S rho hn (VoteMember p) (fun st o hs => record_voteMember st o hs)
    (fun st s => propose_voteMember st s) (fun st => tick_voteMember st)
    (fun st t => poll_voteMember st t) v nd ds h

/-- **Every engine state is `VoteMember` at the node's installed permission.** The permission
is the init's and every handler keeps it; every queued vote is an own gated emission. -/
theorem stateAt_voteMember (hv : rho.ExecutionValid) (v : V) :
    ∀ i, VoteMember (fun s => decide (rho.ownKey v ∈ rho.sel (S.vote.voteRole s)))
      (stateAt S rho hn v i)
  | 0 => by
    rw [stateAt_zero]
    refine ⟨funext fun s => ?_, fun _ h => absurd h List.not_mem_nil⟩
    change (S.vote.installVote _ _).mayVote s = _
    cases hp : S.vote.participationKind with
    | none =>
      have hr : S.vote.voteRole s = .poll := by simp [VoteBinding.voteRole, hp]
      rw [hr]
      simp only [VoteBinding.installVote, hp]
      exact (decide_eq_true (poll_selected S rho hv v)).symm
    | some k => exact S.vote.installVote_mayVote (by simp [hp]) _ _ s
  | i + 1 => by
    match he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact stateAt_voteMember hv v i
    | some e =>
      by_cases hne : e.node = v
      · cases e with
        | tick v' t =>
          simp only [Model.Event.node] at hne; subst hne
          rw [stateAt_tick S rho hn _ he]
          exact tick_pres S rho hn (VoteMember _) (fun st o hs => record_voteMember st o hs)
            (fun st s => propose_voteMember st s) (fun st => tick_voteMember st)
            (fun st t => poll_voteMember st t) v' _ t
            (by
              have h := stateAt_voteMember hv v' i
              rw [stateAt_eq] at h
              exact ⟨h.1, h.2⟩)
        | deliver v' o t =>
          simp only [Model.Event.node] at hne; subst hne
          rw [stateAt_deliver S rho hn _ he]
          exact deliver_pres S rho hn (VoteMember _) (fun st t => poll_voteMember st t)
            (fun st _ _ hs => record_voteMember st _ hs) v' _ o t
            (process_voteMember _ _ _ (by
              have h := stateAt_voteMember hv v' i
              rwa [stateAt_eq] at h))
        | restart v' t =>
          simp only [Model.Event.node] at hne; subst hne
          rw [stateAt_restart S rho hn _ he]
          exact restore_voteMember _ _ t (self_eq_ownKey S rho hn v' i)
            (stateAt_voteMember hv v' i)
      · rw [state_of_other S rho hn v i e he hne]; exact stateAt_voteMember hv v i

/-- The node's vote permission at every cut of the engine is its installed membership. -/
theorem stateAt_mayVote (hv : rho.ExecutionValid) (v : V) (i : Nat) :
    (stateAt S rho hn v i).node.ac.mayVote =
      fun s => decide (rho.ownKey v ∈ rho.sel (S.vote.voteRole s)) :=
  (stateAt_voteMember S rho hn hv v i).1

/-- Any ordinary vote left by delivery processing is an own vote of a slot whose vote role
selects the receiving node. -/
theorem delivery_outbox_vote_member (hv : rho.ExecutionValid) {v : V}
    (_hv' : v ∉ rho.faultyAt 0) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocksWith S)) E).Object) (m : Vote (Fintype.card V))
    (hm : Body.vote (encodeVote m) ∈
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox) :
    m.val = rho.ownKey v ∧ rho.ownKey v ∈ rho.sel (S.vote.voteRole m.slot) :=
  have h := (process_voteMember _ o _ (stateAt_voteMember S rho hn hv v i)).2 m hm
  ⟨h.1.trans ((process_self _ _ _).trans (self_eq_ownKey S rho hn v i)), of_decide_eq_true h.2⟩

end MemberVotesEngine

end Consensus.Goldilocks.Simulation

end

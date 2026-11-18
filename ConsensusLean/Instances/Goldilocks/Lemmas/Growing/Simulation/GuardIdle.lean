module
public import ConsensusLean.Spec.Model.Guard
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Signing
import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # The slashing guard never fires for Goldilocks

On every valid execution of the compiled Goldilocks family, no event puts a candidate to the
engine's slashing protection that it refuses (`guardIdle`). Only an attestation body signed in the
poll role and carrying nothing can conflict (`protects_of_not_att`). Such a candidate comes only
from the ordinary emission of a scheduled poll, the first candidate of its batch, so the guard
checks it against the `seen` log of the poll's duty prefix, where the node's own FG record admits
it (`engine_poll_att_protected_at`: no two engine signings of an honest node are slashable,
`FG.client_safety`). Every other candidate (proposals, forwarding and vote-forward envelopes,
unsigned gossip) passes against any `seen` log. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

section Release

variable {pub : Model.Public} {Out : Type} {P : Model.Protocol pub Out}

/-- Candidates that the guard passes against every `seen` log are never refused, from any node. -/
private theorem guardRefusals_eq_nil (hash : P.Item → Nat) (k : Model.Key pub)
    {cs : List P.Object} (h : ∀ c ∈ cs, ∀ seen, Model.protects P k seen c = true) :
    ∀ nd, Model.guardRefusals P hash k nd cs = [] := by
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro nd
    simp only [Model.guardRefusals, h c List.mem_cons_self, ↓reduceIte, List.nil_append]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

/-- Releasing `cs ++ cs'` checks `cs`, then `cs'` from the node `cs` leaves. -/
private theorem guardRefusals_append (hash : P.Item → Nat) (k : Model.Key pub)
    (cs cs' : List P.Object) : ∀ nd, Model.guardRefusals P hash k nd (cs ++ cs') =
      Model.guardRefusals P hash k nd cs ++
        Model.guardRefusals P hash k (Model.releaseAll P hash k nd cs).1 cs' := by
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro nd
    have hr : (Model.releaseAll P hash k nd (c :: cs)).1 =
        (Model.releaseAll P hash k (Model.releaseAll P hash k nd [c]).1 cs).1 := by
      rw [show c :: cs = [c] ++ cs from rfl, Model.releaseAll_append]
    simp only [List.cons_append, Model.guardRefusals, ih, hr, List.append_assoc]

/-- At most one candidate, which the guard passes against the starting `seen`, is never refused. -/
private theorem guardRefusals_short (hash : P.Item → Nat) (k : Model.Key pub) {nd : Model.Node P}
    {cs : List P.Object} (hl : cs.length ≤ 1) (h : ∀ c ∈ cs, Model.protects P k nd.seen c = true) :
    Model.guardRefusals P hash k nd cs = [] := by
  match cs, hl with
  | [], _ => rfl
  | [c], _ => simp [Model.guardRefusals, h c List.mem_cons_self]

end Release

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E)

omit [DecidableEq V] in
/-- A candidate whose message is not an attestation body passes the guard against any `seen`. -/
private theorem protects_of_msg (k x : Fin (Fintype.card V))
    (seen : List (Model.protoOf (compiled (goldilocks S)) E).Object) (r)
    (m : Model.Msg (Model.protoOf (compiled (goldilocks S)) E).Item
      (Model.protoOf (compiled (goldilocks S)) E).Body) (cs)
    (h : ∀ w, m ≠ .data (.att w)) :
    Model.protects (Model.protoOf (compiled (goldilocks S)) E) k seen (.mk (.signed x r) m cs) =
      true :=
  protects_of_not_att S k seen _ fun _ w he => h w (Model.Obj.mk.inj he).2.1

omit [DecidableEq V] in
/-- Unsigned gossip is never refused. -/
private theorem gossipRefusals_eq_nil (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (st) (t : Time) :
    Model.guardRefusals (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) st t) = [] :=
  guardRefusals_eq_nil _ _ (fun c hc seen => by
    obtain ⟨mc, -, rfl⟩ := Model.mem_gossipCandidates.mp hc
    exact protects_of_not_att S k seen _ fun _ _ h => by cases h) _

omit [DecidableEq V] in
/-- `signedCandidate` signs a concatenation part by part. -/
private theorem signedCandidate_append (v : V)
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (a b : List (Model.Msg (Model.protoOf (compiled (goldilocks S)) E).Item
      (Model.protoOf (compiled (goldilocks S)) E).Body ×
        List (Model.protoOf (compiled (goldilocks S)) E).Object)) :
    rho.signedCandidate v d (a ++ b) = rho.signedCandidate v d a ++ rho.signedCandidate v d b := by
  unfold Model.Run.signedCandidate
  split <;> simp [List.filterMap_append]

omit [DecidableEq V] in
/-- `signedCandidate` signs at most one candidate per message. -/
private theorem signedCandidate_length_le (v : V)
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (a : List (Model.Msg (Model.protoOf (compiled (goldilocks S)) E).Item
      (Model.protoOf (compiled (goldilocks S)) E).Body ×
        List (Model.protoOf (compiled (goldilocks S)) E).Object)) :
    (rho.signedCandidate v d a).length ≤ a.length := by
  unfold Model.Run.signedCandidate
  split
  · exact List.length_filterMap_le _ _
  · simp

/-- **No duty of an actual event prefix has a refused candidate.** A poll's ordinary emission is
the first candidate of its batch, checked against the prefix's `seen`; an attestation there is an
engine signing, which the guard admits (`engine_poll_att_protected_at`). Every other candidate
of every duty is not an attestation body. -/
private theorem dutyRefusals_eq_nil (hv : rho.ExecutionValid) {v : V} {i p : Nat} {nd}
    (hc : EngineDutyCut S rho v i p nd) {d}
    (hd : (∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some d) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t)[p]? = some d) :
    rho.dutyRefusals v nd d = [] := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  unfold Model.Run.dutyRefusals
  split
  · rename_i hsel
    cases d with
    | poll k =>
      have hact : ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll k)).2 =
          ((poll (nd.st.1 hn) (k : Time)).2.toList.map fun bc => (Model.Msg.data bc.1, bc.2)) ++
            ((((nd.st.1 hn).forwards.map fun p => (Body.forward p.1, p.2)) ++
              ((nd.st.1 hn).voteForwards.map fun p =>
                (Body.voteForward p.1 (encodeVote p.2), [voteObj (binding := S.vote) p.2]))).map
              fun bc => (Model.Msg.data bc.1, bc.2)) := by
        change (((goldilocks S (pubOf E)).pollBatch nd.st.1 (k : Time)).2.map _) = _
        simp only [goldilocks, dite_eq_left hn]
        change ((pollBatch (nd.st.1 hn) (k : Time)).2.map _) = _
        exact (congrArg (List.map _) (List.append_assoc _ _ _)).trans (List.map_append ..)
      dsimp only
      refine (congrArg (Model.guardRefusals _ rho.hash (rho.ownKey v) _)
        ((congrArg (rho.signedCandidate v (.poll k)) hact).trans
          (signedCandidate_append S rho v _ _ _))).trans ?_
      refine (guardRefusals_append _ _ _ _ _).trans ?_
      refine List.append_eq_nil_iff.mpr ⟨guardRefusals_short _ _ ?_ fun c hc' => ?_,
        guardRefusals_eq_nil _ _ (fun c hc' seen => ?_) _⟩
      · refine ((signedCandidate_length_le S rho v _ _).trans_eq (List.length_map ..)).trans ?_
        cases (poll (nd.st.1 hn) (k : Time)).2 <;> simp
      · -- the poll's ordinary emission, checked against the prefix's `seen`
        obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
        obtain ⟨⟨b, cs'⟩, hb, he⟩ := List.mem_map.mp hm
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hp := Option.mem_toList.mp hb
        by_cases hatt : ∃ w, b = .att w ∧ cs' = []
        · obtain ⟨w, rfl, rfl⟩ := hatt
          have hr : (Model.protoOf (compiled (goldilocks S)) E).candidateRole (.poll k)
              (.data (.att w)) = .poll :=
            VoteBinding.candidateRole_poll_nonvote S.vote _ k (.att w) fun _ h => by cases h
          exact (congrArg (fun r => Model.protects _ (rho.ownKey v) nd.seen
            (.mk (.signed (rho.ownKey v) r) (.data (.att w)) [])) hr).trans
            (engine_poll_att_protected_at S rho hn hv hc hd hsel hp)
        · exact protects_of_not_att S _ _ _ fun _ w he => hatt
            ⟨w, Model.Msg.data.inj (Model.Obj.mk.inj he).2.1, (Model.Obj.mk.inj he).2.2⟩
      · -- forwarding and vote-forward envelopes
        obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
        apply protects_of_msg
        intro w hw
        subst hw
        obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
        rcases List.mem_append.mp hx with hx | hx <;> obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx <;>
          exact Body.noConfusion (Model.Msg.data.inj (Prod.mk.inj he).1)
    | propose s hs =>
      apply guardRefusals_eq_nil
      intro c hc' seen
      obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
      apply protects_of_msg
      intro w hw
      subst hw
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).propose nd.st.1 s).2).toList at hm
      obtain ⟨⟨par, info, cs'⟩, -, he⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hm)
      cases (Prod.mk.inj he).1
    | act s k' =>
      apply guardRefusals_eq_nil
      intro c hc' seen
      obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
      exact absurd hm List.not_mem_nil
    | pollPropose t =>
      apply guardRefusals_eq_nil
      intro c hc' seen
      obtain ⟨m, cs, hm, -, -, rfl⟩ := rho.mem_signedCandidate.mp hc'
      change _ ∈ (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList at hm
      simp only [goldilocks, dite_eq_left hn] at hm
      cases hm
  · rfl

omit [DecidableEq V] in
/-- The refusals of a duty list vanish if those of each duty at its actual prefix do. -/
private theorem runDutiesRefusals_eq_nil (v : V)
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    ∀ nd, (∀ p d, ds[p]? = some d → rho.dutyRefusals v (rho.runDuties v nd (ds.take p)).1 d = []) →
      rho.runDutiesRefusals v nd ds = [] := by
  induction ds with
  | nil => intro _ _; rfl
  | cons d ds ih =>
    intro nd h
    simp only [Model.Run.runDutiesRefusals]
    rw [show rho.dutyRefusals v nd d = [] from h 0 d rfl, List.nil_append]
    refine ih _ fun p d' hp => ?_
    have h' := h (p + 1) d' (by simpa using hp)
    simpa only [List.take_succ_cons, rho.runDuties_cons] using h'

/-- **The slashing guard never fires for Goldilocks**: on every valid execution, no event puts a
candidate to the engine's slashing protection that it refuses. The honest node's own FG record
keeps it from signing a slashable pair. -/
theorem guardIdle (hv : rho.ExecutionValid) : rho.GuardIdle := by
  intro i
  unfold Model.Run.guardRefusalsAt
  split
  · rename_i v t he
    unfold Model.Run.tickRefusals
    split
    · rename_i hw
      dsimp only
      rw [runDutiesRefusals_eq_nil S rho v _ _ fun p d hp =>
          dutyRefusals_eq_nil S rho hv
            (.tick he hw (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hp).1))
            (Or.inl ⟨t, he, hw, hp⟩),
        gossipRefusals_eq_nil, List.append_nil]
    · rfl
  · rename_i v o t he
    unfold Model.Run.deliverRefusals
    dsimp only
    rw [runDutiesRefusals_eq_nil S rho v _ _ fun p d hp =>
        dutyRefusals_eq_nil S rho hv
          (.deliver he (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hp).1))
          (Or.inr ⟨t, o, he, hp⟩),
      gossipRefusals_eq_nil, List.append_nil]
  · rfl

end Consensus.Goldilocks.Simulation

end

module
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteMember

public section

/-! # Vote bindings: a proper-subset committee

`committeeOne` is a committee binding whose selection is one key per slot. Its votes are signed in
the slot's committee role and other poll bodies keep the poll role (`committeeOne_voteRole`,
`committeeOne_candidateRole_vote`, `committeeOne_candidateRole_att`); initialization installs the
own committee membership as the vote permission (`committeeOne_init_mayVote`), so a node outside
the slot's committee emits no vote of that slot (`committeeOne_nonmember_silent`), at every cut of
a valid engine run as well (`committeeOne_nonmember_silent_at`), while a member of the slot's
committee releases its pending vote, signed in the committee role, at its poll step
(`committeeOne_member_releases_vote`); every admissible
committee has one key, the committee size, a proper subset of every population of two or more
(`committeeOne_committeeSize`, `committeeOne_selected_proper`).
-/

namespace Consensus.Goldilocks.AsChainShape.Regression
open Blocks Shape
open Consensus.Model (Public)

/-- A committee binding selecting one key per slot (`VoteBinding.committee`, nonempty at every
nonempty population). -/
@[expose] def committeeOne : VoteBinding := committee (fun _ => .sized 1) (fun _ _ => le_rfl)

/-- Votes are authenticated in the slot's committee role, not in the poll role. -/
theorem committeeOne_voteRole (s : Slot) : committeeOne.voteRole s = .duty s .vote := rfl

/-- A poll emission of a vote is signed in the vote's committee role. -/
theorem committeeOne_candidateRole_vote {n : Nat} (t : Nat) (v : SA.Vote n) :
    (committeeOne.candidateRole n (.poll t) (.data (.vote (encodeVote v)))).getD .poll =
      .duty v.slot .vote :=
  committeeOne.candidateRole_poll_vote t v

/-- A poll emission of an attestation keeps the poll role. -/
theorem committeeOne_candidateRole_att (n t : Nat) (a : WireAtt) :
    (committeeOne.candidateRole n (.poll t) (.data (.att a))).getD .poll = .poll :=
  committeeOne.candidateRole_poll_nonvote n t _ fun _ h => by cases h

/-- Initialization installs the own membership in the slot's committee as the vote permission. -/
theorem committeeOne_init_mayVote (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) (key : Fin pub.n)
    (p : ShapeRole VoteKind → Bool) (s : Slot) :
    (((goldilocks { S with vote := committeeOne } pub).init key p hn).node.ac).mayVote s =
      p (.duty s .vote) :=
  committeeOne.installVote_mayVote (Option.some_ne_none _) p _ s

/-- A node outside the slot-`s` committee emits no slot-`s` vote from its initial AC state, at
any call, frame and time. -/
theorem committeeOne_nonmember_silent (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (key : Fin pub.n) (p : ShapeRole VoteKind → Bool) (s : Slot)
    (hp : p (.duty s .vote) = false) (Φ : SA.Frm pub.n (List (FG.Att pub.n))) (t : Time)
    (c : (SA.goldilocksSA (({ S with vote := committeeOne } : Setup).params pub hn)
      (List (FG.Att pub.n))
      (S.ro pub.n)).Call) :
    ∀ e ∈ ((SA.goldilocksSA (({ S with vote := committeeOne } : Setup).params pub hn)
      (List (FG.Att pub.n))
      (S.ro pub.n)).step key
        (((goldilocks { S with vote := committeeOne } pub).init key p hn).node.ac) Φ t c).2,
      e.msg.slot ≠ s := by
  intro e he hs
  have h := SA.emits_mayVote (S.ro pub.n) key _ Φ t c e he
  rw [hs, committeeOne_init_mayVote S pub hn key p s, hp] at h
  exact Bool.false_ne_true h

/-- On a valid engine run, a node outside the slot-`s` committee emits no slot-`s` vote from its
AC state at any cut of the run, at any call, frame and time: every handler keeps the installed
permission (`Simulation.stateAt_mayVote`). -/
theorem committeeOne_nonmember_silent_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks { S with vote := committeeOne })) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (v : V) (i : Nat) (s : Slot)
    (hs : rho.ownKey v ∉ rho.sel (.duty s .vote))
    (key : Fin (Fintype.card V)) (Φ : SA.Frm (Fintype.card V) (List (FG.Att (Fintype.card V))))
    (t : Time)
    (c : (SA.goldilocksSA (Setup.params { S with vote := committeeOne } (Model.pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)).Call) :
    ∀ e ∈ ((SA.goldilocksSA (Setup.params { S with vote := committeeOne } (Model.pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)).step key
        (Simulation.stateAt { S with vote := committeeOne } rho hn v i).node.ac Φ t c).2,
      e.msg.slot ≠ s := by
  intro e he hes
  have h := SA.emits_mayVote (S.ro _) key _ Φ t c e he
  rw [hes, Simulation.stateAt_mayVote { S with vote := committeeOne } rho hn hv v i] at h
  exact hs (of_decide_eq_true h)

/-- The committee size, the vote threshold denominator, is `1` at every nonempty population. -/
theorem committeeOne_committeeSize (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) :
    (({ S with vote := committeeOne } : Setup).params pub hn).committeeSize = 1 := by
  change min 1 pub.n = 1
  omega

/-- Every admissible slot committee has the committee size, one key: a proper subset of every
population of two or more. -/
theorem committeeOne_selected_proper (S : Setup) (pub : Public) (hn : 2 ≤ pub.n) (k : VoteKind)
    (T : Finset (Fin pub.n))
    (hT : ((goldilocks { S with vote := committeeOne } pub).skel.kindSel k).Admits T) :
    T.card = (({ S with vote := committeeOne } : Setup).params pub (by omega)).committeeSize ∧
      T ⊂ Finset.univ := by
  change T.card = min 1 pub.n at hT
  refine ⟨hT, Finset.ssubset_univ_iff.2 fun h => ?_⟩
  rw [h, Finset.card_univ, Fintype.card_fin] at hT
  omega

/-- A member of the slot's committee releases its pending vote along the committee-role release
path: when the poll step's outbox starts with the vote body of `m` and the node's key is selected
for the slot-`m.slot` vote duty, the poll step of a valid engine run releases that vote signed in
the committee role `.duty m.slot .vote` (`Simulation.dutyStep_poll_rel`). -/
theorem committeeOne_member_releases_vote {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks { S with vote := committeeOne })) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks { S with vote := committeeOne })) E))
    (t : Nat)
    (m : SA.Vote (Fintype.card V))
    (hb : (Simulation.pollPre
      (Simulation.shapeOf { S with vote := committeeOne } hn nd)).outbox.head? =
      some (.vote (encodeVote m)))
    (hs : rho.ownKey v ∈ rho.sel (.duty m.slot .vote)) :
    (Model.Obj.mk (.signed (rho.ownKey v) (.duty m.slot .vote)) (.data (.vote (encodeVote m))) [] :
      (Model.protoOf (compiled (goldilocks { S with vote := committeeOne })) E).Object) ∈
      (rho.dutyStep v nd (.poll t)).2 := by
  have h := Simulation.dutyStep_poll_rel { S with vote := committeeOne } rho hn v nd t
    (Simulation.poll_selected { S with vote := committeeOne } rho hv v) hb
    (by rw [Simulation.pollRole_vote]; exact hs)
    (Simulation.protects_pollObj_vote { S with vote := committeeOne } rho v _ _ _)
  rwa [Simulation.pollObj, Simulation.pollRole_vote, committeeOne_voteRole] at h

end Consensus.Goldilocks.AsChainShape.Regression

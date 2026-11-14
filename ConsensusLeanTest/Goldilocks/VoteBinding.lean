module
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteMember

public section

/-! # Vote bindings: the population binding and a proper-subset committee

`legacySkeleton`, `legacyShape` and `legacyGoldilocks` are the population shape written without a
vote binding: the population instance's bodies, with only the permission argument the model
interface now passes. No production module imports them. `stock_legacy`: the population binding
equals that shape.

`committeeOne` is a committee binding whose selection is one key per slot. Its votes are signed in
the slot's committee role and other poll bodies keep the poll role (`committeeOne_voteRole`,
`committeeOne_candidateRole_vote`, `committeeOne_candidateRole_att`); initialization installs the
own committee membership as the vote permission (`committeeOne_init_mayVote`), so a node outside
the slot's committee emits no vote of that slot (`committeeOne_nonmember_silent`), at every cut of
a valid engine run as well (`committeeOne_nonmember_silent_at`); every admissible
committee has one key, the committee size, a proper subset of every population of two or more
(`committeeOne_committeeSize`, `committeeOne_selected_proper`).
-/

namespace Consensus.Goldilocks.AsChainShape.Regression
open Blocks Shape
open Consensus.Model (Public)
open SA (SAParams ReplayOrder)

def legacySkeleton (pub : Public) : Skeleton pub.n where
  grid := ⟨4 * pub.ΔAC, mul_pos (by decide) pub.ΔAC_pos⟩
  proposerSel := fun _ => .sized 1
  pollSel := .fixed Finset.univ
  Kind := Empty
  decKind := inferInstance
  kinds := []
  phase := fun k => k.elim
  kindSel := fun k => k.elim
  order := [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliverOrder := [.poll]

noncomputable def legacyShape (sp : SAParams)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) : ChainShape sp.pub Out Info where
  skel := { legacySkeleton sp.pub with grid := ⟨4 * sp.Δ, mul_pos (by decide) sp.toParams.hΔ⟩ }
  State := State sp ro (binding := stock)
  Body := Body
  Durable := State sp ro (binding := stock)
  decBody := inferInstance
  init k _ := ⟨k, Node.init (goldilocksNode sp ro), 0, [], [], false, fun _ => none, [], []⟩
  clock st t := { st with now := t }
  propose := propose
  act := fun _ _ k => k.elim
  pollPropose st _ := (nodeTick st, none)
  poll := poll
  pollBatch := pollBatch
  gossip st _ :=
    match st.relayBuf with
    | [] => []
    | cs => [(.data .relay, cs)]
  process := process
  dependencies := dependencies sp.n (binding := stock)
  recordOwn := recordOwn
  durable := id
  restore := restore
  out g st := outOf st.node st.now g
  conflicts := conflicts (binding := stock)
  isFGAtt := isFGAtt (binding := stock)

noncomputable def legacyGoldilocks (S : Setup) : ChainShapeFamily schema Info := fun pub =>
  let G := fun hn : 1 ≤ pub.n => legacyShape (S.params pub hn) (S.ro _)
  { skel := legacySkeleton pub
    State := PubState S pub (binding := stock)
    Body := Body
    Durable := PubState S pub (binding := stock)
    decBody := inferInstance
    init := fun k p hn => (G hn).init k p
    clock := fun st t hn => (G hn).clock (st hn) t
    propose := fun st s =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).propose (st hn) s).1, ((G hn).propose (st hn) s).2)
      else (st, none)
    act := fun _ _ k => k.elim
    pollPropose := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollPropose (st hn) t).1, ((G hn).pollPropose (st hn) t).2)
      else (st, none)
    poll := fun st t =>
      if hn : 1 ≤ pub.n then (fun _ => ((G hn).poll (st hn) t).1, ((G hn).poll (st hn) t).2)
      else (st, none)
    pollBatch := fun st t =>
      if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollBatch (st hn) t).1, ((G hn).pollBatch (st hn) t).2)
      else (st, [])
    gossip := fun st t => if hn : 1 ≤ pub.n then (G hn).gossip (st hn) t else []
    process := fun st o hs hn => (G hn).process (st hn) o hs
    dependencies := dependencies pub.n (binding := stock)
    recordOwn := fun st o hs hn => (G hn).recordOwn (st hn) o hs
    durable := id
    restore := fun k d t hn => (G hn).restore k (d hn) t
    out := fun g st => if hn : 1 ≤ pub.n then (G hn).out g (st hn) else []
    conflicts := conflicts (binding := stock)
    isFGAtt := isFGAtt (binding := stock) }

/-- The population binding equals the shape written without a vote binding. -/
theorem stock_legacy (S : Setup) : goldilocksWith ⟨S, stock⟩ = legacyGoldilocks S := by
  funext pub
  let X := goldilocksWith ⟨S, stock⟩ pub
  have hphase : (fun _ => 0 : X.skel.Kind → Nat) = fun k => Empty.elim k :=
    funext fun k => nomatch k
  have hact : (fun st _ _ => (st, none) : X.State → Slot → X.skel.Kind →
      X.State × Option (X.Body × List (ShapeObj pub.n X.skel.Kind Info X.Body))) =
      fun _ _ k => Empty.elim k :=
    funext fun _ => funext fun _ => funext fun k => nomatch k
  calc
    X = { X with
      skel := { X.skel with phase := fun _ => 0 }
      act := fun st _ _ => (st, none) } := rfl
    _ = { X with
      skel := { X.skel with phase := fun k => Empty.elim k }
      act := fun _ _ k => Empty.elim k } :=
      congrArg₂ (fun p a => { X with skel := { X.skel with phase := p }, act := a }) hphase hact
    _ = legacyGoldilocks S pub := by
      dsimp only [X, goldilocksWith, legacyGoldilocks]
      congr 1
      funext st t
      by_cases hn : 1 ≤ pub.n
      · simp only [hn, ↓reduceDIte, goldilocksShape, legacyShape]
        cases (st hn).relayBuf <;> rfl
      · simp only [hn, ↓reduceDIte]
        rfl

/-! ## A proper-subset committee binding -/

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
    (((goldilocksWith ⟨S, committeeOne⟩ pub).init key p hn).node.ac).mayVote s =
      p (.duty s .vote) :=
  committeeOne.installVote_mayVote (Option.some_ne_none _) p _ s

/-- A node outside the slot-`s` committee emits no slot-`s` vote from its initial AC state, at
any call, frame and time. -/
theorem committeeOne_nonmember_silent (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (key : Fin pub.n) (p : ShapeRole VoteKind → Bool) (s : Slot)
    (hp : p (.duty s .vote) = false) (Φ : SA.Frm pub.n (List (FG.Att pub.n))) (t : Time)
    (c : (SA.goldilocksSA (S.params pub hn committeeOne) (List (FG.Att pub.n))
      (S.ro pub.n)).Call) :
    ∀ e ∈ ((SA.goldilocksSA (S.params pub hn committeeOne) (List (FG.Att pub.n))
      (S.ro pub.n)).step key
        (((goldilocksWith ⟨S, committeeOne⟩ pub).init key p hn).node.ac) Φ t c).2,
      e.msg.slot ≠ s := by
  intro e he hs
  have h := SA.emits_mayVote (S.ro pub.n) key _ Φ t c e he
  rw [hs, committeeOne_init_mayVote S pub hn key p s, hp] at h
  exact Bool.false_ne_true h

/-- On a valid engine run, a node outside the slot-`s` committee emits no slot-`s` vote from its
AC state at any cut of the run, at any call, frame and time: every handler keeps the installed
permission (`Simulation.stateAt_mayVote`). -/
theorem committeeOne_nonmember_silent_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocksWith ⟨S, committeeOne⟩)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (v : V) (i : Nat) (s : Slot)
    (hs : rho.ownKey v ∉ rho.sel (.duty s .vote))
    (key : Fin (Fintype.card V)) (Φ : SA.Frm (Fintype.card V) (List (FG.Att (Fintype.card V))))
    (t : Time)
    (c : (SA.goldilocksSA (BoundSetup.params ⟨S, committeeOne⟩ (Model.pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)).Call) :
    ∀ e ∈ ((SA.goldilocksSA (BoundSetup.params ⟨S, committeeOne⟩ (Model.pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)).step key
        (Simulation.stateAt ⟨S, committeeOne⟩ rho hn v i).node.ac Φ t c).2,
      e.msg.slot ≠ s := by
  intro e he hes
  have h := SA.emits_mayVote (S.ro _) key _ Φ t c e he
  rw [hes, Simulation.stateAt_mayVote ⟨S, committeeOne⟩ rho hn hv v i] at h
  exact hs (of_decide_eq_true h)

/-- The committee size, the vote threshold denominator, is `1` at every nonempty population. -/
theorem committeeOne_committeeSize (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) :
    (S.params pub hn committeeOne).committeeSize = 1 := by
  change min 1 pub.n = 1
  omega

/-- Every admissible slot committee has the committee size, one key: a proper subset of every
population of two or more. -/
theorem committeeOne_selected_proper (S : Setup) (pub : Public) (hn : 2 ≤ pub.n) (k : VoteKind)
    (T : Finset (Fin pub.n))
    (hT : ((goldilocksWith ⟨S, committeeOne⟩ pub).skel.kindSel k).Admits T) :
    T.card = (S.params pub (by omega) committeeOne).committeeSize ∧ T ⊂ Finset.univ := by
  change T.card = min 1 pub.n at hT
  refine ⟨hT, Finset.ssubset_univ_iff.2 fun h => ?_⟩
  rw [h, Finset.card_univ, Fintype.card_fin] at hT
  omega

end Consensus.Goldilocks.AsChainShape.Regression

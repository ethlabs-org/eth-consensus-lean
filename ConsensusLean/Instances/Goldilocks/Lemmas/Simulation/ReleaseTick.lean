module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Release
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteMember
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsInstance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldFlush
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: what the engine releases at a tick

The engine's tick of an honest node against the node's `on_tick`, release by release
(`tick_public_analysis`): at a public time it releases the queued body, the canonical objects of
the blocks of the tick's cuts, and the votes and the attestation the tick's cuts emit and sign
(`Q`, at most two bodies, drained by the two trailing polls), then unsigned gossip. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams Vote Payload ACState)

variable {binding : VoteBinding}

/-! ## A tick, duty by duty -/

section Unroll

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- What a poll step releases for the head `ob` of the outbox it pops from: the poll object of
the head, when its poll role selects the node. -/
noncomputable def relHead (v : V) (ob : Option Body) :
    List (Model.protoOf (compiled (goldilocks S)) E).Object :=
  ob.elim [] fun b =>
    if rho.ownKey v ∈ rho.sel (pollRole S.vote (pubOf E).n b) then
      [pollObj S rho v b] else []

omit [DecidableEq V] in
/-- `relHead` releases nothing for an empty outbox, and for a head `b` its poll object exactly
when its poll role selects the node. -/
theorem relHead_eq (v : V) (ob : Option Body) :
    relHead S rho v ob = ob.elim [] fun b =>
      if rho.ownKey v ∈ rho.sel (pollRole S.vote (pubOf E).n b) then
        [pollObj S rho v b] else [] := by
  rfl

/-- What the first trailing poll of a tick at `t` from the shape state `st` releases after its
ordinary body and forwards: every held attestation, oldest first, when the release schedule
allows release at `t`. -/
noncomputable def relFlush (v : V) (st : State (S.params (pubOf E) hn) S.vote)
    (t : Time) : List (Model.protoOf (compiled (goldilocks S)) E).Object :=
  (if S.release (pubOf E) st.self t then st.held else []).map (heldObj S rho v)

omit [DecidableEq V] in
/-- `relFlush` releases every held attestation when the schedule allows release at `t`. -/
theorem relFlush_eq (v : V) (st : State (S.params (pubOf E) hn) S.vote) (t : Time) :
    relFlush S rho hn v st t =
      (if S.release (pubOf E) st.self t then st.held else []).map (heldObj S rho v) := by
  rfl

omit [DecidableEq V] in
/-- Releasing the ordinary head alone gives `relHead`, from any runtime state. -/
private theorem release_head (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ob : Option Body) :
    (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v) nd
      (pollOrdinary S rho v (ob.map fun b => (b, [])))).2 = relHead S rho v ob := by
  cases ob with
  | none =>
    rw [pollOrdinary_eq]
    rfl
  | some b =>
    rw [Option.map_some]
    by_cases hk : rho.ownKey v ∈ rho.sel (pollRole S.vote (pubOf E).n b)
    · rw [pollOrdinary_some_pos S rho hk]
      have hr : Model.releasable nd.seen (pollObj S rho v b) = true := by
        simp [Model.releasable, Model.Obj.carried]
      have hd := pollObj_ready S rho v (Model.closure nd.seen) b
      simp only [Model.releaseAll, hr, hd, Bool.true_and, relHead, Option.elim_some, hk]
      rfl
    · rw [pollOrdinary_some_neg S rho hk]
      simp [Model.releaseAll, relHead, hk]

omit [DecidableEq V] in
/-- A poll step of a node selected in the poll role releases `relHead` of the head of
`pollPre`'s outbox. -/
theorem dutyStep_poll_eq (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hempty : (shapeOf S hn nd).forwards = [])
    (hvote : (shapeOf S hn nd).voteForwards = [])
    (hfl : pollFlush (shapeOf S hn nd) (S.release (pubOf E)) = []) :
    (rho.dutyStep v nd (.poll k)).2 =
      relHead S rho v (pollPre (shapeOf S hn nd) (S.release (pubOf E))).outbox.head? := by
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll k) = .poll from rfl,
      hsel, ↓reduceIte]
  rw [signedCandidate_poll S rho hn v nd k hsel, hempty, hvote, hfl]
  simp only [List.map_nil, List.append_nil]
  exact release_head S rho v _ _

omit [DecidableEq V] in
/-- A poll step with no forwards pending releases `relHead` of the head of `pollPre`'s outbox,
then every held attestation it flushes. -/
private theorem dutyStep_poll_first (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hempty : (shapeOf S hn nd).forwards = [])
    (hvote : (shapeOf S hn nd).voteForwards = []) :
    (rho.dutyStep v nd (.poll k)).2 =
      relHead S rho v (pollPre (shapeOf S hn nd) (S.release (pubOf E))).outbox.head? ++
        (pollFlush (shapeOf S hn nd) (S.release (pubOf E))).map (heldObj S rho v) := by
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll k) = .poll from rfl,
      hsel, ↓reduceIte]
  rw [signedCandidate_poll S rho hn v nd k hsel, hempty, hvote]
  simp only [List.map_nil, List.append_nil]
  rw [Model.releaseAll_append, release_head]
  exact congrArg (_ ++ ·) (releaseAll_heldObj S rho v _ _ _)

omit [DecidableEq V] in
/-- Exact poll release decomposition at the actual candidate prefix. The suffix is run on
the state and holdings left by the ordinary head, not the pre-poll holdings. -/
private theorem dutyStep_poll_batch (v : V) (nd : Model.Node (Model.protoOf (compiled
    (goldilocks S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    let P := (Model.protoOf (compiled (goldilocks S)) E)
    let start : Model.Node P := ⟨(P.act nd.st (.poll k)).1, nd.seen⟩
    let ordinary := pollOrdinary S rho v
      ((pollPre (shapeOf S hn nd) (S.release (pubOf E))).outbox.head?.map fun b => (b, []))
    let headRelease := Model.releaseAll P rho.hash (rho.ownKey v) start ordinary
    let forwards : List P.Object := (shapeOf S hn nd).forwards.map
      (fun p => (Model.Obj.mk (.signed (rho.ownKey v) .poll) (.data (.forward p.1)) p.2 :
        P.Object)) ++
      (shapeOf S hn nd).voteForwards.map (fun p =>
        (Model.Obj.mk (.signed (rho.ownKey v) .poll)
          (.data (.voteForward p.1 (encodeVote p.2.1))) [p.2.2] : P.Object)) ++
      (pollFlush (shapeOf S hn nd) (S.release (pubOf E))).map (heldObj S rho v)
    (rho.dutyStep v nd (.poll k)).2 = headRelease.2 ++
      (Model.releaseAll P rho.hash (rho.ownKey v) headRelease.1 forwards).2 := by
  dsimp only
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll k) = .poll from rfl,
      hsel, ↓reduceIte]
  rw [signedCandidate_poll S rho hn v nd k hsel]
  simp only [List.append_assoc]
  exact congrArg Prod.snd (Model.releaseAll_append _ _ _ _ _)

omit [DecidableEq V] in
/-- An awake tick at `t ≥ 0`, duty by duty, when no slot proposal is due. -/
theorem tick_unroll_nil (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true)
    (hnil : (skeleton (pubOf E) S.vote).proposeAt t = []) :
    ∃ N1 N3 N5 N6 : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
      N1 = (rho.dutyStep v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).1 ∧
      N3 = (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 ∧
      N5 = (rho.dutyStep v N3 (.poll t.toNat)).1 ∧
      N6 = (rho.dutyStep v N5 (.poll t.toNat)).1 ∧
      (rho.tick nd v t).2 =
        (rho.dutyStep v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).2 ++
        (rho.dutyStep v N1 (.poll t.toNat)).2 ++
        (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).2 ++
        (rho.dutyStep v N3 (.poll t.toNat)).2 ++ (rho.dutyStep v N5 (.poll t.toNat)).2 ++
        (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v) N6
          (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) N6.st t)).2 := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_⟩
  rw [rho.tick_of_awake nd v t hw]
  dsimp only
  rw [duties_eq S t ht]
  unfold dutiesInit
  rw [hnil]
  rfl

omit [DecidableEq V] in
/-- An awake tick at the start of slot `s > 0`, duty by duty. -/
theorem tick_unroll_propose (v : V) (nd : Model.Node (Model.protoOf (compiled
    (goldilocks S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs]) :
    ∃ N1 N3 N4 N5 N6 : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
      N1 = (rho.dutyStep v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).1 ∧
      N3 = (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 ∧
      N4 = (rho.dutyStep v N3 (.propose s hs)).1 ∧
      N5 = (rho.dutyStep v N4 (.poll t.toNat)).1 ∧
      N6 = (rho.dutyStep v N5 (.poll t.toNat)).1 ∧
      (rho.tick nd v t).2 =
        (rho.dutyStep v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩ (.poll t.toNat)).2 ++
        (rho.dutyStep v N1 (.poll t.toNat)).2 ++
        (rho.dutyStep v (rho.dutyStep v N1 (.poll t.toNat)).1 (.pollPropose t.toNat)).2 ++
        (rho.dutyStep v N3 (.propose s hs)).2 ++
        (rho.dutyStep v N4 (.poll t.toNat)).2 ++ (rho.dutyStep v N5 (.poll t.toNat)).2 ++
        (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v) N6
          (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) N6.st t)).2 := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [rho.tick_of_awake nd v t hw]
  dsimp only
  rw [duties_eq S t ht]
  unfold dutiesInit
  rw [hone]
  rfl

end Unroll

/-! ## The releases of a public tick -/

section TickPublic

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- The tick's first three duties from a node with no FG update due and at most one body queued:
the clock clears the tick flag, so the first poll releases only the queued body and the second
and the node's tick nothing; after them nothing is queued, the node state, the own index and the
held queue are the node's, the clock is the tick's, and the node's tick sets the tick flag. -/
theorem leading_polls (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) (hf : (shapeOf S hn nd).fgDue = false)
    (hb : (shapeOf S hn nd).outbox.length ≤ 1)
    (hempty : (shapeOf S hn nd).forwards = [])
    (hvote : (shapeOf S hn nd).voteForwards = []) :
    let N0 : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t (Model.mempool rho.inbox v t),
        nd.seen⟩
    let N1 := (rho.dutyStep v N0 (.poll t.toNat)).1
    let N2 := (rho.dutyStep v N1 (.poll t.toNat)).1
    (rho.dutyStep v N0 (.poll t.toNat)).2 = relHead S rho v (shapeOf S hn nd).outbox.head? ∧
      (rho.dutyStep v N1 (.poll t.toNat)).2 = [] ∧
      (rho.dutyStep v N2 (.pollPropose t.toNat)).2 = [] ∧
      (rho.dutyStep v N2 (.pollPropose t.toNat)).1.seen =
        nd.seen ++ relHead S rho v (shapeOf S hn nd).outbox.head? ∧
      shapeOf S hn (rho.dutyStep v N2 (.pollPropose t.toNat)).1 =
        { nodeTick (shapeOf S hn N2) (S.sign (pubOf E)) with ticked := true } ∧
      (shapeOf S hn N2).outbox = [] ∧ (shapeOf S hn N2).node = (shapeOf S hn nd).node ∧
      (shapeOf S hn N2).self = (shapeOf S hn nd).self ∧ (shapeOf S hn N2).now = t ∧
      (shapeOf S hn N2).fgDue = false ∧ (shapeOf S hn N2).held = (shapeOf S hn nd).held ∧
      (shapeOf S hn N2).forwards = [] ∧ (shapeOf S hn N2).voteForwards = [] := by
  intro N0 N1 N2
  have hS0 : shapeOf S hn N0 = { shapeOf S hn nd with now := t, ticked := false } := rfl
  have hk0 : (shapeOf S hn N0).ticked = false := by rw [hS0]
  have hpre0 : pollPre (shapeOf S hn N0) (S.release (pubOf E)) = shapeOf S hn N0 := by
    rw [pollPre_eq]; rw [hS0]; simp [hf]
  have hS1 : shapeOf S hn N1 = (pollBatch (shapeOf S hn N0) t.toNat (S.release (pubOf E))).1 :=
    dutyStep_poll S rho hn v N0 _ hsel
  have hk1 : (shapeOf S hn N1).ticked = false := by rw [hS1, pollBatch_ticked, hk0]
  have hpre1 : pollPre (shapeOf S hn N1) (S.release (pubOf E)) = shapeOf S hn N1 := by
    rw [pollPre_eq]; rw [hS1, pollBatch_fgDue]; rfl
  have hout1 : (shapeOf S hn N1).outbox = [] := by
    rw [hS1, pollBatch_outbox, hpre0, hS0]
    change (shapeOf S hn nd).outbox.tail = []
    match hq : (shapeOf S hn nd).outbox with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rw [hq] at hb; simp at hb
  have hS2 : shapeOf S hn N2 = (pollBatch (shapeOf S hn N1) t.toNat (S.release (pubOf E))).1 :=
    dutyStep_poll S rho hn v N1 _ hsel
  have hR1 := dutyStep_poll_eq S rho hn v N0 t.toNat hsel hempty hvote
    (pollFlush_of_unticked _ hk0)
  rw [hpre0, hS0] at hR1
  have hR2 := dutyStep_poll_eq S rho hn v N1 t.toNat hsel
    (by rw [hS1]; exact pollBatch_forwards _ _) (by rw [hS1]; exact pollBatch_voteForwards _ _)
    (pollFlush_of_unticked _ hk1)
  rw [hpre1, hout1] at hR2
  have hR3 := dutyStep_pollPropose_snd S rho hn v N2 t.toNat
  refine ⟨hR1, hR2, hR3, ?_, dutyStep_pollPropose S rho hn v N2 _ hsel, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have e3 := dutyStep_seen S rho v N2 (.pollPropose t.toNat)
    have e2 := dutyStep_seen S rho v N1 (.poll t.toNat)
    have e1 := dutyStep_seen S rho v N0 (.poll t.toNat)
    rw [hR3] at e3
    rw [hR2] at e2
    rw [hR1] at e1
    rw [e3, e2, e1]
    simp only [List.append_nil, relHead, List.head?_nil, Option.elim_none]
    rfl
  · rw [hS2, pollBatch_outbox, hpre1, hout1]; rfl
  · rw [hS2, pollBatch_node_of_fgDue _ _ (by rw [hS1]; exact pollBatch_fgDue _ _)
      (pollFlush_of_unticked _ hk1), hS1,
      pollBatch_node_of_fgDue _ _ (by rw [hS0]; exact hf) (pollFlush_of_unticked _ hk0), hS0]
  · rw [hS2, pollBatch_self, hS1, pollBatch_self, hS0]
  · rw [hS2, pollBatch_now, hS1, pollBatch_now, hS0]
  · rw [hS2]; exact pollBatch_fgDue _ _
  · rw [hS2, pollBatch_held, hS1, pollBatch_held, hS0]
    simp [hf, pollBatch_fgDue, pollBatch_ticked]
  · rw [hS2]; exact pollBatch_forwards _ _
  · rw [hS2]; exact pollBatch_voteForwards _ _

omit [DecidableEq V] in
/-- The slot proposal keeps the vote authentication. -/
theorem propose_voteIO (st : State (S.params (pubOf E) hn) S.vote) s :
    (propose st s).1.voteIO = st.voteIO := by
  rw [propose_eq]; dsimp only; split <;> rfl

omit [DecidableEq V] in
/-- The node's tick keeps the vote authentication. -/
theorem nodeTick_voteIO (st : State (S.params (pubOf E) hn) S.vote) :
    (nodeTick st (S.sign (pubOf E))).voteIO = st.voteIO := by
  rw [nodeTick_eq (sign := _)]; split <;> rfl

omit [DecidableEq V] in
/-- A delivery keeps the vote authentication: the generic `process_io` at Goldilocks' laws. -/
theorem process_voteIO (st : State (S.params (pubOf E) hn) S.vote) o hs :
    (process st o hs).voteIO = st.voteIO :=
  traceEncoding_induction S hn
    (fun e _ io => (∀ st o hs, io ((e.ops hn).process st o hs) = io st) →
      ∀ (st : State (S.params (pubOf E) hn) S.vote) o hs,
        (process st o hs).voteIO = st.voteIO)
    (fun _ h => h)
    (NodeAsChainShape.CanonicalTrace.Encoding.OpLaws.process_io (traceEncoding_ioLaws S hn))
    st o hs

omit [DecidableEq V] in
/-- A duty keeps the vote authentication: the generic `duty_io` at Goldilocks' laws. -/
private theorem dutyStep_voteIO (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    (shapeOf S hn (rho.dutyStep v nd d).1).voteIO = (shapeOf S hn nd).voteIO :=
  traceEncoding_induction S hn
    (fun e _ io => (∀ v nd d, io (NodeAsChainShape.CanonicalTrace.envelope e
        (rho.dutyStep v nd (NodeAsChainShape.CanonicalTrace.engineDuty e d)).1) =
          io (NodeAsChainShape.CanonicalTrace.envelope e nd)) →
      ∀ v nd d, (shapeOf S hn (rho.dutyStep v nd d).1).voteIO = (shapeOf S hn nd).voteIO)
    (fun _ h v nd d => by
      have hd := h v nd d
      rw (config := { transparency := .default }) [NodeAsChainShape.CanonicalTrace.engineDuty_eq,
        NodeAsChainShape.CanonicalTrace.envelope_eq,
        NodeAsChainShape.CanonicalTrace.envelope_eq] at hd
      exact hd)
    (NodeAsChainShape.CanonicalTrace.Encoding.OpLaws.duty_io (traceEncoding_opLaws S hn)
      (traceEncoding_ioLaws S hn) rho)
    v nd d

/-- **Every engine state holds the node's own vote authentication**: the generic `cut_io` at
Goldilocks' laws (`init` installs `rho.voteIO v` and every handler keeps it). -/
theorem stateAt_voteIO (v : V) (i : Nat) : (stateAt S rho hn v i).voteIO = rho.voteIO v :=
  stateAt_voteIO_of_trace S rho hn (NodeAsChainShape.CanonicalTrace.Encoding.OpLaws.cut_io
    (traceEncoding_opLaws S hn) (traceEncoding_ioLaws S hn) rho) v i

omit [DecidableEq V] in
/-- The node's tick at a public time from a state with nothing queued: the AC's tick, its
emissions queued, the FG update due. -/
theorem nodeTick_public (st : State (S.params (pubOf E) hn) S.vote)
    (hp : (S.params (pubOf E) hn).toParams.IsPublic st.now) (h0 : st.outbox = []) :
    (nodeTick st (S.sign (pubOf E))).node = (Node.acCall st.self st.node st.now .tick).1 ∧
      (nodeTick st (S.sign (pubOf E))).outbox =
        emitted st.voteIO [(Node.acCall st.self st.node st.now .tick).2] ∧
      (nodeTick st (S.sign (pubOf E))).fgDue = S.sign (pubOf E) st.self st.now ∧
      (nodeTick st (S.sign (pubOf E))).self = st.self ∧
      (nodeTick st (S.sign (pubOf E))).now = st.now := by
  rw [nodeTick_eq (sign := _)]
  rw [ite_eq_left hp]
  simp [apply, h0]

omit [DecidableEq V] in
/-- The tick's two trailing polls, after the tick step (the tick flag set): the first releases
the head of the outbox after the FG update when it is due (`pollPre`), the pending forwards, then
every held attestation it flushes; the second releases the second body and flushes nothing. -/
private theorem trailing_polls (v : V) (N4 : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (k : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hk4 : (shapeOf S hn N4).ticked = true) :
    let N5 := (rho.dutyStep v N4 (.poll k)).1
    ∃ F : List (Model.protoOf (compiled (goldilocks S)) E).Object,
    (rho.dutyStep v N4 (.poll k)).2 =
        relHead S rho v (pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.head? ++ F ++
          (pollFlush (shapeOf S hn N4) (S.release (pubOf E))).map (heldObj S rho v) ∧
      N5.seen = N4.seen ++
        (relHead S rho v (pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.head? ++ F ++
          (pollFlush (shapeOf S hn N4) (S.release (pubOf E))).map (heldObj S rho v)) ∧
      (rho.dutyStep v N5 (.poll k)).2 =
        relHead S rho v (pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.tail.head? ∧
      (shapeOf S hn (rho.dutyStep v N5 (.poll k)).1).outbox =
        (pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.tail.tail ∧
      (∀ o ∈ F, (∃ τ cs, o = .mk (.signed (rho.ownKey v) .poll) (.data (.forward τ)) cs) ∨
        ∃ τ, ∃ m : AC.Vote (Fintype.card V), ∃ w, o = .mk (.signed (rho.ownKey v) .poll)
          (.data (.voteForward τ (encodeVote m))) [w]) := by
  intro N5
  have hS5 : shapeOf S hn N5 = (pollBatch (shapeOf S hn N4) k (S.release (pubOf E))).1 :=
    dutyStep_poll S rho hn v N4 _ hsel
  have hpre5 : pollPre (shapeOf S hn N5) (S.release (pubOf E)) = shapeOf S hn N5 := by
    rw [pollPre_eq]; rw [hS5, pollBatch_fgDue]; rfl
  have hout5 : (shapeOf S hn N5).outbox =
      (pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.tail := by
    rw [hS5, pollBatch_outbox]
  have hR5 := dutyStep_poll_batch S rho hn v N4 k hsel
  dsimp only at hR5
  rw [Model.releaseAll_append, releaseAll_heldObj] at hR5
  let P := Model.protoOf (compiled (goldilocks S)) E
  let start : Model.Node P := ⟨(P.act N4.st (.poll k)).1, N4.seen⟩
  let head := Model.releaseAll P rho.hash (rho.ownKey v) start
    (pollOrdinary S rho v
      ((pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.head?.map fun b => (b, [])))
  let F := (Model.releaseAll P rho.hash (rho.ownKey v) head.1
    ((shapeOf S hn N4).forwards.map (fun p =>
      .mk (.signed (rho.ownKey v) .poll) (.data (.forward p.1)) p.2) ++
     (shapeOf S hn N4).voteForwards.map (fun p =>
      .mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward p.1 (encodeVote p.2.1))) [p.2.2]))).2
  change (rho.dutyStep v N4 (.poll k)).2 =
    (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v)
      ⟨((Model.protoOf (compiled (goldilocks S)) E).act N4.st (.poll k)).1, N4.seen⟩
      (pollOrdinary S rho v ((pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox.head?.map
        fun b => (b, [])))).2 ++ (F ++
          (pollFlush (shapeOf S hn N4) (S.release (pubOf E))).map (heldObj S rho v)) at hR5
  rw [release_head, ← List.append_assoc] at hR5
  have hR6 := dutyStep_poll_eq S rho hn v N5 k hsel
    (by rw [hS5]; exact pollBatch_forwards _ _) (by rw [hS5]; exact pollBatch_voteForwards _ _)
    (pollFlush_eq_nil (hS5 ▸ heldRefused_pollBatch _ _ hk4))
  rw [hpre5, hout5] at hR6
  have e5 := dutyStep_seen S rho v N4 (.poll k)
  rw [hR5] at e5
  refine ⟨F, hR5, e5, hR6, ?_, ?_⟩
  · have e6 := dutyStep_poll S rho hn v N5 k hsel
    rw [e6, pollBatch_outbox, hpre5, hout5]
  · intro o ho
    change o ∈ (Model.releaseAll _ _ _ _ (_ ++ _)).2 at ho
    rcases List.mem_append.mp (Model.releaseAll_subset _ _ _ _ o ho) with ho | ho
    · obtain ⟨⟨τ, cs⟩, _, rfl⟩ := List.mem_map.mp ho
      exact Or.inl ⟨τ, cs, rfl⟩
    · obtain ⟨⟨τ, m, w⟩, _, rfl⟩ := List.mem_map.mp ho
      exact Or.inr ⟨τ, m, w, rfl⟩

/-- The proposal step of a key that does not propose at `t` makes no cut. -/
theorem tickStep_proposal_not' {sp : ACParams}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp)) (t : Time) (x : Nat)
    (h : ¬ Proposes (P := sp.toParams) proposer self t) :
    Node.tickStep proposer dg self st t x .proposal = (st, []) := by
  simp [Node.tickStep, h]

/-- The node of `v` after the first three duties of its tick at `t` from `nd`. -/
noncomputable def preNode (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
  (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t (Model.mempool rho.inbox v t),
      nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1

/-- **The releases of a public tick.** At an honest node's tick at a public time (when its slot
proposal carries only seen objects), the engine releases, in order: the queued body (at most one)
against the node's `seen`, the canonical objects of the blocks of the node's tick cuts, the first
and the second body of `Q` against the `seen` before each, and unsigned gossip; `Q` is the votes
the tick's cuts emit followed by the attestation they sign, at most two bodies, when the release
schedule allows release at the tick's time (otherwise the attestation is held). The held
attestations (`relFlush`) leave at the end of the first trailing poll's batch, after its body and
forwards: only `pollPropose` sets the tick flag, so the leading polls flush nothing. -/
theorem tick_public_analysis (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (_hv' : v ∉ rho.faultyAt 0) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hrel : ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen) :
    ∃ (N4 N5 : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (Q : List Body)
      (R4 F G : List (Model.protoOf (compiled (goldilocks S)) E).Object),
      rho.releasesAt i =
        relHead S rho v (stateAt S rho hn v i).outbox.head? ++ R4 ++
          (relHead S rho v Q.head? ++ F ++ relFlush S rho hn v (stateAt S rho hn v i) t) ++
          relHead S rho v Q.tail.head? ++ G ∧
      N4.seen = (rho.stateBefore i v).seen ++
        relHead S rho v (stateAt S rho hn v i).outbox.head? ++ R4 ∧
      N5.seen = N4.seen ++
        (relHead S rho v Q.head? ++ F ++ relFlush S rho hn v (stateAt S rho hn v i) t) ∧
      (∀ o ∈ F, (∃ τ cs, o = .mk (.signed (rho.ownKey v) .poll) (.data (.forward τ)) cs) ∨
        ∃ τ, ∃ m : AC.Vote (Fintype.card V), ∃ w, o = .mk (.signed (rho.ownKey v) .poll)
          (.data (.voteForward τ (encodeVote m))) [w]) ∧
      (∀ o ∈ G, o.auth = .none) ∧ Q.length ≤ 2 ∧
      Q = emitted (stateAt S rho hn v i).voteIO
        (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E)
            (rho.ownKey v) t))).2 ++
        (if S.release (pubOf E) (rho.ownKey v) t then
          attBodies (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            (stateAt S rho hn v i).node t
            (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2
          else []) ∧
      R4 = blockObjs (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2 ∧
      (∀ c ∈ R4, ∀ x ∈ c.carried, x ∈ Model.closure ((rho.stateBefore i v).seen ++
        relHead S rho v (stateAt S rho hn v i).outbox.head?)) ∧
      N5 = (rho.dutyStep v N4 (.poll t.toNat)).1 := by
  have hm := List.mem_of_getElem? he
  have ht : 0 ≤ t := (hv.in_horizon _ hm).1
  have hw := hv.tick_awake v t hm
  have hsel : rho.ownKey v ∈ rho.sel .poll := by
    rw [selValid_poll S rho hv.selValid]; exact Finset.mem_univ _
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v i
  obtain ⟨-, hlen⟩ := (atMostOneVote_iff _).1 hamo
  have hf := fgDue_eq_false S rho hn v i
  have hself0 := self_eq_ownKey S rho hn v i
  set nd := rho.stateBefore i v with hnd
  have hσ : stateAt S rho hn v i = shapeOf S hn nd := stateAt_eq S rho hn v i
  rw [hσ] at hlen hf hself0 ⊢
  obtain ⟨hR1, hR2, hR3, hseen3, hS3, hout2, hnode2, hself2, hnow2, hfg2, hheld2, -, -⟩ :=
    leading_polls S rho hn v nd t hsel hf hlen
      (by simpa only [hσ] using forwards_empty S rho hn hv v i)
      (by simpa only [hσ] using voteForwards_empty S rho hn hv v i)
  set X := encodeTxs (Model.mempool rho.inbox v t)
  set H := relFlush S rho hn v (shapeOf S hn nd) t
  set dg := digestOf S rho
  set n1 := (Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).1
  have hp2 : (S.params (pubOf E) hn).toParams.IsPublic
      (shapeOf S hn (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
            (Model.mempool rho.inbox v t),
          nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1).now :=
    by rw [hnow2]; exact hp
  obtain ⟨hn3, ho3, hf3, hs3, hw3⟩ := nodeTick_public S hn _ hp2 hout2
  have hio2 : (shapeOf S hn (rho.dutyStep v (rho.dutyStep v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t (Model.mempool rho.inbox v t),
        nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1).voteIO = (shapeOf S hn nd).voteIO := by
    exact (dutyStep_voteIO S rho hn v _ _).trans ((dutyStep_voteIO S rho hn v _ _).trans rfl)
  rw [hio2] at ho3
  rw [hnode2, hself2, hnow2, hself0] at hn3 ho3
  rw [hself2, hself0] at hs3
  rw [hnow2] at hw3
  rw [hself2, hself0, hnow2] at hf3
  set sg := S.sign (pubOf E) (rho.ownKey v) t with hsg
  -- the cuts of the node's tick
  have hcuts : (exec (runProposer S rho hn) dg (rho.ownKey v)
      (shapeOf S hn nd).node t (.tick X sg)).2 =
      [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] ++
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).2 ++
        (if sg then (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v)
          (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).1 t X
          .fgUpdate).2 else []) :=
    onTick_cuts (sp := S.params (pubOf E) hn)
      (runProposer S rho hn) dg (rho.ownKey v) _ t X sg
  -- the third and fourth duties
  have hpre : preNode S rho v nd t = (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t (Model.mempool rho.inbox v t),
        nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 := rfl
  have hpre_shape := pre_shape S rho hn v nd t hsel
  -- the final step, common to both cases
  have finish : ∀ (N4 : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (R4 : List (Model.protoOf (compiled (goldilocks S)) E).Object) (c2 : List (Cut _)),
      (shapeOf S hn N4).fgDue = sg → (shapeOf S hn N4).self = rho.ownKey v →
      (shapeOf S hn N4).now = t →
      (shapeOf S hn N4).voteIO = (shapeOf S hn nd).voteIO →
      (shapeOf S hn N4).node =
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).1 →
      (shapeOf S hn N4).outbox = emitted (shapeOf S hn nd).voteIO
        [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] ++
          emitted (shapeOf S hn nd).voteIO c2 →
      c2 = (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 t X .proposal).2 →
      R4 = blockObjs c2 →
      N4.seen = nd.seen ++ relHead S rho v (shapeOf S hn nd).outbox.head? ++ R4 →
      (shapeOf S hn N4).outbox.length ≤ 1 →
      (∀ c ∈ R4, ∀ x ∈ c.carried, x ∈ Model.closure (nd.seen ++
        relHead S rho v (shapeOf S hn nd).outbox.head?)) →
      (shapeOf S hn N4).ticked = true → (shapeOf S hn N4).held = (shapeOf S hn nd).held →
      (rho.tick nd v t).2 = relHead S rho v (shapeOf S hn nd).outbox.head? ++ R4 ++
        (rho.dutyStep v N4 (.poll t.toNat)).2 ++
        (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).2 ++
        (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v)
          (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1
          (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E)
            (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1.st t)).2 →
      ∃ (N4 N5 : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (Q : List Body)
        (R4 F G : List (Model.protoOf (compiled (goldilocks S)) E).Object),
        (rho.tick nd v t).2 =
          relHead S rho v (shapeOf S hn nd).outbox.head? ++ R4 ++
            (relHead S rho v Q.head? ++ F ++ H) ++ relHead S rho v Q.tail.head? ++ G ∧
        N4.seen = nd.seen ++ relHead S rho v (shapeOf S hn nd).outbox.head? ++ R4 ∧
        N5.seen = N4.seen ++ (relHead S rho v Q.head? ++ F ++ H) ∧
        (∀ o ∈ F, (∃ τ cs, o = .mk (.signed (rho.ownKey v) .poll) (.data (.forward τ)) cs) ∨
          ∃ τ, ∃ m : AC.Vote (Fintype.card V), ∃ w, o = .mk (.signed (rho.ownKey v) .poll)
            (.data (.voteForward τ (encodeVote m))) [w]) ∧
        (∀ o ∈ G, o.auth = .none) ∧ Q.length ≤ 2 ∧
        Q = emitted (shapeOf S hn nd).voteIO (exec (runProposer S rho hn) dg (rho.ownKey v)
            (shapeOf S hn nd).node t (.tick X sg)).2 ++
          (if S.release (pubOf E) (rho.ownKey v) t then
            attBodies (exec (runProposer S rho hn) dg (rho.ownKey v)
              (shapeOf S hn nd).node t (.tick X sg)).2 else []) ∧
        R4 = blockObjs (exec (runProposer S rho hn) dg (rho.ownKey v)
            (shapeOf S hn nd).node t (.tick X sg)).2 ∧
        (∀ c ∈ R4, ∀ x ∈ c.carried, x ∈ Model.closure (nd.seen ++
          relHead S rho v (shapeOf S hn nd).outbox.head?)) ∧
        N5 = (rho.dutyStep v N4 (.poll t.toNat)).1 := by
    intro N4 R4 c2 hf4 hs4 hw4 hio4 hn4 ho4 hc2 hR4 hseen4 hb4 hcar hk4 hh4 htick
    subst hc2
    obtain ⟨F, hR5, hseen5, hR6, -, hF⟩ := trailing_polls S rho hn v N4 t.toNat hsel hk4
    have hH : (pollFlush (shapeOf S hn N4) (S.release (pubOf E))).map (heldObj S rho v) = H := by
      rw [show H = relFlush S rho hn v (shapeOf S hn nd) t from rfl, relFlush_eq, hself0,
        pollFlush_eq, hs4, hw4, hk4, hh4, Bool.and_true]
    rw [hH] at hR5 hseen5
    obtain ⟨hQ, hem3, hbl3, -⟩ := fgUpdate_outbox_eq (release := S.release (pubOf E))
      (runProposer S rho hn) dg X (shapeOf S hn N4)
    rw [hs4, hn4, hw4] at hQ hem3 hbl3
    rw [hio4] at hem3
    have hpre4 := pollPre_eq (shapeOf S hn N4) (S.release (pubOf E))
    rw [hf4] at hpre4
    refine ⟨N4, (rho.dutyStep v N4 (.poll t.toNat)).1,
      (pollPre (shapeOf S hn N4) (S.release (pubOf E))).outbox, R4, F,
      (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v)
        (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1
        (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E)
          (rho.dutyStep v (rho.dutyStep v N4 (.poll t.toNat)).1 (.poll t.toNat)).1.st t)).2,
      ?_, hseen4, hseen5, hF, gossip_unsigned S rho _ _ _, ?_, ?_, ?_, hcar, rfl⟩
    · rw [htick, hR5, hR6]
    · rw [hpre4]
      cases sg
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [↓reduceIte]
        rcases fgUpdate_outbox_cases (release := S.release (pubOf E)) (shapeOf S hn N4) with
          h | ⟨a, h⟩
        · rw [h]; omega
        · rw [h, List.length_append, List.length_singleton]; omega
    · have hab : attBodies [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] = [] :=
        attBodies_ac _
      have hpb := tickStep_proposal_attBodies (sp := S.params (pubOf E) hn)
        (runProposer S rho hn) dg (rho.ownKey v) n1 t X
      rw [hpre4, hcuts]
      cases sg
      · simp only [Bool.false_eq_true, ite_false, List.append_nil, emitted_append,
          attBodies_append, hab, hpb, ho4, ite_self]
      · simp only [ite_true]
        rw [hQ, ho4, emitted_append, emitted_append, attBodies_append, attBodies_append, hem3, hpb,
          hab]
        simp only [List.append_nil, List.nil_append, List.append_assoc]
    · have hbb : blockObjs (binding := S.vote)
          [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] = [] :=
        blockObjs_ac _
      rw [hR4, hcuts]
      cases sg
      · simp only [Bool.false_eq_true, ite_false, List.append_nil, blockObjs_append, hbb,
          List.nil_append]
        rfl
      · simp only [ite_true, blockObjs_append, hbb, hbl3, List.append_nil, List.nil_append]
        rfl
  simp only [Model.Run.releasesAt, he]
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, hts⟩
  · -- no slot proposal at `t`
    obtain ⟨N1, N3, N5, N6, rfl, rfl, rfl, rfl, heq⟩ := tick_unroll_nil S rho v nd t ht hw hnil
    have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) t :=
      not_proposes S hn (runProposer S rho hn) _ t
        (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    have hc2 := tickStep_proposal_not' (runProposer S rho hn) dg (rho.ownKey v) n1 t X hnp
    have hb3 := outbox_after_pre S rho hn v (shapeOf S hn nd) t ht hf hlen
      (preNode S rho v nd t) hpre_shape
    rw [hnil] at hb3
    have hb3' : (shapeOf S hn (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
            (Model.mempool rho.inbox v t),
          nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1).outbox.length
        ≤ 1 := hb3
    refine finish _ [] [] (by rw [hS3]; exact hf3) (by rw [hS3]; exact hs3)
      (by rw [hS3]; exact hw3) ((dutyStep_voteIO S rho hn v _ _).trans hio2)
      (by rw [hS3, hn3, hc2])
      (by rw [hS3, ho3]; simp [emitted])
      (by rw [hc2]) (by rw [blockObjs_nil]; rfl) (by rw [hseen3]; simp) hb3'
      (fun c hc => absurd hc List.not_mem_nil) (by rw [hS3])
      (by rw [hS3]; exact (nodeTick_held _).trans hheld2) ?_
    rw [heq, hR1, hR2, hR3]
    simp
  · -- the slot proposal of `s`
    obtain ⟨N1, N3, N4, N5, N6, rfl, rfl, rfl, rfl, rfl, heq⟩ :=
      tick_unroll_propose S rho v nd t ht hw s hs hone
    have hts' : t = (S.params (pubOf E) hn).toParams.slotTime s :=
      hts.trans (slotTime_eq S hn s).symm
    set N3 := (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
            (Model.mempool rho.inbox v t),
          nd.seen⟩ (.poll t.toNat)).1 (.poll t.toNat)).1 (.pollPropose t.toNat)).1 with hN3
    have hselfN3 : (shapeOf S hn N3).self = rho.ownKey v := by rw [hS3]; exact hs3
    have hnowN3 : (shapeOf S hn N3).now = t := by rw [hS3]; exact hw3
    have hnodeN3 : (shapeOf S hn N3).node = n1 := by rw [hS3]; exact hn3
    have hfgN3 : (shapeOf S hn N3).fgDue = sg := by rw [hS3]; exact hf3
    have houtN3 : (shapeOf S hn N3).outbox =
        emitted (shapeOf S hn nd).voteIO
          [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node t .tick).2] := by
      rw [hS3]; exact ho3
    have hmem : N3.st.2 = Model.mempool rho.inbox v t :=
      runDuties_mempool S rho v [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
            (Model.mempool rho.inbox v t),
          nd.seen⟩
    have hsp := selValid_proposer S rho hn hv.selValid s
    have hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn N3).now = s := by
      rw [hnowN3, hts']; exact slotOf_slotTime _ s
    have hst : (shapeOf S hn N3).now = (S.params (pubOf E) hn).toParams.slotTime s :=
      hnowN3.trans hts'
    have hrel' : rho.ownKey v ∈ rho.sel (.proposer s) →
        ∀ par info cs, (propose (shapeOf S hn N3) s).2 = some (par, info, cs) →
        ∀ o ∈ cs, o ∈ Model.closure N3.seen := hrel s hs hone
    obtain ⟨hR4, ho4⟩ := dutyStep_propose_full S rho hn v N3 s hs hsp hselfN3 hslot hst hrel'
    have hn4 := dutyStep_propose_node S rho hn v N3 s hs hsp hselfN3 hslot hst hrel'
    rw [hnodeN3, hnowN3, hmem] at hR4 ho4 hn4
    rw [houtN3] at ho4
    have hf4 := dutyStep_propose_pres S rho hn (fun st => st.fgDue = sg)
      (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
      (fun st s h => (propose_fgDue st s).trans h) v N3 s hs hfgN3
    have hs4 := dutyStep_propose_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h) v N3 s hs hselfN3
    have hw4 := dutyStep_propose_pres S rho hn (fun st => st.now = t)
      (fun st o hs h => (recordOwn_now st o hs).trans h)
      (fun st s h => (propose_now st s).trans h) v N3 s hs hnowN3
    have hb3 := outbox_after_pre S rho hn v (shapeOf S hn nd) t ht hf hlen
      (preNode S rho v nd t) hpre_shape
    rw [hone] at hb3
    have hb4 : (shapeOf S hn (rho.dutyStep v N3 (.propose s hs)).1).outbox.length ≤ 1 := hb3
    have hseen4 := dutyStep_seen S rho v N3 (.propose s hs)
    rw [hseen3] at hseen4
    have hcar : ∀ c ∈ (rho.dutyStep v N3 (.propose s hs)).2, ∀ x ∈ c.carried,
        x ∈ Model.closure (nd.seen ++ relHead S rho v (shapeOf S hn nd).outbox.head?) := by
      intro c hc x hx
      have := dutyStep_carried S rho v N3 (.propose s hs) (fun _ h => by cases h) c hc x hx
      rwa [hseen3] at this
    have hio4 : (shapeOf S hn (rho.dutyStep v N3 (.propose s hs)).1).voteIO =
        (shapeOf S hn nd).voteIO := by
      exact (dutyStep_voteIO S rho hn v _ _).trans ((dutyStep_voteIO S rho hn v _ _).trans hio2)
    have hio3 : (shapeOf S hn N3).voteIO = (shapeOf S hn nd).voteIO :=
      (dutyStep_voteIO S rho hn v _ _).trans hio2
    rw [hio3] at ho4
    have hk4 := dutyStep_propose_pres S rho hn (fun st => st.ticked = true)
      (fun st o hs h => (recordOwn_ticked st o hs).trans h)
      (fun st s h => (propose_ticked st s).trans h) v N3 s hs (by rw [hS3])
    have hh4 := dutyStep_propose_pres S rho hn (fun st => st.held = (shapeOf S hn nd).held)
      (fun st o hs h => (recordOwn_held st o hs).trans h)
      (fun st s h => (propose_held st s).trans h) v N3 s hs
      (by rw [hS3]; exact (nodeTick_held _).trans hheld2)
    refine finish _ _ _ hf4 hs4 hw4 hio4 hn4 ho4 rfl hR4 hseen4 hb4 hcar hk4 hh4 ?_
    rw [heq, hR1, hR2, hR3]
    simp

end TickPublic

/-! ## Which attestations a tick releases -/

section Inventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- An attestation's canonical object is the poll object of its attestation body, signed by its
validator. -/
theorem attObj_eq_pollObj {v : V} {b : FG.Att (Fintype.card V)} {q : Body}
    (h : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) = pollObj S rho v q) :
    q = .att (encodeAtt b) ∧ b.val = rho.ownKey v := by
  injection h with h1 h2 h3
  injection h1 with h4 h5
  injection h2 with h6
  exact ⟨h6.symm, h4⟩

omit [DecidableEq V] in
/-- The attestation body encoding is injective. -/
theorem encodeAtt_inj {n : Nat} {a b : FG.Att n} (h : encodeAtt a = encodeAtt b) : a = b := by
  have h1 := decodeAtt_encodeAtt a
  rw [h, decodeAtt_encodeAtt] at h1
  exact (Option.some.inj h1).symm

omit [DecidableEq V] in
/-- A member of `relHead` is the poll object of the head. -/
theorem mem_relHead {v : V} {ob : Option Body} {o}
    (h : o ∈ relHead S rho v ob) : ∃ b, ob = some b ∧ o = pollObj S rho v b := by
  cases ob with
  | none => simp [relHead] at h
  | some b =>
    simp only [relHead, Option.elim_some] at h
    split at h
    · exact ⟨b, rfl, List.mem_singleton.mp h⟩
    · exact absurd h List.not_mem_nil

omit [DecidableEq V] in
/-- No attestation object among the canonical block objects. -/
theorem attObj_not_mem_blockObjs (b : FG.Att (Fintype.card V))
    (cs : List (Cut (goldilocksNode (S.params (pubOf E) hn)))) :
    (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∉
      blockObjs (sp := S.params (pubOf E) hn) cs := by
  intro h
  rw [blockObjs_eq] at h
  obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp h
  match c with
  | .fg (.block B _) =>
    have := List.mem_singleton.mp hc
    injection this with h1 h2 h3
    cases h2
  | .fg (.attestation _) => exact absurd hc List.not_mem_nil
  | .fg (.attest _ _) => exact absurd hc List.not_mem_nil
  | .ac _ => exact absurd hc List.not_mem_nil

omit [DecidableEq V] in
/-- An attestation body among `emitted ++ attBodies` comes from a signing cut. -/
theorem att_mem_bodies {io : VoteAuth (S.params (pubOf E) hn).n S.vote}
    {cs : List (Cut (goldilocksNode (S.params (pubOf E) hn)))}
    {w : WireAtt} (h : Body.att w ∈ emitted io cs ++ attBodies cs) :
    ∃ C a, Cut.fg (.attest C (some a)) ∈ cs ∧ w = encodeAtt a := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp h
    match c with
    | .ac ℓ =>
      obtain ⟨e, -, he⟩ := List.mem_filterMap.mp hc
      obtain ⟨_, -, he⟩ := Option.map_eq_some_iff.mp he
      cases he
    | .fg _ => exact absurd hc List.not_mem_nil
  · rw [attBodies_eq] at h
    obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp h
    match c, hc, hb with
    | .fg (.attest C (some a)), hc, hb =>
      have := List.mem_singleton.mp hb
      injection this with h1
      exact ⟨C, a, hc, h1⟩
    | .fg (.attest _ none), _, hb => exact absurd hb List.not_mem_nil
    | .fg (.block _ _), _, hb => exact absurd hb List.not_mem_nil
    | .fg (.attestation _), _, hb => exact absurd hb List.not_mem_nil
    | .ac _, _, hb => exact absurd hb List.not_mem_nil

end Inventory

section Inventory2

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- `preNode` is the engine's node at the proposal duty (`atProposal`, Steps). -/
theorem preNode_eq_atProposal (v : V) (nd : Model.Node (Model.protoOf (compiled
    (goldilocks S)) E))
    (t : Time) : preNode S rho v nd t = atProposal S rho v nd t := by
  rw [atProposal_eq]; rfl

/-- The proposal of an honest node's tick carries only objects the node has seen
(`proposal_releasable`, Steps). -/
theorem preNode_releasable (_hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time}
    (_hv' : v ∉ rho.faultyAt 0) (he : rho.events[i]? = some (.tick v t)) :
    ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen := by
  rw [preNode_eq_atProposal]
  exact fun s hs hone hsel par info cs h =>
    proposal_releasable S rho hn hv v i t he s par info cs hs hone hsel h

/-- At a tick at a non-public time an honest node releases only its queued body, the held
attestations the release schedule lets its first trailing poll flush, and unsigned gossip. -/
theorem tick_other_releases (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (_hv' : v ∉ rho.faultyAt 0) (he : rho.events[i]? = some (.tick v t))
    (hnp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    ∀ o ∈ rho.releasesAt i, o ∈ relHead S rho v
      (stateAt S rho hn v i).outbox.head? ∨ o ∈ relFlush S rho hn v (stateAt S rho hn v i) t ∨
        o.auth = .none := by
  have hm := List.mem_of_getElem? he
  have ht : 0 ≤ t := (hv.in_horizon _ hm).1
  have hw := hv.tick_awake v t hm
  have hsel : rho.ownKey v ∈ rho.sel .poll := by
    rw [selValid_poll S rho hv.selValid]; exact Finset.mem_univ _
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v i
  obtain ⟨-, hlen⟩ := (atMostOneVote_iff _).1 hamo
  have hf := fgDue_eq_false S rho hn v i
  set nd := rho.stateBefore i v
  have hσ : stateAt S rho hn v i = shapeOf S hn nd := stateAt_eq S rho hn v i
  rw [hσ] at hlen hf ⊢
  obtain ⟨hR1, hR2, hR3, -, hS3, hout2, -, hself2, hnow2, hfg2, hheld2, hfw2, hvf2⟩ :=
    leading_polls S rho hn v nd t hsel hf hlen
      (by simpa only [hσ] using forwards_empty S rho hn hv v i)
      (by simpa only [hσ] using voteForwards_empty S rho hn hv v i)
  have hnil : (skeleton (pubOf E) S.vote).proposeAt t = [] := by
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with
      ⟨h, -⟩ | ⟨s, hs, -, hts⟩
    · exact h
    · exfalso; apply hnp
      rw [hts, ← slotTime_eq S hn s]
      exact (S.params (pubOf E) hn).toParams.slotTime_public s
  obtain ⟨N1, N3, N5, N6, h1, rfl, rfl, rfl, heq⟩ := tick_unroll_nil S rho v nd t ht hw hnil
  rw [← h1] at hR2 hR3 hS3 hout2 hself2 hnow2 hfg2 hheld2 hfw2 hvf2
  set N2 := (rho.dutyStep v N1 (.poll t.toNat)).1
  set N3 := (rho.dutyStep v N2 (.pollPropose t.toNat)).1
  -- at a non-public time the node's tick only sets the tick flag
  have hS3' : shapeOf S hn N3 = { shapeOf S hn N2 with ticked := true } := by
    rw [hS3, nodeTick_eq (sign := _), ite_eq_right (by rw [hnow2]; exact hnp)]
  have hpre3 : pollPre (shapeOf S hn N3) (S.release (pubOf E)) = shapeOf S hn N3 := by
    rw [pollPre_eq, hS3']; simp [hfg2]
  have hR5 := dutyStep_poll_first S rho hn v N3 t.toNat hsel (by rw [hS3']; exact hfw2)
    (by rw [hS3']; exact hvf2)
  have hfl : (pollFlush (shapeOf S hn N3) (S.release (pubOf E))).map (heldObj S rho v) =
      relFlush S rho hn v (shapeOf S hn nd) t := by
    rw [relFlush_eq, pollFlush_eq, hS3']
    simp only [Bool.and_true, hself2, hnow2, hheld2]
  rw [hpre3, hfl, hS3'] at hR5
  have hS5 := dutyStep_poll S rho hn v N3 t.toNat hsel
  have hk3 : (shapeOf S hn N3).ticked = true := by rw [hS3']
  have hout5 : (shapeOf S hn (rho.dutyStep v N3 (.poll t.toNat)).1).outbox = [] := by
    rw [hS5, pollBatch_outbox, hpre3, hS3']; change (shapeOf S hn N2).outbox.tail = []
    rw [hout2]; rfl
  have hpre5 : pollPre (shapeOf S hn (rho.dutyStep v N3 (.poll t.toNat)).1)
      (S.release (pubOf E)) = shapeOf S hn (rho.dutyStep v N3 (.poll t.toNat)).1 := by
    rw [pollPre_eq]; rw [hS5, pollBatch_fgDue]; rfl
  have hR6 := dutyStep_poll_eq S rho hn v (rho.dutyStep v N3 (.poll t.toNat)).1
    t.toNat hsel (by rw [hS5]; exact pollBatch_forwards _ _)
      (by rw [hS5]; exact pollBatch_voteForwards _ _)
      (by rw [hS5]; exact pollFlush_eq_nil (heldRefused_pollBatch _ _ hk3))
  rw [hpre5, hout5] at hR6
  intro o ho
  simp only [Model.Run.releasesAt, he] at ho
  rw [heq, hR1, hR2, hR3, hR5, hR6] at ho
  change o ∈ relHead S rho v (shapeOf S hn nd).outbox.head? ++ [] ++ [] ++
    (relHead S rho v (shapeOf S hn N2).outbox.head? ++ relFlush S rho hn v (shapeOf S hn nd) t) ++
    relHead S rho v none ++ _ at ho
  rw [hout2] at ho
  simp only [relHead, List.head?_nil, Option.elim_none, List.append_nil, List.nil_append] at ho
  rcases List.mem_append.mp ho with ho | ho
  · rcases List.mem_append.mp ho with ho | ho
    · exact Or.inl ho
    · exact Or.inr (Or.inl ho)
  · exact Or.inr (Or.inr (gossip_unsigned S rho _ _ _ o ho))

end Inventory2

/-! ## The releases of a tick -/

section TickReleases

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A signing cut of a generic handler of `self` signs an attestation of `self`. -/
theorem attest_val_of_mem_node_exec {P : Params} {A : NodeAC P}
    (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A)
    {C : A.Blk} {a : FG.Att P.n}
    (h : Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t e).2) : a.val = self := by
  have key : ∀ {st st' : NodeState A} {cs},
      CutChain self t st cs st' → Cut.fg (.attest C (some a)) ∈ cs → a.val = self := by
    intro st st' cs hc
    induction hc with
    | nil => simp
    | @cons st₀ st₁ _ c cs hstep _ ih =>
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        obtain ⟨he, -, -⟩ := hstep
        exact createAtt_val he
      · exact ih hm
  exact key (Compose.exec_is_cut_chain proposer dg self st t e) h

/-- A signing cut of a handler of `self` signs an attestation of `self`. -/
theorem attest_val_of_mem_exec {sp : ACParams}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp)) (t : Time) (e : Event (goldilocksNode sp))
    {C : (goldilocksNode sp).Blk} {a : FG.Att sp.n}
    (h : Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t e).2) : a.val = self :=
  attest_val_of_mem_node_exec (P := sp.toParams) (A := goldilocksNode sp)
    proposer dg self st t e h

/-- A signing cut of an honest node's tick at a public time is a signing of the simulating
trace among the cuts of that engine event. -/
theorem signAt_in_tick {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {C} {b : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign
        (pubOf E) (rho.ownKey v) t))).2) :
    ∃ k, cutMap S rho hn j ≤ k ∧ k < cutMap S rho hn (j + 1) ∧
      (simTrace S rho hn).SignAt (rho.ownKey v) k b := by
  have hj : j < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hEC := eventCuts_tick_public S rho hn j v t he hp
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  have hm'' : m < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t
      (Nat.pair j 0) (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E)
        (rho.ownKey v) t))).length :=
    lt_of_lt_of_eq hm
      (length_groupRecs (sp := S.params (pubOf E) hn) _ _ _ _ _ _ _).symm
  have hm' : m < (eventCuts S rho hn j).length := by
    rw [hEC, List.length_append]; omega
  have hget : (eventCuts S rho hn j)[m] = (groupRecs (runProposer S rho hn)
      (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v j).node t (Nat.pair j 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E)
        (rho.ownKey v) t)))[m] := by
    simp only [hEC]
    exact List.getElem_append_left hm''
  have hk := allCuts_getElem?_add S rho hn j m hj hm'
  rw [List.getElem?_eq_getElem hm'] at hk
  obtain ⟨hnode, -, -, -, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm''
  refine ⟨cutMap S rho hn j + m, by omega, ?_, C, ?_, ?_⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hk]
    simp only [Option.elim_some]
    rw [hget]
    exact hnode
  · rw [simTrace_label, hk]
    simp only [Option.map_some]
    rw [hget, hlab, hcm]

/-- A signing cut of an honest node's tick at a public time is a signing of the simulating
trace before the end of that engine event. -/
theorem signAt_before_tick_end {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {C} {b : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v j).node t (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign
        (pubOf E) (rho.ownKey v) t))).2) :
    ∃ k < cutMap S rho hn (j + 1), (simTrace S rho hn).SignAt (rho.ownKey v) k b :=
  let ⟨k, _, hk, hs⟩ := signAt_in_tick S rho hn he hp hc
  ⟨k, hk, hs⟩

/-- A vote emitted by a cut of `v`'s handler run from its engine state is of a slot whose vote
role selects `v` (the emission gate at the state's installed permission). -/
theorem exec_emit_selected (hv : rho.ExecutionValid) {v : V} {i : Nat} {t : Time}
    {e : Event (goldilocksNode (S.params (pubOf E) hn))}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn))}
    (hℓ : Cut.ac ℓ ∈ (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t e).2) :
    ∀ m ∈ ℓ.emits, rho.ownKey v ∈ rho.sel (S.vote.voteRole m.msg.slot) := fun m hm => by
  have h := emits_mayVote_of_mem_exec _ _ _ _ _ _ hℓ m hm
  rw [stateAt_mayVote S rho hn hv v i] at h
  exact of_decide_eq_true h

end TickReleases

end Consensus.Goldilocks.Simulation

end

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.NodeEngine.Wire
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs

public section

namespace Consensus.Goldilocks.NodeEngine.Concrete
open AsChainShape (Setup)
open Consensus.Model (Public)

/-- The genuine operation, on exactly the nonnegative-time domain supplied upstream. -/
theorem restartSilent (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) :
    RestartSilent (runtime S pub hn).operations.toAC := by
  intro self st Φ t ht
  exact Simulation.restart_emits_nil (sp := S.params pub hn) (S.ro _) self st Φ t ht

/-- The stored-clock contract has no collision or regime premise; Goldilocks proves more. -/
theorem storedClockTips (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (Reach : NodeState (runtime S pub hn).operations.toAC → Time → Prop) :
    StoredClockTips (runtime S pub hn).operations.toAC Reach := by
  intro st t _ hΦ
  exact Regimes.sa_tips (sp := S.params pub hn) (A := st.ac) hΦ t

/-- Restart execution has precisely one AC cut, retaining its actual frame. -/
theorem restartCut (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : State (wire S pub hn)) (t : Time) (ht : 0 ≤ t) :
    (Node.restart st.self st.node t).2 = [.ac ⟨.restart, Node.frame st.node, []⟩] := by
  change [Cut.ac ⟨.restart, Node.frame st.node, _⟩] = _
  rw [restartSilent S pub hn st.self st.node.ac (Node.frame st.node) t ht]

theorem restore_outbox (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : State (wire S pub hn)) (k : Fin pub.n) (t : Time) (ht : 0 ≤ t) :
    (restore (wire S pub hn) k st t).outbox = st.outbox := by
  simp only [restore, apply, emitted, Node.restart, Node.acCall]
  rw [restartSilent S pub hn k st.node.ac (Node.frame st.node) t ht]
  simp

theorem restore_forwards (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : State (wire S pub hn)) (k : Fin pub.n) (t : Time) :
    (restore (wire S pub hn) k st t).forwards = st.forwards := by rfl

theorem restore_relay (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : State (wire S pub hn)) (k : Fin pub.n) (t : Time) :
    (restore (wire S pub hn) k st t).relayBuf = st.relayBuf := by rfl

theorem restore_wrappers (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : State (wire S pub hn)) (k : Fin pub.n) (t : Time) :
    (restore (wire S pub hn) k st t).wrappers = st.wrappers := by rfl

theorem restore_msgForwards (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (st : State (wire S pub hn)) (k : Fin pub.n) (t : Time) (ht : 0 ≤ t) :
    (restore (wire S pub hn) k st t).msgForwards = st.msgForwards := by
  simp only [restore, apply, Node.restart, Node.acCall]
  rw [restartSilent S pub hn k st.node.ac (Node.frame st.node) t ht]
  change st.msgForwards ++ [] = st.msgForwards
  exact List.append_nil _

end Consensus.Goldilocks.NodeEngine.Concrete

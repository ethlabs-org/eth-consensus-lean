module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Engine

@[expose] public section

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public)

/-- AC carriers depend on the count, not positivity. Wire carriers are count independent. -/
structure Family (Info Body : Type) [DecidableEq Info] [Countable Info] where
  State : Nat → Type
  Msg : Nat → Type
  Payload : Nat → Type
  runtime : ∀ (pub : Public) (hn : 1 ≤ pub.n),
    Runtime pub hn (State pub.n) (Msg pub.n) (Payload pub.n)
  wire : ∀ pub hn, Wire (runtime pub hn) Info Body
  decBody : DecidableEq Body
  grid : Public → TimeGrid
  proposerSel : ∀ pub : Public, Nat → Model.SelSpec pub.n
  pollSel : ∀ pub : Public, Model.SelSpec pub.n
  order : List (Step Empty)
  deliverOrder : List (Step Empty)
  dependencies : ∀ n, Model.DependencyPolicy (ShapeObj n Empty Info Body)
  conflicts : ∀ n, ShapeObj n Empty Info Body → ShapeObj n Empty Info Body → Bool
  isFGAtt : ∀ n, ShapeObj n Empty Info Body → Prop

def Family.skeleton {Info Body : Type} [DecidableEq Info] [Countable Info]
    (A : Family Info Body) (pub : Public) : Skeleton pub.n :=
  ⟨A.grid pub, A.proposerSel pub, A.pollSel pub, Empty, inferInstance, [],
    (fun k => k.elim), (fun k => k.elim), none, A.order, A.deliverOrder⟩

/-- Family construction uses only an empty-kind skeleton built directly from the wire policy. -/
noncomputable def shapeFamily {Info Body Out : Type} [DecidableEq Info] [Countable Info]
    (A : Family Info Body) (isFinalized : Out → Bool) : ∀ pub : Public, ChainShape pub Out Info :=
  fun (pub : Public) =>
    let G := fun hn : 1 ≤ pub.n => nodeShape (A.wire pub hn) isFinalized
    { skel := A.skeleton pub
      State := (hn : 1 ≤ pub.n) → State (A.wire pub hn)
      Body := Body
      Durable := (hn : 1 ≤ pub.n) → State (A.wire pub hn)
      decBody := A.decBody
      init := fun k p hn => (G hn).init k p
      clock := fun st t hn => (G hn).clock (st hn) t
      propose := fun st s => if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).propose (st hn) s).1, ((G hn).propose (st hn) s).2) else (st, none)
      act := fun _ _ k => k.elim
      pollPropose := fun st t => if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollPropose (st hn) t).1, ((G hn).pollPropose (st hn) t).2)
        else (st, none)
      poll := fun st t => if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).poll (st hn) t).1, ((G hn).poll (st hn) t).2) else (st, none)
      pollBatch := fun st t => if hn : 1 ≤ pub.n then
        (fun _ => ((G hn).pollBatch (st hn) t).1, ((G hn).pollBatch (st hn) t).2) else (st, [])
      gossip := fun st t => if hn : 1 ≤ pub.n then (G hn).gossip (st hn) t else []
      process := fun st o hs hn => (G hn).process (st hn) o hs
      recordOwn := fun st o hs hn => (G hn).recordOwn (st hn) o hs
      dependencies := A.dependencies pub.n
      durable := id
      restore := fun k st t hn => (G hn).restore k (st hn) t
      out := fun g st => if hn : 1 ≤ pub.n then (G hn).out g (st hn) else []
      conflicts := A.conflicts pub.n
      isFGAtt := A.isFGAtt pub.n }

end Consensus.Goldilocks.NodeEngine

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.NodeEngine.Goldilocks

public section
namespace Consensus.Goldilocks.NodeEngine.Concrete
open AsChainShape (Setup)
open Consensus.Model (Public)
open Blocks Shape

theorem body_carrier (S : Setup) (pub : Public) :
    (shape S pub).Body = (AsChainShape.goldilocks S pub).Body := rfl

theorem skeleton_carrier (S : Setup) (pub : Public) :
    (shape S pub).skel = (AsChainShape.goldilocks S pub).skel := by
  unfold shape shapeFamily Family.skeleton family AsChainShape.goldilocks
    AsChainShape.goldilocksWith AsChainShape.skeleton
  dsimp only
  congr 1
  funext k
  exact nomatch k

theorem message_carrier (S : Setup) (pub : Public) (hn : 1 ≤ pub.n) :
    (runtime S pub hn).operations.toAC.Msg = SA.Vote pub.n := rfl

theorem readPoint_carrier (S : Setup) (pub : Public) (hn : 1 ≤ pub.n)
    (e : Emission pub.n (List (FG.Att pub.n)) (SA.Payload pub.n)
      (runtime S pub hn).operations.toAC.State (SA.Vote pub.n)) :
    (show SA.SAState pub.n from e.readPoint) = e.readPoint := rfl

theorem object_carrier (S : Setup) (pub : Public) :
    ShapeObj pub.n (shape S pub).skel.Kind AsChainShape.Info (shape S pub).Body =
      AsChainShape.Wire pub.n := rfl

theorem reshape_events {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (AsChainShape.goldilocks S)) E) :
    (reshape S rho).events = rho.events := rfl

end Consensus.Goldilocks.NodeEngine.Concrete

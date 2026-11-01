module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Interface
public import ConsensusLean.Lemmas.Model.Candidates

public section

/-! # Abstract forwarding publisher

This model is separate from runtime state; its transitions do not prove actual publication.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Abstract publisher state, separate from the installed runtime state. The map
survives restarts; pending wrappers are drained in acceptance order before the event ends.
OPEN implementation: connecting this state to `State`, actual duties and own proposals. -/
structure ForwardingState (n : Nat) where
  wrappers : Nat → Option (Wire n)
  pending : List (Wire n)

/-- Revised publication transition: remember the exact wrapper and append it to the same-event
drain. Resolve the parent from the durable map, never from a raw parent object. A missing
non-genesis parent fails explicitly; proving this cannot occur on actual acceptance is OPEN.
Callers must establish canonical acceptance first. This is not an installed engine handler. -/
def ForwardingState.enqueue {sp : SA.SAParams} (st : ForwardingState sp.n)
    (origin : Fin sp.n) (t : Time) (B : Blk sp) :
    Option (ForwardingState sp.n) := do
  let root ← B.parent
  let parent ← if root = sp.genesisRoot then some none
    else (st.wrappers root).map some
  let o := forwardObj sp origin t parent B
  return ⟨Function.update st.wrappers B.root (some o), st.pending ++ [o]⟩

/-- Drain the entire event queue in one ordered engine release batch, retaining the durable
map and clearing only the queue. Parent wrappers queued earlier become available to later
guards through `releaseAll`'s seen update. Integration as an executed signed batch is OPEN. -/
noncomputable def ForwardingState.drain {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (st : ForwardingState (Fintype.card V)) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (family S)) E)) :
    ForwardingState (Fintype.card V) ×
      (Model.Node (protoOf (compiled (family S)) E) × List (Wire (Fintype.card V))) :=
  (⟨st.wrappers, []⟩,
    Model.releaseAll (protoOf (compiled (family S)) E) rho.hash origin nd st.pending)

/-- A drain clears pending traffic but keeps the canonical wrapper map. This is a local
producer-state fact, not a release guarantee or a theorem about engine restarts. -/
theorem ForwardingState.drain_persistent {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (st : ForwardingState (Fintype.card V)) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (family S)) E)) :
    (st.drain S rho origin nd).1.wrappers = st.wrappers ∧
      (st.drain S rho origin nd).1.pending = [] := by
  exact ⟨rfl, rfl⟩

end Consensus.Goldilocks.Refinement

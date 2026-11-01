module
public import AvailableChainFGCompose.Statements.ExecutionBridges
public import AvailableChainFGCompose.Statements.Channels
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (Compose import policy)

@[expose] public section

/-! Observed safety, order and pool records over the shared execution observation.
These are the observation-indexed replacements of `FGSafetyStoreLaws` (reachable store
invariant, genesis-only initial tree, new-block provenance), `FGRunOrderLaws.mono` and the
row/proposal-pool keep premises. Environmental authenticity and scope premises
(`FGSafetyWireLaws`, `FGSafetyScopeLaws`) stay separate consumer premises. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}

/-- Reachable store invariant at every observed cut and event prefix, genesis-only initial
tree, provenance of every new FG block (an accepting step or an own release of the same
receiver, with the S decoders' erasure and rows), and the binding of the accepted-body view
`H` to the FG tree. -/
structure FGObservedSafetyLaws (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (Hv : FGHeightView (Fin n)) (f : FGFinalityView (Fin n))
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P) : Prop where
  initial_tf : ∀ x, ∀ B ∈ (R.core (O.stateBefore 0 x)).fg.TF, B = .genesis
  prefix_invariant : ∀ j x, FGStoreInvariant Hv f (R.core (O.stateBefore j x)).fg
  cut_invariant : ∀ x k, k ≤ O.cutLength x →
    FGStoreInvariant Hv f (R.core (O.cutState x k)).fg
  new_block : ∀ x k B, k < O.cutLength x →
    B ∈ (R.core (O.cutState x (k + 1))).fg.TF → B ∉ (R.core (O.cutState x k)).fg.TF →
    ∃ wire, ((∃ o, O.accepts x k o ∧ o.wire = wire) ∨
      (∃ j t, rho.events[j]? = some (.tick x t) ∧ wire ∈ obsOwnReleased O x j ∧
        O.duty x j ≤ k ∧ k < O.done x j)) ∧
      S.proposalErase wire = some (R.erase B) ∧
      B.rows = (S.proposalRows wire).filterMap S.decode
  view_blocks : ∀ x k, k ≤ O.cutLength x →
    H.acceptedBlocks (O.cutState x k) = (R.core (O.cutState x k)).fg.TF.image R.erase
  view_bodies : ∀ x k, k ≤ O.cutLength x → ∀ B,
    B ∈ H.acceptedBlocks (O.cutState x k) ↔
      ∃ b ∈ H.acceptedBodies (O.cutState x k), H.erase b = B
  body_rows : ∀ x k, k ≤ O.cutLength x → ∀ b ∈ H.acceptedBodies (O.cutState x k),
    ∀ B ∈ (R.core (O.cutState x k)).fg.TF, R.erase B = H.erase b →
      B.rows = (W.bodyRows b).filterMap S.decode

/-- Observation-indexed `FGRunOrderLaws.mono`: F-prefix, lexicographic `(h_j, J)` and
`h_max` order between event prefixes of an honest receiver. -/
structure FGObservedOrderLaws (R : FGCoreReads P n Base Proposal Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P) : Prop where
  mono : ∀ i j x, x ∈ rho.honest → i ≤ j →
    FGBlock.Preceq (R.core (O.stateBefore i x)).fg.F (R.core (O.stateBefore j x)).fg.F ∧
      lexKey ((R.core (O.stateBefore i x)).fg.h_j, (R.core (O.stateBefore i x)).fg.J) ≤
        lexKey ((R.core (O.stateBefore j x)).fg.h_j, (R.core (O.stateBefore j x)).fg.J) ∧
      (R.core (O.stateBefore i x)).fg.h_max ≤ (R.core (O.stateBefore j x)).fg.h_max

/-- Row-pool (`rowHeld`) and proposal-pool retention between event prefixes, the separate
keep premise of the strict row-receipt consumers. -/
structure FGObservedPoolLaws (R : FGCoreReads P n Base Proposal Wire)
    (blockRows : P.State → List Wire) (rho : V2.D.Run V P) (O : FGExecutionObs V P) :
    Prop where
  row_keep : ∀ i j x a, i ≤ j →
    rowHeld R blockRows (O.stateBefore i x) a → rowHeld R blockRows (O.stateBefore j x) a
  proposals_keep : ∀ i j x, i ≤ j →
    (R.core (O.stateBefore i x)).proposals <+: (R.core (O.stateBefore j x)).proposals

/-- Local driver suppliers of the observed safety record on `Good` states: genesis-only
initial tree, store invariant, accepted-body view and row binding, and the agreement of
the safety and driver wire readers. -/
structure DriverSafetyStepLaws (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (Hv : FGHeightView (Fin n)) (f : FGFinalityView (Fin n))
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (Good : P.State → Prop) : Prop where
  initial_tf : ∀ B ∈ (R.core P.init).fg.TF, B = .genesis
  invariant : ∀ st, Good st → FGStoreInvariant Hv f (R.core st).fg
  view_blocks : ∀ st, Good st → H.acceptedBlocks st = (R.core st).fg.TF.image R.erase
  view_bodies : ∀ st, Good st → ∀ B,
    B ∈ H.acceptedBlocks st ↔ ∃ b ∈ H.acceptedBodies st, H.erase b = B
  body_rows : ∀ st, Good st → ∀ b ∈ H.acceptedBodies st, ∀ B ∈ (R.core st).fg.TF,
    R.erase B = H.erase b → B.rows = (W.bodyRows b).filterMap S.decode
  erase_reads : S.proposalErase = W.proposalErase
  row_reads : S.proposalRows = W.decodedRows

variable {LeafIn Latest : Type} {Leaf : V2.ProtocolSpecD LeafIn}

/-- E1F obligation (PC line): the observed safety record of the canonical driver observation
from the trace laws, the local step and safety laws and the accepted-body origin bridge. -/
def DriverObservedSafetyStatement (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (Hv : FGHeightView (Fin n)) (f : FGFinalityView (Fin n))
    (Good : P.State → Prop)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop :=
  DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  FGCoreLaws R → DriverCoreStepLaws R H D Step Good → DriverSafetyStepLaws R S Hv f H W Good →
  (∀ x, FGAcceptedBodyOrigin E rho H W (driverFGExecutionObs E rho F T Op) x) →
  FGObservedSafetyLaws R S Hv f H W rho (driverFGExecutionObs E rho F T Op)

theorem DriverObservedSafetyStatement_def (R : FGCoreReads P n Base Proposal Wire)
    (S : FGSafetyReads P n Wire) (Hv : FGHeightView (Fin n)) (f : FGFinalityView (Fin n))
    (Good : P.State → Prop)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    DriverObservedSafetyStatement R S Hv f Good (Leaf := Leaf) E rho H W D L Step F T Op Arrival
        Notify leafState leafWire ActualRead =
      (DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  FGCoreLaws R → DriverCoreStepLaws R H D Step Good → DriverSafetyStepLaws R S Hv f H W Good →
  (∀ x, FGAcceptedBodyOrigin E rho H W (driverFGExecutionObs E rho F T Op) x) →
  FGObservedSafetyLaws R S Hv f H W rho (driverFGExecutionObs E rho F T Op)) := rfl

/-- E1F obligation (PC line): observed order of the canonical driver observation from the order
of every executed honest microstep. -/
def DriverObservedOrderStatement (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop :=
  DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  (∀ kind x st st', x ∈ rho.honest → Step kind x st st' →
    FGBlock.Preceq (R.core st).fg.F (R.core st').fg.F ∧
      lexKey ((R.core st).fg.h_j, (R.core st).fg.J) ≤
        lexKey ((R.core st').fg.h_j, (R.core st').fg.J) ∧
      (R.core st).fg.h_max ≤ (R.core st').fg.h_max) →
  FGObservedOrderLaws R rho (driverFGExecutionObs E rho F T Op)

theorem DriverObservedOrderStatement_def (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    DriverObservedOrderStatement R (Leaf := Leaf) E rho H W D L Step F T Op Arrival
        Notify leafState leafWire ActualRead =
      (DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  (∀ kind x st st', x ∈ rho.honest → Step kind x st st' →
    FGBlock.Preceq (R.core st).fg.F (R.core st').fg.F ∧
      lexKey ((R.core st).fg.h_j, (R.core st).fg.J) ≤
        lexKey ((R.core st').fg.h_j, (R.core st').fg.J) ∧
      (R.core st).fg.h_max ≤ (R.core st').fg.h_max) →
  FGObservedOrderLaws R rho (driverFGExecutionObs E rho F T Op)) := rfl

/-- E1F obligation (PC line): row- and proposal-pool retention of the canonical driver
observation from retention by every executed microstep. -/
def DriverObservedPoolStatement (R : FGCoreReads P n Base Proposal Wire)
    (blockRows : P.State → List Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop :=
  DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  (∀ kind x st st' a, Step kind x st st' →
    rowHeld R blockRows st a → rowHeld R blockRows st' a) →
  (∀ kind x st st', Step kind x st st' → (R.core st).proposals <+: (R.core st').proposals) →
  FGObservedPoolLaws R blockRows rho (driverFGExecutionObs E rho F T Op)

theorem DriverObservedPoolStatement_def (R : FGCoreReads P n Base Proposal Wire)
    (blockRows : P.State → List Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Wire)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    DriverObservedPoolStatement R blockRows (Leaf := Leaf) E rho H W D L Step F T Op Arrival
        Notify leafState leafWire ActualRead =
      (DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  (∀ kind x st st' a, Step kind x st st' →
    rowHeld R blockRows st a → rowHeld R blockRows st' a) →
  (∀ kind x st st', Step kind x st st' → (R.core st).proposals <+: (R.core st').proposals) →
  FGObservedPoolLaws R blockRows rho (driverFGExecutionObs E rho F T Op)) := rfl

end AvailableChain.FGCompose
end

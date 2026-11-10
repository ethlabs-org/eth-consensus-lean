module
public import ConsensusLean.Spec.Shape.Compile
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Node engine carriers and wire data

The AC carriers depend on validator count, never on a proof that the count is positive.
The wire carries policy, not proofs of publication or AC correctness. -/

namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape
open Consensus.Model (Public)

/-- AC operations on fixed carriers. This constructor needs no carrier equalities. -/
structure Operations (P : Params) (S M Q : Type) where
  validPayload : Block P.n (List (FG.Att P.n)) Q → Prop
  validMsg : M → Prop
  holdsMsg : S → M → Prop
  genesisPayload : Q
  initial : S
  onMessage : Fin P.n → S → Frame P.n (List (FG.Att P.n)) Q → Time → M →
    S × List (Emission P.n (List (FG.Att P.n)) Q S M)
  onBlock : Fin P.n → S → Frame P.n (List (FG.Att P.n)) Q → Time →
    Block P.n (List (FG.Att P.n)) Q → S × List (Emission P.n (List (FG.Att P.n)) Q S M)
  onTick : Fin P.n → S → Frame P.n (List (FG.Att P.n)) Q → Time →
    S × List (Emission P.n (List (FG.Att P.n)) Q S M)
  proposal : S → Frame P.n (List (FG.Att P.n)) Q → Time →
    S × Option (DutyHead P.n (List (FG.Att P.n)) Q × Q)
  toFG : S → Frame P.n (List (FG.Att P.n)) Q → Time →
    S × Option (Block P.n (List (FG.Att P.n)) Q)
  confirmed : S → Frame P.n (List (FG.Att P.n)) Q → Time → Block P.n (List (FG.Att P.n)) Q
  head : S → Frame P.n (List (FG.Att P.n)) Q → Time → Block P.n (List (FG.Att P.n)) Q
  restart : Fin P.n → S → Frame P.n (List (FG.Att P.n)) Q → Time →
    S × List (Emission P.n (List (FG.Att P.n)) Q S M)

/-- Assemble the existing node interface without any equality transport. -/
def Operations.toAC {P : Params} {S M Q : Type} (A : Operations P S M Q) : NodeAC P :=
  ⟨S, M, Q, A.validPayload, A.validMsg, A.holdsMsg, A.genesisPayload, A.initial,
   A.onMessage, A.onBlock, A.onTick, A.proposal, A.toFG, A.confirmed, A.head, A.restart⟩

/-- Runtime parameters on the four-delay slot grid, with the validator count fixed literally. -/
def params (pub : Public) (hn : 1 ≤ pub.n) (g δt : Nat) : Params where
  n := pub.n
  hn := hn
  Δ := pub.ΔAC
  hΔ := pub.ΔAC_pos
  slotTime := fun s => 4 * pub.ΔAC * s
  slotTime_zero := by simp
  slotTime_strictMono := fun _ _ h =>
    mul_lt_mul_of_pos_left (by exact_mod_cast h) (by have := pub.ΔAC_pos; linarith)
  slotTime_public := fun s => ⟨4 * s, by ring⟩
  genesisRoot := g
  δt := δt

/-- Runtime data on count-indexed AC carriers. -/
structure Runtime (pub : Public) (hn : 1 ≤ pub.n) (S M Q : Type) where
  genesisRoot : Nat
  δt : Nat
  operations : Operations (params pub hn genesisRoot δt) S M Q

/-- Wire data for one runtime. The committee carrier is deliberately empty. -/
structure Wire {pub : Public} {hn : 1 ≤ pub.n} {S M Q : Type} (R : Runtime pub hn S M Q)
    (Info Body : Type) [DecidableEq Info] [Countable Info] where
  decBody : DecidableEq Body
  decMsg : DecidableEq M
  decHolds : ∀ s m, Decidable (R.operations.holdsMsg s m)
  signer : M → Fin pub.n
  encodeMsg : M → Body
  decodeMsg : Body → Option M
  encodeAtt : FG.Att pub.n → Body
  encodeInfo : List (FG.Att pub.n) → Q → Info
  decodeInfo : Info → Option (List (FG.Att pub.n) × Q)
  payloadMsgs : Q → List M
  payloadObjs : List (FG.Att pub.n) → Q →
    List (ShapeObj pub.n Empty Info Body)
  headerOf : R.operations.toAC.Blk → Header Info
  blockOf : Nat → Header Info → Fin pub.n → List (FG.Att pub.n) → Q →
    R.operations.toAC.Blk
  parentRef : Option Nat → ParentRef
  rootOf : List (Header Info × Nat) → Header Info → Option Nat
  canonEvent : List (Header Info × Nat) → ShapeObj pub.n Empty Info Body →
    Option (Node.Event R.operations.toAC)
  relayBody : Body
  forwardBody : Time → Body
  msgForwardBody : Time → M → Body
  dependencies : Model.DependencyPolicy (ShapeObj pub.n Empty Info Body)
  conflicts : ShapeObj pub.n Empty Info Body → ShapeObj pub.n Empty Info Body → Bool
  isFGAtt : ShapeObj pub.n Empty Info Body → Prop
  grid : TimeGrid
  proposerSel : Nat → Model.SelSpec pub.n
  pollSel : Model.SelSpec pub.n
  order : List (Step Empty)
  deliverOrder : List (Step Empty)
  drain : List Body → List Body × List Body

end Consensus.Goldilocks.NodeEngine

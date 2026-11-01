module
public import AvailableChainFGCompose.Statements.ResetHistory

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface P)
variable (entry : Wire → Option (Height × BlockId))
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → (FGBlock (Fin n)) → Wire → Bool)

structure FGACServiceReads (V : Type) where
  honest : V → Prop
  proposal : Slot → Block → Prop
  proposalTime : Slot → Time
  voteTime : Slot → Time
  gateTime : Slot → Time
  gateLabel : Nat → Slot
  actionHeadLabel : Nat → Slot
  actionTime : Nat → Time
  proposalScope : Slot → Block → Prop
  sourceScope : V → Nat → Block → Prop
  headScope : V → Slot → Prop
  gateScope : V → Slot → Prop
  actionScope : V → Nat → Prop
  headAtLabel : V → Slot → Option Block
  actionHead : V → Nat → Option (Option Block)
  gate : V → Slot → Option (Option Block)
  source : V → Nat → Option (Option Block)
  parent : Slot → Option Block
  gateFloor : V → Slot → Option Block
  frame : V → Nat → Block → Prop
  below : Block → Block → Prop

def InSuffix (pt : FGServicePoint) (horizon t : Time) : Prop :=
  pt.serviceStart ≤ t ∧ t ≤ horizon

structure FGACServiceObservationLaws (A : FGACServiceReads V)
    (T : FGTiming) (R : FGCoreReads P n Base Proposal Wire)
    (O : FGObservationReads R) (E : Generic.Env V) (rho : V2.D.Run V P)
    (I : V2.D.Interface P)
    (gateObs : V → Slot → Option (Option Block))
    (gateFloorObs : V → Slot → Option Block)
    (parentObs : Slot → Option Block)
    (proposalScopeObs : Slot → Block → Prop)
    (sourceScopeObs : V → Nat → Block → Prop)
    (headScopeObs gateScopeObs : V → Slot → Prop)
    (actionScopeObs : V → Nat → Prop) : Prop where
  honest_eq : ∀ x, A.honest x ↔ x ∈ rho.honest
  proposal_eq : ∀ s Q, A.proposal s Q ↔ HonestProposal E rho I s Q
  proposal_time : ∀ s, A.proposalTime s = T.proposal s
  duty_time : ∀ s, T.proposal s = V2.D.proposalTime I s
  vote_time : ∀ s, A.voteTime s = T.vote s
  gate_time : ∀ s, A.gateTime s = T.gate s
  action_time : ∀ q, A.actionTime q = T.action q
  gate_label : ∀ q, A.gateLabel q = q * T.roundSlots
  action_head_label : ∀ q, A.actionHeadLabel q = q * T.roundSlots + 1
  head_eq : ∀ x s, A.headAtLabel x s =
    (postClock E rho x (T.vote s)).map (fun nd => R.headVote nd s)
  action_head_eq : ∀ x q, A.actionHead x q =
    (postClock E rho x (T.action q)).map (fun nd => (R.finalityHead nd).map R.erase)
  source_eq : ∀ x q, A.source x q =
    (postClock E rho x (T.action q)).map (fun nd => (R.source nd).map R.erase)
  gate_eq : ∀ x s, A.gate x s = gateObs x s
  parent_eq : ∀ s, A.parent s = parentObs s
  floor_eq : ∀ x s, A.gateFloor x s = gateFloorObs x s
  below_eq : ∀ B C, A.below B C ↔ Block.Preceq B C
  proposal_scope : ∀ s Q, A.proposalScope s Q ↔ proposalScopeObs s Q
  source_scope : ∀ x q C, A.sourceScope x q C ↔ sourceScopeObs x q C
  head_scope : ∀ x s, A.headScope x s ↔ headScopeObs x s
  gate_scope : ∀ x s, A.gateScope x s ↔ gateScopeObs x s
  action_scope : ∀ x q, A.actionScope x q ↔ actionScopeObs x q
  frame_eq : ∀ x q B, A.frame x q B ↔
    ∀ nd, postClock E rho x (T.action q) = some nd →
      ∃ D, R.erase D = B ∧ D ∈ (R.core nd).fg.TF ∧
        FGBlock.Preceq (O.controls nd).F D ∧
        FGBlock.Preceq (O.controls nd).Z D ∧
        (O.controls nd).lo ≤ (O.height D).h

structure FGACServiceLaws (A : FGACServiceReads V)
    (pt : FGServicePoint) (recoveryStart horizon : Time) : Prop where
  source_chain : ∀ x y r q C D,
    A.honest x → A.honest y → A.sourceScope x r C → A.sourceScope y q D →
    InSuffix pt horizon (A.actionTime r) → InSuffix pt horizon (A.actionTime q) →
    A.source x r = some (some C) → A.source y q = some (some D) →
    Block.Compatible C D
  exact_head : ∀ s Q x, A.proposal s Q → A.proposalScope s Q →
    pt.serviceStart ≤ A.proposalTime s → A.voteTime s ≤ horizon →
    A.honest x → A.headScope x s → A.headAtLabel x s = some Q
  exact_gate : ∀ s Q x, A.proposal s Q → A.proposalScope s Q →
    pt.serviceStart ≤ A.proposalTime s → A.gateTime s ≤ horizon →
    A.honest x → A.gateScope x s → A.gate x s = some (some Q)
  opening_source : ∀ q Q x, A.proposal (A.gateLabel q) Q →
    A.proposalScope (A.gateLabel q) Q →
    pt.serviceStart ≤ A.proposalTime (A.gateLabel q) →
    A.actionTime q ≤ horizon → A.honest x → A.actionScope x q →
    A.gateScope x (A.gateLabel q) → A.source x q = some (some Q)
  proposal_later_head : ∀ s Q x i H,
    A.proposal s Q → A.proposalScope s Q → pt.serviceStart ≤ A.proposalTime s →
    A.honest x → A.headScope x i → s + 1 ≤ i → A.voteTime i ≤ horizon →
    A.headAtLabel x i = some H → A.below Q H
  source_next_head : ∀ y r C x i H,
    A.honest y → A.sourceScope y r C → A.source y r = some (some C) →
    InSuffix pt horizon (A.actionTime r) → A.honest x → A.headScope x i →
    A.gateLabel r + 1 ≤ i → A.voteTime i ≤ horizon →
    A.headAtLabel x i = some H → A.below C H
  covered_source : ∀ s Q q x,
    A.proposal s Q → A.proposalScope s Q → pt.serviceStart ≤ A.proposalTime s →
    Q ≠ .genesis → s < A.gateLabel q →
    A.gateTime s ≤ A.actionTime q → InSuffix pt horizon (A.actionTime q) →
    pt.reset.sStar ≤ A.gateLabel q → recoveryStart ≤ A.voteTime (A.gateLabel q) →
    (∀ y, A.honest y → ∃ H, A.headScope y (A.gateLabel q) ∧
      A.headAtLabel y (A.gateLabel q) = some H ∧ A.below Q H) →
    (∀ y F, A.honest y → A.gateFloor y (A.gateLabel q) = some F → A.below F Q) →
    A.honest x → A.actionScope x q → A.frame x q Q →
    ∃ C, A.source x q = some (some C) ∧ A.below Q C
  parent_transfer : ∀ x r C s Q,
    A.honest x → A.sourceScope x r C → A.source x r = some (some C) →
    InSuffix pt horizon (A.actionTime r) → A.proposal s Q → A.proposalScope s Q →
    A.gateLabel r + 2 ≤ s → A.proposalTime s ≤ horizon → A.below C Q.parent

def FGHistoricalHighTransfer (R : FGCoreReads P n Base Proposal Wire)
    (O : FGObservationReads R) (T : FGTiming) (E : Generic.Env V)
    (rho : V2.D.Run V P) (I : V2.D.Interface P)
    (pt : FGServicePoint) (horizon : Time) : Prop :=
  ∀ x r C, x ∈ rho.honest →
    (postClock E rho x (T.action r)).map R.source = some (some C) →
    pt.reset.M + 1 ≤ (O.height C).h → T.action r ≤ horizon →
    ∀ v Q, HonestProposal E rho I v Q → T.proposal v ≤ horizon →
      r * T.roundSlots + 2 ≤ v → Block.Preceq (R.erase C) Q.parent

/-- The label floor is not part of the historical chain (false for PC-SA sources of PC holders
without an FG identity; FG-SA keeps it in THigh). -/
def FGHistoricalHighChain (R : FGCoreReads P n Base Proposal Wire)
    (O : FGObservationReads R) (T : FGTiming) (E : Generic.Env V)
    (rho : V2.D.Run V P) (pt : FGServicePoint) (horizon : Time) : Prop :=
  ∀ x y r r' C D, x ∈ rho.honest → y ∈ rho.honest →
    (postClock E rho x (T.action r)).map R.source = some (some C) →
    (postClock E rho y (T.action r')).map R.source = some (some D) →
    pt.reset.M + 1 ≤ (O.height C).h → pt.reset.M + 1 ≤ (O.height D).h →
    T.action r ≤ horizon → T.action r' ≤ horizon →
    Block.Compatible (R.erase C) (R.erase D) ∧
      Block.Compatible (R.erase C) pt.reset.source

-- HonestCarrier, heldAtProposal, ValidForParent, onParentChain, HeldBefore.
def TRowsSelect : Prop := ∀ s Q rows j y r (a : Wire),
  HonestCarrier E rho I carrier s Q rows → HonestRowAt S E rho T j y r a
    → ValidForParent E rho I parentFG validFor s Q a
    → heldAtProposal R E rho I blockWireRows s a → a ∈ rows
    ∨ onParentChain E rho I chainWireRows s Q a

def TRowsSync (deltaF : Time) : Prop := ∀ j y r (a : Wire),
  HonestRowAt S E rho T j y r a → E.t_GST ≤ T.action r →
  (T.action r + deltaF ≤ rho.horizon →
    ∀ x ∈ rho.honest, HeldBefore R E rho blockWireRows x a (T.action r + deltaF)) ∧
  (∀ s Q rows, HonestCarrier E rho I carrier s Q rows
    → ValidForParent E rho I parentFG validFor s Q a →
    T.action r + deltaF ≤ T.proposal s → a ∈ rows ∨ onParentChain E rho I chainWireRows s Q a)

def TRowsReceipt (deltaF : Time) : Prop := ∀ j y r (a : Wire),
  HonestRowAt S E rho T j y r a → max (T.action r) E.t_GST + deltaF ≤ rho.horizon →
  ∀ x ∈ rho.honest, HeldBefore R E rho blockWireRows x a (max (T.action r) E.t_GST + deltaF)

end AvailableChain.FGCompose
end

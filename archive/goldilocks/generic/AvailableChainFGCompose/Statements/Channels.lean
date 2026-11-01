module
public import AvailableChainFGCompose.Statements.Selection
public import AvailableChainFGCompose.Statements.Timing
public import AvailableChainGeneric.Statements.V2.Duty.Counts -- shake: keep (re-export)

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
variable (signer : Wire → Option (Fin n)) (valid : Wire → Bool)
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (storedCarrier : P.State → (FGBlock (Fin n)) → Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → (FGBlock (Fin n)) → Height × BlockId)
variable (validFor : P.State → Slot → (FGBlock (Fin n)) → Wire → Bool)

-- Exact proposal meaning from FS/Statements/Counts.lean:18.
-- Do not substitute PCCompanion.HonestProposalAt: that has a different
-- explicit signature witness and needs an additional correspondence proof.
def HonestProposal (E : Generic.Env V) (rho : V2.D.Run V P)
    (I : V2.D.Interface P) (s : Slot) (B : Block) : Prop :=
  Gen.V2.Duty.HonestSlot rho I s ∧ ∃ o,
    V2.D.Run.emits E rho (V2.D.proposerOf rho I s) o (V2.D.proposalTime I s) ∧
    I.block o.payload = some B

def certified (W : (FGBlock (Fin n))) : Set (FGBlock (Fin n)) := {e | ∃ U, FGBlock.Preceq U W ∧
  (e = (O.height U).J ∨ e = (O.finality U).F ∨
    (e = (O.height U).T_h ∧ (O.height U).h < (O.height W).h))}

def namedEntry : NamedHeightPair → Option (Height × BlockId)
  | .empty => none
  | .vote h e _ => some (h, e)

def EntryBelow (e : Height × BlockId) (B : (FGBlock (Fin n))) : Prop :=
  ∃ X, FGBlock.Preceq X B ∧ ((O.height X).h, X.root) = e

def RowSigner (a : Wire) (x : V) : Prop :=
  ∃ i, signer a = some i ∧ safetyHolder S rho i = x

def HonestRowAt (j : Nat) (y : V) (r : Nat) (a : Wire) : Prop :=
  y ∈ rho.honest ∧ rho.events[j]? = some (.tick y (T.action r)) ∧
    S.encode a ∈ V2.D.Run.emitsAt E rho j

def HonestRowBefore (k : Nat) (y : V) (r : Nat) (a : Wire) : Prop :=
  ∃ j < k, HonestRowAt S E rho T j y r a

def RowComplete (x : V) (a : Wire) : Prop :=
  valid a = true ∧ RowSigner S rho signer a x

def HeldAt (i : Nat) (x : V) (W : (FGBlock (Fin n))) : Prop :=
  x ∈ rho.honest ∧ W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF

def BlockInRunBefore (i : Nat) (W : (FGBlock (Fin n))) : Prop :=
  ∃ j < i, ∃ x, HeldAt R E rho j x W

def HonestCarrier (s : Slot) (Q : Block) (rows : List Wire) : Prop :=
  HonestProposal E rho I s Q ∧
  ∃ o, V2.D.Run.emits E rho (V2.D.proposerOf rho I s) o
    (V2.D.proposalTime I s) ∧ carrier o s Q rows

def actionSourceFG (x : V) (r : Nat) : Option (Option (FGBlock (Fin n))) :=
  (postClock E rho x (T.action r)).map R.source

def actionHead (x : V) (r : Nat) : Option (Option (FGBlock (Fin n))) :=
  (postClock E rho x (T.action r)).map R.finalityHead

def actionTriple (Q : FGSelectionReads P n) (x : V) (r : Nat) : Option HeadFields :=
  (postClock E rho x (T.action r)).map (fun nd => (Q.clientInputs nd).2)

def proposalStateAt (s : Slot) : Option P.State :=
  postClock E rho (V2.D.proposerOf rho I s) (V2.D.proposalTime I s)

def proposalHeadAt (head : P.State → Slot → Block) (s : Slot) : Option Block :=
  (proposalStateAt E rho I s).map (fun nd => head nd s)

def headAtLabel (x : V) (s : Slot) : Option Block :=
  (postClock E rho x (T.vote s)).map (fun nd => R.headVote nd s)

def rowHeld (nd : P.State) (a : Wire) : Prop :=
  a ∈ (R.core nd).rowPool ∨ a ∈ blockWireRows nd

def heldAtProposal (s : Slot) (a : Wire) : Prop :=
  ∃ nd, proposalStateAt E rho I s = some nd ∧ rowHeld R blockWireRows nd a

def onParentChain (s : Slot) (Q : Block) (a : Wire) : Prop :=
  ∃ nd, proposalStateAt E rho I s = some nd ∧ a ∈ chainWireRows nd Q.parent

def HeldBefore (x : V) (a : Wire) (d : Time) : Prop :=
  Gen.V2.Duty.HoldsBefore E rho (fun nd => rowHeld R blockWireRows nd a) d x

def ValidForParent (s : Slot) (Q : Block) (a : Wire) : Prop :=
  ∃ nd H, proposalStateAt E rho I s = some nd ∧
    parentFG nd Q.parent = some H ∧ validFor nd s H a = true

def HeightMatch (s : Slot) (Q : Block) (a : Wire) : Prop :=
  ∃ nd H, proposalStateAt E rho I s = some nd ∧
    parentFG nd Q.parent = some H ∧ entry a = some (parentHeight nd s H)

end AvailableChain.FGCompose
end

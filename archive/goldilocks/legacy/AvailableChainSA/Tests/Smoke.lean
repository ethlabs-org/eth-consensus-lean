module
public import AvailableChainSA.Model.Protocol
public meta import AvailableChainSA.Model.Protocol

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/
namespace AvailableChain.SA.Tests
open AvailableChain.Generic

def p : Params := ⟨1, 4, 3, 11, by decide, by decide, by decide, by decide⟩
def B : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0
def C : Block := .node B 2 (nodeRoot B.root 2 0) 0
/-- A sibling of `B` at slot 1 with a different body. -/
def X : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 1) 1

/-- The derived roots keep the old sibling order (`⟨1⟩ < ⟨3⟩`). No check below
compares the two roots: every walk has at most one eligible child of genesis. -/
example : B.root < X.root := by decide

def batch (st : State 4) (r : Slot) (target : Block) (seats : List (Fin 4)) : State 4 :=
  let votes := seats.map (fun i => (⟨.seat r i, .head target⟩ : Wire 4))
  { st with now := gateTime p r
            blocks := [.genesis, B, C, X]
            blockStamp := [(.genesis, 0), (B, 4), (C, 8), (X, 4)]
            votes := votes
            voteStamp := votes.map (fun o => (o, voteTime p r)) }

def low : State 4 := gate p (batch (initial 4) 1 B [0]) 1

def stableWithoutLease : Bool :=
  low.stableRecord == B && low.obligations.isEmpty && savedGenuine low 1 == some (some B)

def fastAtEquality : Bool :=
  let st := gate p (batch (initial 4) 1 B [0, 1]) 1
  st.stableRecord == B && st.obligations == [(B, 2, 21)]

def slow : State 4 :=
  let st := gate p (batch low 2 B [0]) 2
  gate p (batch st 3 B [0]) 3

def slowAfterThree : Bool := slow.obligations == [(B, 2, 29)]

def failedLabelBreaks : Bool :=
  let empty := gate p { low with now := gateTime p 2, votes := [], voteStamp := [] } 2
  let missing := gate p (batch low 3 B [0]) 3
  let failed := gate p (batch empty 3 B [0]) 3
  savedGenuine empty 2 == some none && missing.obligations.isEmpty && failed.obligations.isEmpty

def vetoStillSaves : Bool :=
  let st := gate p (batch { obligations := [(X, 2, 21)] } 1 B [0]) 1
  st.stableRecord == .genesis && savedGenuine st 1 == some (some B) &&
    st.obligations == [(X, 2, 21)]

def ancestorDoesNotRenewChild : Bool :=
  let st := gate p (batch (initial 4) 2 C [0, 1]) 2
  let next := gate p (batch st 3 B [0, 1]) 3
  deadlineOf next C 2 == some 25 && deadlineOf next B 2 == some 29 &&
    next.stableRecord == C

def releaseAtEquality : Bool :=
  let st := batch { obligations := [(B, 2, 29)] } 3 X [0, 1]
  let one := batch { obligations := [(B, 2, 29)] } 3 X [0]
  (release p st 3).obligations.isEmpty && !(release p one 3).obligations.isEmpty

def expiryRetainsHistory : Bool :=
  let st := expire slow 29
  st.obligations.isEmpty && st.stableRecord == B && st.genuine == slow.genuine

example : stableWithoutLease = true := by decide
example : fastAtEquality = true := by decide
example : slowAfterThree = true := by decide
example : failedLabelBreaks = true := by decide
example : vetoStillSaves = true := by decide
example : ancestorDoesNotRenewChild = true := by decide
example : releaseAtEquality = true := by decide
example : expiryRetainsHistory = true := by decide

#eval [stableWithoutLease, fastAtEquality, slowAfterThree, failedLabelBreaks,
  vetoStillSaves, ancestorDoesNotRenewChild, releaseAtEquality, expiryRetainsHistory]

end AvailableChain.SA.Tests
end

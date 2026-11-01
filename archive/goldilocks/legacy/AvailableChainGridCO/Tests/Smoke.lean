module
public import AvailableChainGridCO.Model.Protocol
public import AvailableChainGridCO.Proofs.Handling
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.GridCO.Tests

open AvailableChain
open AvailableChain.Generic
open AvailableChain.GridCO

def smokeParams : Params where
  Δ := 1
  n := 1
  m := 2
  η := 4
  grid := {1}
  θ_R := 1 / 2
  deltaPos := by norm_num
  mLarge := by norm_num
  one_mem := by decide
  levels_pos := by decide
  levels_le := by decide
  etaNonneg := by norm_num
  thetaLower := by norm_num
  thetaUpper := by norm_num
  gridMatchesTheta := by
    intro a h ha hh hθ
    have haQ : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
    interval_cases h
    · norm_num at hθ
      nlinarith
    · norm_num at hθ
      nlinarith

/-- One honest validator and one seat. The seat signs at its public duty. -/
def tinyRun : Run (Fin 1) (gridCO smokeParams) where
  honest := {0}
  horizon := 2
  events := [.tick 0 0, .tick 0 1, .tick 0 2]
  seatOf := fun _ => Equiv.refl (Fin 1)
  proposerOf := fun _ => 0

def tinyHeadCount : Nat :=
  (Run.emittedAt (gridCO smokeParams)
    { Δ := 1, Δ_pos := by norm_num, t_GST := 0,
      t_GST_nonneg := by norm_num, awake := fun _ _ => true }
    tinyRun 1 0 1).length

/-- Expiry at the deadline removes the entry before an act at that tick. -/
def tinyExpiry : Bool :=
  let b := Block.node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0
  let st : State 1 := { obligations := [(b, 1, 5)] }
  (expire st 4).obligations.length == 1 &&
    (expire st 5).obligations.isEmpty

def blockB : Block := Block.node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0
def blockC : Block := Block.node .genesis 2 (nodeRoot Block.genesis.root 2 0) 0

/-- The derived roots keep the old literal order (`⟨1⟩ < ⟨2⟩`). No check below
compares the two roots: no walk has both blocks as eligible children. -/
example : blockB.root < blockC.root := by decide

def headB : Wire 1 := ⟨.seat 1 0, .head blockB⟩
def headC : Wire 1 := ⟨.seat 2 0, .head blockC⟩

/-- A genuine one-seat gate writes the block's level-1 obligation. -/
def tinyGateState : State 1 :=
  { now := 10
    blocks := [.genesis, blockB]
    blockStamp := [(.genesis, 0), (blockB, 4)]
    votes := [headB]
    voteStamp := [(headB, 5)] }

def tinyGatePass : Bool :=
  let st := gate smokeParams tinyGateState 1
  st.stableRecord == blockB && deadlineOf st blockB 1 == some 17

/-- One resolved conflicting HEAD releases a level-1 obligation. -/
def tinyReleaseState : State 1 :=
  { now := 13
    blocks := [.genesis, blockB, blockC]
    blockStamp := [(.genesis, 0), (blockB, 4), (blockC, 9)]
    votes := [headC]
    voteStamp := [(headC, 10)]
    obligations := [(blockB, 1, 17)] }

def tinyReleasePass : Bool :=
  (release smokeParams tinyReleaseState 2).obligations.isEmpty

/-- The source keeps at most two distinct HEADs for one seat and drops a
label that is older than the previous slot. -/
def ingressPass : Bool :=
  let first : Wire 1 := ⟨.seat 1 0, .head blockB⟩
  let second : Wire 1 := ⟨.seat 1 0, .head blockC⟩
  let third : Wire 1 := ⟨.seat 1 0, .head .genesis⟩
  let st : State 1 := { now := 5 }
  let two := admitVote smokeParams (admitVote smokeParams st first) second
  (admitVote smokeParams two third).votes.length == 2 &&
    (admitVote smokeParams { now := 13 } first).votes.isEmpty

/-- A repeated block body does not admit a second proposal or its carried
HEADs. A HEAD outside the stored tree contributes no support score. -/
def blockAdmissionPass : Bool :=
  let first : Wire 1 := ⟨.proposer 1, .proposal blockB [] []⟩
  let other : Wire 1 := ⟨.proposer 1, .proposal blockB [⟨.seat 0 0, .genesis⟩] []⟩
  let st := admitProposal smokeParams ({ now := 4 } : State 1) first blockB []
  let again := admitProposal smokeParams st other blockB [⟨.seat 0 0, .genesis⟩]
  let badChild := Block.node blockB 1 (nodeRoot blockB.root 1 0) 0
  let badParentSlot : Wire 1 := ⟨.proposer 1, .proposal badChild [] []⟩
  let wrongSigner : Wire 1 := ⟨.proposer 1, .proposal blockC [] []⟩
  again.proposals.length == 1 && again.votes.isEmpty &&
    processed again other &&
    (admitProposal smokeParams st badParentSlot badChild []).blocks.length == 2 &&
    (admitProposal smokeParams { st with now := 8 } wrongSigner blockC []).blocks.length == 2 &&
    goldfishScore [.genesis] [headB] [headB] blockB == 0 &&
    goldfishScore [.genesis, blockB] [headB] [headB] blockB == 1

/-- Rejected and duplicate envelopes do not call carried handlers.
An admitted envelope calls only raw HEAD handlers, even if the child
handler itself rejects an old label. Direct calls always count. -/
def handlingPass : Bool :=
  let row : HeadWire 1 := ⟨.seat 1 0, blockB⟩
  let envelope : Wire 1 := ⟨.proposer 2, .proposal blockC [row] []⟩
  let metadata : Wire 1 := ⟨.proposer 2, .proposal blockC [] [row]⟩
  let before : State 1 := { now := 5 }
  let ready : State 1 := { now := 8 }
  let stored := process smokeParams ready envelope
  let late : State 1 := { now := 16 }
  !decide (handles smokeParams before envelope headB) &&
    decide (carries envelope headB) &&
    decide (handles smokeParams before envelope envelope) &&
    decide (handles smokeParams ready envelope headB) &&
    !decide (handles smokeParams stored envelope headB) &&
    !decide (handles smokeParams ready metadata headB) &&
    decide (handles smokeParams late envelope headB) &&
    !(processed (process smokeParams late envelope) headB)

example : tinyHeadCount = 1 := by decide
example : tinyExpiry = true := by decide
example : tinyGatePass = true := by decide
example : tinyReleasePass = true := by decide
example : ingressPass = true := by decide
example : blockAdmissionPass = true := by decide
example : handlingPass = true := by decide
example : stable (Run.readAt (gridCO smokeParams) tinyRun 2 0) = .genesis := by decide

end AvailableChain.GridCO.Tests
end

module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

public section

/-! # P-U execution witness investigation

All three execution candidates remain unresolved: `pu_cex_proposal_floor_top`,
`pu_cex_leaf8_low`, and `pu_cex_viableHead_persists`. The declarations below are client and
transition checks, not reachable counterexamples and not proofs of the old facts.

The stock `ConflictRun` cannot be transported as a witness: its six validators have quorum
four, all four quorum signers are faulty, and its honest set is `{4, 5}`. Thus its fault count
four breaks the required strict bound `f < 2q - n = 2`. No test module is imported here.

At four validators and quorum three, targeting J and then timing out on a sibling entry is
allowed by the real client record. This does not supply either source through `acToFG'`:
that still requires honest node calls, confirmations, and their resulting source choices.
For the proposal candidates, a confirmation must write the lock and the lock must survive
the whole previous-slot pool's unlock before the proposal. Payload length alone does not
bound the child's height: the parent's accumulated participation counts too.

For persistence, a pair of stores is not sufficient: a constant honest set, the fault bound,
NoCollRun, every honest cut of the old FrameWindow, and the actual AC call at the first cut
must all be supplied by a built GoldilocksRun'. None is assumed as a supplier here.
-/

namespace Consensus.Goldilocks.Shadow.PU.Witness

open FG

abbrev gp : FGParams := ⟨4, by decide, 2, 0⟩

def entry (root : Nat) : ChainState 4 :=
  { ChainState.init gp with L := root, s := 1, h := 2, Th := root, ThSlot := 1 }

def target : Att 4 := ⟨1, 2, 10, false, none⟩

def timeout : Att 4 := ⟨1, 2, 20, true, none⟩

/-- The actual client can target one entry and then time out on another at the same height.
This is a local client certificate only; neither entry is asserted reachable. -/
theorem target_then_sibling_timeout :
    Record.empty.createAtt 1 (entry 10) =
      some (target, Record.empty.recordAtt target) ∧
    (Record.empty.recordAtt target).createAtt 1 (entry 20) =
      some (timeout, (Record.empty.recordAtt target).recordAtt timeout) := by
  constructor <;> rfl

def twoParticipants : ChainState 4 :=
  { entry 10 with target := {0, 1}, prog := {0, 1} }

def thirdVote : Att 4 := ⟨2, 2, 10, false, none⟩

/-- One payload attestation, fewer than quorum, still advances when the parent has two.
Any low-child witness must bound cumulative participation, not just its own payload. -/
theorem cumulative_participation_advances :
    [thirdVote].length < gp.q ∧
      ((gp.stateTransition twoParticipants ⟨30, 2, 0, [thirdVote]⟩).map
        ChainState.h) = some 3 := by
  decide

/-- The same one-attestation payload does not advance a parent with no participation. -/
theorem fresh_participation_stays :
    ((gp.stateTransition (entry 10) ⟨30, 2, 0, [thirdVote]⟩).map
      ChainState.h) = some 2 := by
  decide

end Consensus.Goldilocks.Shadow.PU.Witness

end

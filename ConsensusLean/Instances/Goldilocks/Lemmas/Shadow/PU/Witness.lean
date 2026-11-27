module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Client

public section

/-! # P-U execution witness investigation

Classification of the three V-A7 candidates:

* `pu_cex_proposal_floor_top`: **proved**, no counterexample exists. The stock
  `floor_le_warm_proposal_at` holds over shadow runs:
  `Consensus.Goldilocks.Shadow.PU.Witness.floor_le_warm_proposal_at'` (`Shadow/PU/WitnessFloor`).
  The paper trace assumed the honest proposal on a height-`h_j` head above `J` carries fewer
  than `q` attestations; `proposal_attestations` includes `J`'s whole justification quorum (and
  the predecessor's finality quorum), so it crosses (`proposal_crosses`).
* `pu_cex_leaf8_low`: **proved**, by the same supplier:
  `Consensus.Goldilocks.Shadow.PU.Witness.rounds_le_warm_proposal_at'`.
* `pu_cex_viableHead_persists`: **unresolved**. The old-window fact is superseded by the proved
  `Generic.FrameWindow.viableHead_persists'` (V-B4) and no shadow theorem uses it;
  whether it needs a
  verdict is a scope decision with the owner. A paper candidate run (not built) is recorded in
  the lane report.

The declarations below are client and transition checks used for the persistence candidate.

The stock `ConflictRun` cannot be transported as a witness: its six validators have quorum
four, all four quorum signers are faulty, and its honest set is `{4, 5}`. Thus its fault count
four breaks the required strict bound `f < 2q - n = 2`. No test module is imported here.

At four validators and quorum three, targeting J and then timing out on a sibling entry is
allowed by the real client record. This does not supply either source through `acToFG'`:
that still requires honest node calls, confirmations, and their resulting source choices.
Payload length alone does not bound a child's height: the parent's accumulated participation
counts too.

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

/-- Three real client votes on the common genesis entry, shared by both sibling chains. -/
def genesisVotes : List (Att 4) :=
  ([0, 1, 2] : List (Fin 4)).map fun v => ⟨v, 1, 0, false, none⟩

/-- The height-two entry state of a sibling, produced from the common genesis quorum. -/
def siblingState (root : Nat) : ChainState 4 :=
  (gp.stateTransition (ChainState.init gp) ⟨root, 2, 0, genesisVotes⟩).getD
    (ChainState.init gp)

/-- Both siblings enter height two while still justifying only genesis. -/
theorem shared_genesis_entries :
    ∀ root, (siblingState root).h = 2 ∧ (siblingState root).Th = root ∧
      (siblingState root).hj = 1 ∧ (siblingState root).J = 0 := by
  intro root
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The actual genesis client produces each attestation used in the shared quorum. -/
theorem genesis_votes_created :
    ∀ v : Fin 4, Record.empty.createAtt v (ChainState.init gp) =
      some (⟨v, 1, 0, false, none⟩,
        Record.empty.recordAtt (⟨v, 1, 0, false, none⟩ : Att 4)) := by
  intro v
  rfl

/-- Votes on J's entry finalize genesis and justify J at height two. -/
def justifyVotes : List (Att 4) :=
  ([0, 1, 2] : List (Fin 4)).map fun v => ⟨v, 2, 10, false, some (1, 0)⟩

/-- The competing sibling is crossed by timeouts, not target votes. -/
def siblingTimeouts : List (Att 4) :=
  ([0, 1, 2] : List (Fin 4)).map fun v => ⟨v, 2, 20, true, some (1, 0)⟩

/-- At slot four, the J branch justifies height two while the sibling only times out.
These are transition certificates; the honest AC source/signing prefix is still missing. -/
theorem justify_and_timeout_crossings :
    ((gp.stateTransition (siblingState 10) ⟨30, 4, 0, justifyVotes⟩).map
      (fun s => (s.h, s.hj, s.J))) = some (3, 2, 10) ∧
    ((gp.stateTransition (siblingState 20) ⟨40, 4, 0, siblingTimeouts⟩).map
      (fun s => (s.h, s.hj, s.J))) = some (3, 1, 0) := by
  decide

/-- Each signer first targets J's real entry and then times out on its sibling's entry,
starting with the record left by its genesis signature. This checks the finality pair too. -/
theorem sibling_votes_created (v : Fin 4) :
    let g : Att 4 := ⟨v, 1, 0, false, none⟩
    let j : Att 4 := ⟨v, 2, 10, false, some (1, 0)⟩
    let e : Att 4 := ⟨v, 2, 20, true, some (1, 0)⟩
    (Record.empty.recordAtt g).createAtt v (siblingState 10) =
      some (j, (Record.empty.recordAtt g).recordAtt j) ∧
    ((Record.empty.recordAtt g).recordAtt j).createAtt v (siblingState 20) =
      some (e, ((Record.empty.recordAtt g).recordAtt j).recordAtt e) := by
  constructor <;> rfl

/-- The off-J branch after its first timeout crossing. -/
def contestBranch : ChainState 4 :=
  (gp.stateTransition (siblingState 20) ⟨40, 4, 0, siblingTimeouts⟩).getD
    (ChainState.init gp)

/-- A second timeout quorum creates the gap without raising justification. -/
def nextTimeouts : List (Att 4) :=
  ([0, 1, 2] : List (Fin 4)).map fun v => ⟨v, 3, 40, true, none⟩

/-- The persistence candidate's second crossing: height four, still no non-genesis J
on the off-J branch. A store holding the other branch can retain its height-two J. -/
theorem gap_timeout_crossing :
    ((gp.stateTransition contestBranch ⟨50, 6, 0, nextTimeouts⟩).map
      (fun s => (s.h, s.hj, s.J))) = some (4, 1, 0) := by
  decide

/-- A timeout at height three requires a prior target of the other height-three entry.
The earlier height-two sibling timeout suppresses the J finality pair, so it is `none`. -/
theorem gap_votes_created (v : Fin 4) :
    let g : Att 4 := ⟨v, 1, 0, false, none⟩
    let j : Att 4 := ⟨v, 2, 10, false, some (1, 0)⟩
    let e : Att 4 := ⟨v, 2, 20, true, some (1, 0)⟩
    let r := ((Record.empty.recordAtt g).recordAtt j).recordAtt e
    let a : Att 4 := ⟨v, 3, 30, false, none⟩
    let b : Att 4 := ⟨v, 3, 40, true, none⟩
    let s := (gp.stateTransition (siblingState 10) ⟨30, 4, 0, justifyVotes⟩).getD
      (ChainState.init gp)
    r.createAtt v s = some (a, r.recordAtt a) ∧
      (r.recordAtt a).createAtt v contestBranch =
        some (b, (r.recordAtt a).recordAtt b) := by
  constructor <;> rfl

end Consensus.Goldilocks.Shadow.PU.Witness

end

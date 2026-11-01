module
public import AvailableChainSAPC.Model.Protocol
public meta import AvailableChainSAPC.Model.Protocol

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/
namespace AvailableChain.SAPC.Tests

def p : Params := ⟨4, 4, 2, 28, by decide, by decide, by decide, by decide⟩
def x : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0
def c : Block := .node x 2 (nodeRoot x.root 2 0) 0
def y : Block := .node .genesis 5 (nodeRoot Block.genesis.root 5 0) 0
def d : Block := .node x 9 (nodeRoot x.root 9 0) 0

/-- The derived roots keep the old literal sibling orders (x ⟨1⟩ < y ⟨5⟩;
c ⟨2⟩ < d ⟨9⟩ < the slot-4 child ⟨44⟩ of `carriedDisableCheck`). No check below
depends on these orders. -/
example : x.root < y.root := by decide
example : c.root < d.root := by decide
example : d.root < (Block.node x 4 (nodeRoot x.root 4 1) 1).root := by decide

def head (r : Slot) (i : Fin 4) (b : Block)
    (ack : Option (Slot × Block) := none) : HeadWire 4 := ⟨.seat r i, ⟨b, ack⟩⟩

def withBlocks : State 4 := { base := {
  blocks := [.genesis, x, c, y, d]
  blockStamp := [(.genesis, 0), (x, 1), (c, 2), (y, 3), (d, 4)] } }

def atTime (st : State 4) (t : Time) : State 4 := { st with base := { st.base with now := t } }

def cPC : PC 4 := ⟨2, c, [head 3 0 c (some (2, c)), head 3 1 c (some (2, c)),
  head 3 2 c (some (2, c))]⟩

def archivedOld : State 4 :=
  cPC.witnesses.foldl (admitHead p) (atTime withBlocks 140)

/-- Old acks form a PC but do not reenter the ordinary age window. -/
def oldArchiveCheck : Bool :=
  archivedOld.bestPC == some cPC && archivedOld.base.votes.isEmpty &&
    archivedOld.receivedHeads.length == 3 &&
    archivedOld.base.stableRecord == .genesis && archivedOld.base.obligations.isEmpty

def futureCheck : Bool :=
  let st := admitHead p (atTime withBlocks 16) (head 2 0 c)
  st.receivedHeads.isEmpty && st.base.votes.isEmpty

def ackVariantsCheck : Bool :=
  let st := (admitHead p (admitHead p (atTime withBlocks 48) (head 3 0 c))
    (head 3 0 c (some (2, c))))
  st.receivedHeads.length == 2 && st.base.votes.length == 1 &&
    (archiveEquivocators st 3).isEmpty && !(capBroken p st)

def rawCopiesCheck : Bool :=
  let st := [head 3 0 x, head 3 0 c, head 3 0 y].foldl (admitHead p) (atTime withBlocks 48)
  st.receivedHeads.length == 3 && st.base.votes.length == 2 &&
    (archiveEquivocators st 3).length == 1 && !(capBroken p st)

def capByLabelCheck : Bool :=
  let st := [head 2 0 c, head 2 0 y, head 3 1 c, head 3 1 y].foldl
    (admitHead p) (atTime (initial 4) 48)
  let more := admitHead p (admitHead p st (head 3 0 x)) (head 3 0 y)
  !(capBroken p st) && capBroken p more && more.base.blocks == [.genesis]

def invalidPCCheck : Bool :=
  let duplicate := { cPC with witnesses := List.replicate 3 (head 3 0 c (some (2, c))) }
  let nonextending := { cPC with witnesses := [head 3 0 y (some (2, c)),
    head 3 1 c (some (2, c)), head 3 2 c (some (2, c))] }
  !(pcWellFormed p duplicate) && !(pcWellFormed p nonextending) &&
    pcWellFormed p cPC &&
    (process p (atTime withBlocks 140) ⟨.none, .pc duplicate⟩).receivedHeads.isEmpty

def rawAfterEquivocationCheck : Bool :=
  let copies := [head 3 0 x, head 3 1 x, head 3 2 x]
  let st := (copies ++ cPC.witnesses).foldl (admitHead p) (atTime withBlocks 48)
  capBroken p st && st.bestPC == some cPC &&
    (collectPCs p st).bestPC == some cPC

def latePathCheck : Bool :=
  let unknown := cPC.witnesses.foldl (admitHead p) (atTime (initial 4) 140)
  let withX := process p unknown ⟨.proposer 1, .proposal x [] [] none⟩
  let withC := process p withX ⟨.proposer 2, .proposal c [] [] none⟩
  unknown.bestPC.isNone && withX.bestPC.isNone && withC.bestPC == some cPC

def stampCheck : Bool :=
  let st := receiveHead p (atTime withBlocks 49) (head 3 0 c)
  let later := receiveHead p (atTime st 51) (head 3 0 c)
  later.receivedHeads.length == 1 && stampHead later (head 3 0 c) == 49 &&
    GridCO.stampVote later.base (baseWire (head 3 0 c)) == 49

def cHeads : List (HeadWire 4) := [head 2 0 c, head 2 1 c, head 2 2 c]

def timelyCheck : Bool :=
  let st := cHeads.foldl (admitHead p) (atTime withBlocks 38)
  let early := saveTimely p st 2
  let missed := saveTimely p (atTime withBlocks 40) 2
  let late := cHeads.foldl (admitHead p) missed
  savedTimely early 2 == some (some c) &&
    savedTimely (saveTimely p late 2) 2 == some none &&
    ackFor early 3 c == some (2, c) && (ackFor early 3 y).isNone

def frozenSelectionCheck : Bool :=
  let st := { archivedOld with bestPC := none, frozenPC := [(2, none)] }
  let live := installPC st cPC
  let carried : Wire 4 := ⟨.proposer 3,
    .proposal (.node c 3 (nodeRoot c.root 3 0) 0) [] [] (some cPC)⟩
  (selectedPC p live 3).isNone &&
    selectedPC p { live with proposals := [carried] } 3 == some cPC &&
    preferPC (some cPC) { cPC with target := x } == some cPC

/-- Local gate replay of the lease/S mismatch from red-team execution M.
This is a transition regression, not an ExecutionValid run witness. -/
def mismatchInput : State 4 :=
  let st := admitHead p (atTime withBlocks 166) (head 10 0 d)
  { st with bestPC := some cPC, base := { st.base with
      now := gateTime p 10, stableRecord := y, genuine := [(9, some d)] } }

def prefixGuardCheck : Bool :=
  let st := gate p mismatchInput 10
  SA.confirmation p mismatchInput.base 10 == some d &&
    st.base.stableRecord == y && st.base.goldfishRecord == d &&
    SA.savedGenuine st.base 10 == some (some d) &&
    GridCO.deadlineOf st.base x (releaseThreshold p) == some (gateTime p 10 + lifetime p) &&
    (GridCO.deadlineOf st.base d (releaseThreshold p)).isNone &&
    !(Block.compatible x st.base.stableRecord)

def wholeFiniteGuardCheck : Bool :=
  let st := { mismatchInput with base := { mismatchInput.base with
    obligations := [(y, releaseThreshold p, 400)] } }
  let after := gate p st 10
  after.base.obligations == st.base.obligations &&
    after.base.stableRecord == y && SA.savedGenuine after.base 10 == some (some d)

def floorAndLeaseCheck : Bool :=
  let st := atTime withBlocks 48
  let raw := [baseWire (head 2 0 y), baseWire (head 2 1 y)]
  let tree := st.base.blocks
  -- Use label 5, since Y has slot 5 and needs a valid score target.
  let raw := raw.map (fun o => { o with auth := .seat 5 ((GridCO.headSeat? o).getD 0) })
  let floorY := floor p st tree raw raw 6
  let anchored := choice p st tree raw raw 6 (some cPC)
  let locked := { st with base := { st.base with obligations := [(x, 2, 400)] } }
  floorY == y && anchored == y &&
    Block.preceq x (choice p locked tree raw raw 6 (some cPC)) &&
    preliminaryAnchor x (some cPC) == c

def expiryCheck : Bool :=
  let st := { archivedOld with base := { archivedOld.base with obligations := [(c, 2, 148)] } }
  let after := clock p st 148
  after.base.obligations.isEmpty && after.bestPC == st.bestPC

def releaseEqualityCheck : Bool :=
  let st := [head 5 0 y, head 5 1 y].foldl (admitHead p) (atTime withBlocks 86)
  let base := { st.base with obligations := [(x, 2, 200)] }
  GridCO.releaseCount p.engine base 5 x == 2 &&
    (GridCO.release p.engine base 5).obligations.isEmpty

def carriedDisableCheck : Bool :=
  let before := [head 3 0 x, head 3 1 x].foldl (admitHead p) (atTime withBlocks 64)
  let b := Block.node x 4 (nodeRoot x.root 4 1) 1
  let proposal : Wire 4 := ⟨.proposer 4,
    .proposal b [head 3 0 c, head 3 1 c] [] none⟩
  let after := process p before proposal
  !(capBroken p before) && capBroken p after && after.proposals == [proposal]

/-- A full proposal/preparation/ack/gate replay. Original emitted payloads
enter state only through explicit delivery, including the reader's own copy.
The three honest seats can have this same state; seat 3 stays silent. -/
def completeRoundCheck : Bool :=
  let start := (List.range 5).foldl (fun st j => clock p st (4 * j)) (initial 4)
  let proposal := propose p start 1
  let afterProposal := match proposal with
    | some msg => process p start ⟨.proposer 1, msg⟩
    | none => start
  let prepare := clock p afterProposal 20
  let withHeads := match act p prepare 1 with
    | some msg => ([0, 1, 2] : List (Fin 4)).foldl
        (fun st i => process p st ⟨.seat 1 i, msg⟩) prepare
    | none => prepare
  let saved := clock p withHeads 24
  let ackState := clock p (clock p (clock p saved 28) 32) 36
  let ack := act p ackState 2
  let withAcks := match ack with
    | some msg => ([0, 1, 2] : List (Fin 4)).foldl
        (fun st i => process p st ⟨.seat 2 i, msg⟩) ackState
    | none => ackState
  let done := clock p withAcks 40
  proposal == some (.proposal x [] [] none) && prepare.receivedHeads.isEmpty &&
    savedTimely saved 1 == some (some x) &&
    ack == some (.head ⟨x, some (1, x)⟩) &&
    ackState.bestPC.isNone && withAcks.bestPC.isSome &&
    strong done == x && stable done == x && confirmed done == x &&
    GridCO.deadlineOf done.base x 2 == some 68

def smokeChecks : List (String × Bool) := [
  ("old archive PC without base replay", oldArchiveCheck),
  ("future label rejection", futureCheck),
  ("ack-only base projection", ackVariantsCheck),
  ("uncapped raw archive and two-target base cache", rawCopiesCheck),
  ("one-label unresolved cap evidence", capByLabelCheck),
  ("invalid PC witnesses", invalidPCCheck),
  ("raw PC after equivocation and disablement", rawAfterEquivocationCheck),
  ("path receipt completes old PC", latePathCheck),
  ("first receipt stamps", stampCheck),
  ("timely save and actual-head ack", timelyCheck),
  ("frozen/carried selection and equal-rank tie", frozenSelectionCheck),
  ("lease loop outside stable veto", prefixGuardCheck),
  ("whole-tip finite guard", wholeFiniteGuardCheck),
  ("F4 floor and mandatory lease", floorAndLeaseCheck),
  ("finite expiry retains PC", expiryCheck),
  ("release at equality", releaseEqualityCheck),
  ("carried signatures disable mode before choice", carriedDisableCheck),
  ("complete proposal/preparation/ack/gate round", completeRoundCheck)]

#eval smokeChecks

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Kernel reduction covers all 18 state-transition checks, including PC assembly.
theorem smokePass : smokeChecks.all Prod.snd = true := by decide

end AvailableChain.SAPC.Tests
end

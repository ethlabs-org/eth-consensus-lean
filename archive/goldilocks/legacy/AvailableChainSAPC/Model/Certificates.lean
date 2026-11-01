module
public import AvailableChainSAPC.Model.Objects

@[expose] public section
namespace AvailableChain.SAPC

/-- Distinct seats at one label; ack-only differences are not equivocation. -/
def archiveEquivocators {n : Nat} (st : State n) (r : Slot) : List (Fin n) :=
  let heads := st.receivedHeads.filter (fun o => headLabel? o == some r)
  (heads.filterMap headSeat?).dedup.filter (fun i =>
    2 ≤ ((heads.filter (fun o => headSeat? o == some i)).map
      (fun o => o.payload.target)).dedup.length)

/-- Count one label at a time, including old and unresolved evidence. -/
def capBroken (p : Params) {n : Nat} (st : State n) : Bool :=
  (st.receivedHeads.filterMap headLabel?).any
    (fun r => pcFaultCap p < (archiveEquivocators st r).length)

def pcWitness {n : Nat} (s : Slot) (b : Block) (o : HeadWire n) : Bool :=
  headLabel? o == some (s + 1) && o.payload.ack == some (s, b) &&
    Block.preceq b o.payload.target && o.payload.target.slot ≤ s + 1

/-- Structural certificate checks do not remove equivocators. -/
def pcWellFormed (p : Params) {n : Nat} (c : PC n) : Bool :=
  0 < c.slot && c.target != .genesis && c.target.slot == c.slot &&
    c.witnesses.length == pcQuorum p &&
    (c.witnesses.filterMap headSeat?).dedup.length == pcQuorum p &&
    c.witnesses.all (pcWitness c.slot c.target)

def pcPaths {n : Nat} (st : State n) (c : PC n) : Bool :=
  pathKnown st c.target && c.witnesses.all (fun o => pathKnown st o.payload.target)

def pcValid (p : Params) {n : Nat} (st : State n) (c : PC n) : Bool :=
  pcWellFormed p c && pcPaths st c &&
    c.witnesses.all (fun o => o ∈ st.receivedHeads)

/-- Rank uses the target slot. Keep the existing object on every tie. -/
def preferPC {n : Nat} (old : Option (PC n)) (candidate : PC n) : Option (PC n) :=
  match old with
  | none => some candidate
  | some previous => if previous.slot < candidate.slot then some candidate else old

def installPC {n : Nat} (st : State n) (c : PC n) : State n :=
  { st with bestPC := preferPC st.bestPC c }

/-- Scan in receipt order; retain the first witness for each seat. -/
def firstPerSeat {n : Nat} (heads : List (HeadWire n)) : List (HeadWire n) :=
  heads.foldl (fun acc o =>
    if acc.any (fun old => headSeat? old == headSeat? o) then acc else acc ++ [o]) []

def assemblePC (p : Params) {n : Nat} (st : State n)
    (s : Slot) (b : Block) : Option (PC n) :=
  let witnesses := (firstPerSeat (st.receivedHeads.filter (fun o =>
    pcWitness s b o && pathKnown st o.payload.target))).take (pcQuorum p)
  let c := PC.mk s b witnesses
  if pcValid p st c then some c else none

/-- Both modes assemble old certificates, without an upper deadline. -/
def collectPCs (p : Params) {n : Nat} (st : State n) : State n :=
  let candidates := (st.receivedHeads.filterMap (fun o => o.payload.ack)).eraseDups
  candidates.foldl (fun acc (s, b) =>
    match assemblePC p acc s b with
    | none => acc
    | some c => installPC acc c) st

/-- N counts exact raw targets with receipts and paths before the cutoff. -/
def timelyCandidate (p : Params) {n : Nat} (st : State n)
    (r : Slot) (b : Block) : Bool :=
  0 < r && b != .genesis && b.slot == r && pathBefore st (earlyTime p r) b &&
    pcQuorum p ≤ ((st.receivedHeads.filter (fun o =>
      headLabel? o == some r && o.payload.target == b &&
      stampHead st o < earlyTime p r)).filterMap headSeat?).dedup.length

def savedTimely {n : Nat} (st : State n) (r : Slot) : Option (Option Block) :=
  (st.timely.find? (fun row => row.1 == r)).map Prod.snd

/-- Latch success and failure. Late receipts cannot reopen this save. -/
def saveTimely (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  if (savedTimely st r).isSome then st else
    { st with timely := st.timely ++ [(r,
      ((st.receivedHeads.map (fun o => o.payload.target)).find?
        (timelyCandidate p st r)))] }

def ackFor {n : Nat} (st : State n) (r : Slot) (target : Block) : Option (Slot × Block) :=
  if r == 0 then none else
    match savedTimely st (r - 1) with
    | some (some b) => if Block.preceq b target then some (r - 1, b) else none
    | _ => none

end AvailableChain.SAPC
end

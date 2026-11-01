module
public import AvailableChainModel.Generic.Run
public import AvailableChainModel.Objects.Blocks
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace AvailableChain.LStar

open AvailableChain.Generic

/-- Goldfish slot length and L* memory and lock durations.
Source: guarded-override.md §§2, 3.1, 10.1; the phase guard is from
two-set-recovery.md §4.3. -/
structure Params where
  Δ : Time
  L : Time
  η : Time
  deltaPos : 0 < Δ
  lockLong : 4 * Δ < L
  etaNonneg : 0 ≤ η
  /-- Expiry guard (two-set-recovery.md §4.3): a lock deadline `d_j + L`
  never falls in `(v_(r+1), d_r]`, where expiry would precede the gate.
  Deadlines have phase `2Δ + L` modulo `4Δ`. -/
  lockPhase : 0 < L % (4 * Δ) ∧ L % (4 * Δ) ≤ 3 * Δ

def proposalTime (p : Params) (s : Slot) : Time := 4 * p.Δ * s
def voteTime (p : Params) (s : Slot) : Time := proposalTime p s + p.Δ
def earlyTime (p : Params) (s : Slot) : Time := proposalTime p s + 2 * p.Δ
def freezeTime (p : Params) (s : Slot) : Time := proposalTime p s + 3 * p.Δ
def gateTime (p : Params) (s : Slot) : Time := proposalTime p s + 6 * p.Δ

/-- Signed HEADs inside proposals retain the proposer's raw and resolved views.
Source: verified-consensus docs/PROTOCOL.md §§2.1–2.3, `propose_block` and
`goldfish_vote`. No FG, SG, height, grade, or acknowledgement payload exists. -/
abbrev HeadWire (n : Nat) := Signed Slot n Block

inductive Msg (n : Nat) where
  | head (target : Block)
  | proposal (b : Block) (view supportView : List (HeadWire n))
  deriving DecidableEq, Repr

abbrev Wire (n : Nat) := Signed Slot n (Msg n)

def fromHead {n : Nat} (o : HeadWire n) : Wire n :=
  ⟨o.auth, .head o.payload⟩

def toHead? {n : Nat} (o : Wire n) : Option (HeadWire n) :=
  match o.payload with
  | .head b => some ⟨o.auth, b⟩
  | _ => none

def headTarget? {n : Nat} (o : Wire n) : Option Block :=
  match o.payload with
  | .head b => some b
  | _ => none

def headLabel? {n : Nat} (o : Wire n) : Option Slot :=
  match o.auth, o.payload with
  | .seat r _, .head _ => some r
  | _, _ => none

def headSeat? {n : Nat} (o : Wire n) : Option (Fin n) :=
  match o.auth, o.payload with
  | .seat _ i, .head _ => some i
  | _, _ => none

def sameSeat {n : Nat} (a b : Wire n) : Bool :=
  match a.auth, b.auth with
  | .seat r i, .seat s j => r == s && i == j
  | _, _ => false

/-- Local store. Receipt stamps use the last public tick, as in
verified-consensus `StoreBase.lean` and `Handlers.lean`. -/
structure State (n : Nat) where
  now : Time := 0
  blocks : List Block := [.genesis]
  blockStamp : List (Block × Time) := [(.genesis, 0)]
  votes : List (Wire n) := []
  voteStamp : List (Wire n × Time) := []
  proposals : List (Wire n) := []
  /-- Label, raw frozen pool, resolved frozen pool, frozen block domain. -/
  frozen : List (Slot × List (Wire n) × List (Wire n) × List Block) := []
  early : List (Slot × List (Wire n)) := []
  lock : Option (Block × Time) := none
  stableRecord : Block := .genesis
  goldfishRecord : Block := .genesis
  deriving Repr

def initial (n : Nat) : State n := {}

def blockKnown {n : Nat} (st : State n) (b : Block) : Bool := b ∈ st.blocks

def stampBlock {n : Nat} (st : State n) (b : Block) : Time :=
  ((st.blockStamp.find? (fun row => row.1 == b)).map Prod.snd).getD st.now

def stampVote {n : Nat} (st : State n) (o : Wire n) : Time :=
  ((st.voteStamp.find? (fun row => row.1 == o)).map Prod.snd).getD st.now

/-- `resolution_time = max(receipt(vote), receipt(head))`, or infinity for
an unknown head. Source: PROTOCOL.md §2.2, `resolution_time`. -/
def resolvedBefore {n : Nat} (st : State n) (o : Wire n) (cutoff : Time) : Bool :=
  match headTarget? o with
  | none => false
  | some b => blockKnown st b && b.slot ≤ (headLabel? o).getD 0 &&
      stampVote st o < cutoff && stampBlock st b < cutoff

def votesAt {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  st.votes.filter (fun o => headLabel? o == some r)

def seats (n : Nat) (xs : List (Wire n)) : List (Fin n) :=
  (xs.filterMap headSeat?).eraseDups

def seatVotes {n : Nat} (xs : List (Wire n)) (i : Fin n) : List (Wire n) :=
  xs.filter (fun o => headSeat? o == some i)

def equivocates {n : Nat} (xs : List (Wire n)) (i : Fin n) : Bool :=
  2 ≤ ((seatVotes xs i).eraseDups).length

/-- Each equivocating seat contributes one point to every subtree. Other
seats contribute once if a support vote covers the block. Source:
verified-consensus `ForkChoice/Goldfish.lean`, `goldfish_score`. -/
def goldfishScore {n : Nat} (raw support : List (Wire n)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | some target => Block.preceq b target
      | none => false))).length

def voterCount {n : Nat} (xs : List (Wire n)) : Nat := (seats n xs).length

/-- The source GHOST walk, with the greatest root winning a score tie.
Source: verified-consensus `ForkChoice/Goldfish.lean`, `ghost`. -/
def ghostStep (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) : Option Block :=
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  let best := children.foldl (fun best b =>
    match best with
    | none => some b
    | some old =>
      if score old < score b || (score old == score b && old.root < b.root)
      then some b else best) none
  match best with
  | none => none
  | some b =>
      if children.any (fun c => c != b && score c == score b && c.root == b.root)
      then none else some b

def ghostWalk (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) : Nat → Block → Block
  | 0, b => b
  | fuel + 1, b =>
      match ghostStep tree score eligible b with
      | none => b
      | some c => ghostWalk tree score eligible fuel c

def ghost (anchor : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) : Block :=
  ghostWalk tree score eligible tree.length anchor

def liveRoot {n : Nat} (st : State n) : Block :=
  (st.lock.map Prod.fst).getD .genesis

def advance (old candidate : Block) : Block :=
  if Block.preceq candidate old then old else candidate

/-- The proposal-time raw pool and its resolved subset.
Source: verified-consensus `ForkChoice/Views.lean`, `proposer_view`. -/
def proposerView {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  votesAt st (s - 1)

def proposerSupportView {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  (proposerView st s).filter (fun o =>
    match headTarget? o with
    | some b => blockKnown st b && b.slot ≤ s - 1
    | none => false)

def proposalsAt {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  st.proposals.filter (fun o =>
    match o.payload with
    | .proposal b _ _ => b.slot == s
    | _ => false)

def carriedRaw {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  ((proposalsAt st s).flatMap (fun o =>
    match o.payload with
    | .proposal _ raw _ => raw.map fromHead
    | _ => [])).filter (fun o => headLabel? o == some (s - 1))

def carriedSupport {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  ((proposalsAt st s).flatMap (fun o =>
    match o.payload with
    | .proposal _ _ support => support.map fromHead
    | _ => [])).filter (fun o =>
      headLabel? o == some (s - 1) &&
      match headTarget? o with
      | some b => blockKnown st b && b.slot ≤ s - 1
      | none => false)

def frozenAt {n : Nat} (st : State n) (r : Slot) :
    Option (List (Wire n) × List (Wire n) × List Block) :=
  ((st.frozen.find? (fun row => row.1 == r)).map Prod.snd)

/-- The previous-slot freeze is a local clock evaluation. Its saved block
domain and vote subsets are later merged with current proposals. -/
def freeze (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  let cutoff := freezeTime p r
  let raw := (votesAt st r).filter (fun o => stampVote st o < cutoff)
  let support := (votesAt st r).filter (fun o => resolvedBefore st o cutoff)
  let blocks := st.blocks.filter (fun b => stampBlock st b < cutoff)
  { st with frozen := st.frozen ++ [(r, raw, support, blocks)] }

/-- Previous-slot freeze and proposal merge. Source:
verified-consensus `ForkChoice/Views.lean`, `voter_view`,
`voter_support_view`, `voter_processed_block_tree`. -/
def voterView (_p : Params) {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  let pool := match frozenAt st (s - 1) with
    | some (raw, _, _) => raw
    | none => []
  (pool ++ carriedRaw st s).eraseDups

def voterSupportView (_p : Params) {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  let pool := match frozenAt st (s - 1) with
    | some (_, support, _) => support
    | none => []
  (pool ++ carriedSupport st s).eraseDups

def voterTree (_p : Params) {n : Nat} (st : State n) (s : Slot) : List Block :=
  let proposals := (proposalsAt st s).filterMap (fun o =>
    match o.payload with
    | .proposal b _ _ => some b
    | _ => none)
  let frozenBlocks := match frozenAt st (s - 1) with
    | some (_, _, blocks) => blocks
    | none => []
  st.blocks.filter (fun b =>
    b ∈ frozenBlocks ||
      proposals.any (fun q => Block.preceq b q))

/-- With no heights or finality, the Goldfish eligibility clauses are
strict majority for an old child and unconditional for a current-slot child.
Source: PROTOCOL.md §2.2, `goldfish_eligible`. -/
def goldfishEligible {n : Nat} (raw support : List (Wire n))
    (current : Slot) (b : Block) : Bool :=
  b.slot == current || 2 * goldfishScore raw support b > voterCount raw

def forkChoice {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (Wire n)) (current : Slot) : Block :=
  ghost (liveRoot st) tree (goldfishScore raw support)
    (goldfishEligible raw support current)

def propose (_p : Params) {n : Nat} (st : State n) (s : Slot) : Option (Msg n) :=
  if s == 0 then none else
    let raw := proposerView st s
    let support := proposerSupportView st s
    let parent := forkChoice st st.blocks raw support s
    let b := Block.node parent s (nodeRoot parent.root s 0) 0
    some (.proposal b (raw.filterMap toHead?) (support.filterMap toHead?))

def act (p : Params) {n : Nat} (st : State n) (s : Slot) : Option (Msg n) :=
  if s == 0 then some (.head .genesis) else
    some (.head (forkChoice st (voterTree p st s)
      (voterView p st s) (voterSupportView p st s) s))

def admitVote (p : Params) {n : Nat} (st : State n) (o : Wire n) : State n :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      let current := (st.now / (4 * p.Δ)).toNat
      -- Late votes of old labels are admitted: they enter the memory
      -- denominator (guarded-override.md §3.1, lstar-recovery.md §2), and
      -- the receipt stamp keeps them out of frozen, early, and late views.
      if current < r || decide (o ∈ st.votes) ||
          equivocates (votesAt st r) i then st else
        { st with votes := st.votes ++ [o], voteStamp := st.voteStamp ++ [(o, st.now)] }
  | _, _ => st

/-- Block admission then carried-vote admission, following the source
`Handlers.lean` order. The support subset remains fixed metadata. -/
def admitProposal (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw : List (HeadWire n)) : State n :=
  let current := (st.now / (4 * p.Δ)).toNat
  if b.slot > current || b ∈ st.blocks || !blockKnown st b.parent then st else
    let st' := { st with
      blocks := st.blocks ++ [b]
      blockStamp := st.blockStamp ++ [(b, st.now)]
      proposals := st.proposals ++ [o] }
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st'

def process (p : Params) {n : Nat} (st : State n) (o : Wire n) : State n :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => admitVote p st o
  | .proposer _, .proposal b raw _ => admitProposal p st o b raw
  | _, _ => st

def wellFormed {n : Nat} (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => true
  | .proposer s, .proposal b raw support =>
      s == b.slot && b.parent?.isSome && b.parent.slot < s &&
      raw.all (fun v => match v.auth with
        | .seat r _ => r == s - 1
        | _ => false) &&
      support.all (fun v => decide (v ∈ raw))
  | _, _ => false

def depsPresent {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.payload with
  | .head _ => true
  | .proposal b _ _ => blockKnown st b.parent

def processed {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.payload with
  | .head _ => decide (o ∈ st.votes)
  | .proposal _ _ _ => decide (o ∈ st.proposals)

def carries {n : Nat} (parent child : Wire n) : Prop :=
  match parent.payload with
  | .head _ => False
  | .proposal _ raw support => child ∈ raw.map fromHead ∨ child ∈ support.map fromHead

/-- Direct delivery calls its handler. Carried raw HEAD handlers run only
when the containing block enters the store, as in the reference
`Execution.handles` / `NamedReceiptCalls.postCore` admission test.
`carries` stays structural for signature checks. -/
def handles (p : Params) {n : Nat} (st : State n) (parent child : Wire n) : Prop :=
  parent = child ∨ match parent.payload with
    | .proposal b raw _ =>
        b ∉ st.blocks ∧ b ∈ (process p st parent).blocks ∧ child ∈ raw.map fromHead
    | .head _ => False

def earlyVotes (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  (votesAt st r).filter (fun o => resolvedBefore st o (earlyTime p r))

def savedEarly {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  ((st.early.find? (fun row => row.1 == r)).map Prod.snd).getD []

/-- `D_i[r,u]`: max distinct seats among labels in the fixed vote-time
window. An equivocating seat occurs once. Source: guarded-override.md §3.1. -/
def memoryDenominator (p : Params) {n : Nat} (st : State n) (r : Slot) : Nat :=
  let labels := (st.votes.filterMap headLabel?).eraseDups
  labels.foldl (fun d j =>
    if voteTime p r - p.η ≤ voteTime p j && voteTime p j ≤ voteTime p r
    then max d (voterCount (votesAt st j)) else d) 0

def quorum (d : Nat) : Nat := (3 * d + 3) / 4

def lateVotes (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  (votesAt st r).filter (fun o => stampVote st o < gateTime p r)

def cleanSupport (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  (earlyVotes p st r).filter (fun o =>
    !(lateVotes p st r).any (fun u => sameSeat u o && u != o))

/-- Genuine Goldfish confirmation at `d_r`: the early resolved subset,
late equivocation exclusion, and strict majority of late participants.
The walk starts at genesis (the FG root of the source), not at the lock:
only proposal and HEAD walks start at the lock (guarded-override.md §10.1).
Source: PROTOCOL.md §2.1 `update_confirmation`. -/
def confirmation (p : Params) {n : Nat} (st : State n) (r : Slot) : Option Block :=
  let support := cleanSupport p st r
  let late := lateVotes p st r
  let eligible := fun b => 2 * goldfishScore support support b > voterCount late
  let h := ghost .genesis st.blocks (goldfishScore support support) eligible
  if eligible h then some h else none

def bestEligible (xs : List Block) : Option Block :=
  xs.foldl (fun best b =>
    match best with
    | none => some b
    | some old =>
        if old.depth < b.depth || (old.depth == b.depth && old.root < b.root)
        then some b else best) none

/-- At the gate, only the saved early support can install or renew a lock.
The Goldfish record advances independently. Expiry was processed first by
`clock`. Source: guarded-override.md §§4.2, 10.1. -/
def gate (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  match confirmation p st r with
  | none => st
  | some h =>
      let st := { st with goldfishRecord := advance st.goldfishRecord h }
      let early := savedEarly st r
      let q := quorum (memoryDenominator p st r)
      let candidates := st.blocks.filter (fun b =>
        Block.preceq b h &&
        (match st.lock with
         | none => true
         | some (locked, _) => Block.compatible locked b) &&
        q ≤ goldfishScore early early b)
      match bestEligible candidates with
      | none => st
      | some b =>
          let chosen := match st.lock with
            | none => some b
            | some (locked, _) =>
                if Block.prec b locked then
                  if q ≤ goldfishScore early early locked then some locked else none
                else some b
          match chosen with
          | none => st
          | some target =>
              let newLock : Option (Block × Time) := some (target, gateTime p r + p.L)
              { st with lock := newLock, stableRecord := advance st.stableRecord target }

/-- Local public-time evaluations run for awake and asleep nodes. Equality
checks make each cutoff run once; same-time expiry precedes acquisition. -/
def clock (p : Params) {n : Nat} (st : State n) (t : Time) : State n :=
  let newLock := st.lock.bind (fun pair => if t < pair.2 then some pair else none)
  let st := { st with now := t, lock := newLock }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p st fSlot else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { st with early := st.early ++ [(eSlot, earlyVotes p st eSlot)] }
    else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p st dSlot else st

def confirmed {n : Nat} (st : State n) : Block :=
  if Block.preceq st.stableRecord st.goldfishRecord
  then st.goldfishRecord else st.stableRecord

def stable {n : Nat} (st : State n) : Block := st.stableRecord

def block {n : Nat} : Msg n → Option Block
  | .proposal b _ _ => some b
  | .head _ => none

def slotsAt (p : Params) (t : Time) : List Slot :=
  (List.range (t.toNat + 1)).filter (fun s => proposalTime p s == t)

def duties (p : Params) (t : Time) : List Slot :=
  (List.range (t.toNat + 1)).filter (fun s => voteTime p s == t)

private theorem proposal_le_time (p : Params) (s : Slot) (t : Time)
    (h : proposalTime p s = t) : s ≤ t.toNat := by
  have hd : 1 ≤ p.Δ := by
    simpa using (Int.add_one_le_iff.mpr p.deltaPos)
  have hs : 0 ≤ (s : ℤ) := Int.natCast_nonneg s
  have hprod := mul_nonneg hs (show 0 ≤ 4 * p.Δ - 1 by nlinarith [hd])
  have ht : (s : ℤ) ≤ t := by
    dsimp [proposalTime] at h
    nlinarith [hprod]
  have htn : 0 ≤ t := le_trans hs ht
  have hcast := Int.toNat_of_nonneg htn
  exact_mod_cast (show (s : ℤ) ≤ (t.toNat : ℤ) by simpa [hcast] using ht)

private theorem vote_le_time (p : Params) (s : Slot) (t : Time)
    (h : voteTime p s = t) : s ≤ t.toNat := by
  have hd : 1 ≤ p.Δ := by
    simpa using (Int.add_one_le_iff.mpr p.deltaPos)
  have hs : 0 ≤ (s : ℤ) := Int.natCast_nonneg s
  have hprod := mul_nonneg hs (show 0 ≤ 4 * p.Δ - 1 by nlinarith [hd])
  have ht : (s : ℤ) ≤ t := by
    dsimp [voteTime, proposalTime] at h
    nlinarith [hprod]
  have htn : 0 ≤ t := le_trans hs ht
  have hcast := Int.toNat_of_nonneg htn
  exact_mod_cast (show (s : ℤ) ≤ (t.toNat : ℤ) by simpa [hcast] using ht)

theorem slotsAt_spec (p : Params) (s : Slot) (t : Time) :
    s ∈ slotsAt p t ↔ proposalTime p s = t := by
  simp only [slotsAt, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (proposal_le_time p s t h), h⟩

theorem duties_spec (p : Params) (s : Slot) (t : Time) :
    s ∈ duties p t ↔ voteTime p s = t := by
  simp only [duties, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (vote_le_time p s t h), h⟩

theorem slotsAt_nodup (p : Params) (t : Time) : (slotsAt p t).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

theorem duties_nodup (p : Params) (t : Time) : (duties p t).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

/-- Permanent rejection (design §2 E4). Two refusals are permanent:
- a HEAD that is not yet processed, whose seat already equivocates at its
  label `r` (`admitVote`; equivocation evidence only grows);
- a proposal wire that is not yet processed, whose block is already stored
  (`admitProposal`; stored blocks are never removed). A faulty proposer can
  sign two wires with the same block; the store refuses the second wire for
  good.
Both handlers return the state unchanged in these cases. Late HEADs of old
labels are admitted, so no old-label clause applies. The future-label refusal
(`current < r`) is temporary, so `excludes` does not test the clock; a HEAD of
a future label is excluded only by the equivocation clause. A processed
object is not excluded. An object whose authentication does not match its
payload (for example a HEAD with proposer authentication) is also refused for
good, but it fails the wire check (`wellFormed`), and
`DeliveryWellFormed.wire` keeps it out of every valid run. -/
def excludes {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat r i, .head _ => !decide (o ∈ st.votes) && equivocates (votesAt st r) i
  | .proposer _, .proposal b _ _ => !decide (o ∈ st.proposals) && decide (b ∈ st.blocks)
  | _, _ => false

/-- The C* instance: seat identities occur in authentication only. Every
seat of a label signs the same payload. Source: CONTRACT.md §2a. -/
def lstar (p : Params) (n : Nat) : ProtocolSpec n where
  State := State n
  Label := Slot
  Payload := Msg n
  init := initial n
  clock := clock p
  actTime := voteTime p
  duties := duties p
  duties_spec := duties_spec p
  duties_nodup := duties_nodup p
  act := act p
  proposalTime := proposalTime p
  slotsAt := slotsAt p
  slotsAt_spec := slotsAt_spec p
  slotsAt_nodup := slotsAt_nodup p
  propose := propose p
  gossip := fun _ _ => []
  process := process p
  wellFormed := wellFormed
  depsPresent := depsPresent
  processed := processed
  excludes := excludes
  handles := handles p
  carries := carries

end AvailableChain.LStar
end

module
public import AvailableChainModel.Generic.Run
public import AvailableChainModel.Objects.Blocks -- shake: keep (re-export)
public import AvailableChainGridCO.Model.Walk
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace AvailableChain.GridCO

open AvailableChain.Generic

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The shared engine has two lease admission rules. The default is Grid CO.
SA uses the same engine with `slowArming = true`. -/
class LeasePolicy where
  slowArming : Bool

instance gridLeasePolicy : LeasePolicy := ⟨false⟩

abbrev slowLeasePolicy : LeasePolicy := ⟨true⟩

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Largest grid level no greater than the observed support. -/
def gridLevel (n : Nat) (grid : Finset Nat) (h : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun g => g ∈ grid && g ≤ h)).foldl max 0

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Grid counted-obligations parameters. The grid is fixed in honest code. -/
structure Params where
  Δ : Time
  n : Nat
  m : Nat
  η : Time
  grid : Finset Nat
  θ_R : ℚ
  deltaPos : 0 < Δ
  mLarge : 2 ≤ m
  one_mem : 1 ∈ grid
  levels_pos : ∀ g ∈ grid, 0 < g
  levels_le : ∀ g ∈ grid, g ≤ n
  etaNonneg : 0 ≤ η
  thetaLower : (1 / 2 : ℚ) ≤ θ_R
  thetaUpper : θ_R ≤ (3 / 4 : ℚ)
  /-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The grid has enough levels for each admissible current count. -/
  gridMatchesTheta : ∀ a h : Nat, 1 ≤ a → h ≤ n →
    θ_R * ((h + a : Nat) : ℚ) < (h : ℚ) → a < gridLevel n grid h

def lifetime (p : Params) : Time := (4 * (p.m : Time) - 1) * p.Δ

def proposalTime (p : Params) (s : Slot) : Time := 4 * p.Δ * s
def voteTime (p : Params) (s : Slot) : Time := proposalTime p s + p.Δ
def earlyTime (p : Params) (s : Slot) : Time := proposalTime p s + 2 * p.Δ
def freezeTime (p : Params) (s : Slot) : Time := proposalTime p s + 3 * p.Δ
def releaseTime (p : Params) (s : Slot) : Time := proposalTime p s + 5 * p.Δ
def gateTime (p : Params) (s : Slot) : Time := proposalTime p s + 6 * p.Δ

/-- [ROOT-DIGEST-2 W1; DC GoldfishVote] Select the signed HEAD target type. -/
inductive HeadMode where
  | block
  | root
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST-2 W1; DC GoldfishVote] Legacy bodies or root identifiers. -/
@[reducible] def HeadTarget : HeadMode → Type
  | .block => Block
  | .root => BlockId

instance (mode : HeadMode) : DecidableEq (HeadTarget mode) := by
  cases mode <;> unfold HeadTarget <;> infer_instance

instance (mode : HeadMode) : Repr (HeadTarget mode) := by
  cases mode <;> unfold HeadTarget <;> infer_instance

/-- [ROOT-DIGEST-2 W1; DC GoldfishVote] The signed target retains its auth. -/
abbrev HeadWire (n : Nat) (mode : HeadMode := .block) := Signed Slot n (HeadTarget mode)

/-- [ROOT-DIGEST-2 W1; DC NamedObject] Shared wire payloads indexed by HEAD mode. -/
inductive Msg (n : Nat) (mode : HeadMode := .block) where
  | head (target : HeadTarget mode)
  | proposal (b : Block) (view supportView : List (HeadWire n mode))
  deriving DecidableEq, Repr

/-- [ROOT-DIGEST-2 W1; DC NamedObject] Authentication and mode-indexed payload. -/
abbrev Wire (n : Nat) (mode : HeadMode := .block) := Signed Slot n (Msg n mode)

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Resolve in the specified domain. -/
def resolveTarget (mode : HeadMode) (tree : List Block) : HeadTarget mode → Option Block :=
  match mode with
  | .block => fun (B : Block) => if B ∈ tree then some B else none
  | .root => fun r => Block.findByRoot? tree r

/-- [ROOT-DIGEST-2 W1; DC GoldfishVote] The signed name of a selected body. -/
def targetOfBlock (mode : HeadMode) (B : Block) : HeadTarget mode :=
  match mode with
  | .block => B
  | .root => B.root

def fromHead {n : Nat} {mode : HeadMode} (o : HeadWire n mode) : Wire n mode :=
  ⟨o.auth, .head o.payload⟩

def toHead? {n : Nat} {mode : HeadMode} (o : Wire n mode) : Option (HeadWire n mode) :=
  match o.payload with
  | .head b => some ⟨o.auth, b⟩
  | _ => none

def headTarget? {n : Nat} {mode : HeadMode} (o : Wire n mode) : Option (HeadTarget mode) :=
  match o.payload with
  | .head b => some b
  | _ => none

def headLabel? {n : Nat} {mode : HeadMode} (o : Wire n mode) : Option Slot :=
  match o.auth, o.payload with
  | .seat r _, .head _ => some r
  | _, _ => none

def headSeat? {n : Nat} {mode : HeadMode} (o : Wire n mode) : Option (Fin n) :=
  match o.auth, o.payload with
  | .seat _ i, .head _ => some i
  | _, _ => none

def sameSeat {n : Nat} {mode : HeadMode} (a b : Wire n mode) : Bool :=
  match a.auth, b.auth with
  | .seat r i, .seat s j => r == s && i == j
  | _, _ => false

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Local store. Receipt stamps use the last public tick, as in
verified-consensus `StoreBase.lean` and `Handlers.lean`. -/
structure State (n : Nat) (mode : HeadMode := .block) where
  now : Time := 0
  blocks : List Block := [.genesis]
  blockStamp : List (Block × Time) := [(.genesis, 0)]
  votes : List (Wire n mode) := []
  voteStamp : List (Wire n mode × Time) := []
  proposals : List (Wire n mode) := []
  /-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Label, raw frozen pool, resolved frozen pool, frozen block domain. -/
  frozen : List (Slot × List (Wire n mode) × List (Wire n mode) × List Block) := []
  early : List (Slot × List (Wire n mode)) := []
  /-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Local raw gate results. `none` records an empty gate, not a missing label.
  Only SA uses this field; Grid CO leaves it empty. -/
  genuine : List (Slot × Option Block) := []
  /-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
One deadline per block and grid level. -/
  obligations : List (Block × Nat × Time) := []
  /-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Frozen label-r raw and resolved release views before the next HEAD. -/
  releaseSnapshots : List (Slot × List (Wire n mode) × List (Wire n mode)) := []
  stableRecord : Block := .genesis
  goldfishRecord : Block := .genesis
  /-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Temporary resolution domain for an active view. -/
  headDomain : Option (List Block) := none
  deriving Repr

def initial (n : Nat) (mode : HeadMode := .block) : State n mode := {}

def blockKnown {n : Nat} {mode : HeadMode} (st : State n mode) (b : Block) : Bool := b ∈ st.blocks

def stampBlock {n : Nat} {mode : HeadMode} (st : State n mode) (b : Block) : Time :=
  ((st.blockStamp.find? (fun row => row.1 == b)).map Prod.snd).getD st.now

def stampVote {n : Nat} {mode : HeadMode} (st : State n mode) (o : Wire n mode) : Time :=
  ((st.voteStamp.find? (fun row => row.1 == o)).map Prod.snd).getD st.now

/-- [ROOT-DIGEST-2 W1; DC Blocks.find?] Domain pinned before active filtering. -/
def resolutionTree {n : Nat} {mode : HeadMode} (st : State n mode) : List Block :=
  match mode with
  | .block => st.blocks
  | .root => st.headDomain.getD st.blocks

/-- [ROOT-DIGEST-2 W1; DC Goldfish] Resolve, then test active membership. -/
def resolvedHead? {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) : Option Block := do
  let target ← headTarget? o
  let B ← resolveTarget mode (resolutionTree st) target
  if B ∈ st.blocks then some B else none

/-- [ROOT-DIGEST-2 W1; DC resolution_time] Test the resolved body's slot and receipts. -/
def resolvedBefore {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) (cutoff : Time) : Bool :=
  match resolvedHead? st o with
  | none => false
  | some B => decide (B.slot ≤ (headLabel? o).getD 0) &&
      decide (stampVote st o < cutoff) && decide (stampBlock st B < cutoff)

def votesAt {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) : List (Wire n mode) :=
  st.votes.filter (fun o => headLabel? o == some r)

def seats (n : Nat) {mode : HeadMode} (xs : List (Wire n mode)) : List (Fin n) :=
  (xs.filterMap headSeat?).dedup

def seatVotes {n : Nat} {mode : HeadMode} (xs : List (Wire n mode)) (i : Fin n) : List
    (Wire n mode) :=
  xs.filter (fun o => headSeat? o == some i)

def equivocates {n : Nat} {mode : HeadMode} (xs : List (Wire n mode)) (i : Fin n) : Bool :=
  2 ≤ ((seatVotes xs i).eraseDups).length

/-- [ROOT-DIGEST-2 W1; DC goldfish_score] Resolve in domain and filter into tree. -/
def goldfishScoreOn {n : Nat} {mode : HeadMode} (domain tree : List Block)
    (raw support : List (Wire n mode)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | none => false
      | some target => match resolveTarget mode domain target with
        | none => false
        | some B => decide (B ∈ tree) && decide (B.slot ≤ (headLabel? o).getD 0) &&
            Block.preceq b B))).length

/-- [ROOT-DIGEST-2 W1; DC goldfish_score] Resolve and count on one tree. -/
def goldfishScore {n : Nat} {mode : HeadMode} (tree : List Block)
    (raw support : List (Wire n mode)) (b : Block) : Nat :=
  goldfishScoreOn tree tree raw support b

def voterCount {n : Nat} {mode : HeadMode} (xs : List (Wire n mode)) : Nat := (seats n xs).length

def liveRoot {n : Nat} {mode : HeadMode} (st : State n mode) : Block :=
  ((st.obligations.filterMap (fun (b, _, expiry) =>
    if st.now < expiry then some b else none)).foldl (fun best b =>
      if best.depth < b.depth ||
         (best.depth == b.depth && best.root < b.root) then b else best)
    .genesis)

def advance (old candidate : Block) : Block :=
  if Block.preceq candidate old then old else candidate

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The proposal-time raw pool and its resolved subset.
Source: verified-consensus `ForkChoice/Views.lean`, `proposer_view`. -/
def proposerView {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List (Wire n mode) :=
  votesAt st (s - 1)

def proposerSupportView {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  (proposerView st s).filter (fun o =>
    match resolvedHead? st o with
    | some b => b.slot ≤ s - 1
    | none => false)

def proposalsAt {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List (Wire n mode) :=
  st.proposals.filter (fun o =>
    match o.payload with
    | .proposal b _ _ => b.slot == s
    | _ => false)

def carriedRaw {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List (Wire n mode) :=
  ((proposalsAt st s).flatMap (fun o =>
    match o.payload with
    | .proposal _ raw _ => raw.map fromHead
    | _ => [])).filter (fun o => headLabel? o == some (s - 1))

def carriedSupport {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  ((proposalsAt st s).flatMap (fun o =>
    match o.payload with
    | .proposal _ _ support => support.map fromHead
    | _ => [])).filter (fun o =>
      headLabel? o == some (s - 1) &&
      match resolvedHead? st o with
      | some b => b.slot ≤ s - 1
      | none => false)

def frozenAt {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) :
    Option (List (Wire n mode) × List (Wire n mode) × List Block) :=
  ((st.frozen.find? (fun row => row.1 == r)).map Prod.snd)

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The previous-slot freeze is a local clock evaluation. Its saved block
domain and vote subsets are later merged with current proposals. -/
def freeze (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) : State n mode :=
  let cutoff := freezeTime p r
  let raw := (votesAt st r).filter (fun o => stampVote st o < cutoff)
  let support := (votesAt st r).filter (fun o => resolvedBefore st o cutoff)
  let blocks := st.blocks.filter (fun b => stampBlock st b < cutoff)
  { st with frozen := st.frozen ++ [(r, raw, support, blocks)] }

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Previous-slot freeze and proposal merge. Source:
verified-consensus `ForkChoice/Views.lean`, `voter_view`,
`voter_support_view`, `voter_processed_block_tree`. -/
def voterView (_p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  let pool := match frozenAt st (s - 1) with
    | some (raw, _, _) => raw
    | none => []
  (pool ++ carriedRaw st s).eraseDups

def voterSupportView (_p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (s : Slot) : List (Wire n mode) :=
  let pool := match frozenAt st (s - 1) with
    | some (_, support, _) => support
    | none => []
  (pool ++ carriedSupport st s).eraseDups

def voterTree (_p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (s : Slot) : List Block :=
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

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
With no heights or finality, the Goldfish eligibility clauses are
strict majority for an old child and unconditional for a current-slot child.
Source: PROTOCOL.md §2.2, `goldfish_eligible`. -/
def goldfishEligible {n : Nat} {mode : HeadMode} (tree : List Block) (raw support : List
    (Wire n mode))
    (current : Slot) (b : Block) : Bool :=
  b.slot == current || 2 * goldfishScore tree raw support b > voterCount raw

def forkChoice {n : Nat} {mode : HeadMode} (st : State n mode) (tree : List Block)
    (raw support : List (Wire n mode)) (current : Slot) : Block :=
  ghost (liveRoot st) tree (goldfishScore st.blocks raw support)
    (goldfishEligible st.blocks raw support current)

def propose (_p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : Option
    (Msg n mode) :=
  if s == 0 then none else
    let raw := proposerView st s
    let support := proposerSupportView st s
    let parent := forkChoice st st.blocks raw support s
    let b := Block.node parent s (nodeRoot parent.root s 0) 0
    some (.proposal b (raw.filterMap toHead?) (support.filterMap toHead?))

def act (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : Option
    (Msg n mode) :=
  if s == 0 then some (.head (targetOfBlock mode .genesis)) else
    some (.head (targetOfBlock mode (forkChoice st (voterTree p st s)
      (voterView p st s) (voterSupportView p st s) s)))

def admitVote (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (o : Wire n mode) : State n mode :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      let current := (st.now / (4 * p.Δ)).toNat
      -- Retain old-label HEADs for relay and equivocation evidence. Receipt
      -- stamps keep them out of earlier frozen views and snapshots.
      if r < current - 1 || current < r || decide (o ∈ st.votes) ||
          equivocates (votesAt st r) i then st else
        { st with votes := st.votes ++ [o], voteStamp := st.voteStamp ++ [(o, st.now)] }
  | _, _ => st

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Block admission then carried-vote admission, following the source
`Handlers.lean` order. The support subset remains fixed metadata. -/
def admitProposal (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (o : Wire n mode)
    (b : Block) (raw : List (HeadWire n mode)) : State n mode :=
  let current := (st.now / (4 * p.Δ)).toNat
  let correctProposer := match o.auth with
    | .proposer s => s == b.slot
    | _ => false
  if b.slot > current || !blockKnown st b.parent || b ∈ st.blocks ||
      !(b.parent.slot < b.slot) || !correctProposer then st else
    let st' := { st with
      blocks := st.blocks ++ [b]
      blockStamp := st.blockStamp ++ [(b, st.now)]
      proposals := st.proposals ++ [o] }
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st'

def process (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (o : Wire n mode) : State n mode :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => admitVote p st o
  | .proposer _, .proposal b raw _ => admitProposal p st o b raw
  | _, _ => st

def wellFormed {n : Nat} {mode : HeadMode} (o : Wire n mode) : Bool :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => true
  | .proposer s, .proposal b raw support =>
      s == b.slot && b.parent?.isSome && b.parent.slot < s &&
      raw.all (fun v => match v.auth with
        | .seat r _ => r == s - 1
        | _ => false) &&
      support.all (fun v => decide (v ∈ raw))
  | _, _ => false

def depsPresent {n : Nat} {mode : HeadMode} (st : State n mode) (o : Wire n mode) : Bool :=
  match o.payload with
  | .head _ => true
  | .proposal b _ _ => blockKnown st b.parent

def processed {n : Nat} {mode : HeadMode} (st : State n mode) (o : Wire n mode) : Bool :=
  match o.payload with
  | .head _ => decide (o ∈ st.votes)
  | .proposal b _ _ => blockKnown st b

def carries {n : Nat} {mode : HeadMode} (parent child : Wire n mode) : Prop :=
  match parent.payload with
  | .head _ => False
  | .proposal _ raw support => child ∈ raw.map fromHead ∨ child ∈ support.map fromHead

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
A direct delivery calls its handler. A proposal calls its raw HEAD
handlers only when its block enters the store. This matches the reference
`Execution.handles` / `NamedReceiptCalls.postCore` admission test.
Support metadata alone does not cause a call; `carries` remains structural
for signature checks, including rejected proposals. -/
def handles (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (parent child : Wire n mode) : Prop :=
  parent = child ∨ match parent.payload with
    | .proposal b raw _ =>
        b ∉ st.blocks ∧ b ∈ (process p st parent).blocks ∧ child ∈ raw.map fromHead
    | .head _ => False

def earlyVotes (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) : List
    (Wire n mode) :=
  (votesAt st r).filter (fun o => resolvedBefore st o (earlyTime p r))

def savedEarly {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) : List (Wire n mode) :=
  ((st.early.find? (fun row => row.1 == r)).map Prod.snd).getD []

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
`D_i[r,u]`: max distinct seats among labels in the fixed vote-time
window. An equivocating seat occurs once. Source: guarded-override.md §3.1. -/
def lateVotes (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) : List
    (Wire n mode) :=
  (votesAt st r).filter (fun o => stampVote st o < gateTime p r)

def cleanSupport (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (r : Slot) : List (Wire n mode) :=
  (earlyVotes p st r).filter (fun o =>
    !(lateVotes p st r).any (fun u => sameSeat u o && u != o))

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Genuine Goldfish confirmation at `d_r` with the walk anchored at `a`:
early resolved support, late equivocation exclusion, and a strict majority
of late participants. The final test checks the walk result itself. -/
def confirmationFrom (p : Params) {n : Nat} {mode : HeadMode} (a : Block) (st : State n mode)
    (r : Slot) :
    Option Block :=
  let support := cleanSupport p st r
  let late := lateVotes p st r
  let eligible := fun b => 2 * goldfishScoreOn
    (resolutionTree st) st.blocks support support b > voterCount late
  let h := ghost a st.blocks (goldfishScoreOn
    (resolutionTree st) st.blocks support support) eligible
  if eligible h then some h else none

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Genuine Goldfish confirmation at `d_r`: early resolved support,
late equivocation exclusion, and a strict majority of late participants.
The walk starts at genesis; proposals and HEADs start at the live root. -/
def confirmation (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (r : Slot) : Option Block :=
  let support := cleanSupport p st r
  let late := lateVotes p st r
  let eligible := fun b => 2 * goldfishScoreOn
    (resolutionTree st) st.blocks support support b > voterCount late
  let h := ghost .genesis st.blocks (goldfishScoreOn
    (resolutionTree st) st.blocks support support) eligible
  if eligible h then some h else none

theorem confirmation_eq_from_genesis (p : Params) {n : Nat} {mode : HeadMode}
    (st : State n mode) (r : Slot) :
    confirmation p st r = confirmationFrom p .genesis st r := rfl

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
A resolved label-r HEAD contributes to release only when its seat has
exactly one known label-r HEAD and its target conflicts with the obligation. -/
def releaseCount (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot)
    (b : Block) : Nat :=
  let raw := votesAt st r
  let resolved := raw.filter (fun o => resolvedBefore st o (releaseTime p r))
  ((seats n resolved).filter (fun i =>
    !equivocates raw i &&
    (seatVotes resolved i).any (fun o =>
      match resolvedHead? st o with
      | some target => !Block.compatible target b
      | none => false))).length

def expire {n : Nat} {mode : HeadMode} (st : State n mode) (t : Time) : State n mode :=
  { st with obligations := st.obligations.filter (fun (_, _, deadline) => t < deadline) }

def release (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (r : Slot) : State n mode :=
  let raw := votesAt st r
  let resolved := raw.filter
    (fun o => resolvedBefore st o (releaseTime p r))
  { st with
    releaseSnapshots := st.releaseSnapshots ++ [(r, raw, resolved)]
    obligations := st.obligations.filter
      (fun (b, g, _) => releaseCount p st r b < g) }

def deadlineOf {n : Nat} {mode : HeadMode} (st : State n mode) (b : Block)
    (g : Nat) : Option Time :=
  ((st.obligations.find? (fun (target, level, _) =>
    target == b && level == g)).map (fun (_, _, deadline) => deadline))

def writeObligation {n : Nat} {mode : HeadMode} (st : State n mode) (b : Block) (g : Nat)
    (deadline : Time) : State n mode :=
  let newDeadline := max (deadlineOf st b g |>.getD deadline) deadline
  { st with obligations :=
    st.obligations.filter (fun (target, level, _) =>
      !(target == b && level == g)) ++ [(b, g, newDeadline)] }

def prefixSupport (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot)
    (b : Block) : Nat :=
  goldfishScoreOn (resolutionTree st) st.blocks (cleanSupport p st r) (cleanSupport p st r) b

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The single SA release threshold is the ceiling of half the seats. -/
def releaseThreshold (p : Params) : Nat := (p.n + 1) / 2

def savedGenuine {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot) : Option
    (Option Block) :=
  (st.genuine.find? (fun row => row.1 == r)).map Prod.snd

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Save the raw result before the local guard. A saved label is immutable. -/
def recordGenuine [LeasePolicy] {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot)
    (result : Option Block) : List (Slot × Option Block) :=
  if LeasePolicy.slowArming && !(savedGenuine st r).isSome then
    st.genuine ++ [(r, result)] else st.genuine

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The current genuine result is supplied separately. The preceding `m-1`
labels must all exist and cover the same prefix. No negative label is used. -/
def slowEligible (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode) (r : Slot)
    (b : Block) : Bool :=
  p.m ≤ r + 1 && (List.range (p.m - 1)).all (fun j =>
    match savedGenuine st (r - (j + 1)) with
    | some (some C) => Block.preceq b C
    | _ => false)

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The shared gate changes only the selected lease levels. SA selects
its one level after either admission test. The outer gate checks containment. -/
def admissionLevels [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (r : Slot) (b : Block) : List Nat :=
  if LeasePolicy.slowArming then
    if releaseThreshold p ≤ prefixSupport p st r b || slowEligible p st r b then
      [releaseThreshold p] else []
  else
    (List.range (p.n + 1)).filter (fun g => g ∈ p.grid && g ≤ prefixSupport p st r b)

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
A genuine gate advances G. It advances S and writes obligations only
when the result is compatible with every live target. The walk starts at `a`. -/
def gateFrom [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode} (a : Block)
    (st : State n mode) (r : Slot) :
    State n mode :=
  match confirmationFrom p a st r with
  | none => { st with genuine := recordGenuine st r none }
  | some h =>
      let levels := admissionLevels p st r
      let st := { st with
        goldfishRecord := advance st.goldfishRecord h
        genuine := recordGenuine st r (some h) }
      if st.obligations.any (fun (target, _, _) =>
        !Block.compatible target h) then st else
        let st := { st with stableRecord := advance st.stableRecord h }
        let prefixes := st.blocks.filter (fun b =>
          b != .genesis && Block.preceq b h)
        prefixes.foldl (fun acc b =>
          (levels b).foldl
            (fun acc g => writeObligation acc b g (gateTime p r + lifetime p)) acc) st

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
A genuine gate advances G. It advances S and writes obligations only
when the result is compatible with every live target. -/
def gate [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (r : Slot) : State n mode :=
  match confirmation p st r with
  | none => { st with genuine := recordGenuine st r none }
  | some h =>
      let levels := admissionLevels p st r
      let st := { st with
        goldfishRecord := advance st.goldfishRecord h
        genuine := recordGenuine st r (some h) }
      if st.obligations.any (fun (target, _, _) =>
        !Block.compatible target h) then st else
        let st := { st with stableRecord := advance st.stableRecord h }
        let prefixes := st.blocks.filter (fun b =>
          b != .genesis && Block.preceq b h)
        prefixes.foldl (fun acc b =>
          (levels b).foldl
            (fun acc g => writeObligation acc b g (gateTime p r + lifetime p)) acc) st

theorem gate_eq_from_genesis [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode}
    (st : State n mode)
    (r : Slot) : gate p st r = gateFrom p .genesis st r := rfl

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Local public-time evaluations run for awake and asleep nodes. Equality
checks make each cutoff run once; same-time expiry precedes acquisition.
The gate walk starts at `a`. -/
def clockFrom [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode} (a : Block)
    (st : State n mode) (t : Time) :
    State n mode :=
  let st := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p st fSlot else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { st with early := st.early ++ [(eSlot, earlyVotes p st eSlot)] }
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p st qSlot else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gateFrom p a st dSlot else st

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Local public-time evaluations run for awake and asleep nodes. Equality
checks make each cutoff run once; same-time expiry precedes acquisition. -/
def clock [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (t : Time) : State n mode :=
  let st := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p st fSlot else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { st with early := st.early ++ [(eSlot, earlyVotes p st eSlot)] }
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p st qSlot else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p st dSlot else st

theorem clock_eq_from_genesis [LeasePolicy] (p : Params) {n : Nat} {mode : HeadMode}
    (st : State n mode)
    (t : Time) : clock p st t = clockFrom p .genesis st t := rfl

def confirmed {n : Nat} {mode : HeadMode} (st : State n mode) : Block := st.stableRecord

def stable {n : Nat} {mode : HeadMode} (st : State n mode) : Block := st.stableRecord

def block {n : Nat} {mode : HeadMode} : Msg n mode → Option Block
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

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
Permanent rejection (design §2 E4) of a HEAD that is not yet processed:
its label `r` is before the previous slot (the clock only goes forward), or
its seat already equivocates at `r`. `admitVote` returns the state unchanged
in both cases, and in no later state of a valid run accepts the HEAD. A
processed HEAD is not excluded, and a proposal is never excluded. "Exactly the
permanent refusals" is a statement about objects that pass the wire check
(`wellFormed`). An ill-formed object is outside every valid run by
`DeliveryWellFormed.wire`, so `excludes` does not have to cover it. -/
def excludes (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
    (o : Wire n mode) : Bool :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      !decide (o ∈ st.votes) &&
        (decide (r + 1 < (st.now / (4 * p.Δ)).toNat) || equivocates (votesAt st r) i)
  | _, _ => false

/-- [ROOT-DIGEST-2 W1; DC shared Goldfish engine]
The C* instance: seat identities occur in authentication only. Every
seat of a label signs the same payload. Source: CONTRACT.md §2a. -/
def gridCO [LeasePolicy] (p : Params) : ProtocolSpec p.n where
  State := State p.n
  Label := Slot
  Payload := Msg p.n
  init := initial p.n
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
  excludes := excludes p
  handles := handles p
  carries := carries

private theorem proposalTime_eq_1_export : type_of% (@proposalTime.eq_1) := @proposalTime.eq_1
private theorem gateTime_eq_1_export : type_of% (@gateTime.eq_1) := @gateTime.eq_1
private theorem initial_eq_1_export : type_of% (@initial.eq_1) := @initial.eq_1
private theorem blockKnown_eq_1_export : type_of% (@blockKnown.eq_1) := @blockKnown.eq_1
private theorem votesAt_eq_1_export : type_of% (@votesAt.eq_1) := @votesAt.eq_1
private theorem equivocates_eq_1_export : type_of% (@equivocates.eq_1) := @equivocates.eq_1
private theorem writeObligation_eq_1_export : type_of% (@writeObligation.eq_1) :=
  @writeObligation.eq_1
private theorem excludes_eq_1_export : type_of% (@excludes.eq_1) := @excludes.eq_1

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem act_eq_1_export :
    type_of% (@act.eq_1) := @act.eq_1
private theorem admissionLevels_eq_1_export :
    type_of% (@admissionLevels.eq_1) := @admissionLevels.eq_1
private theorem admitVote_eq_1_export :
    type_of% (@admitVote.eq_1) := @admitVote.eq_1
private theorem cleanSupport_eq_1_export :
    type_of% (@cleanSupport.eq_1) := @cleanSupport.eq_1
private theorem earlyVotes_eq_1_export :
    type_of% (@earlyVotes.eq_1) := @earlyVotes.eq_1
private theorem expire_eq_1_export :
    type_of% (@expire.eq_1) := @expire.eq_1
private theorem forkChoice_eq_1_export :
    type_of% (@forkChoice.eq_1) := @forkChoice.eq_1
private theorem headTarget_eq_1_export :
    type_of% (@headTarget?.eq_1) := @headTarget?.eq_1
private theorem process_eq_1_export :
    type_of% (@process.eq_1) := @process.eq_1
private theorem releaseThreshold_eq_1_export :
    type_of% (@releaseThreshold.eq_1) := @releaseThreshold.eq_1
private theorem resolutionTree_eq_1_export :
    type_of% (@resolutionTree.eq_1) := @resolutionTree.eq_1
private theorem resolutionTree_eq_2_export :
    type_of% (@resolutionTree.eq_2) := @resolutionTree.eq_2
private theorem resolveTarget_eq_1_export :
    type_of% (@resolveTarget.eq_1) := @resolveTarget.eq_1
private theorem resolveTarget_eq_2_export :
    type_of% (@resolveTarget.eq_2) := @resolveTarget.eq_2
private theorem resolvedHead_eq_1_export :
    type_of% (@resolvedHead?.eq_1) := @resolvedHead?.eq_1
private theorem seatVotes_eq_1_export :
    type_of% (@seatVotes.eq_1) := @seatVotes.eq_1
private theorem seats_eq_1_export :
    type_of% (@seats.eq_1) := @seats.eq_1
private theorem targetOfBlock_eq_1_export :
    type_of% (@targetOfBlock.eq_1) := @targetOfBlock.eq_1
private theorem targetOfBlock_eq_2_export :
    type_of% (@targetOfBlock.eq_2) := @targetOfBlock.eq_2
private theorem voterCount_eq_1_export :
    type_of% (@voterCount.eq_1) := @voterCount.eq_1
private theorem voterSupportView_eq_1_export :
    type_of% (@voterSupportView.eq_1) := @voterSupportView.eq_1
private theorem voterView_eq_1_export :
    type_of% (@voterView.eq_1) := @voterView.eq_1

end AvailableChain.GridCO
end

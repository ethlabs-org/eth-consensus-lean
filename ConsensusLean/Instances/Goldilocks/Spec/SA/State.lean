module
public import Mathlib.Order.WithBot
public import Mathlib.Data.Set.Defs
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Schedule

@[expose] public section

/-! # Goldilocks SA: votes, payload, state

goldilocks-spec.tex §"State" and §"Votes and views".

* The wire message is the Goldfish vote `(val_index, s, H)`, which names its head by root.
  Signatures are not modelled (as for the FG's attestations): the signer of a vote is its
  validator, the committee of every slot is `V` (so the committee test holds by typing), and
  unforgeability is a run premise (claims §"Runs").
* The payload of a block is `(votes, support_votes)`, two lists.
* The state `𝒜 = (gf_votes[·], timestamp[·], saved_confirmation[·], locks, latest_confirmed,
  fg_reported, voted_slot, restart_time)`. The AC holds blocks only by name (root). Stamps are
  on the extended time line `ETime` (`⊥ = −∞`, `⊤ = +∞`): `timestamp[genesis] = −∞`, and a vote
  or block the AC never accepted reads `+∞` (no rule reads such a stamp at a reachable state).
  `restart_time` is `−∞` before any restart. Saved confirmations are kept for every integer
  slot, negative ones included (`⊥` initially). -/

namespace Consensus.Goldilocks.SA

/-- A Goldfish vote `(val_index, s, H)`: validator `val`, slot `slot`, head named by root. -/
structure Vote (n : Nat) where
  /-- The validator (the signer). -/
  val : Fin n
  /-- The slot of the vote. -/
  slot : Nat
  /-- The root of the head. -/
  head : Nat
  deriving DecidableEq

/-- The AC payload of a block: `(votes, support_votes)`. -/
abbrev Payload (n : Nat) := List (Vote n) × List (Vote n)

/-- A lock `(B, j, f, e)`: a block (by root), the slot of the confirmation that wrote it, the
fast bit, and its expiry. -/
structure Lock where
  /-- The root of the locked block. -/
  block : Nat
  /-- The slot of the confirmation that wrote the lock. -/
  slot : Nat
  /-- The fast bit. -/
  fast : Bool
  /-- The last slot of its life (inclusive), fixed at its write (for every lock the SA writes,
  `slot + 2 ≤ expiry ≤ slot + k`). -/
  expiry : Nat
  deriving DecidableEq

/-- The extended time line: `⊥ = −∞`, `⊤ = +∞`. -/
abbrev ETime := WithBot (WithTop Time)

/-- A finite time on the extended line. -/
def ETime.of (t : Time) : ETime := ((t : WithTop Time) : WithBot (WithTop Time))

/-- The Goldilocks AC state. -/
structure SAState (n : Nat) where
  /-- `gf_votes[s]`: the accepted slot-`s` votes, in the order of acceptance. -/
  pool : Nat → List (Vote n)
  /-- `timestamp[x]` of a vote: when the AC accepted it (`+∞`: never). -/
  voteStamp : Vote n → ETime
  /-- `timestamp[x]` of a block, by root (`−∞` for genesis, `+∞`: never). -/
  blockStamp : Nat → ETime
  /-- `saved_confirmation[s]`: the result of the slot-`s` update (a root), or `⊥`. -/
  saved : Int → Option Nat
  /-- `locks`: the set of locks. -/
  locks : Set Lock
  /-- `latest_confirmed`: the stored confirmed block (a root). -/
  latestConfirmed : Nat
  /-- `fg_reported`: the latest block given to the FG (a root). -/
  fgReported : Nat
  /-- `voted_slot`: the slot of the latest vote (`−1` initially). -/
  votedSlot : Int
  /-- `restart_time`: the time of the latest restart (`−∞` initially). -/
  restartTime : WithBot Time
  /-- Own historical vote permission, installed by the execution at init and kept across
  restarts by `ac_restart` (`acRestart`). The population-wide stock binding permits every slot. -/
  mayVote : Nat → Bool := fun _ => true

namespace SAState

variable {n : Nat}

/-- `initial_ac()`: empty pools and locks, `⊥` saved everywhere, `timestamp = {genesis ↦ −∞}`,
genesis as the confirmed and the reported block, `voted_slot = −1`, `restart_time = −∞`. -/
def initial (g : Nat) : SAState n where
  pool := fun _ => []
  voteStamp := fun _ => ⊤
  blockStamp := fun r => if r = g then ⊥ else ⊤
  saved := fun _ => none
  locks := ∅
  latestConfirmed := g
  fgReported := g
  votedSlot := -1
  restartTime := ⊥

/-- The slot-`s` pool for an integer slot: empty for a negative slot. -/
def poolAt (A : SAState n) (s : Int) : List (Vote n) := if s < 0 then [] else A.pool s.toNat

end SAState

/-- `joined(𝒜, t)`: `restart_time ≤ t_{slot(t)-1}`, awake with no restart since the start of the
previous slot. -/
def joined (sp : SAParams) (A : SAState sp.n) (t : Time) : Prop :=
  A.restartTime ≤ ((sp.ts ((sp.slot t : Int) - 1) : Time) : WithBot Time)

end Consensus.Goldilocks.SA

end

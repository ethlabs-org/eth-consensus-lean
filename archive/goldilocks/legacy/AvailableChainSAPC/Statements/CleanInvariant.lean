module
public import AvailableChainSAPC.Statements.Contract

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A protected path is closed under ancestry. It need not contain every
admitted proposal or every HEAD target. -/
structure CleanPath (path : Block → Prop) : Prop where
  genesis : path .genesis
  closed : ∀ a b, Block.Preceq a b → path b → path a
  comparable : ∀ a b, path a → path b → Block.Compatible a b

/-- The finite part of the joint invariant. Rows are justified by their
raw sources, not by the false assertion that every row is below S. -/
structure CleanStateOnPath {n : Nat} (path : Block → Prop)
    (st : GridCO.State n) : Prop where
  stable : path st.stableRecord
  goldfish : path st.goldfishRecord
  finite : ∀ b g d, (b, g, d) ∈ st.obligations → path b
  saved : ∀ r b, (r, some b) ∈ st.genuine → path b

/-- An honest timely-N source is an actual early tick and its successful
immutable save. This is stronger than a later archive quorum. -/
def HonestTimelySource {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (r : Slot) (b : Block) : Prop :=
  ∃ v ∈ rho.honest, ∃ j < index,
    rho.events[j]? = some (.tick v (earlyTime p r)) ∧
    savedTimely (Run.stateBefore (sapc p) rho (j + 1) v) r = some (some b)

/-- Conditional path facts retained from round 9. This is not an induction
invariant for arbitrary paths. See `JointCleanInvariant` below for the
run-determined statement.

One collection of chronological facts, for all honest event-prefix
states. Outside the cap, path membership is required at actual authority
uses: gate, HEAD, and proposal ticks. Storage alone is not a use. Disabled
PCs remain in the archive.
Uncapped timely saves are not all asserted to be on one path. A failed
N transfer must instead disable its later authority (the event-step task).

`accessible` records an honest admitted path; `transferred` records its
continuation at actual HEAD duties. Both are needed. Mere block storage
does not establish that a walk follows the path. -/
structure CleanPathFacts {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (index : Nat) (path : Block → Prop) : Prop where
  chain : CleanPath path
  states : ∀ i, i ≤ index → ∀ v ∈ rho.honest,
    CleanStateOnPath path (Run.stateBefore (sapc p) rho i v).base
  accessible : ∀ b, path b → b = .genesis ∨
    ∃ v ∈ rho.honest, ∃ i, i ≤ index ∧
      pathKnown (Run.stateBefore (sapc p) rho i v) b = true
  finiteSources : ∀ v ∈ rho.honest, ∀ b g d,
    (b, g, d) ∈ (Run.stateBefore (sapc p) rho index v).base.obligations →
    ∃ j < index, ∃ r c,
      rho.events[j]? = some (.tick v (gateTime p r)) ∧
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some c ∧
      Block.Preceq b c
  genuine : ∀ j, j < index → ∀ v ∈ rho.honest, ∀ r b,
    rho.events[j]? = some (.tick v (gateTime p r)) →
    SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b → path b
  transferred : ∀ j, j < index → ∀ v ∈ rho.honest, ∀ r b,
    rho.events[j]? = some (.tick v (gateTime p r)) →
    SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b →
    ∀ k, k < index → ∀ w ∈ rho.honest, ∀ s, r < s →
      rho.events[k]? = some (.tick w (voteTime p s)) →
      Block.Preceq b (headTarget p
        (clock p (Run.stateBefore (sapc p) rho k w) (voteTime p s)) s)
  certificates : ∀ i, i ≤ index → ∀ v ∈ rho.honest, ∀ c,
    pcValid p (Run.stateBefore (sapc p) rho i v) c = true →
    HonestTimelySource p rho i c.slot c.target ∧
      (FaultBound (sapc p) (pcFaultCap p) rho → path c.target)
  timely : ∀ i, i ≤ index → ∀ v ∈ rho.honest, ∀ r b,
    savedTimely (Run.stateBefore (sapc p) rho i v) r = some (some b) →
    HonestTimelySource p rho i r b ∧
      (FaultBound (sapc p) (pcFaultCap p) rho → path b)
  cappedMode : FaultBound (sapc p) (pcFaultCap p) rho →
    ∀ i, i ≤ index → ∀ v ∈ rho.honest,
      capBroken p (Run.stateBefore (sapc p) rho i v) = false
  authentic : ∀ i, i ≤ index → ∀ v ∈ rho.honest, ∀ r seat data,
    (⟨.seat r seat, data⟩ : HeadWire p.n) ∈
      (Run.stateBefore (sapc p) rho i v).receivedHeads →
    rho.seatOf r seat ∈ rho.honest →
    Run.emits (sapc p) E rho (rho.seatOf r seat)
      (fromHead ⟨.seat r seat, data⟩) (voteTime p r)

  gateAuthorities : ∀ i, i < index → ∀ v ∈ rho.honest, ∀ r c,
    rho.events[i]? = some (.tick v (gateTime p r)) →
    capBroken p (Run.stateBefore (sapc p) rho i v) = false →
    (Run.stateBefore (sapc p) rho i v).bestPC = some c → path c.target
  headAuthorities : ∀ i, i < index → ∀ v ∈ rho.honest, ∀ r c,
    rho.events[i]? = some (.tick v (voteTime p r)) →
    capBroken p (clock p (Run.stateBefore (sapc p) rho i v) (voteTime p r)) = false →
    selectedPC p (clock p (Run.stateBefore (sapc p) rho i v) (voteTime p r)) r = some c →
    path c.target
  proposalAuthorities : ∀ i, i < index → ∀ v ∈ rho.honest, ∀ r c,
    rho.events[i]? = some (.tick v (proposalTime p r)) →
    capBroken p (clock p (Run.stateBefore (sapc p) rho i v) (proposalTime p r)) = false →
    (clock p (Run.stateBefore (sapc p) rho i v) (proposalTime p r)).bestPC = some c →
    path c.target

/-- Sources that actually occur in the run. Mere block storage is not a
source. Uncapped N storage is not a source either: a failed N can lose
all PC authority before its first gate effect. -/
inductive CleanRunSource {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (index : Nat) : Block → Prop
  | genuine (j : Nat) (hj : j < index) (v : V) (hv : v ∈ rho.honest)
      (r : Slot) (b : Block)
      (tick : rho.events[j]? = some (.tick v (gateTime p r)))
      (raw : SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b) :
      CleanRunSource p rho index b
  | timely (r : Slot) (b : Block) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
      (source : HonestTimelySource p rho index r b) : CleanRunSource p rho index b
  | gate (j : Nat) (hj : j < index) (v : V) (hv : v ∈ rho.honest)
      (r : Slot) (c : PC p.n)
      (tick : rho.events[j]? = some (.tick v (gateTime p r)))
      (active : capBroken p (Run.stateBefore (sapc p) rho j v) = false)
      (selected : (Run.stateBefore (sapc p) rho j v).bestPC = some c) :
      CleanRunSource p rho index c.target
  | head (j : Nat) (hj : j < index) (v : V) (hv : v ∈ rho.honest)
      (r : Slot) (c : PC p.n)
      (tick : rho.events[j]? = some (.tick v (voteTime p r)))
      (active : capBroken p (clock p (Run.stateBefore (sapc p) rho j v)
        (voteTime p r)) = false)
      (selected : selectedPC p (clock p (Run.stateBefore (sapc p) rho j v)
        (voteTime p r)) r = some c) : CleanRunSource p rho index c.target
  | proposal (j : Nat) (hj : j < index) (v : V) (hv : v ∈ rho.honest)
      (r : Slot) (c : PC p.n)
      (tick : rho.events[j]? = some (.tick v (proposalTime p r)))
      (active : capBroken p (clock p (Run.stateBefore (sapc p) rho j v)
        (proposalTime p r)) = false)
      (selected : (clock p (Run.stateBefore (sapc p) rho j v)
        (proposalTime p r)).bestPC = some c) : CleanRunSource p rho index c.target

/-- The least ancestry-closed set generated by actual clean sources.
This function has no path argument and makes no choice of a stored branch.
Whether its members are comparable is a proof obligation. -/
def cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (index : Nat) (b : Block) : Prop :=
  b = .genesis ∨ ∃ c, CleanRunSource p rho index c ∧ Block.Preceq b c

/-- Event-prefix form of the ordered genuine history used by the shared
SA/Grid CO induction. Continuation at actual HEADs is the `transferred`
field of `CleanPathFacts`. -/
def OrderedGenuine {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) : Prop :=
  ∀ j, j < index → ∀ k, k < index → ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    ∀ r s b c, r < s →
      rho.events[j]? = some (.tick v (gateTime p r)) →
      rho.events[k]? = some (.tick w (gateTime p s)) →
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b →
      SA.confirmation p (Run.stateBefore (sapc p) rho k w).base s = some c →
      Block.Preceq b c

/-- The new induction statement is determined by the run. Its base part
is ordered genuine history with actual honest HEAD continuation and
finite lease sources. The additional clauses concern timely saves, PC
witnesses and authority, and the mode flag under the cap. -/
structure JointCleanInvariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (index : Nat) : Prop where
  facts : CleanPathFacts p E rho index (cleanRunPath p rho index)
  ordered : OrderedGenuine p rho index

end AvailableChain.SAPC
end

module
public import AvailableChainSA.Model.Protocol

@[expose] public section
namespace AvailableChain.SAPC

abbrev Params := SA.Params
abbrev lifetime := SA.lifetime
abbrev proposalTime := SA.proposalTime
abbrev voteTime := SA.voteTime
abbrev earlyTime := SA.earlyTime
abbrev freezeTime := SA.freezeTime
abbrev releaseTime := SA.releaseTime
abbrev gateTime := SA.gateTime
abbrev releaseThreshold := SA.releaseThreshold

def pcFaultCap (p : Params) : Nat := (p.n - 1) / 3
def pcQuorum (p : Params) : Nat := (2 * p.n + 2) / 3

/-- The ack is in the original HEAD signature. It is not a second duty. -/
structure HeadData where
  target : Block
  ack : Option (Slot × Block) := none
  deriving DecidableEq, Repr

abbrev HeadWire (n : Nat) := Signed Slot n HeadData

structure PC (n : Nat) where
  slot : Slot
  target : Block
  witnesses : List (HeadWire n)
  deriving DecidableEq, Repr

inductive Msg (n : Nat) where
  | head (data : HeadData)
  | proposal (b : Block) (view supportView : List (HeadWire n)) (pc : Option (PC n))
  | pc (certificate : PC n)
  deriving DecidableEq, Repr

abbrev Wire (n : Nat) := Signed Slot n (Msg n)

def fromHead {n : Nat} (o : HeadWire n) : Wire n := ⟨o.auth, .head o.payload⟩

/-- Internal base key only. This function does not create a signature. -/
def baseHead {n : Nat} (o : HeadWire n) : GridCO.HeadWire n :=
  ⟨o.auth, o.payload.target⟩

def baseWire {n : Nat} (o : HeadWire n) : GridCO.Wire n :=
  GridCO.fromHead (baseHead o)

def baseProposal {n : Nat} (o : Wire n) (b : Block)
    (raw support : List (HeadWire n)) : GridCO.Wire n :=
  ⟨o.auth, .proposal b (raw.map baseHead) (support.map baseHead)⟩

/-- The ordinary engine stores base keys. Complete signatures stay in the
archive and proposal store. All ordinary views, stamps, leases, release,
raw history, and GHOST operations are shared with SA. -/
structure State (n : Nat) where
  base : GridCO.State n := GridCO.initial n
  proposals : List (Wire n) := []
  receivedHeads : List (HeadWire n) := []
  headStamp : List (HeadWire n × Time) := []
  timely : List (Slot × Option Block) := []
  bestPC : Option (PC n) := none
  frozenPC : List (Slot × Option (PC n)) := []
  deriving Repr

def initial (n : Nat) : State n := {}

def headLabel? {n : Nat} (o : HeadWire n) : Option Slot :=
  match o.auth with
  | .seat r _ => some r
  | _ => none

def headSeat? {n : Nat} (o : HeadWire n) : Option (Fin n) :=
  match o.auth with
  | .seat _ i => some i
  | _ => none

/-- Full admitted ancestry is required for N and PC evidence. -/
def pathKnown {n : Nat} (st : State n) : Block → Bool
  | .genesis => GridCO.blockKnown st.base .genesis
  | b@(.node parent _ _ _) => GridCO.blockKnown st.base b && pathKnown st parent

def stampHead {n : Nat} (st : State n) (o : HeadWire n) : Time :=
  ((st.headStamp.find? (fun row => row.1 == o)).map Prod.snd).getD st.base.now

def pathBefore {n : Nat} (st : State n) (cutoff : Time) : Block → Bool
  | .genesis => GridCO.blockKnown st.base .genesis &&
      GridCO.stampBlock st.base .genesis < cutoff
  | b@(.node parent _ _ _) => GridCO.blockKnown st.base b &&
      GridCO.stampBlock st.base b < cutoff && pathBefore st cutoff parent

def stable {n : Nat} (st : State n) : Block := st.base.stableRecord
def confirmed {n : Nat} (st : State n) : Block := st.base.stableRecord
def strong {n : Nat} (st : State n) : Block :=
  (st.bestPC.map PC.target).getD .genesis

def block {n : Nat} : Msg n → Option Block
  | .proposal b _ _ _ => some b
  | _ => none

end AvailableChain.SAPC
end

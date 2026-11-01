module
public import AvailableChainSAPC.Model.Certificates

@[expose] public section
namespace AvailableChain.SAPC

/-- Archive a complete signature once. Only the base projection enters
the shared two-target cache, with its original base receipt stamp. -/
def receiveHead (p : Params) {n : Nat} (st : State n) (o : HeadWire n) : State n :=
  match o.auth with
  | .seat r _ =>
      if (st.base.now / (4 * p.Δ)).toNat < r then st else
        let st := if o ∈ st.receivedHeads then st else
          { st with receivedHeads := st.receivedHeads ++ [o],
                    headStamp := st.headStamp ++ [(o, st.base.now)] }
        { st with base := GridCO.admitVote p.engine st.base (baseWire o) }
  | _ => st

def admitHead (p : Params) {n : Nat} (st : State n) (o : HeadWire n) : State n :=
  collectPCs p (receiveHead p st o)

/-- Reuse the exact shared block admission test. The empty final argument
defers carried HEAD calls to the handler for complete signatures. -/
def proposalBase (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) : GridCO.State n :=
  GridCO.admitProposal p.engine st.base (baseProposal o b raw support) b []

def proposalEnters (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) : Bool :=
  !(GridCO.blockKnown st.base b) &&
    GridCO.blockKnown (proposalBase p st o b raw support) b

def pcMembers {n : Nat} (c : Option (PC n)) : List (HeadWire n) :=
  (c.map PC.witnesses).getD []

def admitProposal (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) (c : Option (PC n)) : State n :=
  if proposalEnters p st o b raw support then
    let st := { st with
      base := proposalBase p st o b raw support
      proposals := st.proposals ++ [o] }
    collectPCs p ((raw ++ pcMembers c).foldl (receiveHead p) st)
  else st

def pcEnvelopeReady (p : Params) {n : Nat} (st : State n) (c : PC n) : Bool :=
  pcWellFormed p c && pcPaths st c &&
    c.slot + 1 ≤ (st.base.now / (4 * p.Δ)).toNat

def process (p : Params) {n : Nat} (st : State n) (o : Wire n) : State n :=
  match o.auth, o.payload with
  | .seat _ _, .head h => admitHead p st ⟨o.auth, h⟩
  | .proposer _, .proposal b raw support c => admitProposal p st o b raw support c
  | .none, .pc c =>
      if pcEnvelopeReady p st c then
        let st := c.witnesses.foldl (receiveHead p) st
        -- A direct valid encoding takes priority over an assembled tie.
        collectPCs p (installPC st c)
      else st
  | _, _ => st

def wellFormed (p : Params) {n : Nat} (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => true
  | .proposer s, .proposal b raw support c =>
      s == b.slot && b.parent?.isSome && b.parent.slot < s &&
      raw.all (fun v => match v.auth with
        | .seat r _ => r == s - 1
        | _ => false) &&
      support.all (fun v => v ∈ raw) &&
      (match c with | none => true | some cert => pcWellFormed p cert)
  | .none, .pc c => pcWellFormed p c
  | _, _ => false

def depsPresent {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.payload with
  | .head _ => true
  | .proposal b _ _ _ => GridCO.blockKnown st.base b.parent
  | .pc c => pcPaths st c

def processed (p : Params) {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.payload with
  | .head h => ⟨o.auth, h⟩ ∈ st.receivedHeads
  | .proposal b _ _ _ => GridCO.blockKnown st.base b
  | .pc c => pcValid p st c

/-- Structural signature obligations include rejected containers. -/
def carries {n : Nat} (parent child : Wire n) : Prop :=
  match parent.payload with
  | .head _ => False
  | .proposal _ raw support c =>
      child ∈ (raw ++ support ++ pcMembers c).map fromHead
  | .pc c => child ∈ c.witnesses.map fromHead

/-- Member calls follow the actual admission branches, not containment. -/
def handles (p : Params) {n : Nat} (st : State n) (parent child : Wire n) : Prop :=
  parent = child ∨ match parent.auth, parent.payload with
    | .proposer _, .proposal b raw support c =>
        proposalEnters p st parent b raw support = true ∧
          child ∈ (raw ++ pcMembers c).map fromHead
    | .none, .pc c =>
        pcEnvelopeReady p st c = true ∧ child ∈ c.witnesses.map fromHead
    | _, _ => False

end AvailableChain.SAPC
end

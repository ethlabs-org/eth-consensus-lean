module
public import AvailableChainSAPC.Model.Handlers

@[expose] public section
namespace AvailableChain.SAPC

def frozenPCAt {n : Nat} (st : State n) (r : Slot) : Option (PC n) :=
  ((st.frozenPC.find? (fun row => row.1 == r)).map Prod.snd).getD none

/-- The HEAD does not consult a later live PC. Start with the freeze,
then compare valid carried PCs in the stored proposal order. -/
def selectedPC (p : Params) {n : Nat} (st : State n) (r : Slot) : Option (PC n) :=
  st.proposals.foldl (fun best o =>
    match o.payload with
    | .proposal b _ _ (some c) =>
        if b.slot == r && pcValid p st c then preferPC best c else best
    | _ => best) (frozenPCAt st (r - 1))

def deepest (blocks : List Block) : Block :=
  blocks.foldl (fun best b =>
    if best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root) then b else best) .genesis

/-- Use the ordinary eligible walk from genesis, then take its deepest
non-genesis prefix with more than f support. Paths add no votes. -/
def floor (p : Params) {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot) : Block :=
  let score := GridCO.goldfishScore st.base.blocks raw support
  let w := GridCO.ghost .genesis tree score
    (GridCO.goldfishEligible st.base.blocks raw support r)
  deepest (st.base.blocks.filter (fun b =>
    b != .genesis && Block.preceq b w && pcFaultCap p < score b))

def preliminaryAnchor (f : Block) {n : Nat} (c : Option (PC n)) : Block :=
  match c with
  | none => f
  | some cert =>
      if f == .genesis || Block.preceq f cert.target then cert.target else f

/-- Every finite target is mandatory. An F4 floor cannot bypass a lease. -/
def mandatoryRoot (r anchor : Block) : Block :=
  if Block.preceq r anchor then anchor else r

def choice (p : Params) {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot) (c : Option (PC n)) : Block :=
  if capBroken p st then GridCO.forkChoice st.base tree raw support r else
    let anchor := preliminaryAnchor (floor p st tree raw support r) c
    GridCO.ghost (mandatoryRoot (GridCO.liveRoot st.base) anchor) tree
      (GridCO.goldfishScore st.base.blocks raw support)
      (GridCO.goldfishEligible st.base.blocks raw support r)

def activeVoterTree (p : Params) {n : Nat} (st : State n) (r : Slot)
    (c : Option (PC n)) : List Block :=
  let plain := GridCO.voterTree p.engine st.base r
  let support := GridCO.voterSupportView p.engine st.base r
  st.base.blocks.filter (fun b => b ∈ plain ||
    support.any (fun o => match GridCO.headTarget? o with
      | some h => Block.preceq b h
      | none => false) ||
    (match c with | some cert => Block.preceq b cert.target | none => false) ||
    st.base.obligations.any (fun (h, _, expiry) =>
      st.base.now < expiry && Block.preceq b h))

def headTarget (p : Params) {n : Nat} (st : State n) (r : Slot) : Block :=
  if r == 0 then .genesis else
    let c := selectedPC p st r
    let tree := if capBroken p st then GridCO.voterTree p.engine st.base r
      else activeVoterTree p st r c
    choice p st tree (GridCO.voterView p.engine st.base r)
      (GridCO.voterSupportView p.engine st.base r) r c

def act (p : Params) {n : Nat} (st : State n) (r : Slot) : Option (Msg n) :=
  let h := headTarget p st r
  some (.head ⟨h, ackFor st r h⟩)

/-- Recover an original complete signature for each internal base key.
The raw archive, rather than a synthetic signed projection, is sent. -/
def originalHeads {n : Nat} (st : State n)
    (keys : List (GridCO.Wire n)) : List (HeadWire n) :=
  keys.filterMap (fun key => st.receivedHeads.find? (fun o => baseWire o == key))

def propose (p : Params) {n : Nat} (st : State n) (r : Slot) : Option (Msg n) :=
  if r == 0 then none else
    let raw := GridCO.proposerView st.base r
    let support := GridCO.proposerSupportView st.base r
    let parent := choice p st st.base.blocks raw support r st.bestPC
    let b := Block.node parent r (nodeRoot parent.root r 0) 0
    some (.proposal b (originalHeads st raw) (originalHeads st support) st.bestPC)

end AvailableChain.SAPC
end

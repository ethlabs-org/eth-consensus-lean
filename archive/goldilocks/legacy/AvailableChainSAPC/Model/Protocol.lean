module
public import AvailableChainSAPC.Model.Choice

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic

def pcOK {n : Nat} (c : Option (PC n)) (b : Block) : Bool :=
  match c with
  | none => true
  | some cert => Block.compatible b cert.target

/-- [ROOT-DIGEST-2 W1; DC deferred behavior]
A pure extension of the SA gate. The finite guard tests the whole
raw result. The stable write and each prefix lease have separate PC guards.
Without PC authority this calls the proved SA transition directly. -/
def gateWithPC (p : Params) {n : Nat} (st : GridCO.State n) (r : Slot)
    (c : Option (PC n)) : GridCO.State n :=
  match c with
  | none => SA.gate p st r
  | some _ =>
      match SA.confirmation p st r with
      | none => { st with
          genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r none }
      | some h =>
          let levels := @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block st r
          let st := { st with
            goldfishRecord := GridCO.advance st.goldfishRecord h
            genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .block st r (some h) }
          if st.obligations.any (fun (target, _, _) =>
            !Block.compatible target h) then st else
            let st := if pcOK c h then
              { st with stableRecord := GridCO.advance st.stableRecord h } else st
            let prefixes := st.blocks.filter (fun b =>
              b != .genesis && Block.preceq b h && pcOK c b)
            prefixes.foldl (fun acc b =>
              (levels b).foldl (fun acc g => GridCO.writeObligation acc b g
                (gateTime p r + lifetime p)) acc) st

def gate (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  { st with base := gateWithPC p st.base r (if capBroken p st then none else st.bestPC) }

/-- Shared clock phases, with an immutable PC freeze and timely N save.
Expiry and release precede the HEAD; the gate uses the live PC mode. -/
def clock (p : Params) {n : Nat} (st : State n) (t : Time) : State n :=
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    { st with base := GridCO.freeze p.engine st.base fSlot,
              frozenPC := if st.frozenPC.any (fun row => row.1 == fSlot)
                then st.frozenPC else st.frozenPC ++ [(fSlot, st.bestPC)] }
    else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    saveTimely p { st with base := { st.base with early := st.base.early ++
      [(eSlot, GridCO.earlyVotes p.engine st.base eSlot)] } } eSlot
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    { st with base := GridCO.release p.engine st.base qSlot } else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p st dSlot else st

/-- The fixed engine signs one HEAD at each duty. Emission changes no state. -/
def sapc (p : Params) : ProtocolSpec p.n where
  State := State p.n
  Label := Slot
  Payload := Msg p.n
  init := initial p.n
  clock := clock p
  actTime := voteTime p
  duties := GridCO.duties p.engine
  duties_spec := GridCO.duties_spec p.engine
  duties_nodup := GridCO.duties_nodup p.engine
  act := act p
  proposalTime := proposalTime p
  slotsAt := GridCO.slotsAt p.engine
  slotsAt_spec := GridCO.slotsAt_spec p.engine
  slotsAt_nodup := GridCO.slotsAt_nodup p.engine
  propose := propose p
  gossip := fun st _ => match st.bestPC with | none => [] | some c => [.pc c]
  process := process p
  wellFormed := wellFormed p
  depsPresent := depsPresent
  processed := processed p
  excludes := fun _ _ => false
  handles := handles p
  carries := carries

end AvailableChain.SAPC
end

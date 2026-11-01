module
public import AvailableChainPCSA.Model.FrameCore

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; pcsa-decisions R-a; GridCO admissionLevels] The lease levels
of a prefix at gate `s`: the one SA level when the prefix is slow admissible
(`J = {k}`: `k` consecutive saved results cover it). There is no τ fast lease. -/
def slowLevels (p : Params) {n : Nat} (v : GridCO.State n .root) (s : Slot) (b : Block) :
    List Nat :=
  if SA.Root.slowEligible p.toParams v s b then [SA.releaseThreshold p.toParams] else []

/-- [PC-SA M1; pcsa34-r4.3 §3.7] Run the SA gate on the active view.
A genuine result advances G. It advances S only if no live lease conflicts
with the result. Each slow write must pass the rank check. Each write or
renewal stores `ρ_s` and keeps the maximum deadline. -/
def gateFrom (p : Params) {n : Nat} (a : Block) (cs : List (PC n)) (ρ : Option PCRank)
    (st : State n) (s : Slot) : State n :=
  let v := actView st
  let q := p.toParams.engine
  match SA.Root.confirmationFrom p.toParams a v s with
  | none => { st with base := { st.base with
      genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s none } }
  | some h =>
      let st := { st with base := { st.base with
        goldfishRecord := GridCO.advance v.goldfishRecord h
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some h) } }
      if st.base.obligations.any (fun row => st.base.now < row.2.2 &&
          !Block.compatible row.1 h) then st else
        let st := { st with base := { st.base with
          stableRecord := GridCO.advance st.base.stableRecord h } }
        let prefixes := v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
          leaseWriteOK cs ρ b)
        prefixes.foldl (fun acc b =>
          (slowLevels p (actView acc) s b).foldl
            (fun acc g => writeLease acc b g
              (GridCO.gateTime q s + GridCO.lifetime q) ρ) acc) st

theorem gateFrom_def (p : Params) {n : Nat} (a : Block) (cs : List (PC n)) (ρ : Option PCRank)
    (st : State n) (s : Slot) :
    gateFrom p a cs ρ st s =
      (let v := actView st
       let q := p.toParams.engine
       match SA.Root.confirmationFrom p.toParams a v s with
       | none => { st with base := { st.base with
           genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s none } }
       | some h =>
           let st := { st with base := { st.base with
             goldfishRecord := GridCO.advance v.goldfishRecord h
             genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some h) } }
           if st.base.obligations.any (fun row => st.base.now < row.2.2 &&
               !Block.compatible row.1 h) then st else
             let st := { st with base := { st.base with
               stableRecord := GridCO.advance st.base.stableRecord h } }
             let prefixes := v.blocks.filter (fun b => b != .genesis && Block.preceq b h &&
               leaseWriteOK cs ρ b)
             prefixes.foldl (fun acc b =>
               (slowLevels p (actView acc) s b).foldl
                 (fun acc g => writeLease acc b g
                   (GridCO.gateTime q s + GridCO.lifetime q) ρ) acc) st) := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.7] If label `s` is not saved, read its
rank stamp and run the gate from `Σ.F`. Then normalize S against F. -/
def gateStep (p : Params) (st : State p.n) (s : Slot) : State p.n :=
  let a := eraseFG st.fg.F
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    gateFrom p a st.pcs (gateRank p st s) st s
  normalizeS st

theorem gateStep_def (p : Params) (st : State p.n) (s : Slot) :
    gateStep p st s =
      (let a := eraseFG st.fg.F
       let st := if (GridCO.savedGenuine st.base s).isSome then st else
         gateFrom p a st.pcs (gateRank p st s) st s
       normalizeS st) := rfl

/-- [PC-SA M1; FG-SA Clock.lean clockPre; pcsa-decisions R-f]
[spec 683–694, 709–752; M8] The tick before the gate: set the time and
expire leases; the freeze (on the active view) and the PC snapshot at `z_s`
(the latest held PC; written once per label, as `recordGenuine`; review fix
4); the early cache at `e_s` (on the active view; the ack
duty reads it); the release at `q_{s−1}` (on the active view). The step order
and the time tests are those of `GridCO.clockFrom`. -/
def clockPre (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let q := p.toParams
  let st := { st with base := GridCO.expire { st.base with now := t } t }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == SA.freezeTime q fSlot then
    { onView (fun v => GridCO.freeze q.engine v fSlot) st with
      pcSnapshot := if (st.pcSnapshot.find? (fun row => row.1 == fSlot)).isSome then
        st.pcSnapshot else st.pcSnapshot ++ [(fSlot, st.pcs)] } else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == SA.earlyTime q eSlot then
    onView (fun v =>
      { v with early := v.early ++ [(eSlot, GridCO.earlyVotes q.engine v eSlot)] }) st
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == SA.releaseTime q qSlot then
    onView (fun v => SA.Root.release q v qSlot) st else st

/-- [PC-SA M1] [spec 683–694, 709–752; M8] The tick: `clockPre`, then the composite gate at
`d_{s−1}`. The duties are not here (Q1). -/
def clock (p : Params) (st : State p.n) (t : Time) : State p.n :=
  let st := clockPre p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == SA.gateTime p.toParams dSlot then gateStep p st dSlot else st

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem pcsa_clock_eq_1_export :
    type_of% (@clock.eq_1) := @clock.eq_1
private theorem pcsa_clockPre_eq_1_export :
    type_of% (@clockPre.eq_1) := @clockPre.eq_1
private theorem pcsa_gateStep_eq_1_export :
    type_of% (@gateStep.eq_1) := @gateStep.eq_1

end AvailableChain.PCSA
end

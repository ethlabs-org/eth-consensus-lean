module
public import AvailableChainFGSA.Model.Frame -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [Sleep v6; P24] Keep the durable store and clear the AC pools and caches. -/
def wipe (p : Params) (st : State p.n) (w : Time) : State p.n :=
  { st with
    base := { GridCO.initial p.n .root with
      now := w
      blocks := st.base.blocks
      blockStamp := st.base.blocks.map (fun b =>
        (b, if b = .genesis then 0 else w))
      obligations := st.base.obligations
      stableRecord := st.base.stableRecord }
    fastWrite := []
    restartTime := some w }

/-- [Sleep v6; plan §14.3] Non-genesis retained proposals in admission order. -/
def restartSources (p : Params) (st : State p.n) : List (NamedProposal p.n) :=
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) =>
        if N.erase != .genesis && decide (∃ B ∈ Next.tree p st, eraseFG B = N.erase) then
          some N else none
    | _ => none)

/-- [Sleep v6; P24] Replay raw HEAD lists in admission order. -/
def restartVotes (p : Params) (st : State p.n) : List (Wire p.n) :=
  let retained := Next.tree p st
  st.proposals.flatMap (fun o =>
    match o.decode with
    | some (.block _ N) =>
        if N.erase != .genesis &&
            decide (∃ B ∈ retained, eraseFG B = N.erase) then
          N.raw.map (fun h => (⟨h.auth, .head h.payload⟩ : Wire p.n))
        else []
    | _ => [])

/-- [Sleep v6; P24] The vote handler accepts the replay at the exact wake time. -/
def acRestart (p : Params) (st : State p.n) (w : Time) : State p.n :=
  (restartVotes p st).foldl (process p) (wipe p st w)

-- Generate the restart equations in their home module.
private theorem wipe_eq_1_export : type_of% (@wipe.eq_1) := @wipe.eq_1
private theorem restartVotes_eq_1_export :
    type_of% (@restartVotes.eq_1) := @restartVotes.eq_1
private theorem restartSources_eq_1_export :
    type_of% (@restartSources.eq_1) := @restartSources.eq_1
private theorem acRestart_eq_1_export : type_of% (@acRestart.eq_1) := @acRestart.eq_1

end AvailableChain.FGSA
end

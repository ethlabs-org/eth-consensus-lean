module
public import AvailableChainFGSARun.Proofs.NamedScope -- shake: keep (axioms)

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.HeadRoots

/-- Two geometric bodies have the same identifier and different slots and ancestry. -/
def X : Block := .node .genesis 1 ⟨9⟩ 0
def Y : Block := .node (.node .genesis 2 ⟨8⟩ 0) 7 ⟨9⟩ 1
def Z : Block := .node .genesis 1 ⟨10⟩ 0
def vote (s : Slot) (B : Block) : GridCO.Wire 4 .root := ⟨.seat s 0, .head B.root⟩
def saParams : SA.Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide }
def params : GridCO.Params := saParams.engine
def empty : GridCO.State 4 .root := { GridCO.initial 4 .root with now := 8 }
def first : GridCO.State 4 .root := GridCO.admitVote params empty (vote 2 X)
def repeated : GridCO.State 4 .root :=
  GridCO.admitVote params { first with now := 9 } (vote 2 Y)

/-- Equal root names give one wire, one receipt stamp, and no equivocation. -/
theorem same_identifier : vote 2 X = vote 2 Y ∧
    repeated.votes = [vote 2 X] ∧ repeated.voteStamp = [(vote 2 X, 8)] ∧
    GridCO.equivocates repeated.votes 0 = false := by decide +kernel

/-- Different roots at one label equivocate. Labels remain part of vote identity. -/
theorem distinct_identifiers :
    GridCO.equivocates [vote 2 X, vote 2 Z] 0 = true ∧
    vote 2 X ≠ vote 3 X ∧ GridCO.votesAt
      { empty with votes := [vote 2 X, vote 3 X] } 2 = [vote 2 X] := by decide +kernel

def received : GridCO.State 4 .root :=
  { first with blocks := [.genesis, X], blockStamp := [(X, 9)], now := 10 }

/-- Unknown votes remain participants; later receipt resolves the same wire. -/
theorem later_resolution : first.votes = [vote 2 X] ∧
    GridCO.voterCount first.votes = 1 ∧ GridCO.resolvedHead? first (vote 2 X) = none ∧
    GridCO.proposerSupportView first 3 = [] ∧
    GridCO.resolvedHead? received (vote 2 Y) = some X ∧
    GridCO.proposerSupportView received 3 = [vote 2 X] := by decide +kernel

/-- Slot and receipt checks use the resolved body, including the strict cutoff. -/
theorem resolved_slot_and_stamp : Y.slot = 7 ∧ X.slot = 1 ∧
    GridCO.resolvedBefore received (vote 2 Y) 10 = true ∧
    GridCO.resolvedBefore received (vote 2 Y) 9 = false ∧
    GridCO.resolvedBefore { received with blockStamp := [(X, 10)] } (vote 2 Y) 10 = false := by
  decide +kernel

/-- Distinct bodies make the identifier ambiguous; repeated identical bodies do not. -/
theorem ambiguity :
    GridCO.resolvedHead? { received with blocks := [.genesis, X, Y] } (vote 2 X) = none ∧
    GridCO.resolvedHead? { received with blocks := [.genesis, X, X] } (vote 2 X) = some X := by
  decide +kernel

/-- An active subset retains the complete cumulative resolution domain. -/
theorem pinned_domain :
    GridCO.resolvedHead? { received with blocks := [X], headDomain := some [.genesis, X, Y] }
      (vote 2 X) = none ∧
    GridCO.goldfishScoreOn (mode := .root) [.genesis, X, Y] [X]
      [vote 2 X] [vote 2 X] X = 0 ∧
    GridCO.goldfishScore (mode := .root) [X] [vote 2 X] [vote 2 X] X = 1 := by
  decide +kernel

/-- The production active-view constructor pins its cumulative domain too. -/
theorem active_domain :
    let st : State 4 := { base := { received with blocks := [.genesis, X, Y] } }
    (actView st).headDomain = some [.genesis, X, Y] ∧
      GridCO.resolvedHead? (actView st) (vote 2 X) = none := by decide +kernel

#print axioms same_identifier
#print axioms distinct_identifiers
#print axioms later_resolution
#print axioms resolved_slot_and_stamp
#print axioms ambiguity
#print axioms pinned_domain
#print axioms active_domain

end AvailableChain.FGSA.Run.Tests.HeadRoots
end

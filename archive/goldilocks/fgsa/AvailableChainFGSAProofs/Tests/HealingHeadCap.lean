module
public import AvailableChainFGSAProofs.Proofs.Healing.HeadRelay -- shake: keep (test environment)

public section

namespace AvailableChain.FGSA.Run.Tests.HealingHeadCap
open AvailableChain.SimplexFG

abbrev params : Params :=
  ⟨⟨1, 4, 2, 64, by decide, by decide, by decide, by decide⟩,
    2, 4, by decide, 2, by decide, fun d => ⟨d.slot + 10⟩⟩

abbrev first : HeadWire 4 := ⟨.seat (.head 0) 0, ⟨1⟩⟩
abbrev second : HeadWire 4 := ⟨.seat (.head 0) 0, ⟨2⟩⟩
abbrev refused : HeadWire 4 := ⟨.seat (.head 0) 0, ⟨3⟩⟩
abbrev capState : State 4 :=
  admitHead params (admitHead params (initialAt 4 4) 0 0 first.payload)
    0 0 second.payload
abbrev body : NamedProposal 4 := namedProposal params .genesis 1 0 [refused] [] []
abbrev carried : State 4 := admitBlock params capState 1 body

/-- Actual handler replay: the proposal is admitted, but its third HEAD is refused. -/
theorem carried_refused_after_cap :
    (⟨.proposer 1, .proposal body⟩ : Wire 4) ∈ carried.proposals ∧
    baseVote refused ∈ headVotes params carried 1 ∧
    baseVote refused ∉ carried.base.votes ∧
    GridCO.equivocates (GridCO.votesAt carried.base 0) 0 = true ∧
    carried.base.votes = [baseVote first, baseVote second] := by decide +kernel

/-- The count excludes the capped seat even though the carried raw HEAD is present. -/
theorem capped_seat_not_clean :
    baseVote refused ∉ GridCO.cleanSupport params.toParams.engine (actView carried) 0 := by
  decide +kernel

#print axioms AvailableChain.FGSA.Run.Tests.HealingHeadCap.carried_refused_after_cap
#print axioms AvailableChain.FGSA.Run.Tests.HealingHeadCap.capped_seat_not_clean

end AvailableChain.FGSA.Run.Tests.HealingHeadCap
end

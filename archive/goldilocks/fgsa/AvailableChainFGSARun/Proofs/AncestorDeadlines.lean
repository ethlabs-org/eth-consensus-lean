module
public import AvailableChainFGSARun.Proofs.AncestorDeadlinesStore
public import AvailableChainFGSARun.Proofs.Protocol

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In : Type} {c : AppCodec In}

/-- [helper] The own-record step keeps the store by `recordOwn_st`. -/
theorem ancestorDeadlines_recordOwn (nd : Node p) (o : Obj p)
    (h : AncestorDeadlines nd.st) :
    AncestorDeadlines (((fgsa p c).recordOwn nd o).st) := by
  rw [recordOwn_st]
  exact h

/-- Restore keeps obligations and their ancestor deadlines at the wake time. -/
theorem ancestorDeadlines_restore (d : State p.n × SimplexFG.RecordOnce) (w : Time)
    (h : AncestorDeadlines d.1) :
    AncestorDeadlines (((fgsa p c).restore d w).st) :=
  ancestorDeadlines_acRestart p d.1 w h

end AvailableChain.FGSA.Run
end

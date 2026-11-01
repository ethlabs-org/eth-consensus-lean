module
public import AvailableChainFGSAProofs.Statements.CleanInvariant

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

/-- F2.0 review contract for the Clean proof tree. The statement stays in
Statements/CleanInvariant; this entry point adds no proof.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
abbrev CleanInterface := @CleanAGStmt (ΔF := ΔF)

end AvailableChain.FGSA.Run
end

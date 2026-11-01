module
public import AvailableChainPCSA.Model.Store

public section

/-! PC-SA store facts (pcsa34-r4.3 §3.1; proof plan §3). -/

namespace AvailableChain.PCSA

/-- The initial store holds no PC (pcsa34-r4.3 §3.1). -/
theorem initial_pcs (n : Nat) : (initial n).pcs = [] := rfl

end AvailableChain.PCSA
end

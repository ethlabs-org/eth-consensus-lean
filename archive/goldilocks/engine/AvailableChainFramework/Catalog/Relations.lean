module
public import AvailableChainFramework.Catalog.Profiles

@[expose] public section

/-! Relations between profiles. `ac-4.3` gives the core floor at the core
constant `D := C.D_c`. -/

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- The four core claims are the first four entries of `ac-4.3`, with the core
constant `D := C.D_c` (PHASE1A-REPORT, plan 1b input 3). -/
theorem core_holdsAt_of_ac43 {I : Instance} {C : Constants} (h : ac43.holdsAt I C) :
    core.holdsAt I C.D_c := by
  obtain ⟨hC, h⟩ := h
  refine ⟨hC.delays_nonneg.1, fun e he => ?_⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact h ⟨safeConfirmed, fun _ => ()⟩ (.head _)
  rcases List.mem_cons.1 he with rfl | he
  · exact h ⟨safeStable, fun _ => ()⟩ (.tail _ (.head _))
  rcases List.mem_cons.1 he with rfl | he
  · exact h ⟨prefixOrder, fun _ => ()⟩ (.tail _ (.tail _ (.head _)))
  rcases List.mem_singleton.1 he with rfl
  exact h ⟨includedConfirmed, fun C => C.D_c⟩ (.tail _ (.tail _ (.tail _ (.head _))))

end AvailableChain.Framework.Catalog

end

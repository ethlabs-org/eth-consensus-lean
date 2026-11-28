module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutBase

public section

/-! # Goldilocks FG store: the steps of G1.10 at the scope of C1.1

Store-local facts used by the growing-fault cut (`Growing/Compose/Cut`): one block of the state
transition (`step_fields`) and compatibility through an ancestor (`compatible_of_anc`). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- A block below one that is compatible with `B` is compatible with `B`. -/
theorem compatible_of_anc {n : Nat} {FGP ACP : Type} {S : Set (Block n FGP ACP)}
    (hS : Coherent S) {A B C : Block n FGP ACP} (hAC : Goldilocks.Anc S A C)
    (hC : Compatible S C B) : Compatible S A B := by
  rcases hC with hCB | hBC
  · exact Or.inl (hAC.trans hCB)
  · exact Anc.total hS hAC hBC

section Run

variable {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-! ## The tree of an honest node -/

/-! ## The scope of C1.1 -/

end Run

end Consensus.Goldilocks.Store

end

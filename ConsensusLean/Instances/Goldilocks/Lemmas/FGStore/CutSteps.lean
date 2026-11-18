module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutBase

public section

/-! # Goldilocks FG store: the steps of G1.10 at the scope of C1.1

Store-local facts used by the growing-fault cut (`Growing/Compose/Cut`): one block of the state
transition (`step_fields`) and compatibility through an ancestor (`compatible_of_anc`). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- One accepted block keeps the height and the entry, or enters the next height by itself; it
keeps the justification, or justifies the parent's entry at the parent's height. -/
theorem step_fields {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ((σ'.h = σ.h ∧ σ'.Th = σ.Th) ∨ (σ'.h = σ.h + 1 ∧ σ'.Th = B.root)) ∧
      ((σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

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

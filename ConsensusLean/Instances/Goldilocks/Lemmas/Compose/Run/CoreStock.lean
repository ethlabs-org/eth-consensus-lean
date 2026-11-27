module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Core

public section

/-! # The stock bridges of the run-facts bundles

`Store.onBlock_eq_onBlockWith` and `Store.Reachable.reachableWith` (the stock store at the stock
finality update) and `Node.CutStep.with` (the stock cut law is `CutStepWith` at
`Store.updateFinality` and `Node.frame`). -/

namespace Consensus.Goldilocks

open AC (ACParams Payload)

namespace Store

variable {P : Params} {ACP : Type}

/-- The stock acceptance is `onBlockWith` at the stock finality update. -/
theorem onBlock_eq_onBlockWith (st : Store P ACP) (B : NodeBlock P ACP) :
    st.onBlock B = st.onBlockWith updateFinality B := by
  rw [onBlockWith_eq]
  rfl

/-- A reachable store is reached with the stock finality update. -/
theorem Reachable.reachableWith {acp₀ : ACP} {st : Store P ACP} (h : st.Reachable acp₀) :
    ReachableWith updateFinality acp₀ st := by
  rw [reachableWith_eq]
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    refine ih.tail ((stepWith_iff _ _ _).2 ?_)
    rcases hs with ⟨B, hB⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨B, (onBlock_eq_onBlockWith _ B) ▸ hB⟩
    · exact Or.inr ⟨a, ha⟩

end Store

variable {sp : ACParams}

/-- The stock cut law is the cut law at the stock finality update and frame. -/
theorem Node.CutStep.with {self : Fin sp.n} {t : Time} {st st' : NodeState (goldilocksNode sp)}
    {c : Cut (goldilocksNode sp)} (h : Node.CutStep self t st c st') :
    CutStepWith Store.updateFinality Node.frame self t st c st' := by
  rcases c with ⟨⟨B, _ | _⟩ | a | ⟨C, _ | a⟩⟩ | ℓ
  · exact (cutStepWith_block_false B).2 ⟨by rw [← Store.onBlock_eq_onBlockWith]; exact h.1, h.2⟩
  · exact (cutStepWith_block_true B).2
      ⟨h.1, by rw [← Store.onBlock_eq_onBlockWith]; exact h.2.1, h.2.2⟩
  · exact (cutStepWith_attestation a).2 h
  · exact (cutStepWith_attest_none C).2 h
  · exact (cutStepWith_attest_some C a).2 h
  · exact (cutStepWith_ac ℓ).2 h

end Consensus.Goldilocks

end

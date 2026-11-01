module
public import AvailableChainPCSAProofs.Proofs.Shared.Roots

public section

/-! The N-target root step of pcsa34-r4.3a §5.2.2(d).
The run induction must supply the earlier-PC, same-slot, and lock bounds.
Compatibility with arbitrary honest HEADs is not required. -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- At the next vote, the root is below the N target when earlier PCs and
locks are below it, same-slot PCs target it, and no later PC is selected.
These are the three source cases in r4.3a step (d). -/
theorem pcsa_clean_N_root (p : Params) (st : State p.n) (view : Option (PC p.n))
    (i : Slot) (X : Block) (hz : (controls p st).Z = .genesis)
    (htime : ∀ pc ∈ view, pc.slot ≤ i)
    (hprior : ∀ pc ∈ view, pc.slot < i → Block.Preceq pc.target X)
    (hsame : ∀ pc ∈ view, pc.slot = i → pc.target = X)
    (hlocks : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Preceq row.1 X) :
    Block.Preceq (liveRoot p st view) X ∧ Block.Compatible (liveRoot p st view) X := by
  have hb : Block.Preceq (walkBase p st view) X := by
    cases view with
    | none =>
      change Block.Preceq (eraseFG (controls p st).Z) X
      rw [hz]
      exact block_genesis_preceq X
    | some pc =>
      change Block.Preceq (if frameActive p st pc then pc.target else _) X
      split
      · rcases (htime pc rfl).lt_or_eq with h | h
        · exact hprior pc rfl h
        · rw [hsame pc rfl h]
          exact block_preceq_refl X
      · rw [hz]
        exact block_genesis_preceq X
  have hr := pcsa_liveRoot_below_bound p st view X hb hlocks
  exact ⟨hr, block_compatible_of_common hr (block_preceq_refl X)⟩

end AvailableChain.PCSA
end

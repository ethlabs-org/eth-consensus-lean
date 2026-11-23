module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkFacts

@[expose] public section

/-! # The AC's walk and restart facts: statements and axioms

Each fact of `Lemmas/AC/WalkFacts` restated as a named theorem, with its axioms pinned. -/

namespace Consensus.Goldilocks.WalkFactsTest

open AC

variable {sp : ACParams} {FGP : Type}

/-- The memoryless walk. -/
theorem ghost_eq_of_visited {S tree : Set (Blk sp.n FGP)} (hS : Coherent S) (hT : tree ⊆ S)
    (hfin : tree.Finite) {sc : Blk sp.n FGP → Nat} {el : Blk sp.n FGP → Prop} {N : Nat}
    (hN : tree.ncard ≤ N) {a₀ a₁ : Blk sp.n FGP} (h01 : Anc S a₀ a₁)
    (h1H : Anc S a₁ (ghost sp tree sc el N a₀)) :
    ghost sp tree sc el N a₁ = ghost sp tree sc el N a₀ :=
  AC.ghost_eq_of_visited hS hT hfin hN h01 h1H

/-- The empty set has no deepest block. -/
theorem deepest_empty (Φ : Frm sp.n FGP) : deepest Φ (∅ : Set (Blk sp.n FGP)) = none :=
  AC.deepest_empty Φ

/-- A block receipt keeps the latest restart. -/
theorem blockReceipt_restartTime (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime :=
  AC.blockReceipt_restartTime A t B

/-- A negative time is in slot `0`. -/
theorem slot_of_neg {t : Time} (ht : t < 0) : sp.slot t = 0 :=
  AC.slot_of_neg ht

end Consensus.Goldilocks.WalkFactsTest

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.WalkFactsTest.ghost_eq_of_visited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.WalkFactsTest.ghost_eq_of_visited

/-- info: 'Consensus.Goldilocks.WalkFactsTest.deepest_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.WalkFactsTest.deepest_empty

/-- info: 'Consensus.Goldilocks.WalkFactsTest.blockReceipt_restartTime' depends on axioms: [propext] -/
#guard_msgs in #print axioms Consensus.Goldilocks.WalkFactsTest.blockReceipt_restartTime

/-- info: 'Consensus.Goldilocks.WalkFactsTest.slot_of_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.WalkFactsTest.slot_of_neg

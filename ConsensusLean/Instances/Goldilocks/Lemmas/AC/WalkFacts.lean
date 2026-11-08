module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer

public section

/-! # Facts of the SA: the memoryless walk, the empty deepest set, the restart time

A leaf module: no module of the library imports it except where a proof uses one of its facts.

* `ghost_eq_of_visited`: a walk with at least as many steps as its tree has blocks, started from a
  block `a₁` that extends `a₀` and lies on the walk from `a₀`, ends where the walk from `a₀` ends;
* `deepest_empty`: the empty set has no deepest block;
* `blockReceipt_restartTime`: a block receipt keeps the latest restart;
* `slot_of_neg`: a negative time is in slot `0`. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- **The memoryless walk**: a long enough walk from a block `a₁` on the walk from `a₀` that extends
`a₀` ends where the walk from `a₀` ends. -/
theorem ghost_eq_of_visited {S tree : Set (Blk sp.n FGP)} (hS : Coherent S) (hT : tree ⊆ S)
    (hfin : tree.Finite) {sc : Blk sp.n FGP → Nat} {el : Blk sp.n FGP → Prop} {N : Nat}
    (hN : tree.ncard ≤ N) {a₀ a₁ : Blk sp.n FGP} (h01 : Anc S a₀ a₁)
    (h1H : Anc S a₁ (ghost sp tree sc el N a₀)) :
    ghost sp tree sc el N a₁ = ghost sp tree sc el N a₀ := by
  obtain ⟨k, hkN, hk⟩ := ghost_visits hS hT N h01 h1H
  have hadd : ghost sp tree sc el N a₀ = ghost sp tree sc el (N - k) a₁ := by
    rw [← hk, ← ghost_add, Nat.add_sub_cancel' hkN]
  have hstop := ghost_stopped (sc := sc) (el := el) hS hT hfin hN a₀
  rw [hadd] at hstop ⊢
  exact ghost_fuel_stable (Nat.sub_le N k) hstop

/-- The empty set has no deepest block. -/
theorem deepest_empty (Φ : Frm sp.n FGP) : deepest Φ (∅ : Set (Blk sp.n FGP)) = none := by
  unfold deepest
  split_ifs with h
  · obtain ⟨B, hB, -⟩ := h
    exact absurd hB (Set.notMem_empty B)
  · rfl

/-- A block receipt keeps the latest restart. -/
theorem blockReceipt_restartTime (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  have key : ∀ (l : List (Vote sp.n)) (A₀ : SAState sp.n),
      (l.foldl (fun A v => admitVote sp A t v) A₀).restartTime = A₀.restartTime := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons v l ih => exact fun A₀ => (ih _).trans (admitVote_restartTime A₀ t v)
  exact key _ _

/-- A negative time is in slot `0`. -/
theorem slot_of_neg {t : Time} (ht : t < 0) : sp.slot t = 0 := by
  simp [SAParams.slot, Params.slotOf, Int.toNat_of_nonpos ht.le]

end Consensus.Goldilocks.SA

end

module
public import ConsensusProblem
public import Mathlib.Tactic
@[expose] public section
namespace Consensus.Shape.Tests.Problem

def point : EnvPoint Bool :=
  ⟨⟨1, by decide, 0, fun _ _ => true⟩, Finset.univ, 2,
    fun _ t => if t = 0 then [42] else []⟩

def incompatible : Trace Bool Nat :=
  ⟨point, 2, fun i => (i : Int), fun _ v _ => if v then [1] else [2]⟩

def rollback : Trace Bool Nat :=
  ⟨point, 2, fun i => (i : Int), fun _ _ i => if i = 1 then [1] else []⟩

def omitted : Trace Bool Tx :=
  ⟨point, 2, fun i => (i : Int), fun _ _ _ => []⟩

theorem incompatible_laws : incompatible.Laws := by
  constructor
  · rfl
  · intro i j hij _; change (i : Int) ≤ j; exact_mod_cast hij
  · intro i hi; change (i : Int) ≤ 2; change i ≤ 2 at hi; exact_mod_cast hi

theorem rollback_laws : rollback.Laws := ⟨incompatible_laws.1, incompatible_laws.2, incompatible_laws.3⟩

theorem omitted_laws : omitted.Laws := ⟨incompatible_laws.1, incompatible_laws.2, incompatible_laws.3⟩

theorem incompatible_not_agree : ¬ incompatible.Agree .confirmed 0 := by
  intro h
  have hc := h true (Finset.mem_univ _) false (Finset.mem_univ _) 1 1
    (by unfold Trace.InCuts Trace.endCut incompatible; decide)
    (by unfold Trace.InCuts Trace.endCut incompatible; decide)
  change Compatible [1] [2] at hc
  simpa [Compatible, List.prefix_cons_inj] using hc

theorem rollback_not_monotone : ¬ rollback.Monotone .confirmed 0 := by
  intro h
  have hp := h true (Finset.mem_univ _) 1 2 (by unfold Trace.InCuts Trace.endCut rollback; decide) (by decide)
    (by unfold Trace.InCuts Trace.endCut rollback; decide)
  change [1] <+: [] at hp
  simpa using hp

theorem omitted_not_txLive : ¬ omitted.TxLive 0 .confirmed 0 1 := by
  intro h
  have hs : point.SubmittedToSome 42 0 := by
    exact ⟨true, Finset.mem_univ _, 0, le_rfl, le_rfl, rfl, by simp [point]⟩
  have hr : point.Ready 0 true 2 := by
    exact ⟨Finset.mem_univ _, fun _ _ _ => rfl⟩
  have hx := h 42 0 2 (le_refl _) hs (by decide) (by decide) true hr
  change 42 ∈ [] at hx
  cases hx
end Consensus.Shape.Tests.Problem
end

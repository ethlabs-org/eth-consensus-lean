module
public import Mathlib.Data.List.Sort -- shake: keep (re-export)
public import Mathlib.Order.Monotone.Basic -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- SublistStageFoldStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
def SublistStageFoldStatement : Prop :=
  ∀ {ι α : Type} [Preorder α] (f : ι → α → α),
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    ∀ (xs ys : List ι), xs.Sublist ys → ∀ (u v : α), u ≤ v →
      xs.foldl (fun x i => f i x) u ≤ ys.foldl (fun x i => f i x) v

/-- SublistStageFoldStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem SublistStageFoldStatement_def : SublistStageFoldStatement =
    (∀ {ι α : Type} [Preorder α] (f : ι → α → α),
      (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
      ∀ (xs ys : List ι), xs.Sublist ys → ∀ (u v : α), u ≤ v →
        xs.foldl (fun x i => f i x) u ≤ ys.foldl (fun x i => f i x) v) := by rfl

/-- OrderedStageFoldStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
def OrderedStageFoldStatement : Prop :=
  ∀ {α : Type} [Preorder α] {n : Nat} (f : Fin n → α → α),
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ (u₀ : α),
      vis.foldl (fun x i => f i x) u₀ ≤
        (List.finRange n).foldl (fun x i => f i x) u₀

/-- OrderedStageFoldStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem OrderedStageFoldStatement_def : OrderedStageFoldStatement =
    (∀ {α : Type} [Preorder α] {n : Nat} (f : Fin n → α → α),
      (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
      ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ (u₀ : α),
        vis.foldl (fun x i => f i x) u₀ ≤
          (List.finRange n).foldl (fun x i => f i x) u₀) := by rfl

/-- NatOrderedStageFoldStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
def NatOrderedStageFoldStatement : Prop :=
  ∀ {n : Nat} (f : Fin n → Nat → Nat),
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ (u₀ : Nat),
      vis.foldl (fun x i => f i x) u₀ ≤
        (List.finRange n).foldl (fun x i => f i x) u₀

/-- NatOrderedStageFoldStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem NatOrderedStageFoldStatement_def : NatOrderedStageFoldStatement =
    (∀ {n : Nat} (f : Fin n → Nat → Nat),
      (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
      ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ (u₀ : Nat),
        vis.foldl (fun x i => f i x) u₀ ≤
          (List.finRange n).foldl (fun x i => f i x) u₀) := by rfl

/-- ProductOrderedStageFoldStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
def ProductOrderedStageFoldStatement : Prop :=
  ∀ {n : Nat} (f : Fin n → (Int × Int) → (Int × Int)),
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ (u₀ : Int × Int),
      vis.foldl (fun x i => f i x) u₀ ≤
        (List.finRange n).foldl (fun x i => f i x) u₀

/-- ProductOrderedStageFoldStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306 (nearest fold).
INTENTIONAL: Extract a pure preorder theorem; no DC sorted-stage contract.
S1:587–609; 21-healing.md:2233–2263. Consumers: HG.8a, F4.FF7, F5.H.11-Q. -/
theorem ProductOrderedStageFoldStatement_def : ProductOrderedStageFoldStatement =
    (∀ {n : Nat} (f : Fin n → (Int × Int) → (Int × Int)),
      (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
      ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ (u₀ : Int × Int),
        vis.foldl (fun x i => f i x) u₀ ≤
          (List.finRange n).foldl (fun x i => f i x) u₀) := by rfl

end AvailableChain.Gen.Pure

module
public import AvailableChainGeneric.Statements.Pure.Stages -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- ChainSearchStatement searches at fixed offsets with a free reachable-range guard.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
def ChainSearchStatement : Prop :=
  ∀ (P guard : Nat → Prop) (g s k q : Nat), 1 ≤ g → 1 ≤ k →
    (∀ q', guard q' → ∃ p, q' ≤ p ∧ p < q' + g ∧ P p) →
    (∀ j, j < k → ∀ q', q ≤ q' → q' ≤ q + j * (s + g - 1) → guard q') →
    ∃ p : Nat → Nat, (∀ j, j < k → P (p j)) ∧
      q ≤ p 0 ∧ p 0 < q + g ∧
      (∀ j, j + 1 < k → p j + s ≤ p (j + 1) ∧ p (j + 1) < p j + s + g) ∧
      p (k - 1) ≤ q + k * (g - 1) + (k - 1) * s

/-- ChainSearchStatement_def gives the first-unfold equation.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
theorem ChainSearchStatement_def : ChainSearchStatement =
    (∀ (P guard : Nat → Prop) (g s k q : Nat), 1 ≤ g → 1 ≤ k →
    (∀ q', guard q' → ∃ p, q' ≤ p ∧ p < q' + g ∧ P p) →
    (∀ j, j < k → ∀ q', q ≤ q' → q' ≤ q + j * (s + g - 1) → guard q') →
    ∃ p : Nat → Nat, (∀ j, j < k → P (p j)) ∧
      q ≤ p 0 ∧ p 0 < q + g ∧
      (∀ j, j + 1 < k → p j + s ≤ p (j + 1) ∧ p (j + 1) < p j + s + g) ∧
      p (k - 1) ≤ q + k * (g - 1) + (k - 1) * s) := by rfl

/-- AntitoneChainSearchStatement uses the guard at the greatest reachable start.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
def AntitoneChainSearchStatement : Prop :=
  ∀ (P guard : Nat → Prop) (g s k q : Nat), 1 ≤ g → 1 ≤ k →
    (∀ q', guard q' → ∃ p, q' ≤ p ∧ p < q' + g ∧ P p) →
    (∀ a b, a ≤ b → guard b → guard a) →
    guard (q + (k - 1) * (s + g - 1)) →
    ∃ p : Nat → Nat, (∀ j, j < k → P (p j)) ∧
      q ≤ p 0 ∧ p 0 < q + g ∧
      (∀ j, j + 1 < k → p j + s ≤ p (j + 1) ∧ p (j + 1) < p j + s + g) ∧
      p (k - 1) ≤ q + k * (g - 1) + (k - 1) * s

/-- AntitoneChainSearchStatement_def gives the first-unfold equation.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
theorem AntitoneChainSearchStatement_def : AntitoneChainSearchStatement =
    (∀ (P guard : Nat → Prop) (g s k q : Nat), 1 ≤ g → 1 ≤ k →
    (∀ q', guard q' → ∃ p, q' ≤ p ∧ p < q' + g ∧ P p) →
    (∀ a b, a ≤ b → guard b → guard a) →
    guard (q + (k - 1) * (s + g - 1)) →
    ∃ p : Nat → Nat, (∀ j, j < k → P (p j)) ∧
      q ≤ p 0 ∧ p 0 < q + g ∧
      (∀ j, j + 1 < k → p j + s ≤ p (j + 1) ∧ p (j + 1) < p j + s + g) ∧
      p (k - 1) ≤ q + k * (g - 1) + (k - 1) * s) := by rfl

/-- TwoStepChainSearchStatement gives the QF4 two-search contract for any shift.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
def TwoStepChainSearchStatement : Prop :=
  ∀ (P guard : Nat → Prop) (g s q : Nat), 1 ≤ g →
    (∀ q', guard q' → ∃ p, q' ≤ p ∧ p < q' + g ∧ P p) →
    (∀ a b, a ≤ b → guard b → guard a) → guard (q + (s + g - 1)) →
    ∃ p p', P p ∧ P p' ∧ q ≤ p ∧ p < q + g ∧
      p + s ≤ p' ∧ p' < p + s + g ∧ p' ≤ q + 2 * (g - 1) + s ∧
      (s = 3 → p' ≤ q + 2 * g + 1)

/-- TwoStepChainSearchStatement_def gives the first-unfold equation.
DC: INTENTIONAL additive recurrence search contract. It extends the stage searches in
Generic statements, Legacy/Definitions, Bridge, and Lean stage/finRange searches;
nearest fold: DecoupledConsensusProofs/Bridge/FinalizedLive.lean:298–306.
Consumers: F4.QF4 (22:1731–1743, k = 2, s = 3),
F5.H.9-Q/H.10-Q (21:2336–2344, k ≤ 3, s = 2).
Monotone time and data readiness are lane bridges. -/
theorem TwoStepChainSearchStatement_def : TwoStepChainSearchStatement =
    (∀ (P guard : Nat → Prop) (g s q : Nat), 1 ≤ g →
    (∀ q', guard q' → ∃ p, q' ≤ p ∧ p < q' + g ∧ P p) →
    (∀ a b, a ≤ b → guard b → guard a) → guard (q + (s + g - 1)) →
    ∃ p p', P p ∧ P p' ∧ q ≤ p ∧ p < q + g ∧
      p + s ≤ p' ∧ p' < p + s + g ∧ p' ≤ q + 2 * (g - 1) + s ∧
      (s = 3 → p' ≤ q + 2 * g + 1)) := by rfl

end AvailableChain.Gen.Pure

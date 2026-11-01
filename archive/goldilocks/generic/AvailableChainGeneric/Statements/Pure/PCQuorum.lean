module
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Generic Pure layer: the PC thresholds of the 3n/4 PC-SA design and their
seat-count contracts. A seat acks block `B` at slot `s` when it holds
`q_N = ⌈3n/4⌉` exact HEADs on `B`; a PC is `q_A = ⌈n/2⌉` acks. Source:
`tip-stability/codex/reports/sa-alternatives/pcsa-decisions.md`, user decision
2026-10-05 23:11; `pcsa-v2-plan-fable.md` M0. Seats are `Fin n`, so a
`Finset` counts an equivocating seat once. Definitions, contract Props and
defining equations only. -/

namespace AvailableChain.Gen.Pure

/-- The exact-HEAD count `q_N n = ⌈3n/4⌉` that lets a seat ack. -/
def qN (n : Nat) : Nat := (3 * n + 3) / 4

theorem qN_def (n : Nat) : qN n = (3 * n + 3) / 4 := by rw [qN]

/-- The ack count `q_A n = ⌈n/2⌉` that forms a PC. -/
def qA (n : Nat) : Nat := (n + 1) / 2

theorem qA_def (n : Nat) : qA n = (n + 1) / 2 := by rw [qA]

/-- Two `q_N` seat sets share at least `q_A` seats (`2 q_N − n ≥ ⌈n/2⌉`). -/
def QNInterCardStatement : Prop :=
  ∀ {n : Nat} {Q Q' : Finset (Fin n)},
    qN n ≤ Q.card → qN n ≤ Q'.card → qA n ≤ (Q ∩ Q').card

/-- Defining equation. -/
theorem QNInterCardStatement_def : QNInterCardStatement =
    (∀ {n : Nat} {Q Q' : Finset (Fin n)},
      qN n ≤ Q.card → qN n ≤ Q'.card → qA n ≤ (Q ∩ Q').card) := by rfl

/-- A set of at least `q_A` seats has a seat outside a set of fewer than
`q_A` seats (the faulty seats). -/
def QAHonestStatement : Prop :=
  ∀ {n : Nat} {A F : Finset (Fin n)},
    F.card < qA n → qA n ≤ A.card → ∃ v ∈ A, v ∉ F

/-- Defining equation. -/
theorem QAHonestStatement_def : QAHonestStatement =
    (∀ {n : Nat} {A F : Finset (Fin n)},
      F.card < qA n → qA n ≤ A.card → ∃ v ∈ A, v ∉ F) := by rfl

/-- Two `q_N` seat sets share a seat outside a set of fewer than `q_A`
seats. `F.card < q_A n` is `2 F.card < n`, that is `a < n/2`. This bound is
sufficient for safety only. Liveness (honest seats alone reach `q_N`) needs
`a ≤ n/4`. -/
def QNInterHonestStatement : Prop :=
  ∀ {n : Nat} {Q Q' F : Finset (Fin n)},
    F.card < qA n → qN n ≤ Q.card → qN n ≤ Q'.card → ∃ v ∈ Q ∩ Q', v ∉ F

/-- Defining equation. -/
theorem QNInterHonestStatement_def : QNInterHonestStatement =
    (∀ {n : Nat} {Q Q' F : Finset (Fin n)},
      F.card < qA n → qN n ≤ Q.card → qN n ≤ Q'.card → ∃ v ∈ Q ∩ Q', v ∉ F) := by rfl

/-- At one slot, `q_N` exact-HEAD sets on two blocks name the same block.
`sent v b`: seat `v` sent an exact HEAD on `b` at that slot. A seat outside
`F` sends at most one exact HEAD per slot, and `F.card < q_A n`. Conflicting
blocks are distinct, so they cannot both have a `q_N` set. -/
def QNHeadUniqueStatement : Prop :=
  ∀ {n : Nat} {B : Type} (sent : Fin n → B → Prop) (F S S' : Finset (Fin n)) (b b' : B),
    (∀ v, v ∉ F → ∀ x y, sent v x → sent v y → x = y) →
    F.card < qA n →
    (∀ v ∈ S, sent v b) → (∀ v ∈ S', sent v b') →
    qN n ≤ S.card → qN n ≤ S'.card → b = b'

/-- Defining equation. -/
theorem QNHeadUniqueStatement_def : QNHeadUniqueStatement =
    (∀ {n : Nat} {B : Type} (sent : Fin n → B → Prop) (F S S' : Finset (Fin n)) (b b' : B),
      (∀ v, v ∉ F → ∀ x y, sent v x → sent v y → x = y) →
      F.card < qA n →
      (∀ v ∈ S, sent v b) → (∀ v ∈ S', sent v b') →
      qN n ≤ S.card → qN n ≤ S'.card → b = b') := by rfl

end AvailableChain.Gen.Pure

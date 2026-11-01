module
public import AvailableChainGeneric.Statements.Pure.Stages -- shake: keep (re-export)
public import Mathlib.Data.Int.Basic -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- Ordered stage suppliers give a tagged stop or the terminal stage.
Consumers: F5.H.10, HG.3, HG.5, HG.8a, H.11 and H.11-Q. Sources: S1b:389–437;
21:1324–1328,1474–1523,2253–2256,2429–2439.
DC: additive (no DC counterpart); reason:
ordered stages and tagged local stop suppliers are inputs. -/
def StageOrStopStatement : Prop :=
  ∀ {α : Type} [Preorder α] {n : Nat}
    (timeOf : Nat → Int) (clock : α → Int)
    (f : Fin n → α → α)
    (stage : Nat → Nat → α → Prop) (stop : Fin 3 → Nat → Prop),
    Monotone timeOf → Monotone clock →
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    (∀ c e e', e ≤ e' → stop c e → stop c e') →
    (∀ (i : Fin n) (e : Nat) (x : α),
      stage i.val e x → timeOf e ≤ clock x →
      ∃ e' y, e ≤ e' ∧ timeOf e' ≤ clock y ∧ y ≤ f i x ∧
        ((∃ c : Fin 3, stop c e') ∨
          ∃ j : Nat, i.val < j ∧ j ≤ n ∧ stage j e' y)) →
    ∀ (e₀ : Nat) (x₀ : α), stage 0 e₀ x₀ → timeOf e₀ ≤ clock x₀ →
      ∃ e x, e₀ ≤ e ∧ timeOf e₀ ≤ timeOf e ∧ timeOf e ≤ clock x ∧
        x ≤ (List.finRange n).foldl (fun y i => f i y) x₀ ∧
        ((∃ c : Fin 3, stop c e) ∨ stage n e x)

/-- This equation unfolds the closed contract.
Consumers: F5.H.10, HG.3, HG.5, HG.8a, H.11 and H.11-Q. Sources: S1b:389–437;
21:1324–1328,1474–1523,2253–2256,2429–2439.
DC: additive (no DC counterpart); reason:
ordered stages and tagged local stop suppliers are inputs. -/
theorem StageOrStopStatement_def : StageOrStopStatement =
    (∀ {α : Type} [Preorder α] {n : Nat}
    (timeOf : Nat → Int) (clock : α → Int)
    (f : Fin n → α → α)
    (stage : Nat → Nat → α → Prop) (stop : Fin 3 → Nat → Prop),
    Monotone timeOf → Monotone clock →
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    (∀ c e e', e ≤ e' → stop c e → stop c e') →
    (∀ (i : Fin n) (e : Nat) (x : α),
      stage i.val e x → timeOf e ≤ clock x →
      ∃ e' y, e ≤ e' ∧ timeOf e' ≤ clock y ∧ y ≤ f i x ∧
        ((∃ c : Fin 3, stop c e') ∨
          ∃ j : Nat, i.val < j ∧ j ≤ n ∧ stage j e' y)) →
    ∀ (e₀ : Nat) (x₀ : α), stage 0 e₀ x₀ → timeOf e₀ ≤ clock x₀ →
      ∃ e x, e₀ ≤ e ∧ timeOf e₀ ≤ timeOf e ∧ timeOf e ≤ clock x ∧
        x ≤ (List.finRange n).foldl (fun y i => f i y) x₀ ∧
        ((∃ c : Fin 3, stop c e) ∨ stage n e x)) := by rfl

end AvailableChain.Gen.Pure

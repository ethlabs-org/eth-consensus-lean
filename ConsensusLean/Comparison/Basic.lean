module
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import Mathlib.Order.WithBot

@[expose] public section

/-! # Comparison properties: shared vocabulary (statements)

The untrusted comparison layer states, for a protocol, **bound functions** over environment
parameters (a `ΔAC`-coefficient per parameter point, `⊤` for no claim) and the claims they bound.
Comparing two protocols' bound functions pointwise compares their proved guarantees, not their
actual performance (`Dominates`).

This module holds what every profile shares:

* `Bound Q`, `AdverseMonotone` (a bound never improves when the parameter point becomes more
  adverse) and `Dominates`;
* the asynchrony classes `AsyncClass` (`any`: arbitrary delivery during the incident; `split G`:
  two groups of validators, delivery inside a group stays `ΔAC`-bounded; delivery-only) with their
  order (`split` is below `any`);
* the incident geometry `IncidentNet a b₀ b₁` (synchronous before `b₀`, the class's asynchrony on
  `[b₀, b₁)`, partially synchronous from `b₁`; with `any` it is the L0 `OutageNet b₀ b₁`);
* `FullAwake`: every validator honest at a time of `[0, horizon]` is awake then;
* the heal point `healAt b₁ c = max b₁ 0 + c·ΔAC`, anchored as the contract's `System.heal`.

Bound inputs are environment quantities only: the bounds read parameter points, never a run's
trace or outputs. Statements only: the proofs are in `Proofs/Comparison`. -/

namespace Consensus.Comparison

/-- A bound: a `ΔAC`-coefficient per parameter point; `⊤` is no claim. -/
abbrev Bound (Q : Type) := Q → WithTop ℕ

/-- A bound is monotone in the adverse parameters: a more adverse point (`q ≤ q'`, the
coordinatewise order of each parameter type, which implies inclusion of the run classes) never has
a better bound. -/
def AdverseMonotone {Q : Type} [LE Q] (b : Bound Q) : Prop :=
  ∀ q q', q ≤ q' → b q ≤ b q'

/-- `bX` dominates `bY`: at every parameter point the guarantee of `bX` is at least as good (a
smaller coefficient, or both `⊤`). A comparison of proved guarantees, not of performance. -/
def Dominates {Q : Type} (bX bY : Bound Q) : Prop :=
  ∀ q, bX q ≤ bY q

/-- `bX` strictly dominates `bY`: it dominates, and is strictly better at some point. -/
def StrictlyDominates {Q : Type} (bX bY : Bound Q) : Prop :=
  Dominates bX bY ∧ ∃ q, bX q < bY q

/-- The asynchrony classes of an incident. `any`: arbitrary delivery on `[b₀, b₁)` (the contract's
sense). `split G`: the validators are split into two groups by `G`; delivery inside a group stays
`ΔAC`-bounded, delivery across groups is arbitrary until `b₁` (the simulator's window split). The
split is **delivery-only**: it constrains when sends are held, not which signed contents reach a
group by other routes (a held-content refinement, which needs signature-origin vocabulary that the
generic `CommLog` lacks, would be a separate class). -/
inductive AsyncClass (V : Type) where
  | any
  | split (G : V → Bool)

namespace AsyncClass

variable {V : Type}

/-- The class order: `split G` is below `any` (less adverse: it has more delivery guarantees), and
`split G ≤ split G'` only for `G = G'`. -/
def Le : AsyncClass V → AsyncClass V → Prop
  | _, .any => True
  | .split G, .split G' => G = G'
  | .any, .split _ => False

instance : LE (AsyncClass V) := ⟨Le⟩

theorem le_def (a a' : AsyncClass V) : a ≤ a' ↔ Le a a' := Iff.rfl

end AsyncClass

section Net

variable {V M : Type} (p : EnvPoint V) (L : CommLog V M)

/-- **In-group synchrony before `b₁`**, a `Delivers`-style clause restricted to pairs in one
group of `G`: a send at `t < b₁` by a node honest at `t` is held at `a + Δ − 1`, for every start
`a ≥ t`, by every node of the sender's group honest at that deadline and awake throughout
`[a, a + Δ − 1]` (`Δ = ΔAC`; `ΔFG` for FG attestations); the obligation stays after the sender's
compromise. Transactions submitted before `b₁` to a node honest and awake at the submission are
held in the same way by the nodes of the recipient's group. Delivery across groups is not
constrained here (the partial synchrony from `b₁` serves it). -/
structure GroupSync (G : V → Bool) (b₁ : Time) : Prop where
  msgs : ∀ v m t, L.sent v m t → p.HonestAt v t → ¬ L.fgAtt m → t < b₁ → ∀ w, G w = G v →
    ∀ a, t ≤ a → a + p.env.ΔAC - 1 ≤ p.horizon → p.HonestAt w (a + p.env.ΔAC - 1) →
      p.AwakeOnClosed w a (a + p.env.ΔAC - 1) → L.Held p w m (a + p.env.ΔAC - 1)
  fgAtts : ∀ v m t, L.sent v m t → p.HonestAt v t → L.fgAtt m → t < b₁ → ∀ w, G w = G v →
    ∀ a, t ≤ a → a + p.env.ΔFG - 1 ≤ p.horizon → p.HonestAt w (a + p.env.ΔFG - 1) →
      p.AwakeOnClosed w a (a + p.env.ΔFG - 1) → L.Held p w m (a + p.env.ΔFG - 1)
  txs : ∀ u x τ, 0 ≤ τ → τ < b₁ → p.HonestAt u τ → p.env.awake u τ = true → x ∈ p.submit u τ →
    ∀ w, G w = G u → ∀ a, τ ≤ a → a + p.env.ΔAC - 1 ≤ p.horizon →
      p.HonestAt w (a + p.env.ΔAC - 1) → p.AwakeOnClosed w a (a + p.env.ΔAC - 1) →
      L.TxHeld w x (a + p.env.ΔAC - 1)

/-- The class's delivery guarantee during the incident: none beyond the outage network for `any`,
in-group synchrony before `b₁` for `split G`. -/
def GroupSyncOn : AsyncClass V → Time → Prop
  | .any, _ => True
  | .split G, b₁ => GroupSync p L G b₁

end Net

section Run

variable {V : Type} (S : System V)

/-- **The incident geometry** of run `r`: synchronous for deadlines up to `b₀`, partially
synchronous with GST `b₁` (the L0 `OutageNet b₀ b₁`), and the class's delivery guarantee during the
incident. With `any` it is `OutageNet b₀ b₁`. -/
def IncidentNet (a : AsyncClass V) (b₀ b₁ : Time) (r : S.Run) : Prop :=
  (S.log r).OutageNet (S.pt r) b₀ b₁ ∧ GroupSyncOn (S.pt r) (S.log r) a b₁

/-- **Full participation**: every validator honest at a time of `[0, horizon]` is awake then. No
validator sleeps; faults may grow. -/
def FullAwake (r : S.Run) : Prop :=
  ∀ v t, 0 ≤ t → t ≤ (S.pt r).horizon → (S.pt r).HonestAt v t → (S.pt r).env.awake v t = true

/-- The heal point of coefficient `c` after an incident ending at `b₁`: `max b₁ 0 + c·ΔAC`, the
contract's `System.heal` anchor at GST `b₁`. -/
def healAt (b₁ : Time) (c : ℕ) (r : S.Run) : Time := max b₁ 0 + (c : Time) * (S.pt r).env.ΔAC

end Run

end Consensus.Comparison

end

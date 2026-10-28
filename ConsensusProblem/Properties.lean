module
public import ConsensusProblem.Basic

@[expose] public section

/-! # The consensus problem: properties (layer 0)

Properties of a trace, generic in the element type (transaction ledgers here;
block chains in a protocol shape). Safety and nesting read at every event cut (a
client can expose any intermediate state); liveness and resilience read at the
end of a time, for ready readers. Every property names the output identifier
it reads. Accountability uses a trace together with
its evidence and conviction rule; non-framing is a property of a system run. -/

namespace Consensus

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- No two honest reads of `g` at cuts from `t₀` on conflict. -/
def Agree (g : Id) (t₀ : Time) : Prop :=
  ∀ u ∈ tr.point.honest, ∀ v ∈ tr.point.honest, ∀ i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
    Compatible (tr.read g u i) (tr.read g v j)

/-- Each honest node's reads of `g` only extend, cut by cut, from `t₀` on. -/
def Monotone (g : Id) (t₀ : Time) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j →
    tr.read g v i <+: tr.read g v j

/-- Safety of `g` from `t₀`. -/
def Safe (g : Id) (t₀ : Time) : Prop := tr.Agree g t₀ ∧ tr.Monotone g t₀

/-- Safety from `t₀` for ready readers only (a node asleep since long ago may
hold an old fork). -/
def ReadySafe (c : Time) (g : Id) (t₀ : Time) : Prop :=
  (∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
  (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)

/-- Output `g₁` is a prefix of output `g₂` in every honest read. -/
def Nested (g₁ g₂ : Id) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ i, i ≤ tr.cuts → tr.read g₁ v i <+: tr.read g₂ v i

/-- Reader `w` is eligible for resilience at `t` (window `[b₀, b₁)`, catch-up
`c`): it was caught up before the window and stayed awake since (awake
throughout `[max 0 (b₀ − c − 1), t]`), or it caught up after the window
(awake throughout `[t − c − 1, t]` with `b₁ ≤ t − c − 1`). Nodes that wake
during the window are eligible once caught up after it: during the window
there is no delivery guarantee. -/
def ResilienceReader (c b₀ b₁ : Time) (w : V) (t : Time) : Prop :=
  tr.point.AwakeOnClosed w (max 0 (b₀ - c - 1)) t ∨
    (b₁ ≤ t - c - 1 ∧ tr.point.AwakeOnClosed w (t - c - 1) t)

/-- Resilience, during and after the window `[b₀, b₁)`: every honest read of
`src` at `T` is a prefix of the `dst` read, at every `t ∈ [b₀, horizon]`, of
every honest `ResilienceReader`. -/
def ProtectedThrough (c : Time) (src dst : Id) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ t, b₀ ≤ t → t ≤ tr.point.horizon →
    ∀ w ∈ tr.point.honest, tr.ResilienceReader c b₀ b₁ w t →
    tr.readAt src v T <+: tr.readAt dst w t

/-- The weaker non-contradiction form of `ProtectedThrough` (same
quantifiers; defined, not advertised). -/
def CompatibleThrough (c : Time) (src dst : Id) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ t, b₀ ≤ t → t ≤ tr.point.horizon →
    ∀ w ∈ tr.point.honest, tr.ResilienceReader c b₀ b₁ w t →
    Compatible (tr.readAt src v T) (tr.readAt dst w t)

end Trace

/-- Transaction liveness of `g` from `start` with delay `D` (a duration): a
transaction submitted to some awake honest node by `t ≥ start` is in the ledger of
every ready reader at every time `t' ∈ [max t GST + Δ + D, horizon]`. -/
def Trace.TxLive {V Id : Type} (tr : Trace V Tx Id) (c : Time) (g : Id) (start D : Time) : Prop :=
  ∀ x t t', start ≤ t → tr.point.SubmittedToSome x t →
    max t tr.point.env.gst + tr.point.env.Δ + D ≤ t' → t' ≤ tr.point.horizon →
    ∀ v, tr.point.Ready c v t' → x ∈ tr.readAt g v t'

/-- Non-vacuity of `TxLive` (used by realizability witnesses): a transaction
submitted at `t ≥ start` to an awake honest `u`, and a *different* honest `w`
that never receives it by submission, is ready at a reachable deadline
`t' ≥ max t GST + Δ + D`, `t' ≤ horizon`. -/
def Trace.TxLiveActive {V α Id : Type} (tr : Trace V α Id) (c : Time) (start D : Time) : Prop :=
  ∃ (x : Tx) (t t' : Time) (u w : V), start ≤ t ∧ 0 ≤ t ∧ u ∈ tr.point.honest ∧
    tr.point.env.awake u t = true ∧ x ∈ tr.point.submit u t ∧ w ∈ tr.point.honest ∧ w ≠ u ∧
    (∀ τ, x ∉ tr.point.submit w τ) ∧
    max t tr.point.env.gst + tr.point.env.Δ + D ≤ t' ∧ t' ≤ tr.point.horizon ∧
    tr.point.Ready c w t'

/-- Validators convicted by evidence, independently of an execution model. -/
noncomputable def convicted {V O : Type} [Fintype V]
    (convicts : Set O → V → Prop) (A : Set O) : Finset V := by
  classical
  exact Finset.univ.filter (convicts A)

/-- Two honest reads are compatible, or their joint evidence convicts fraction α. -/
def Trace.AccountablySafe {V β O Id : Type} [Fintype V] (tr : Trace V β Id)
    (view : V → Nat → Set O) (convicts : Set O → V → Prop) (α : ℚ) (g : Id) (t₀ : Time) : Prop :=
  ∀ u ∈ tr.point.honest, ∀ v ∈ tr.point.honest, ∀ i j,
    tr.InCuts t₀ i → tr.InCuts t₀ j →
    Compatible (tr.read g u i) (tr.read g v j) ∨
      (Fintype.card V : ℚ) * α ≤ (Consensus.convicted convicts (view u i ∪ view v j)).card

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] (S : System V) (r : S.Run)

/-- Validators convicted by a set of evidence. -/
noncomputable def convicted (A : Set S.Obs) : Finset V :=
  Consensus.convicted (S.convicts r) A

/-- Accountable safety, using the generic trace-and-evidence property. -/
abbrev AccountablySafe (α : ℚ) (g : S.schema.Id) (t₀ : Time) : Prop :=
  (S.trace r).AccountablySafe (S.view r) (S.convicts r) α g t₀

/-- No honest validator is convicted by what the honest nodes saw. -/
def NonFraming : Prop :=
  ∀ v ∈ (S.trace r).point.honest, ¬ S.convicts r (S.honestEvidence r) v

/-- The whole honest evidence convicts at least fraction `α` of the validators
(weaker than local accountability: the evidence exists somewhere, its
enforcement is a binding). -/
def GloballySlashable (α : ℚ) (run : S.Run) : Prop :=
  (Fintype.card V : ℚ) * α ≤ (S.convicted run (S.honestEvidence run)).card

end System

end Consensus

end

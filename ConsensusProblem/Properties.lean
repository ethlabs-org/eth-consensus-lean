module
public import ConsensusProblem.Basic

@[expose] public section

/-! # The consensus problem: properties (layer 0)

Properties of a trace, generic in the element type (transaction ledgers here;
block chains in a protocol shape). Safety and nesting read at every event cut (a
client can expose any intermediate state); liveness and persistence read at the
end of a time, for ready readers. Accountability uses a trace together with
its evidence and conviction rule; non-framing is a property of a system run. -/

namespace Consensus

namespace Trace

variable {V α : Type} (tr : Trace V α)

/-- No two honest reads of `g` at cuts from `t₀` on conflict. -/
def Agree (g : Out) (t₀ : Time) : Prop :=
  ∀ u ∈ tr.point.honest, ∀ v ∈ tr.point.honest, ∀ i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
    Compatible (tr.read g u i) (tr.read g v j)

/-- Each honest node's reads of `g` only extend, cut by cut, from `t₀` on. -/
def Monotone (g : Out) (t₀ : Time) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j →
    tr.read g v i <+: tr.read g v j

/-- Safety of `g` from `t₀`. -/
def Safe (g : Out) (t₀ : Time) : Prop := tr.Agree g t₀ ∧ tr.Monotone g t₀

/-- Safety from `t₀` for ready readers only (a node asleep since long ago may
hold an old fork). -/
def ReadySafe (c : Time) (g : Out) (t₀ : Time) : Prop :=
  (∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
  (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)

/-- Output `g₁` is a prefix of output `g₂` in every honest read. -/
def Nested (g₁ g₂ : Out) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ i, i ≤ tr.cuts → tr.read g₁ v i <+: tr.read g₂ v i

/-- Persistence of `g` on `[b₀, b₁)`: every honest read at `T` is, at every time
of `[b₀, b₁)`, a prefix of the read of every honest node awake throughout
`[max 0 (b₀ − c − 1), t]` (ready before `b₀`, not restarted since). -/
def PersistsThrough (c : Time) (g : Out) (T b₀ b₁ : Time) : Prop :=
  ∀ v ∈ tr.point.honest, ∀ t, b₀ ≤ t → t < b₁ → ∀ w ∈ tr.point.honest,
    tr.point.AwakeOnClosed w (max 0 (b₀ - c - 1)) t →
    tr.readAt g v T <+: tr.readAt g w t

end Trace

/-- Transaction liveness of `g` from `start` with delay `D` (a duration): a
transaction submitted to some awake honest node by `t ≥ start` is in the ledger of
every ready reader at every time `t' ∈ [max t GST + Δ + D, horizon]`. -/
def Trace.TxLive {V : Type} (tr : Trace V Tx) (c : Time) (g : Out) (start D : Time) : Prop :=
  ∀ x t t', start ≤ t → tr.point.SubmittedToSome x t →
    max t tr.point.env.gst + tr.point.env.Δ + D ≤ t' → t' ≤ tr.point.horizon →
    ∀ v, tr.point.Ready c v t' → x ∈ tr.readAt g v t'

/-- Validators convicted by evidence, independently of an execution model. -/
noncomputable def convicted {V O : Type} [Fintype V]
    (convicts : Set O → V → Prop) (A : Set O) : Finset V := by
  classical
  exact Finset.univ.filter (convicts A)

/-- Two honest reads are compatible, or their joint evidence convicts fraction α. -/
def Trace.AccountablySafe {V β O : Type} [Fintype V] (tr : Trace V β)
    (view : V → Nat → Set O) (convicts : Set O → V → Prop) (α : ℚ) (g : Out) (t₀ : Time) : Prop :=
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
abbrev AccountablySafe (α : ℚ) (g : Out) (t₀ : Time) : Prop :=
  (S.trace r).AccountablySafe (S.view r) (S.convicts r) α g t₀

/-- No honest validator is convicted by what the honest nodes saw. -/
def NonFraming : Prop :=
  ∀ v ∈ (S.trace r).point.honest, ¬ S.convicts r (S.honestEvidence r) v

end System

end Consensus

end

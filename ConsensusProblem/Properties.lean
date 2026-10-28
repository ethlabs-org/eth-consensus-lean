module
public import ConsensusProblem.Basic

@[expose] public section

/-! # The consensus problem: properties (L0)

Properties of a trace, generic in the element type (transaction ledgers here;
block chains in a protocol shape). Safety and nesting read at every event cut (a
client can expose any intermediate state); liveness and resilience read at the
end of a time, for ready readers. Every property names the output identifier
it reads. Accountability uses a trace together with
its evidence and conviction rule; non-framing is a property of a system run. -/

namespace Consensus

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- No two reads of `g` by readers `R` at cuts from `t₀` on conflict (the
reader is checked at the time of its cut). -/
def AgreeAmong (R : V → Time → Prop) (g : Id) (t₀ : Time) : Prop :=
  ∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j → R u (tr.cutTime i) → R v (tr.cutTime j) →
    Compatible (tr.read g u i) (tr.read g v j)

/-- The reads of `g` by a reader `R` at two cuts from `t₀` on only extend
(the reader is checked at both cuts). -/
def MonotoneAmong (R : V → Time → Prop) (g : Id) (t₀ : Time) : Prop :=
  ∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j → R v (tr.cutTime i) → R v (tr.cutTime j) →
    tr.read g v i <+: tr.read g v j

/-- Each honest node's reads of `g` only extend, cut by cut, from `t₀` on. -/
abbrev Monotone (g : Id) (t₀ : Time) : Prop :=
  tr.MonotoneAmong (fun v _ => v ∈ tr.point.honest) g t₀

/-- Safety from `t₀` for ready readers only (a node asleep since long ago may
hold an old fork). -/
def ReadySafe (c : Time) (g : Id) (t₀ : Time) : Prop :=
  tr.AgreeAmong (tr.point.Ready c) g t₀ ∧ tr.MonotoneAmong (tr.point.Ready c) g t₀

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

/-- `tr'` is the prefix of `tr` up to time `b`: the same environment point
with horizon `b`, the cuts of `tr` through the end of time `b`, and the same
cut times and reads on them. -/
structure PrefixOf (tr' tr : Trace V α Id) (b : Time) : Prop where
  point : tr'.point = { tr.point with horizon := b }
  cuts : tr'.cuts = tr.endCut b
  cutTime : ∀ i, i ≤ tr'.cuts → tr'.cutTime i = tr.cutTime i
  read : ∀ g v i, i ≤ tr'.cuts → tr'.read g v i = tr.read g v i

/-- Resilience for ready sources at reading times `t ∈ [b₀, b]`: the read of
`src` at `T` of every node **ready** at `T` is a prefix of the `dst` read at
`t` of every honest `ResilienceReader`. A node that is awake but not caught up
at `T` may expose a stale ledger, which nobody must keep (sleepy safety, too,
restricts only ready readers). -/
def ProtectedUpTo (c : Time) (src dst : Id) (T b₀ b₁ b : Time) : Prop :=
  ∀ v, tr.point.Ready c v T → ∀ t, b₀ ≤ t → t ≤ b →
    ∀ w ∈ tr.point.honest, tr.ResilienceReader c b₀ b₁ w t →
    tr.readAt src v T <+: tr.readAt dst w t

/-- Resilience for ready sources, during and after the window `[b₀, b₁)`:
`ProtectedUpTo` at every reading time `t ∈ [b₀, horizon]`. -/
def ProtectedThrough (c : Time) (src dst : Id) (T b₀ b₁ : Time) : Prop :=
  tr.ProtectedUpTo c src dst T b₀ b₁ tr.point.horizon

end Trace

/-- Transaction liveness of `g` from `start` with delay `D` (a duration),
serving every submission: a transaction submitted to some awake honest node by
`t` is in the ledger of every ready reader at every time
`t' ∈ [max t start + Δ + D, horizon]`. No GST: every regime's `start` is at or
after its GST. -/
def Trace.TxLive {V Id : Type} (tr : Trace V Tx Id) (c : Time) (g : Id) (start D : Time) : Prop :=
  ∀ x t t', tr.point.SubmittedToSome x t → max t start + tr.point.env.Δ + D ≤ t' →
    t' ≤ tr.point.horizon → ∀ v, tr.point.Ready c v t' → x ∈ tr.readAt g v t'

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

/-- Accountable safety of a run of the system: `Trace.AccountablySafe` with the
system's trace, views and convictions for that run. -/
abbrev AccountablySafe (α : ℚ) (g : S.schema.Id) (t₀ : Time) : Prop :=
  (S.trace r).AccountablySafe (S.view r) (S.convicts r) α g t₀

/-- No honest validator is convicted by what the honest nodes saw. -/
def NonFraming : Prop :=
  ∀ v ∈ (S.trace r).point.honest, ¬ S.convicts r (S.honestEvidence r) v

end System

end Consensus

end

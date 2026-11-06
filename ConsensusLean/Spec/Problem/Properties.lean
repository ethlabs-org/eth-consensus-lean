module
public import ConsensusLean.Spec.Problem.Basic

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

/-- Each node's reads of `g` only extend, cut by cut, from `t₀` on, at the cuts
at which it is honest (honest at the later cut implies honest at the earlier). -/
abbrev Monotone (g : Id) (t₀ : Time) : Prop :=
  tr.MonotoneAmong (fun v t => tr.point.HonestAt v t) g t₀

/-- Safety from `t₀` for ready readers only (a node asleep since long ago may
hold an old fork). -/
def ReadySafe (c : Time) (g : Id) (t₀ : Time) : Prop :=
  tr.AgreeAmong (tr.point.Ready c) g t₀ ∧ tr.MonotoneAmong (tr.point.Ready c) g t₀

/-- Output `g₁` is a prefix of output `g₂` in every read of a node honest at its
cut. -/
def Nested (g₁ g₂ : Id) : Prop :=
  ∀ v i, i ≤ tr.cuts → tr.point.HonestAt v (tr.cutTime i) → tr.read g₁ v i <+: tr.read g₂ v i

/-- `tr'` is the prefix of `tr` up to time `b`: the same environment point
with horizon `b`, the cuts of `tr` through the end of time `b`, and the same
cut times and reads on them. -/
structure PrefixOf (tr' tr : Trace V α Id) (b : Time) : Prop where
  point : tr'.point = { tr.point with horizon := b }
  cuts : tr'.cuts = tr.endCut b
  cutTime : ∀ i, i ≤ tr'.cuts → tr'.cutTime i = tr.cutTime i
  read : ∀ g v i, i ≤ tr'.cuts → tr'.read g v i = tr.read g v i

/-- Recovery for ready sources at reading times `t ∈ [t₀, b]`: the read of
`src` at `T` of every node ready at `T` is a prefix of the `dst` read at `t`
of every node ready at `t`. No reader is excluded for having slept, woken or
restarted earlier: being ready at `t` (awake throughout the catch-up before
`t`) is the only reader condition. -/
def ProtectedReadyUpTo (c : Time) (src dst : Id) (T t₀ b : Time) : Prop :=
  ∀ v, tr.point.Ready c v T → ∀ t, t₀ ≤ t → t ≤ b → ∀ w, tr.point.Ready c w t →
    tr.readAt src v T <+: tr.readAt dst w t

/-- Recovery for ready sources from `t₀`: `ProtectedReadyUpTo` at every
reading time `t ∈ [t₀, horizon]`. -/
def ProtectedReadyFrom (c : Time) (src dst : Id) (T t₀ : Time) : Prop :=
  tr.ProtectedReadyUpTo c src dst T t₀ tr.point.horizon

end Trace

/-- Transaction liveness of `g` from `start` with delay `D` (a duration),
serving every submission: a transaction submitted to a node honest and awake at
the submission (possibly compromised later) by
`t` is in the ledger of every ready reader at every time
`t' ∈ [max t start + ΔAC + D, horizon]`. No GST: every regime's `start` is at or
after its GST. -/
def Trace.TxLive {V Id : Type} (tr : Trace V Tx Id) (c : Time) (g : Id) (start D : Time) : Prop :=
  ∀ x t t', tr.point.SubmittedToSome x t → max t start + tr.point.env.ΔAC + D ≤ t' →
    t' ≤ tr.point.horizon → ∀ v, tr.point.Ready c v t' → x ∈ tr.readAt g v t'

/-- Validators convicted by evidence, independently of an execution model. -/
noncomputable def convicted {V O : Type} [Fintype V]
    (convicts : Set O → V → Prop) (A : Set O) : Finset V := by
  classical
  exact Finset.univ.filter (convicts A)

/-- Two reads by nodes honest at their own cuts are compatible, or the two views
at those cuts convict fraction α. A read stays covered after its reader is
compromised. -/
def Trace.AccountablySafe {V β O Id : Type} [Fintype V] (tr : Trace V β Id)
    (view : V → Nat → Set O) (convicts : Set O → V → Prop) (α : ℚ) (g : Id) (t₀ : Time) : Prop :=
  ∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j →
    tr.point.HonestAt u (tr.cutTime i) → tr.point.HonestAt v (tr.cutTime j) →
    Compatible (tr.read g u i) (tr.read g v j) ∨
      (Fintype.card V : ℚ) * α ≤ (Consensus.convicted convicts (view u i ∪ view v j)).card

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] (S : System V) (r : S.Run)

/-- Accountable safety of a run of the system: `Trace.AccountablySafe` with the
system's trace, views and convictions for that run. -/
abbrev AccountablySafe (α : ℚ) (g : S.schema.Id) (t₀ : Time) : Prop :=
  (S.trace r).AccountablySafe (S.view r) (S.convicts r) α g t₀

/-- A validator honest at `d` is not convicted by the evidence nodes saw while
honest by `d` (`honestEvidenceBy`). A validator honest once and compromised later
can be convicted by objects its extracted key signs afterwards. -/
def NonFraming : Prop :=
  ∀ v d, (S.trace r).point.HonestAt v d → ¬ S.convicts r (S.honestEvidenceBy r d) v

end System

end Consensus

end

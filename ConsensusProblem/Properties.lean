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

/-- No two honest reads of `g` at cuts from `t₀` on conflict. -/
abbrev Agree (g : Id) (t₀ : Time) : Prop := tr.AgreeAmong (fun v _ => v ∈ tr.point.honest) g t₀

/-- Each honest node's reads of `g` only extend, cut by cut, from `t₀` on. -/
abbrev Monotone (g : Id) (t₀ : Time) : Prop :=
  tr.MonotoneAmong (fun v _ => v ∈ tr.point.honest) g t₀

/-- Safety of `g` from `t₀`. -/
def Safe (g : Id) (t₀ : Time) : Prop := tr.Agree g t₀ ∧ tr.Monotone g t₀

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

/-- `ReadySafe` restricted to cuts at times `≤ b`: the past up to `b` is safe
for ready readers. -/
def ReadySafeUpTo (c : Time) (g : Id) (t₀ b : Time) : Prop :=
  (∀ u v i j, tr.InCuts t₀ i → tr.InCuts t₀ j → tr.cutTime i ≤ b → tr.cutTime j ≤ b →
      tr.point.Ready c u (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      Compatible (tr.read g u i) (tr.read g v j)) ∧
  (∀ v i j, tr.InCuts t₀ i → i ≤ j → tr.InCuts t₀ j → tr.cutTime j ≤ b →
      tr.point.Ready c v (tr.cutTime i) → tr.point.Ready c v (tr.cutTime j) →
      tr.read g v i <+: tr.read g v j)

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

namespace PrefixOf

variable {tr' tr : Trace V α Id} {b : Time}

/-- The prefix has the same environment. -/
theorem env (h : tr'.PrefixOf tr b) : tr'.point.env = tr.point.env := by
  rw [h.point]

/-- A cut of the full trace at a time `≤ b` is a cut of the prefix. -/
theorem le_cuts (h : tr'.PrefixOf tr b) {i : Nat} (hi : i ≤ tr.cuts) (hb : tr.cutTime i ≤ b) :
    i ≤ tr'.cuts := by
  rw [h.cuts]; exact Nat.le_findGreatest hi hb

/-- Ends of times `≤ b` agree. -/
theorem endCut_eq (h : tr'.PrefixOf tr b) {t : Time} (ht : t ≤ b) :
    tr'.endCut t = tr.endCut t := by
  have hle : tr'.cuts ≤ tr.cuts := by rw [h.cuts]; exact Nat.findGreatest_le _
  have hk := (Nat.findGreatest_eq_iff (P := fun i => tr.cutTime i ≤ t)).mp
    (rfl : tr.endCut t = tr.endCut t)
  have hkb : tr'.cuts = Nat.findGreatest (fun i => tr.cutTime i ≤ b) tr.cuts := h.cuts
  change Nat.findGreatest (fun i => tr'.cutTime i ≤ t) tr'.cuts = tr.endCut t
  rw [Nat.findGreatest_eq_iff]
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have hkc : tr.endCut t ≤ tr'.cuts := by
    by_cases h0 : tr.endCut t = 0
    · rw [h0]; exact Nat.zero_le _
    · rw [hkb]; exact Nat.le_findGreatest hk1 (le_trans (hk2 h0) ht)
  refine ⟨hkc, fun h0 => ?_, fun n hn hn' => ?_⟩
  · rw [h.cutTime _ hkc]; exact hk2 h0
  · rw [h.cutTime _ hn']; exact hk3 hn (le_trans hn' hle)

/-- Reads at the end of times `≤ b` agree. -/
theorem readAt_eq (h : tr'.PrefixOf tr b) {t : Time} (ht : t ≤ b) (g : Id) (v : V) :
    tr'.readAt g v t = tr.readAt g v t := by
  unfold readAt
  rw [h.endCut_eq ht, h.read]
  rw [← h.endCut_eq ht]; exact Nat.findGreatest_le _

/-- Ready-reader safety of the prefix is safety of the full trace up to `b`. -/
theorem readySafeUpTo (h : tr'.PrefixOf tr b) {c : Time} {g : Id} {t₀ : Time}
    (hs : tr'.ReadySafe c g t₀) : tr.ReadySafeUpTo c g t₀ b := by
  have hR : ∀ c v t, tr'.point.Ready c v t ↔ tr.point.Ready c v t := by
    intro c v t; rw [h.point]; rfl
  have hin : ∀ i, tr.InCuts t₀ i → tr.cutTime i ≤ b → tr'.InCuts t₀ i ∧ i ≤ tr'.cuts := by
    intro i hi hb
    have hc := h.le_cuts hi.1 hb
    exact ⟨⟨hc, by rw [h.cutTime i hc]; exact hi.2⟩, hc⟩
  constructor
  · intro u v i j hi hj hbi hbj hu hv
    obtain ⟨hi', hic⟩ := hin i hi hbi
    obtain ⟨hj', hjc⟩ := hin j hj hbj
    have := hs.1 u v i j hi' hj' (by rw [hR, h.cutTime i hic]; exact hu)
      (by rw [hR, h.cutTime j hjc]; exact hv)
    rwa [h.read g u i hic, h.read g v j hjc] at this
  · intro v i j hi hij hj hbj hvi hvj
    obtain ⟨hj', hjc⟩ := hin j hj hbj
    have hic : i ≤ tr'.cuts := le_trans hij hjc
    have hi' : tr'.InCuts t₀ i := ⟨hic, by rw [h.cutTime i hic]; exact hi.2⟩
    have := hs.2 v i j hi' hij hj' (by rw [hR, h.cutTime i hic]; exact hvi)
      (by rw [hR, h.cutTime j hjc]; exact hvj)
    rwa [h.read g v i hic, h.read g v j hjc] at this

/-- Resilience of the prefix is resilience of the full trace at reading times
in `[b₀, b]` (for a protected time `T ≤ b₀`). -/
theorem protectedUpTo (h : tr'.PrefixOf tr b) {c : Time} {src dst : Id} {T b₀ b₁ : Time}
    (hT : T ≤ b₀) (hp : tr'.ProtectedThrough c src dst T b₀ b₁) :
    tr.ProtectedUpTo c src dst T b₀ b₁ b := by
  intro v hv t ht htb w hw hr
  have hpt := h.point
  have hhz : tr'.point.horizon = b := by rw [hpt]
  have := hp v (by rw [hpt]; exact hv) t ht (by rw [hhz]; exact htb) w (by rw [hpt]; exact hw)
    (by unfold ResilienceReader at hr ⊢; rw [hpt]; exact hr)
  rwa [h.readAt_eq (le_trans hT (le_trans ht htb)), h.readAt_eq htb] at this

end PrefixOf

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

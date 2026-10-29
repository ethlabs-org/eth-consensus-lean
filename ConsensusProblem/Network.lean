module
public import ConsensusProblem.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # The network (L0)

Network conditions on a run's communication log (`CommLog`, opaque messages).
The delivery rule is Francesco's rule, normal delivery:

> every message an honest node sends at `t` is received, within the delivery
> bound, by every honest node that is awake over the delivery interval, and is
> re-served, within the bound, to nodes that wake later.

`Delivers` states it for a deadline function `dl` (`msgs`): for every start
`a ≥ t`, an honest node awake throughout `[a, dl a]` holds the message at
`dl a`. With `dl a = max a GST + Δ`: a node awake over `[t, max(t, GST) + Δ]`
has it by `max(t, GST) + Δ`, and a node that wakes at `u` (and stays awake)
has it by `max(u, GST) + Δ`. Transactions (`txs`) follow the same rule. Partial
synchrony (`PSync g`), synchrony up to a cut (`SyncUntil b`) and the outage
network (`OutageNet b₀ b₁`) are instances; `EagerFrom g` is the shape of the
model's canonical logs. Receipt is network service, not protocol use: what
arrives at a deadline is first used by the node's next tick, and that slack
belongs to the protocol. Sends are covered at every time, submissions from
`0`. -/

namespace Consensus

namespace CommLog

variable {V M : Type} (p : EnvPoint V) (L : CommLog V M)

/-- `w` has `m` at `d`: it sent or received `m` at some `t' ≤ d`, with no wake
of `w` in `(t', d]` (a restart loses earlier receipts). Receipt *at* `d`
counts ("received by that time"). -/
def Held (w : V) (m : M) (d : Time) : Prop :=
  ∃ t', t' ≤ d ∧ (L.sent w m t' ∨ L.recv w m t') ∧ ∀ u, t' < u → u ≤ d → ¬ Wakes p.env w u

/-- `w` has transaction `x` at `d`: it is in `w`'s inbox at some `τ ∈ [0, d]`
(the inbox survives restarts). -/
def TxHeld (w : V) (x : Tx) (d : Time) : Prop :=
  ∃ τ, 0 ≤ τ ∧ τ ≤ d ∧ x ∈ L.inbox w τ

/-- Delivery with deadline function `dl`, for deadlines up to `cut` and up to
the horizon. -/
structure Delivers (dl : Time → Time) (cut : Time) : Prop where
  /-- Francesco's rule (normal delivery): an honest send at `t` is held at
  `dl a`, for every start `a ≥ t`, by every honest node awake throughout the
  delivery interval `[a, dl a]`. At `a = t` this is delivery within the bound
  to nodes awake over `[t, dl t]`; at a later `a` it is re-service, within the
  bound, to a node that wakes at `a` (a restart loses earlier receipts, see
  `Held`). -/
  msgs : ∀ v ∈ p.honest, ∀ m t, L.sent v m t → ∀ w ∈ p.honest, ∀ a, t ≤ a →
    dl a ≤ cut → dl a ≤ p.horizon → p.AwakeOnClosed w a (dl a) → L.Held p w m (dl a)
  /-- Transactions submitted to an awake honest node, likewise: held at
  `dl a`, for every start `a` at or after the submission, by every honest node
  awake throughout `[a, dl a]`. -/
  txs : ∀ u ∈ p.honest, ∀ x τ, 0 ≤ τ → p.env.awake u τ = true → x ∈ p.submit u τ →
    ∀ w ∈ p.honest, ∀ a, τ ≤ a → dl a ≤ cut → dl a ≤ p.horizon →
      p.AwakeOnClosed w a (dl a) → L.TxHeld w x (dl a)

/-- Partial synchrony with GST `g`: deadline `max a g + Δ`, up to the horizon.
`PSync 0` is synchrony. -/
def PSync (g : Time) : Prop := L.Delivers p (fun a => max a g + p.env.Δ) p.horizon

/-- Synchrony (`Δ`-delivery) for deadlines up to `b`. -/
def SyncUntil (b : Time) : Prop := L.Delivers p (fun a => a + p.env.Δ) b

/-- The outage network: synchronous for deadlines up to `b₀`, partially
synchronous with GST `b₁` (asynchronous during `[b₀, b₁)`). -/
def OutageNet (b₀ b₁ : Time) : Prop := L.SyncUntil p b₀ ∧ L.PSync p b₁

/-- Eager from `g`: every honest send at `t` is received by every honest node
at every awake time `a` with `max t g ≤ a ≤ horizon`; no message is received
before `g`; transactions submitted to awake honest nodes are relayed at once to
every awake honest node. `g > horizon`: a silent network. -/
structure EagerFrom (g : Time) : Prop where
  recv : ∀ v ∈ p.honest, ∀ m t, L.sent v m t → ∀ w ∈ p.honest, ∀ a, max t g ≤ a →
    a ≤ p.horizon → p.env.awake w a = true → L.recv w m a
  quiet : ∀ w m t, L.recv w m t → g ≤ t
  txs : ∀ u ∈ p.honest, ∀ x τ, 0 ≤ τ → p.env.awake u τ = true → x ∈ p.submit u τ →
    ∀ w ∈ p.honest, ∀ a, τ ≤ a → p.env.awake w a = true → x ∈ L.inbox w a

/-- The log agrees with `L'` at all times `≤ b` (prefix agreement): sends,
receipts and inboxes. Inbox agreement is quantified separately, so it is not
vacuous when the message type is empty. -/
def AgreesUpTo (L' : CommLog V M) (b : Time) : Prop :=
  (∀ v m t, t ≤ b → (L.sent v m t ↔ L'.sent v m t) ∧ (L.recv v m t ↔ L'.recv v m t)) ∧
    ∀ v t, t ≤ b → L.inbox v t = L'.inbox v t

end CommLog

end Consensus

end

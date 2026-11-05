module
public import ConsensusLean.Spec.Problem.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # The network (L0)

Network conditions on a run's communication log (`CommLog`, opaque messages).
The delivery rule is normal delivery:

> every message an honest node sends at `t` is received, strictly before the
> delivery bound, by every honest node that is awake over the delivery
> interval, and is re-served, strictly before the bound, to nodes that wake
> later.

The delivery interval is half-open, `[t, max(t, GST) + ΔAC)`, as in the paper's
`Sync`; on integer time, "strictly before `d`" is "by `d − 1`". `Delivers`
states it for a deadline function `dl` (`msgs`, every message that is not an
FG attestation): for every start `a ≥ t`, an honest node awake throughout `[a, dl a]`
holds the message at `dl a`. With `dl a = max a GST + ΔAC − 1`: a node awake
over `[t, max(t, GST) + ΔAC − 1]` has it by `max(t, GST) + ΔAC − 1`, and a node
that wakes at `u` (and stays awake) has it by `max(u, GST) + ΔAC − 1`. So a
tick at `max(t, GST) + ΔAC`, which runs before the deliveries of its time, reads
it. At `ΔAC = 1` this is same-time delivery (a receipt at the send's time
counts, `Held`); realizability starts at `ΔAC = 2` (`Realizable`). FG attestation
messages (`CommLog.fgAtt`) follow the same rule with their own deadline function `dlF`
(`fgAtts`, bound `ΔFG`, deadline `max a GST + ΔFG − 1`); neither bound is assumed
to bound the other, and an FG attestation is never served by the `msgs` clause.
Transactions (`txs`) follow the rule of `dl`. Partial synchrony (`PSync g`),
synchrony up to a cut (`SyncUntil b`) and the outage network
(`OutageNet b₀ b₁`) are instances; `EagerFrom g` is the shape of the model's
canonical logs. Receipt is raw network service, independent of dependency readiness
or protocol admission: the model passes each arrival to the total `process` handler
(whose own releases leave then). Its resulting state is read by the next tick,
at the latest the tick at the bound itself; buffering and retries belong to the
protocol. Sends are covered at every time, submissions from `0`. -/

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

/-- Delivery with deadline function `dl` for messages and transactions and
`dlF` for FG attestations, for deadlines up to the time `cut` (a time, not a trace cut
index) and up to the horizon. -/
structure Delivers (dl dlF : Time → Time) (cut : Time) : Prop where
  /-- Normal delivery: an honest send at `t` of a message
  that is not an FG attestation is held at `dl a`, for every start `a ≥ t`, by every
  honest node awake throughout the delivery interval `[a, dl a]`. At `a = t`
  this is delivery by `dl t` (for `PSync`, strictly before the bound) to nodes
  awake over `[t, dl t]`; at a later `a` it is re-service, by `dl a`, to a node
  that wakes at `a` (a restart loses earlier receipts, see `Held`). -/
  msgs : ∀ v ∈ p.honest, ∀ m t, L.sent v m t → ¬ L.fgAtt m → ∀ w ∈ p.honest, ∀ a, t ≤ a →
    dl a ≤ cut → dl a ≤ p.horizon → p.AwakeOnClosed w a (dl a) → L.Held p w m (dl a)
  /-- The same rule for FG attestations, with the FG deadline `dlF`. -/
  fgAtts : ∀ v ∈ p.honest, ∀ m t, L.sent v m t → L.fgAtt m → ∀ w ∈ p.honest, ∀ a, t ≤ a →
    dlF a ≤ cut → dlF a ≤ p.horizon → p.AwakeOnClosed w a (dlF a) → L.Held p w m (dlF a)
  /-- Transactions submitted to an awake honest node, likewise: held at
  `dl a`, for every start `a` at or after the submission, by every honest node
  awake throughout `[a, dl a]`. -/
  txs : ∀ u ∈ p.honest, ∀ x τ, 0 ≤ τ → p.env.awake u τ = true → x ∈ p.submit u τ →
    ∀ w ∈ p.honest, ∀ a, τ ≤ a → dl a ≤ cut → dl a ≤ p.horizon →
      p.AwakeOnClosed w a (dl a) → L.TxHeld w x (dl a)

/-- Partial synchrony with GST `g`: held strictly before `max a g + ΔAC` (deadline
`max a g + ΔAC − 1`), and strictly before `max a g + ΔFG` for FG attestations, up to the
horizon. `PSync 0` is synchrony. -/
def PSync (g : Time) : Prop :=
  L.Delivers p (fun a => max a g + p.env.ΔAC - 1) (fun a => max a g + p.env.ΔFG - 1) p.horizon

/-- Synchrony (held strictly before `a + ΔAC`, `a + ΔFG` for FG attestations) for deadlines up
to `b`. -/
def SyncUntil (b : Time) : Prop :=
  L.Delivers p (fun a => a + p.env.ΔAC - 1) (fun a => a + p.env.ΔFG - 1) b

/-- The outage network: synchronous for deadlines up to `b₀`, partially
synchronous with GST `b₁` (asynchronous during `[b₀, b₁)`). -/
def OutageNet (b₀ b₁ : Time) : Prop := L.SyncUntil p b₀ ∧ L.PSync p b₁

/-- Eager from `g`: every honest send at `t` is received by every honest node
at every awake time `a` with `max t g < a ≤ horizon` (strictly after the send
and after `g`: a send made in reaction to a receipt at `t` cannot be served at
`t` itself); no message is received before `g`; transactions submitted to
awake honest nodes are relayed at once to every awake honest node.
`g > horizon`: a silent network. -/
structure EagerFrom (g : Time) : Prop where
  recv : ∀ v ∈ p.honest, ∀ m t, L.sent v m t → ∀ w ∈ p.honest, ∀ a, max t g < a →
    a ≤ p.horizon → p.env.awake w a = true → L.recv w m a
  quiet : ∀ w m t, L.recv w m t → g ≤ t
  txs : ∀ u ∈ p.honest, ∀ x τ, 0 ≤ τ → p.env.awake u τ = true → x ∈ p.submit u τ →
    ∀ w ∈ p.honest, ∀ a, τ ≤ a → p.env.awake w a = true → x ∈ L.inbox w a

/-- The log agrees with `L'` at all times `≤ b` (prefix agreement): sends,
receipts and inboxes, and it has the same message class. Inbox agreement is
quantified separately, so it is not vacuous when the message type is empty. -/
def AgreesUpTo (L' : CommLog V M) (b : Time) : Prop :=
  (∀ v m t, t ≤ b → (L.sent v m t ↔ L'.sent v m t) ∧ (L.recv v m t ↔ L'.recv v m t)) ∧
    (∀ v t, t ≤ b → L.inbox v t = L'.inbox v t) ∧ L.fgAtt = L'.fgAtt

end CommLog

end Consensus

end

module
public import ConsensusProblem.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # The network (L0)

Network conditions on a run's communication log (`CommLog`, opaque messages).
The delivery rule is Francesco's sentence:

> every message an honest node sends at `t` is received by every honest node
> that is awake at `max(t, GST) + Δ`, by that time.

`Delivers.msgs` is that sentence for a deadline function `dl` ("received by
that time" is `Held`: receipt at the deadline itself counts, and a restart
loses earlier receipts). Re-service to nodes that wake later (the sleepy model)
is a separate, named clause, `Delivers.rewake`: a node awake at a later
deadline `dl a` (`a > t`) has the message then, even if it slept in between.
Transactions submitted to an awake honest node are delivered likewise
(`Delivers.txs`; inboxes survive restarts).

Partial synchrony with GST `g` (`PSync g`), synchrony up to a cut
(`SyncUntil b`) and the outage network (`OutageNet b₀ b₁`) are instances.
`EagerFrom g` is the shape of the log that the model's canonical runs have:
every honest send is received at every later awake time from `g` on, and
nothing earlier; it meets every deadline function above the identity and `g`.

Receipt is not processing: the model orders restarts, then ticks, then
deliveries within a time unit, so a message received at the deadline is
processed at the next tick. That slack belongs to the protocol, not to the
network.

Times are from `0`: sends and submissions at negative times are not covered
(none occur in a valid model run), so `PSync 0` is `SyncUntil horizon`. -/

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
  /-- Francesco's rule: an honest send at `t` is held, by `dl t`, by every
  honest node awake at `dl t`. -/
  msgs : ∀ v ∈ p.honest, ∀ m t, 0 ≤ t → L.sent v m t → ∀ w ∈ p.honest,
    dl t ≤ cut → dl t ≤ p.horizon → p.env.awake w (dl t) = true → L.Held p w m (dl t)
  /-- Re-service to later wakers (sleepy model): the same at every later
  deadline `dl a`, `a > t`. A node awake at `dl a` has `m` then, even if it
  slept in between. -/
  rewake : ∀ v ∈ p.honest, ∀ m t, 0 ≤ t → L.sent v m t → ∀ w ∈ p.honest, ∀ a, t < a →
    dl a ≤ cut → dl a ≤ p.horizon → p.env.awake w (dl a) = true → L.Held p w m (dl a)
  /-- Transactions submitted to an awake honest node, likewise, at every
  deadline `dl a` with `a` at or after the submission. -/
  txs : ∀ u ∈ p.honest, ∀ x τ, 0 ≤ τ → p.env.awake u τ = true → x ∈ p.submit u τ →
    ∀ w ∈ p.honest, ∀ a, τ ≤ a → dl a ≤ cut → dl a ≤ p.horizon →
      p.env.awake w (dl a) = true → L.TxHeld w x (dl a)

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

/-- The log agrees with `L'` at all times `≤ b` (prefix agreement). -/
def AgreesUpTo (L' : CommLog V M) (b : Time) : Prop :=
  ∀ v m t, t ≤ b →
    (L.sent v m t ↔ L'.sent v m t) ∧ (L.recv v m t ↔ L'.recv v m t) ∧ L.inbox v t = L'.inbox v t

variable {p L}

/-- A receipt at the deadline itself is holding. -/
theorem held_of_recv {w : V} {m : M} {d : Time} (h : L.recv w m d) : L.Held p w m d :=
  ⟨d, le_rfl, Or.inr h, fun _ h₁ h₂ => absurd (lt_of_lt_of_le h₁ h₂) (lt_irrefl _)⟩

/-- Reindexing: delivery for `dl` gives delivery for every deadline function
`dl'` that is `dl` at a later start (`dl' a = dl (f a)`, `a ≤ f a`) with a
smaller cut. At a send time `t` with `f t > t` this uses `rewake`. -/
theorem Delivers.reindex {dl dl' f : Time → Time} {cut cut' : Time} (h : L.Delivers p dl cut)
    (hf : ∀ a, a ≤ f a) (hd : ∀ a, dl' a = dl (f a)) (hc : cut' ≤ cut) :
    L.Delivers p dl' cut' := by
  constructor
  · intro v hv m t ht0 hs w hw hdc hdh haw
    rw [hd] at hdc hdh haw ⊢
    rcases (hf t).lt_or_eq with hlt | heq
    · exact h.rewake v hv m t ht0 hs w hw (f t) hlt (le_trans hdc hc) hdh haw
    · rw [← heq] at hdc hdh haw ⊢
      exact h.msgs v hv m t ht0 hs w hw (le_trans hdc hc) hdh haw
  · intro v hv m t ht0 hs w hw a hta hdc hdh haw
    rw [hd] at hdc hdh haw ⊢
    exact h.rewake v hv m t ht0 hs w hw (f a) (lt_of_lt_of_le hta (hf a)) (le_trans hdc hc)
      hdh haw
  · intro u hu x τ hτ hua hx w hw a hτa hdc hdh haw
    rw [hd] at hdc hdh haw ⊢
    exact h.txs u hu x τ hτ hua hx w hw (f a) (le_trans hτa (hf a)) (le_trans hdc hc) hdh haw

/-- A smaller cut is weaker. -/
theorem Delivers.mono_cut {dl : Time → Time} {cut cut' : Time} (h : L.Delivers p dl cut)
    (hc : cut' ≤ cut) : L.Delivers p dl cut' :=
  h.reindex (f := id) (fun _ => le_rfl) (fun _ => rfl) hc

/-- A later GST is weaker. -/
theorem PSync.mono {g g' : Time} (hg : g ≤ g') (h : L.PSync p g) : L.PSync p g' := by
  apply h.reindex (f := fun a => max a g') (fun a => le_max_left a g') ?_ le_rfl
  intro a
  show max a g' + p.env.Δ = max (max a g') g + p.env.Δ
  rw [max_assoc, max_eq_left hg]

/-- Synchrony up to a cut is weaker at a smaller cut. -/
theorem SyncUntil.mono {b b' : Time} (hb : b' ≤ b) (h : L.SyncUntil p b) : L.SyncUntil p b' :=
  Delivers.mono_cut h hb

/-- `PSync 0` is synchrony up to the horizon (and so up to every cut). -/
theorem PSync.syncUntil_zero (h : L.PSync p 0) (b : Time) : L.SyncUntil p b := by
  constructor
  · intro v hv m t ht0 hs w hw _ hdh haw
    have := h.msgs v hv m t ht0 hs w hw
    simp only [max_eq_left ht0] at this
    exact this hdh hdh haw
  · intro v hv m t ht0 hs w hw a hta _ hdh haw
    have := h.rewake v hv m t ht0 hs w hw a hta
    simp only [max_eq_left (le_trans ht0 hta.le)] at this
    exact this hdh hdh haw
  · intro u hu x τ hτ hua hx w hw a hτa _ hdh haw
    have := h.txs u hu x τ hτ hua hx w hw a hτa
    simp only [max_eq_left (le_trans hτ hτa)] at this
    exact this hdh hdh haw

/-- An eager log meets every deadline function at or above `max a g` from
time `0` on, at every cut. -/
theorem EagerFrom.delivers {g : Time} (h : L.EagerFrom p g) {dl : Time → Time}
    (hdl : ∀ a, 0 ≤ a → max a g ≤ dl a) (cut : Time) : L.Delivers p dl cut := by
  constructor
  · intro v hv m t ht0 hs w hw _ hdh haw
    exact held_of_recv (h.recv v hv m t hs w hw (dl t) (hdl t ht0) hdh haw)
  · intro v hv m t ht0 hs w hw a hta _ hdh haw
    have ha0 : 0 ≤ a := le_trans ht0 hta.le
    refine held_of_recv (h.recv v hv m t hs w hw (dl a) ?_ hdh haw)
    exact le_trans (max_le_max hta.le le_rfl) (hdl a ha0)
  · intro u hu x τ hτ hua hx w hw a hτa _ _ haw
    have hle : τ ≤ dl a := le_trans hτa (le_trans (le_max_left a g) (hdl a (le_trans hτ hτa)))
    exact ⟨dl a, le_trans hτ hle, le_rfl, h.txs u hu x τ hτ hua hx w hw (dl a) hle haw⟩

/-- An eager log from `g` is partially synchronous with every GST `g' ≥ g`. -/
theorem EagerFrom.psync {g g' : Time} (h : L.EagerFrom p g) (hg : g ≤ g') : L.PSync p g' := by
  apply h.delivers
  intro a _
  have := p.env.Δ_pos
  exact max_le (le_trans (le_max_left a g') (by linarith))
    (le_trans hg (le_trans (le_max_right a g') (by linarith)))

/-- An eager log from `g ≤ 0` is synchronous up to every cut. -/
theorem EagerFrom.syncUntil {g : Time} (h : L.EagerFrom p g) (hg : g ≤ 0) (b : Time) :
    L.SyncUntil p b := by
  apply h.delivers
  intro a ha
  have := p.env.Δ_pos
  exact max_le (by linarith) (by linarith)

end CommLog

end Consensus

end

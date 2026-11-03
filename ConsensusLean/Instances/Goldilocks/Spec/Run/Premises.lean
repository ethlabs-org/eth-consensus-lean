module
public import Mathlib.Data.Set.Card
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Model

@[expose] public section

/-! # Goldilocks runs: the premises

The premises of the claims (fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"Premises")
over a run (`Spec/Run/Model`), for the honest validators `H`:

* **`Sync`** (`SyncOn`, with a window `W` on the send time, a window `Wr` on the acceptance time
  for the acceptance relay, and a map `eff` to the effective send time; `SyncRun a b` is
  `Sync[a, b]`, `GSTRun g` is `GST(g)`): every AC message that an
  honest `x` sends or admits (also from the payload of an accepted block) at a time `τ` in the
  window is processed by every honest `y` at a time in `[τ, max(eff τ, w_y) + Δ)`, `w_y` the
  latest wake of `y` at or before its processing (the delivery of that send or forward, not an
  earlier processing; a refused receipt triggers nothing); every block an honest `x` sends (its
  own proposal) or accepts at `τ` in the window is processed (`fg_on_block`, accepted or
  refused) by every honest `y` in that interval, and **acceptance relay**: a block accepted at a
  time in the relay window is accepted by every honest `y` whose `Σ.F` it extends before the
  deadline; attestations likewise with `Δ_F`, from a signing or an admission, except that an
  attestation has no lower bound: a processing before the signing or admission counts. Its
  processing is never refused (`fg_on_attestation` only adds it to the pool, which keeps it,
  also across a restart), so an earlier one leaves `a` in the pool as a later one would; and an
  honest node forwards an admitted attestation as the same object, which the network counts as
  held from an earlier receipt (absent a wake in between). Not in CLAIMS, whose `Sync` row has
  attestations "in the same form" (not before the send). Blocks and messages keep the lower
  bound: they are forwarded in fresh wrappers, and an earlier receipt of a block can be refused.
  Over the run, "processed by `y` before the deadline" reads: at every call of `y` at or after
  the deadline, `y` has processed it at a cut before its own deadline (as `SyncAC`).
  `GST(g)` is `Sync[g, ∞)` with every object sent
  before `g` processed as if sent at `g` (`eff τ = max τ g`). The claims' "as if sent at `g`"
  is read for the deadline only: the deadline becomes `max(g, w_y) + Δ`, while the lower bound
  of the delivery interval stays the real send time, so an object sent before `g` may be
  delivered before `g` (goldilocks#7, wording clarification for the claims). The acceptance relay
  of `GST(g)` covers only acceptances at `τ ≥ g` (claims: `Sync`'s relay "covers only `τ ≥ g`";
  `GST(g)` re-delivers old objects, it does not make them accepted, since a block refused for a
  missing parent is not delivered again): pre-`g` acceptance catch-up is the separate regime
  premise `Catch(κ)` (`Healing.CatchRun`).
  `SyncOn` also carries the positivity `0 < Δ_F` and the order `Δ ≤ Δ_F` (claims
  §"Parameters"; the generic network keeps the two bounds unordered), so every premise built on
  it has them. The order is there because an attestation admitted from a block is forwarded in
  the block's relay wrapper, which the network serves within `Δ`, not `Δ_F`
  (`docs/decisions.md`, 2026-11-03).
* **`Sleepy`**: `Sync[0, ∞)` and `f < h_t` at every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}`, `h_t` the
  honest validators awake and joined at `t` (`JoinedAt`: every restart at or before `t` is at
  or before `t_{slot(t) − 1}`; in slot `0`, no restart).
* **`Healthy(g)`**: `GST(g)`, every honest validator awake on `[max(g, 0), ∞)`,
  `f ≤ ⌊(n − 1)/3⌋`.

**Infinite runs.** Under `Healthy(g)` (an honest node awake at every later time) and under
`Sleepy` (`f < h_t` needs an honest node awake at every slot's `t_s`), the awake clamp
`awake_in_horizon` makes cut times unbounded, with labelled coverage beyond any finite
observation horizon, and a tick of every awake honest node at every public time
(`tick_of_awake`). This is the intended reading:
runs are `Nat`-indexed traces of the protocol running forever, and a finite trace is a prefix
that says nothing after its last cut, so it satisfies neither regime premise. That the two
premises are satisfiable by such a run (together with `Node.LocalRun`) is the kind (a) witness
`periodicRun_localRun` with `periodicRun_healthy` and `periodicRun_sleepy` in
`ConsensusLeanTest/GoldilocksRun.lean`.

`NoColl` is `Compose.NoCollRun` (`Statements/Compose/Run`: `Compose.NoCollOn` on the blocks
that occur in the run and genesis), stated where it is used. `Outage` and `Weak` are the regime
milestone's. -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- `y` is joined at `t`: every restart of `y` at or before `t` is at or before
`t_{slot(t) − 1}` (none when `t` is in slot `0`). -/
def JoinedAt (y : Fin P.n) (t : Time) : Prop :=
  ∀ k, tr.RestartAt y k → tr.time k ≤ t →
    0 < P.slotOf t ∧ tr.time k ≤ P.slotTime (P.slotOf t - 1)

/-- `h_t`: the number of honest validators awake and joined at `t`. -/
noncomputable def honestAwakeJoined (H : Set (Fin P.n)) (t : Time) : Nat :=
  {y | y ∈ H ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard

/-- `f < h_t`, with `f` the number of faulty (non-honest) validators. -/
def FaultBound (H : Set (Fin P.n)) (t : Time) : Prop := Hᶜ.ncard < tr.honestAwakeJoined H t

/-- `y` has processed the AC message `m` by cut `j` within the deadline of an object of
effective time `τ`: at a cut `k ≤ j`, not before the object's time `τ₀`, before `y`'s deadline
as of `k`. -/
def MsgDeliveredBy (y : Fin P.n) (j : Nat) (τ₀ τ : Time) (m : A.Msg) : Prop :=
  ∃ k ≤ j, τ₀ ≤ tr.time k ∧ tr.ProcessMsgAt y k m ∧ tr.time k < tr.deadline y k τ P.Δ

/-- `y` has processed the block `B` by cut `j` within the deadline (as `MsgDeliveredBy`). -/
def BlockDeliveredBy (y : Fin P.n) (j : Nat) (τ₀ τ : Time) (B : A.Blk) : Prop :=
  ∃ k ≤ j, τ₀ ≤ tr.time k ∧ tr.BlockCallAt y k B ∧ tr.time k < tr.deadline y k τ P.Δ

/-- `y` has accepted the block `B` by cut `j` within the deadline. -/
def BlockAcceptedBy (y : Fin P.n) (j : Nat) (τ : Time) (B : A.Blk) : Prop :=
  ∃ k ≤ j, tr.AcceptAt y k B ∧ tr.time k < tr.deadline y k τ P.Δ

/-- `y` has processed the attestation `a` by cut `j` within the deadline with `Δ_F`, at a cut
before its own deadline; an earlier processing counts (no lower bound, unlike blocks and
messages). -/
def AttDeliveredBy (y : Fin P.n) (j : Nat) (τ ΔF : Time) (a : FG.Att P.n) : Prop :=
  ∃ k ≤ j, tr.ProcessAttAt y k a ∧ tr.time k < tr.deadline y k τ ΔF

/-- **`Sync` over a run**, for the sends in the window `W` with effective send time `eff`
(claims §"Premises", `Sync[a, b]` and `GST(g)`; goldilocks `a470648c`). -/
structure SyncOn (H : Set (Fin P.n)) (ΔF : Time) (W Wr : Time → Prop) (eff : Time → Time) :
    Prop where
  /-- The attestation delay `Δ_F` is positive. -/
  deltaF : 0 < ΔF
  /-- The attestation delay is at least the delay of blocks and messages (claims
  §"Parameters"): an attestation admitted from a block is forwarded with the block. -/
  delta_le : P.Δ ≤ ΔF
  /-- Every AC message an honest node sends or admits in the window is processed by every honest
  node before its deadline. -/
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m → W (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (eff (tr.time i)) m
  /-- Every block an honest node sends (its own proposal) or accepts in the window is processed
  by every honest node before its deadline. -/
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B → W (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (eff (tr.time i)) B
  /-- Acceptance relay: every block an honest node accepts in the relay window `Wr` is accepted
  before its deadline by every honest node whose `Σ.F` it extends (inside the honest blocks of the
  run, as `SyncAC` inside `U`). -/
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → Wr (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (eff (tr.time i)) B
  /-- Every attestation an honest node signs or admits in the window is processed by every honest
  node before its deadline with `Δ_F`, possibly before the signing or admission. -/
  attestation : ∀ x ∈ H, ∀ i a, tr.SendOrAdmitAttAt x i a → W (tr.time i) →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (eff (tr.time i)) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (eff (tr.time i)) ΔF a

/-- **`Sync[a, b]`**: the sends at `τ ∈ [a, b]`, at their own time. -/
def SyncRun (H : Set (Fin P.n)) (ΔF a b : Time) : Prop :=
  tr.SyncOn H ΔF (fun τ => a ≤ τ ∧ τ ≤ b) (fun τ => a ≤ τ ∧ τ ≤ b) id

/-- Synchrony before an outage, for recipient deadlines at most `b`. Unlike `SyncRun`,
the cutoff applies to the deadline including the recipient's latest wake, not merely to
the sender's time. A later call still checks an earlier qualifying deadline, but a wake
whose deadline lies after `b` creates no pre-outage service obligation. All processing
lower bounds (none for attestations, as in `SyncOn`) and strict upper bounds are unchanged. -/
structure SyncBefore (H : Set (Fin P.n)) (ΔF b : Time) : Prop where
  /-- The attestation delay `Δ_F` is positive. -/
  deltaF : 0 < ΔF
  /-- The attestation delay is at least `Δ`, as in `SyncOn`. -/
  delta_le : P.Δ ≤ ΔF
  /-- Message service for nonnegative sends/admissions with recipient deadline at most `b`. -/
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (tr.time i) m
  /-- Block processing with the same recipient deadline cutoff. -/
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (tr.time i) B
  /-- The existing acceptance-relay obligation, restricted to pre-outage deadlines.
  This remains a protocol premise, not a consequence of network receipt alone. -/
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (tr.time i) B
  /-- Attestation service uses its own delay, including in the cutoff. -/
  attestation : ∀ x ∈ H, ∀ i a, tr.SendOrAdmitAttAt x i a → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) ΔF ≤ b →
      tr.deadline y j (tr.time i) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (tr.time i) ΔF a

/-- **`GST(g)`**: `Sync[g, ∞)`, and an object sent before `g` is processed as if sent at `g`:
its deadline is `max(g, w_y) + Δ'`; it may still be delivered before `g`. The acceptance relay
covers only acceptances at `τ ≥ g` (pre-`g` acceptance catch-up is `Catch(κ)`). -/
def GSTRun (H : Set (Fin P.n)) (ΔF g : Time) : Prop :=
  tr.SyncOn H ΔF (fun _ => True) (fun τ => g ≤ τ) (fun τ => max τ g)

/-- **`Sleepy`**: `Sync[0, ∞)` and `f < h_t` at every `t ∈ {t_s, t_s + Δ, t_s + 2Δ}`. -/
def SleepyRun (H : Set (Fin P.n)) (ΔF : Time) : Prop :=
  tr.SyncOn H ΔF (fun τ => 0 ≤ τ) (fun τ => 0 ≤ τ) id ∧
    ∀ s : Nat, tr.FaultBound H (P.slotTime s) ∧ tr.FaultBound H (P.slotTime s + P.Δ) ∧
      tr.FaultBound H (P.slotTime s + 2 * P.Δ)

/-- **`Healthy(g)`**: `GST(g)`, every honest validator awake on `[max(g, 0), ∞)`, and
`f ≤ ⌊(n − 1)/3⌋`. With `awake_in_horizon`, a `Healthy` run is infinite (intended). -/
def HealthyRun (H : Set (Fin P.n)) (ΔF g : Time) : Prop :=
  tr.GSTRun H ΔF g ∧ (∀ y ∈ H, ∀ t, max g 0 ≤ t → tr.awake y t) ∧ 3 * Hᶜ.ncard ≤ P.n - 1

end Consensus.Goldilocks.RunTrace

end

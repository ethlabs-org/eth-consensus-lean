module
public import ConsensusLean.Spec.Problem.CorrectProtocol

@[expose] public section

/-! # Continuation after healing under corruption growth (generic, an untrusted side property)

A side property, not part of `CorrectProtocol`: correctness does not include continuation
(`docs/decisions.md`). It asks what a healed run keeps when the corruption grows past the healthy
bound afterwards. Generic over `System`, but an untrusted milestone statement: outside the trusted
surface and the spec snapshots, reached by no Challenge statement; the Goldilocks instance is
`GoldilocksContinues` (`Milestones/Statements/Continuation`).

**The hand-over regime** (`System.Handover K g T`): the run is healthy from GST `g` up to the
hand-over time `T` and only sleepy from `T` on.

* Up to `T`: partial synchrony from `g` (it stays in force after `T`), fewer than fraction `β` of
  the validators compromised by `T` (faults only grow, so at every time up to `T`), every validator
  honest at a time of `[max g 0, T]` awake then, and the FG delay within its bound.
* From `T` on: the sleepy participation bound only. At every time `t ∈ [T, horizon]` the validators
  ready at `t` and still honest at the look-ahead `min (t + ahead·ΔAC) horizon` exceed fraction `θ`
  of themselves and the validators compromised by then (`SleepyOn`, on the retained view).
  Validators may sleep, wake and be compromised. At the standard `θ = ½` the compromised ones stay
  fewer than the ready ones, so `2 f < n` at the horizon when `T ≤ horizon` (and `f < β·n ≤ n/2`
  when `T > horizon`): the corruption can grow from below `β·n` (`n/3` at the standard `β`) at `T`
  to `⌊(n − 1)/2⌋`.
* Throughout: for every two reads by nodes honest at their cuts, the evidence of the two views
  convicts fewer than fraction `α` of the validators (`ConvictedBelow`, the negation of the
  conviction disjunct of `AccountablySafe`). With `Behaviour.finalAccountable` it makes the final
  reads of nodes honest at their cuts compatible; a protocol whose available and stable outputs
  read finality needs it once the corruption passes `α·n`.

**The claims** (`Continues`), for the available and the stable output, at every index, on a run
that hands over at or after the heal point: ready-reader safety from the heal point through the
horizon (the progress premise on `[ready, heal]`, as for `healedSafe`), and transaction liveness
from the heal point with the healed latency (progress from `ready` to the horizon). The final output
has no continuation claim: after `T` fewer than two thirds of the validators may be honest.
The time-local scopes are those of correctness: a read made while ready stays covered after its
reader is compromised (`ReadySafe` reads each reader's readiness at its own read), and a
transaction submitted to a validator honest and awake at the submission stays owed after that
validator is compromised (`TxLive`). Messages are owed by the delivery law (`PSync`) when they are
released; a relay is a protocol send, so a validator compromised before it relays owes nothing.
No claim says that later reads extend the reads at the hand-over (only that they are compatible).

**Non-vacuity** (`realizable`, for at least five validators): at every `ΔAC > 1`, `ΔFG > 1` within
the FG delay bound and every GST `≥ 0`, a valid excuse-free run hands over at or after the heal
point, has at least fraction `β` compromised by a time `κ`, and has both claims active after `κ`.

Statements only: no proofs here. -/

namespace Consensus

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] (S : System V) {Prog : Type}

/-- For every two reads by nodes honest at their cuts, the evidence of the two views convicts
fewer than fraction `α` of the validators: the conviction disjunct of `AccountablySafe` never
holds. -/
def ConvictedBelow (K : Contract Prog) (r : S.Run) : Prop :=
  ∀ u v i j, i ≤ (S.trace r).cuts → j ≤ (S.trace r).cuts →
    (S.pt r).HonestAt u ((S.trace r).cutTime i) → (S.pt r).HonestAt v ((S.trace r).cutTime j) →
    ((convicted (S.convicts r) (S.view r u i ∪ S.view r v j)).card : ℚ) <
      K.params.α * Fintype.card V

/-- **The hand-over regime** at `T` after GST `g`: healthy up to `T` (partial synchrony from `g`,
fewer than fraction `β` compromised by `T`, full participation on `[max g 0, T]`, the FG delay
within its bound), sleepy participation from `T` to the horizon, and fewer than fraction `α`
convicted by any two honest views. -/
def Handover (K : Contract Prog) (g T : Time) (r : S.Run) : Prop :=
  (S.log r).PSync (S.pt r) g ∧ (S.pt r).HealthyOn K.params.β g T ∧
    (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC ∧
    (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) T (S.pt r).horizon ∧
    S.ConvictedBelow K r

end System

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

/-- **Continuation after healing**: the available and stable outputs stay safe and live on runs
that hand over to the sleepy regime at or after the heal point. A side property, not part of
`CorrectProtocol`. -/
structure Continues (S : System V) (X : Progress S Prog) (K : Contract Prog) : Prop where
  /-- Available and stable: ready-reader safety from the heal point through the horizon, on a
  run that hands over at or after the heal point (progress needed only on `[ready, heal]`). -/
  continuedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → S.schema.output cap = some g →
    ∀ i gst T, S.Holds
      (fun r => S.Handover K gst T r ∧ S.heal K cap i gst r ≤ T ∧
        S.prog X K cap i (S.ready K gst r) (S.heal K cap i gst r) r)
      (fun r => (S.trace r).ReadySafe (S.cDur K r) g (S.heal K cap i gst r))
  /-- Available and stable: transaction liveness from the heal point with the healed latency, on
  a run that hands over at or after the heal point, with progress from `ready` to the horizon. -/
  continuedLive : ∀ cap g, (cap = .available ∨ cap = .stable) → S.schema.output cap = some g →
    ∀ i gst T, S.Holds
      (fun r => S.Handover K gst T r ∧ S.heal K cap i gst r ≤ T ∧
        S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K cap i gst r) (S.lat K cap i r))
  /-- Non-vacuity, for at least five validators: at every delay (the FG delay within its bound),
  every GST `≥ 0` and every available or stable capability and index, a valid excuse-free run
  hands over at a `T` at or after the heal point, has at least fraction `β` compromised by a time
  `κ`, and exercises both claims after `κ`. -/
  realizable : 5 ≤ Fintype.card V → ∀ cap i (ΔAC ΔFG g : Time), (cap = .available ∨ cap = .stable) →
    1 < ΔAC → 1 < ΔFG → ΔFG ≤ (K.params.fgDelay : Time) * ΔAC → 0 ≤ g →
    ∃ r T κ, S.Valid r ∧ ¬ S.Excuse r ∧ (S.pt r).env.ΔAC = ΔAC ∧ (S.pt r).env.ΔFG = ΔFG ∧
      S.Handover K g T r ∧ S.heal K cap i g r ≤ T ∧
      S.prog X K cap i (S.ready K g r) (S.pt r).horizon r ∧
      K.params.β * Fintype.card V ≤ ((S.pt r).faultCount κ : ℚ) ∧
      (S.pt r).TxLiveActive (S.cDur K r) κ (S.lat K cap i r) ∧ SafeActive (S.cDur K r) κ (S.pt r)

end Consensus

end

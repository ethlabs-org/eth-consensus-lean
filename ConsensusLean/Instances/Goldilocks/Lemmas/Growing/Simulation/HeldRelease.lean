module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Release of held attestations: the abstract cores

A node may sign an FG attestation at a time its release schedule refuses publication; it then
holds the attestation and publishes every held one at the first awake poll whose time the
schedule allows. This file proves the two timing facts the late-release proofs need, for one
validator and one signed item, over abstract data:

* `release : Time → Bool`, the validator's release schedule, with *release liveness of gap `R`*:
  from every `t ≥ t₀` some `t'` with `t ≤ t' ≤ t + R·Δ` has `release t' = true`;
* `awake : Time → Prop`, the times at which the validator polls;
* `released : Time → Prop`, the times at which the item is published;
* `withheld : Time → Prop`, any property of the item that its publication ends, for instance
  that it is still in the node's `held` queue.

The held-queue semantics enter as one premise each. *Flush*: at an awake time `t ≥ s` that the
schedule allows, up to the bound `e + R·Δ` (the engine polls only within its horizon), an item
signed at `s` and not yet published in `[s, t)` is published at `t` (the first poll of an allowed
tick empties the queue, and a signing at an allowed time publishes at once). *Gone*: an item
published at some `r ∈ [s, t]` is not withheld at `t`.

Contents: `released_by_of_release_liveness`, the release bound measured from the signing time.

## Instantiation

Fix the setup `S`, the public configuration `pub = pubOf E`, a validator `y` and an attestation `a`
that `y` signs at trace index `k`, so `s := tr.time k`.

* `release := S.release pub y` (the `Setup.release` field), `R := A.releaseGap`, `Δ := P.Δ`
  (`= pub.ΔAC`) and `t₀ := 0`; `hlive` is `ReleaseGapAt P release R 0` at `y`, which
  `A.release_liveness` supplies (`ContractAssumptions`).
* `awake := tr.awake y`; the start `e := max s g` (the run's `eff (tr.time k)`), with
  `0 ≤ s ≤ e`. Healthy runs supply `hawake` from `y` honest
  at `e + R·Δ` and awake from `g` on (`HealthyRunAt`, `Interface.awake_to`).
* `released r := ReleasedFrom S rho (rho.key y) (attObj a) r`. `hflush` is the engine's held-queue
  invariant read at the first poll of tick `t`: `a` was signed at `s`, so it is either in the
  outbox at `s` (released in the batch at `s`) or in `State.held`, and `pollBatch` with
  `release (st.now) = true` releases every held attestation.
* `withheld t := a ∈ st.held` for the node's state `st` at tick `t`. `hgone` follows from the
  invariant that `held` holds own signings not yet released; if `a` can be signed more than once,
  instantiate `s` with its latest signing at or before `t`. A held attestation is not in the
  node's pool, so its own proposals cannot carry it before its release.

At these arguments `released_by_of_release_liveness` gives the simulation interface's release bound: an attestation signed at `k` is released at some `r` with
`tr.time k ≤ r ≤ max (tr.time k) g + R·Δ`. -/

namespace Consensus.Goldilocks.Simulation

variable {release : Time → Bool} {awake released : Time → Prop} {Δ s e t₀ : Time} {R : ℕ}

/-- Release by the gap bound: under release liveness of gap `R`, with the validator awake on
`[e, e + R·Δ]` for a start `e ≥ max s t₀`, the flush rule publishes an item signed at `s` at some
`r` with `s ≤ r ≤ e + R·Δ`. -/
theorem released_by_of_release_liveness
    (hlive : ∀ t, t₀ ≤ t → ∃ t', t ≤ t' ∧ t' ≤ t + (R : Time) * Δ ∧ release t' = true)
    (ht₀ : t₀ ≤ e) (hse : s ≤ e) (hawake : ∀ t, e ≤ t → t ≤ e + (R : Time) * Δ → awake t)
    (hflush : ∀ t, s ≤ t → t ≤ e + (R : Time) * Δ → awake t → release t = true →
      (∀ r, s ≤ r → r < t → ¬released r) → released t) :
    ∃ r, s ≤ r ∧ r ≤ e + (R : Time) * Δ ∧ released r := by
  obtain ⟨t', het, hte, hrel⟩ := hlive e ht₀
  by_cases hb : ∃ r, s ≤ r ∧ r < t' ∧ released r
  · obtain ⟨r, hsr, hrt, hr⟩ := hb
    exact ⟨r, hsr, hrt.le.trans hte, hr⟩
  · exact ⟨t', hse.trans het, hte, hflush t' (hse.trans het) hte (hawake t' het hte) hrel
      fun r hsr hrt hr => hb ⟨r, hsr, hrt, hr⟩⟩

end Consensus.Goldilocks.Simulation

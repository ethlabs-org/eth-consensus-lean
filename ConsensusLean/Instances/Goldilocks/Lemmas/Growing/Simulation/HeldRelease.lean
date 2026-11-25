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

Contents: `released_by_of_release_liveness` (the release bound measured from the signing time),
`not_withheld_of_release_liveness` (after that bound, the item is no longer withheld), and
`att_released_by`, the first one on a run trace.

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

The simulation interface's bound `att_released_by` is then `released_by_of_release_liveness` at
these arguments: an attestation signed at `k` is released at some `r` with
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

/-- Not withheld after the gap bound: under the premises of `released_by_of_release_liveness`, an
item signed at `s` is no longer withheld at any `t ≥ e + R·Δ`. At `e := s` this is the validator
awake on `[s, s + R·Δ]` and `s + R·Δ ≤ t`. -/
theorem not_withheld_of_release_liveness {withheld : Time → Prop} {t : Time}
    (hlive : ∀ t, t₀ ≤ t → ∃ t', t ≤ t' ∧ t' ≤ t + (R : Time) * Δ ∧ release t' = true)
    (ht₀ : t₀ ≤ e) (hse : s ≤ e) (hawake : ∀ t, e ≤ t → t ≤ e + (R : Time) * Δ → awake t)
    (hflush : ∀ t, s ≤ t → t ≤ e + (R : Time) * Δ → awake t → release t = true →
      (∀ r, s ≤ r → r < t → ¬released r) → released t)
    (hgone : ∀ r, s ≤ r → r ≤ t → released r → ¬withheld t)
    (ht : e + (R : Time) * Δ ≤ t) : ¬withheld t :=
  have ⟨r, hsr, hre, hr⟩ := released_by_of_release_liveness hlive ht₀ hse hawake hflush
  hgone r hsr (hre.trans ht) hr

/-- **`att_released_by`: an attestation is released by its release bound.** On a run trace `tr`
with time-indexed honest set `H` (antitone), a release schedule of gap `R` from `0`
(`ReleaseGapAt`), the healthy participation through `b` and the flush rule `hflush` (an honest
awake node whose schedule allows release at `t` releases every own signing not released since),
an attestation signed at `k` by `y` honest then is released at some `r` with
`time k ≤ r ≤ max (time k) g + R·Δ`, by `y` still honest at `r`. For `R ≠ 0` the signer must be
honest at that bound (`hyR`, the premise of `SyncOnAt.attestation`) and the bound within `b`;
for `R = 0` the release is at the signing itself. -/
theorem att_released_by {P : Params} {A : NodeAC P} (tr : RunTrace A)
    {H : Time → Set (Fin P.n)} {rel : Fin P.n → Time → Bool} {R : ℕ} {g b : Time}
    {released : Fin P.n → FG.Att P.n → Time → Prop}
    (hgap : ReleaseGapAt P rel R 0) (hanti : ∀ y s t, s ≤ t → y ∈ H t → y ∈ H s)
    (hawake : ∀ y t, max g 0 ≤ t → t ≤ b → y ∈ H t → tr.awake y t)
    (hsignAwake : ∀ y k a, y ∈ H (tr.time k) → tr.SignAt y k a → tr.awake y (tr.time k))
    (hflush : ∀ y k a t, tr.SignAt y k a → tr.time k ≤ t → y ∈ H t → tr.awake y t →
      rel y t = true → (∀ r, tr.time k ≤ r → r < t → ¬released y a r) → released y a t)
    {y : Fin P.n} {k : Nat} {a : FG.Att P.n} (h0 : 0 ≤ tr.time k) (hy : y ∈ H (tr.time k))
    (hs : tr.SignAt y k a) (hyR : R ≠ 0 → y ∈ H (max (tr.time k) g + (R : Time) * P.Δ))
    (hb : R ≠ 0 → max (tr.time k) g + (R : Time) * P.Δ ≤ b) :
    ∃ r, tr.time k ≤ r ∧ r ≤ max (tr.time k) g + (R : Time) * P.Δ ∧ released y a r ∧
      y ∈ H r := by
  have hRΔ : 0 ≤ (R : Time) * P.Δ := mul_nonneg (Nat.cast_nonneg R) P.hΔ.le
  have core : ∀ e, tr.time k ≤ e → e ≤ max (tr.time k) g →
      (∀ t, e ≤ t → t ≤ e + (R : Time) * P.Δ → y ∈ H t ∧ tr.awake y t) →
      ∃ r, tr.time k ≤ r ∧ r ≤ max (tr.time k) g + (R : Time) * P.Δ ∧ released y a r ∧
        y ∈ H r := by
    intro e hse hem haw
    obtain ⟨r, hsr, hre, hr⟩ := released_by_of_release_liveness (release := rel y)
      (awake := fun t => y ∈ H t ∧ tr.awake y t) (released := released y a) (hgap y)
      (h0.trans hse) hse haw fun t hst _ hat hrel hn => hflush y k a t hs hst hat.1 hat.2 hrel hn
    exact ⟨r, hsr, hre.trans (by linarith), hr,
      hanti y r _ hre (haw _ (le_add_of_nonneg_right hRΔ) le_rfl).1⟩
  by_cases hR : R = 0
  · subst hR
    refine core _ le_rfl (le_max_left _ _) fun t ht ht' => ?_
    have : t = tr.time k := le_antisymm (by simpa using ht') ht
    subst this
    exact ⟨hy, hsignAwake y k a hy hs⟩
  · refine core _ (le_max_left _ _) le_rfl fun t ht ht' => ?_
    have hyt := hanti y t _ ht' (hyR hR)
    exact ⟨hyt, hawake y t (max_le ((le_max_right _ _).trans ht)
      (h0.trans ((le_max_left _ _).trans ht))) (ht'.trans (hb hR)) hyt⟩

end Consensus.Goldilocks.Simulation

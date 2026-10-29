module
public import ConsensusLean.Spec.Shape.Run
public import ConsensusLean.Spec.Shape.ProgressFit

@[expose] public section

/-! # Witness activity (L2)

The definitions in the statement of `regimes_realizable` (moved from
`ConsensusLean/Proofs/RegimesRealizable/Main.lean`). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-! ## Witness activity

`regimes_realizable` returns `RealizableActive`, so these definitions are part
of its statement. -/

section Activity

variable (F : ShapeFamily O Info) (K : Contract ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The length of one window of the progress requirement of `cap` at `i` on
the grid at `Δ`, pattern span included (`0` for a bound on the validators
not ready). -/
def progLen (cap : Capability) (i : K.Idx) (E : Env V) : Time :=
  match K.progress cap i with
  | .recur ρ => (ρ.len : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ
  | .notReadyAtMost _ => 0

/-- The progress requirement of `cap` at `i` is active from `start`:
one whole window (with the pattern's span, for a recurrence) from
`max start 0` lies inside the horizon, so the requirement is not met
vacuously (`PatternRecurrence.exists_inside`; for a bound below the validator
count, `NotReadyOn.readyAt_nonempty`). -/
def ProgressActive (cap : Capability) (i : K.Idx) (start : Time) {E : Env V}
    (rho : Model.Run (compiled F) E) : Prop :=
  max start 0 + progLen F K cap i E ≤ rho.horizon

/-- Every window of the progress requirement of `cap` at `i` holds a bad
proposer slot on run `rho`: for a recurrence, every `gap` consecutive slots
contain a slot whose proposer selection is nonempty and entirely faulty (so
every time window `(t, t + gap·slot]`, `t ≥ 0`, holds one). A bound on the
validators not ready has no proposer slots: nothing is asked (its tolerant
indices, `m ≥ n`, hold on every point, whoever leads). -/
def BadProposerEvery (cap : Capability) (i : K.Idx) {E : Env V}
    (rho : Model.Run (compiled F) E) : Prop :=
  match K.progress cap i with
  | .recur ρ => ∀ a : Slot, ∃ s, a ≤ s ∧ s < a + (ρ.gap : Nat) ∧
      (rho.sel (ShapeRole.proposer s)).Nonempty ∧
      ∀ k ∈ rho.sel (ShapeRole.proposer s), rho.key k ∉ rho.honest
  | .notReadyAtMost _ => True

/-- L0 `Realizable` of the compiled system, with every sleepy and healthy
witness (stress included) also having an active progress window
(`ProgressActive`) from the start of its progress premise. -/
structure RealizableActive (V : Type) [Fintype V] [DecidableEq V] : Prop where
  sleepy : ∀ cap i (Δ : Time), 0 < Δ → ∃ r, (Sys F V).Witness r ∧ ((Sys F V).pt r).env.Δ = Δ ∧
    (Sys F V).SleepyLive (shapeProgress F V) K cap i r ∧ ProgressActive F K cap i 0 r.2
  healthy : ∀ cap i (Δ g : Time), 0 < Δ → 0 ≤ g → ∃ r, (Sys F V).Witness r ∧
    ((Sys F V).pt r).env.Δ = Δ ∧ (Sys F V).HealthyLive (shapeProgress F V) K cap i g r ∧
    SafeActive ((Sys F V).cDur K r) ((Sys F V).heal K cap i g r) ((Sys F V).pt r) ∧
    ProgressActive F K cap i ((Sys F V).ready K g r) r.2
  sleepyStress : ∀ cap, (cap = .available ∨ cap = .stable) → (O.output cap).isSome →
    ∀ Δ : Time, 0 < Δ → ∃ i r, (Sys F V).Witness r ∧ ((Sys F V).pt r).env.Δ = Δ ∧
      (Sys F V).SleepyLive (shapeProgress F V) K cap i r ∧
      ((Sys F V).pt r).AwakeAtMost 2 ∧ ProgressActive F K cap i 0 r.2
  outage : ∀ (Δ : Time) (k : Nat), 0 < Δ → ∃ r T b₀ b₁, (Sys F V).Witness r ∧
    ((Sys F V).pt r).env.Δ = Δ ∧ (Sys F V).Outage K T b₀ b₁ r ∧
    OutageActive ((Sys F V).cDur K r) T b₀ b₁ ((Sys F V).pt r) ∧ (k : Time) * Δ ≤ T
  /-- Bad proposer slots: every provided output is live, at some index, on a
  healthy witness from every GST whose every progress window holds a faulty
  proposer slot (`BadProposerEvery`). A requirement that needs an honest
  ready proposer in every slot (e.g. `recur ⟨single, 1⟩`) fails here. Not
  part of L0 `Realizable` (L0 has no proposers). -/
  badProposer : ∀ cap, (O.output cap).isSome → ∀ (Δ g : Time), 0 < Δ → 0 ≤ g →
    ∃ i r, (Sys F V).Witness r ∧ ((Sys F V).pt r).env.Δ = Δ ∧
      (Sys F V).HealthyLive (shapeProgress F V) K cap i g r ∧
      ProgressActive F K cap i ((Sys F V).ready K g r) r.2 ∧ BadProposerEvery F K cap i r.2

end Activity

end Consensus.Shape

end

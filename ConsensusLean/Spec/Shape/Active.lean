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

variable (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The length of one window of the progress requirement of `cap` at `i` on
the instance's grid, pattern span included (`0` for a bound on the validators
not ready). -/
def progLen (cap : Capability) (i : K.Idx) (E : Env V) : Time :=
  match K.progress cap i with
  | .recur ρ => (ρ.len : Time) * (F (pubOf E)).skel.grid.slotLen
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
contain a slot whose proposer selection is nonempty and entirely faulty from
the start (so
every time window `(t, t + gap·slot]`, `t ≥ 0`, holds one). A bound on the
validators not ready has no proposer slots: nothing is asked (its tolerant
indices, `m ≥ n`, hold on every point, whoever leads). -/
def BadProposerEvery (cap : Capability) (i : K.Idx) {E : Env V}
    (rho : Model.Run (compiled F) E) : Prop :=
  match K.progress cap i with
  | .recur ρ => ∀ a : Slot, ∃ s, a ≤ s ∧ s < a + (ρ.gap : Nat) ∧
      (rho.sel (ShapeRole.proposer s)).Nonempty ∧
      ∀ k ∈ rho.sel (ShapeRole.proposer s), rho.key k ∈ rho.faultyAt 0
  | .notReadyAtMost _ => True

/-- L0 `Realizable` of the compiled system, with every sleepy and healthy
witness (stress included) also having an active progress window
(`ProgressActive`) from the start of its progress premise. The ordinary regime
witnesses (`sleepy`, `healthy`, `outage`) show that the regimes can occur and do
not depend on which outputs are provided: the sleepy and healthy witnesses are
asked at every capability and index, provided or not, and the outage witness
names no output; only `sleepyStress` and `badProposer` are gated by the provided
outputs. -/
structure RealizableActive (V : Type) [Fintype V] [DecidableEq V] : Prop where
  sleepy : ∀ cap i (ΔAC ΔFG : Time), 1 < ΔAC → 1 < ΔFG → ∃ r, (Sys F V).WitnessAt ΔAC ΔFG r ∧
    (Sys F V).SleepyLive (shapeProgress F V) K cap i r ∧ ProgressActive F K cap i 0 r.2
  healthy : ∀ cap i (ΔAC ΔFG g : Time), 1 < ΔAC → 1 < ΔFG → ΔFG ≤ (K.params.fgDelay : Time) * ΔAC →
    0 ≤ g → ∃ r, (Sys F V).WitnessAt ΔAC ΔFG r ∧
    (Sys F V).HealthyLive (shapeProgress F V) K cap i g r ∧
    SafeActive ((Sys F V).cDur K r) ((Sys F V).heal K cap i g r) ((Sys F V).pt r) ∧
    ProgressActive F K cap i ((Sys F V).ready K g r) r.2
  sleepyStress : ∀ cap, (cap = .available ∨ cap = .stable) → (O.output cap).isSome →
    ∃ i, ∀ ΔAC ΔFG : Time, 1 < ΔAC → 1 < ΔFG → ∃ r, (Sys F V).WitnessAt ΔAC ΔFG r ∧
      (Sys F V).SleepyLive (shapeProgress F V) K cap i r ∧
      ((Sys F V).pt r).AwakeAtMost 2 ∧ ProgressActive F K cap i 0 r.2
  outage : ∀ (ΔAC ΔFG : Time) (k : Nat), 1 < ΔAC → 1 < ΔFG →
    ∃ r T b₀ b₁, (Sys F V).WitnessAt ΔAC ΔFG r ∧
    (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ r ∧
    OutageActive ((Sys F V).cDur K r) ((K.params.recovery : Time) * ΔAC) T b₀ b₁
      ((Sys F V).pt r) ∧ (k : Time) * ΔAC ≤ T
  /-- Bad proposer slots: every provided output is live, at some index, on a
  healthy witness from every GST whose every progress window holds a faulty
  proposer slot (`BadProposerEvery`). A requirement that needs an honest
  ready proposer in every slot (e.g. `recur ⟨single, 1⟩`) fails here. Not
  part of L0 `Realizable` (L0 has no proposers). -/
  badProposer : ∀ cap, (O.output cap).isSome → ∀ (ΔAC ΔFG g : Time), 1 < ΔAC → 1 < ΔFG →
    ΔFG ≤ (K.params.fgDelay : Time) * ΔAC → 0 ≤ g →
    ∃ i r, (Sys F V).WitnessAt ΔAC ΔFG r ∧
      (Sys F V).HealthyLive (shapeProgress F V) K cap i g r ∧
      ProgressActive F K cap i ((Sys F V).ready K g r) r.2 ∧ BadProposerEvery F K cap i r.2
  /-- Growth, sleepy (L0 `Realizable.sleepyGrowth`, with an active progress
  window). -/
  sleepyGrowth : ∀ cap i (ΔAC ΔFG : Time), 1 < ΔAC → 1 < ΔFG → ∃ r, (Sys F V).Valid r ∧
    ¬ (Sys F V).Excuse r ∧ ((Sys F V).pt r).env.ΔAC = ΔAC ∧ ((Sys F V).pt r).env.ΔFG = ΔFG ∧
    (Sys F V).SleepyLive (shapeProgress F V) K cap i r ∧
    GrowthActive ((Sys F V).cDur K r) 0 ((Sys F V).lat K cap i r) ((Sys F V).pt r) ∧
    ProgressActive F K cap i 0 r.2
  /-- Growth, healthy (L0 `Realizable.healthyGrowth`, with an active progress
  window). -/
  healthyGrowth : ∀ cap i (ΔAC ΔFG g : Time), 1 < ΔAC → 1 < ΔFG →
    ΔFG ≤ (K.params.fgDelay : Time) * ΔAC → 0 ≤ g → ∃ r, (Sys F V).Valid r ∧
    ¬ (Sys F V).Excuse r ∧ ((Sys F V).pt r).env.ΔAC = ΔAC ∧ ((Sys F V).pt r).env.ΔFG = ΔFG ∧
    (Sys F V).HealthyLive (shapeProgress F V) K cap i g r ∧
    GrowthActive ((Sys F V).cDur K r) ((Sys F V).heal K cap i g r) ((Sys F V).lat K cap i r)
      ((Sys F V).pt r) ∧
    ProgressActive F K cap i ((Sys F V).ready K g r) r.2
  /-- Growth, outage (L0 `Realizable.outageGrowth`). -/
  outageGrowth : ∀ (ΔAC ΔFG : Time) (k : Nat), 1 < ΔAC → 1 < ΔFG →
    ∃ r T b₀ b₁ u κ, (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧
    ((Sys F V).pt r).env.ΔAC = ΔAC ∧ ((Sys F V).pt r).env.ΔFG = ΔFG ∧
    (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ r ∧
    OutageActive ((Sys F V).cDur K r) ((K.params.recovery : Time) * ΔAC) T b₀ b₁
      ((Sys F V).pt r) ∧ (k : Time) * ΔAC ≤ T ∧ ((Sys F V).pt r).Ready ((Sys F V).cDur K r) u T ∧
    T < κ ∧ u ∈ ((Sys F V).pt r).faultyAt κ ∧ ∃ w t, (Sys F V).recoveryAt K b₁ r ≤ t ∧
      t ≤ ((Sys F V).pt r).horizon ∧ κ ≤ t ∧ ((Sys F V).pt r).Ready ((Sys F V).cDur K r) w t

end Activity

end Consensus.Shape

end

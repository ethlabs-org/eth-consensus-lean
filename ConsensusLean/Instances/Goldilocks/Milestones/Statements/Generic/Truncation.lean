module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing

@[expose] public section

/-! # Generic finite-horizon healing contracts

Every implication is UNPROVED. These types supply no theorem evidence.
-/

namespace Consensus.Goldilocks.Generic

open SA (gbar)
open Healing (cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg}

/-- Honest restarts are bounded only through the finite horizon. -/
def NoRestartUpTo (tr : RunTrace A) (H : Time → Set (Fin P.n)) (t b : Time) : Prop :=
  ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ t

/-- Warm proposal supply, with the original non-strict signing cutoff, for signers honest at
their signing and at `c_z`. -/
structure DrainOutputs (O : ACHealing A sg runs) (tr : RunTrace A) (proposer : Nat → Fin P.n)
    (H : Time → Set (Fin P.n)) (g : Time) (G Ld : Nat) (b : Time) : Prop where
  warm : ∀ {s₀ N floor : Nat} {kindJ : Prop} {J : A.Blk},
    SlotWindow tr H s₀ N floor kindJ J →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ + Ld ≤ N → P.slotTime N + 2 * P.Δ ≤ b →
    (∀ v k att, v ∈ H (max (cutZ P g) (tr.time k)) → tr.SignAt v k att →
      tr.time k ≤ P.slotTime N + 2 * P.Δ → att.h ≤ HZ tr H g) →
    ProposalGap tr H proposer G s₀ N →
    ∃ u, (s₀ ≤ u ∧ s₀ + O.warmup ≤ u) ∧ u ≤ s₀ + Ld ∧
      ∃ z kB B, z ∈ H (P.slotTime u + P.Δ) ∧ z = proposer u ∧
        tr.ProposesAt z kB B ∧ B.slot = u ∧
          HZ tr H g ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + 1

/-- UNPROVED old-premise rise contract, retaining the timeout and strict no-advance cutoff. -/
def rise_reset_rounds_at (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b T : Time}
    {s₀ N G floor : Nat} {kindJ : Prop} {J : A.Blk},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindow tr H s₀ N floor kindJ J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → O.follow ≤ P.δt → 1 ≤ G →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    ProposalGap tr H proposer G s₀ N → P.slotTime N + 2 * P.Δ ≤ b →
    (H b).Nonempty → T ≤ b → NoAdvance tr H g T →
    ∀ (r : Nat) {u : Nat} {z : Fin P.n} {kB : Nat} {B : A.Blk},
      s₀ ≤ u → s₀ + O.warmup ≤ u → u + r * (P.δt + G - 1) + 1 ≤ N →
      P.slotTime (u + r * (P.δt + G - 1) + 1) + 2 * P.Δ ≤ T →
      z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
      HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + r →
      ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (u + r * (P.δt + G - 1) + 1) + 2 * P.Δ

/-- UNPROVED whole-run endpoint, with the public four-delay grid assumption explicit. -/
def exists_reset_of_drain_rounds_noRestartAfter_at (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b r : Time} {G Ld : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (H b).Nonempty → O.follow ≤ P.δt → 6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time) →
    0 ≤ r → gbar g ≤ r → 1 ≤ G → cutZ P g + P.Δ + 1 ≤ r + 4 * P.Δ →
    resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld ≤ b →
    (∀ s₀ N : Nat, r + 4 * P.Δ ≤ P.slotTime s₀ →
      P.slotTime N + 2 * P.Δ < resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld →
      ProposalGap tr H proposer G s₀ N) → DrainOutputs A sg O tr proposer H g G Ld b →
    ∃ a, IsReset tr H g a ∧ a ≤ resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld

/-- UNPROVED finite-horizon endpoint; restarts are constrained only up to b. -/
def exists_reset_of_drain_rounds_awake_at (O : ACHealing A sg runs) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b r : Time} {G Ld : Nat},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    CatchRun tr H g (2 * P.Δ) → NoRestartUpTo A tr H (gbar g) b →
    (H b).Nonempty → O.follow ≤ P.δt → 6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time) →
    0 ≤ r → gbar g ≤ r → 1 ≤ G → cutZ P g + P.Δ + 1 ≤ r + 4 * P.Δ →
    resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld ≤ b →
    (∀ s₀ N : Nat, r + 4 * P.Δ ≤ P.slotTime s₀ →
      P.slotTime N + 2 * P.Δ < resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld →
      ProposalGap tr H proposer G s₀ N) → DrainOutputs A sg O tr proposer H g G Ld b →
    ∃ a, IsReset tr H g a ∧ a ≤ resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld

end Consensus.Goldilocks.Generic

end

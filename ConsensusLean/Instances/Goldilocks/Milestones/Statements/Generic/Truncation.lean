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

/-- Honest restarts are bounded only through the finite horizon. -/
def NoRestartUpTo (tr : RunTrace A) (H : Time → Set (Fin P.n)) (t b : Time) : Prop :=
  ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ t

/-- Warm proposal supply, with the original non-strict signing cutoff. -/
structure DrainOutputs (O : ACHealing A sg) (tr : RunTrace A) (proposer : Nat → Fin P.n)
    (H : Time → Set (Fin P.n)) (g : Time) (G Ld : Nat) (b : Time) : Prop where
  warm : ∀ {s₀ N floor : Nat} {kindJ : Prop} {J : A.Blk},
    SlotWindow tr H s₀ N floor kindJ J →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → s₀ + Ld ≤ N → P.slotTime N + 2 * P.Δ ≤ b →
    (∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k ≤ P.slotTime N + 2 * P.Δ → att.h ≤ HZ tr H g) →
    ProposalGap tr H proposer G s₀ N →
    ∃ u, (s₀ ≤ u ∧ O.Warm tr H s₀ u) ∧ u ≤ s₀ + Ld ∧
      ∃ z kB B, z ∈ H (P.slotTime u + P.Δ) ∧ z = proposer u ∧
        tr.ProposesAt z kB B ∧ B.slot = u ∧
          HZ tr H g ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + 1

/-- UNPROVED service transfer; the service horizon need not equal the truncation time. -/
def resetService_truncH : Prop :=
  ∀ (tr : RunTrace A) H g ΔF b' b,
    Service tr H g ΔF b' → Service tr (truncH H b) g ΔF b'

/-- UNPROVED catch-up transfer. -/
def catchRun_truncH : Prop :=
  ∀ (tr : RunTrace A) H g κ b, CatchRun tr H g κ → CatchRun tr (truncH H b) g κ

/-- UNPROVED honest-block inclusion under truncation. -/
def honestBlocksAt_truncH_subset : Prop :=
  ∀ (tr : RunTrace A) H b, tr.HonestBlocksAt (truncH H b) ⊆ tr.HonestBlocksAt H

/-- UNPROVED snapshot identity when the snapshot time survives. -/
def HZ_truncH : Prop :=
  ∀ (tr : RunTrace A) H g b, cutZ P g ≤ b → HZ tr (truncH H b) g = HZ tr H g

/-- UNPROVED proposal-gap transfer with the final vote deadline inside the horizon. -/
def proposalGap_truncH : Prop :=
  ∀ (tr : RunTrace A) H proposer G s₀ N b,
    ProposalGap tr H proposer G s₀ N → P.slotTime N + P.Δ ≤ b →
    ProposalGap tr (truncH H b) proposer G s₀ N

/-- UNPROVED proposal-gap projection to the original honest sets. -/
def proposalGap_of_truncH : Prop :=
  ∀ (tr : RunTrace A) H proposer G s₀ N b,
    ProposalGap tr (truncH H b) proposer G s₀ N → ProposalGap tr H proposer G s₀ N

/-- UNPROVED frame-window projection, preserving all reads up to its upper endpoint. -/
def frameWindow_of_truncH : Prop :=
  ∀ (tr : RunTrace A) H lo hi b floor kindJ J,
    FrameWindow tr (truncH H b) lo hi floor kindJ J → hi ≤ b →
    FrameWindow tr H lo hi floor kindJ J

/-- UNPROVED warm-output transfer, using run and warmth truncation fields of the protocol. -/
def drainOutputs_truncH (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g b : Time} {G Ld : Nat},
    O.Run proposer dg H tr → DrainOutputs A sg O tr proposer H g G Ld b → cutZ P g ≤ b →
    DrainOutputs A sg O tr proposer (truncH H b) g G Ld b

/-- UNPROVED reset projection, retaining the minimality condition at later honest signings. -/
def isReset_of_truncH : Prop :=
  ∀ (tr : RunTrace A) H g a b, cutZ P g ≤ b →
    IsReset tr (truncH H b) g a → a ≤ b → IsReset tr H g a

/-- UNPROVED original proposal-membership leaf. -/
def proposal_mem_at : Prop :=
  ∀ {proposer dg H tr} {p : Fin P.n} {k : Nat} {B : A.Blk},
    Growing.LocalRun proposer dg H sg tr → Compose.NoCollRun dg tr →
    p ∈ H (tr.time k) → tr.ProposesAt p k B → B ∈ (tr.state p (k + 1)).fg.tree

/-- UNPROVED old-premise rise contract, retaining the timeout and strict no-advance cutoff. -/
def rise_reset_rounds_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF b T : Time} {s₀ N G floor : Nat} {kindJ : Prop} {J : A.Blk},
    SlotWindow tr H s₀ N floor kindJ J →
    O.Run proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → 3 ≤ P.δt → 1 ≤ G →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    ProposalGap tr H proposer G s₀ N → P.slotTime N + 2 * P.Δ ≤ b →
    (H b).Nonempty → T ≤ b → NoAdvance tr H g T →
    ∀ (r : Nat) {u : Nat} {z : Fin P.n} {kB : Nat} {B : A.Blk},
      s₀ ≤ u → O.Warm tr H s₀ u → u + r * (P.δt + G - 1) + 1 ≤ N →
      P.slotTime (u + r * (P.δt + G - 1) + 1) + 2 * P.Δ ≤ T →
      z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
      HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + r →
      ∃ a, IsReset tr H g a ∧ a ≤ P.slotTime (u + r * (P.δt + G - 1) + 1) + 2 * P.Δ

/-- UNPROVED whole-run endpoint, with the public four-delay grid assumption explicit. -/
def exists_reset_of_drain_rounds_noRestartAfter_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF b r : Time} {G Ld : Nat},
    (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
    O.Run proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (H b).Nonempty → 3 ≤ P.δt → 6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time) →
    0 ≤ r → gbar g ≤ r → 1 ≤ G → cutZ P g + P.Δ + 1 ≤ r + 4 * P.Δ →
    resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld ≤ b →
    (∀ s₀ N : Nat, r + 4 * P.Δ ≤ P.slotTime s₀ →
      P.slotTime N + 2 * P.Δ < resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld →
      ProposalGap tr H proposer G s₀ N) → DrainOutputs A sg O tr proposer H g G Ld b →
    ∃ a, IsReset tr H g a ∧ a ≤ resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld

/-- UNPROVED finite-horizon endpoint; restarts are constrained only up to b. -/
def exists_reset_of_drain_rounds_awake_at (O : ACHealing A sg) : Prop :=
  ∀ {proposer dg H tr} {g ΔF b r : Time} {G Ld : Nat},
    (∀ s : Nat, P.slotTime s = (s : Time) * (4 * P.Δ)) →
    O.Run proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) → Service tr H g ΔF b →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    CatchRun tr H g (2 * P.Δ) → NoRestartUpTo A tr H (gbar g) b →
    (H b).Nonempty → 3 ≤ P.δt → 6 * P.Δ + ΔF ≤ 4 * P.Δ * (P.δt : Time) →
    0 ≤ r → gbar g ≤ r → 1 ≤ G → cutZ P g + P.Δ + 1 ≤ r + 4 * P.Δ →
    resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld ≤ b →
    (∀ s₀ N : Nat, r + 4 * P.Δ ≤ P.slotTime s₀ →
      P.slotTime N + 2 * P.Δ < resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld →
      ProposalGap tr H proposer G s₀ N) → DrainOutputs A sg O tr proposer H g G Ld b →
    ∃ a, IsReset tr H g a ∧ a ≤ resetBoundRounds r P.Δ (2 * P.Δ) P.δt G Ld

end Consensus.Goldilocks.Generic

end

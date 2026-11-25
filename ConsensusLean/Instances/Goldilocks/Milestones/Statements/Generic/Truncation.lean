module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Healing

@[expose] public section

/-! # Generic finite-horizon healing contracts

These types supply no theorem evidence. Each implication is proved over any healing supplier by
the theorem its docstring names.
-/

namespace Consensus.Goldilocks.Generic

open AC (gbar)
open Healing (FirstCutAfter cutZ)
open Healing.Growing (HZ IsReset CatchRun NoRestartAfter)

variable {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
variable {runs : ACRun A sg} {hold : Time}

/-- Honest restarts are bounded only through the finite horizon. -/
def NoRestartUpTo (tr : RunTrace A) (H : Time → Set (Fin P.n)) (t b : Time) : Prop :=
  ∀ y k, y ∈ H (tr.time k) → tr.RestartAt y k → tr.time k ≤ b → tr.time k ≤ t

/-- Old-premise rise contract, retaining the timeout and strict no-advance cutoff. Proved over any
supplier by `rise_reset_rounds_at_of` (Lemmas/Generic/HealingEdges). -/
def rise_reset_rounds_at (O : ACHealing A sg runs hold) : Prop :=
  ∀ {cm proposer dg H tr} {βK : ℚ} {g ΔF b T : Time}
    {s₀ N Gp floor : Nat} {kindJ : Prop} {J : A.Blk},
    βK ≤ 1 / 2 → CommitteeFaultsUpTo βK cm H g b →
    SlotWindowWithin tr H O.reportDelay s₀ N floor kindJ J →
    runs.Run cm proposer dg H tr → Compose.NoCollRun dg tr → Service tr H g ΔF b hold →
    (∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t) →
    (∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ P.n - 1) →
    CatchRun tr H g (2 * P.Δ) → NoRestartAfter tr H (gbar g) →
    (∀ s, P.slotTime s + 4 * P.Δ ≤ P.slotTime (s + 1)) →
    (∀ s, shiftDelay P O.reportDelay (P.slotTime (s + 1) + 2 * P.Δ) + ΔF ≤
      P.slotTime (s + P.δt)) →
    (∃ k, FirstCutAfter tr k (cutZ P g) ∧ tr.time k ≤ b) →
    gbar g + 4 * P.Δ ≤ P.slotTime s₀ → O.follow ≤ P.δt → 1 ≤ Gp →
    (∀ s, P.slotTime s + 6 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)) →
    ProposalGap tr H proposer Gp s₀ N → shiftDelay P O.reportDelay (P.slotTime N + 2 * P.Δ) ≤ b →
    (H b).Nonempty → T ≤ b → NoAdvance tr H g T →
    ∀ (r : Nat) {u : Nat} {z : Fin P.n} {kB : Nat} {B : A.Blk},
      s₀ ≤ u → s₀ + O.warmup ≤ u → u + r * (P.δt + Gp - 1) + 1 ≤ N →
      shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ) ≤ T →
      z ∈ H (P.slotTime u + P.Δ) → z = proposer u → tr.ProposesAt z kB B → B.slot = u →
      HZ tr H g + 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h + r →
      ∃ a, IsReset tr H g a ∧
        a ≤ shiftDelay P O.reportDelay (P.slotTime (u + r * (P.δt + Gp - 1) + 1) + 2 * P.Δ)

end Consensus.Goldilocks.Generic

end

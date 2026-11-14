module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.B2
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # Relay from independently honest held-state observations

The source is observed at a time bounding its preceding events; it need not remain honest
at the receiver's observation. Relay debts survive compromise of the sender.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The reset service of a Goldilocks run is the generic service (`Generic.Service`), field for
field. -/
theorem ResetService.toService {g ΔF b : Time} (h : ResetService tr H g ΔF b) :
    Generic.Service tr H g ΔF b :=
  ⟨h.deltaF, h.message, h.block, h.relay, h.signedRow⟩

/-- Relay and catch-up carry a held block to a receiver whose height has not passed it. -/
theorem held_of_relay_le_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ τ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {x z : Fin sp.n} {i m : Nat} (hτ0 : 0 ≤ τ) (hx : x ∈ H τ)
    (hz : z ∈ H (tr.time m))
    (hf : (H (max τ (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state x i).fg.tree)
    (hh : (tr.state z m).fg.hmax ≤ ((tr.state x i).fg.σ B.root).h)
    (hτ : ∀ k < i, tr.time k ≤ τ)
    (hcall : ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max τ g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : B ∈ (tr.state z m).fg.tree :=
  Generic.held_of_relay_le_at_from hrun.toLocalRun hnc hsvc.toService hcatch hτ0 hx hz hf hB hh
    hτ hcall hcm

/-- After its relay obligation is paid, a receiver has at least the snapshot height. -/
theorem HZ_le_hmax_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b κ : Time}
    (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    (hH : (H (cutZ sp.toParams g)).Nonempty)
    (hsnap : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {z : Fin sp.n} {m : Nat} (hz : z ∈ H (tr.time m))
    (hf : (H (max (cutZ sp.toParams g) (tr.time m)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.n)
    (hcall : ∃ j < m, tr.IsCall z j ∧
      tr.deadline z j (max (cutZ sp.toParams g) g) sp.Δ ≤ tr.time j)
    (hcm : gbar g + κ ≤ tr.time m) : HZ tr H g ≤ (tr.state z m).fg.hmax :=
  Generic.HZ_le_hmax_at_from hrun.toLocalRun hnc hsvc.toService hcatch hH hsnap hz hf hcall hcm

end Consensus.Goldilocks.Healing.Growing

end

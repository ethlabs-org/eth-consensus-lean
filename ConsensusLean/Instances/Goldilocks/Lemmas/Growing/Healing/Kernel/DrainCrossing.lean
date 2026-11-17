module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # Row crossing with independently honest observations

The proposal's store is read at its own cut. Historical source states are transported by
replay agreement, and the quorum is counted at consumption, not at signing.
-/

namespace Consensus.Goldilocks.Healing.Growing

namespace KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Delivered historical rows cross one height; honesty is read separately at every cut
(`Generic.round_cross_at_from` at the Goldilocks requirements from the run's starts). -/
theorem round_cross_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b v : Time}
    (hsvc : ResetService tr H g ΔF b) (hnr : NoRestartAfter tr H (gbar g))
    {P D X : SA.Blk sp.n (List (FG.Att sp.n))} (hPH : P ∈ tr.HonestBlocksAt H)
    (hPD : Anc (tr.HonestBlocksAt H) P D) (hpar : X.parent = some D.root)
    {p : Fin sp.n} {kX : Nat} (hp : p ∈ H (tr.time kX))
    (hX : tr.ProposesAt p kX X) (hf : 3 * (H (tr.time kX))ᶜ.ncard ≤ sp.n - 1)
    (hv : gbar g ≤ v) (hvx : v + ΔF ≤ tr.time kX) (hkb : tr.time kX ≤ b)
    (hage : P.slot + sp.toParams.fg.δt ≤ X.slot)
    (hrow : ∀ y ∈ H (tr.time kX),
      (∃ w c, w ∈ H (tr.time c) ∧ P ∈ (tr.state w c).fg.tree ∧
        ∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧
          tr.time k ≤ v ∧ att.h = ((tr.state w c).fg.σ P.root).h ∧
          att.T = ((tr.state w c).fg.σ P.root).Th) ∨
      ∃ R, Anc (tr.HonestBlocksAt H) R D ∧ ∃ w c, w ∈ H (tr.time c) ∧
        P ∈ (tr.state w c).fg.tree ∧ R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ R.root).h) :
    P ∈ (tr.state p (kX + 1)).fg.tree ∧ X ∈ (tr.state p (kX + 1)).fg.tree ∧
      ((tr.state p (kX + 1)).fg.σ P.root).h + 1 ≤
        ((tr.state p (kX + 1)).fg.σ X.root).h :=
  Generic.round_cross_at_from hrun.toLocalRun
    (fun y => Compose.requirements_from sp ro (hrun.vstart y)) hrun.genesis_root_ok hnc
    hsvc.signedRow hnr hPH hPD hpar hp hX hf hv hvx hkb hage hrow

end KernelProof

end Consensus.Goldilocks.Healing.Growing

end

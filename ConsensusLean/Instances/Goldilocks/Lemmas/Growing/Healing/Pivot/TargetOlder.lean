module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources

public section

/-! # Comparing a supported target with an older high origin

The supporter is honest at its vote, not at the origin's write or at a later read.
The high-origin vote guarantee remains the explicit kernel boundary.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- An own-cut honest supporter compares its target with an older bounded origin. -/
theorem target_compatible_older_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {r m q l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hrb : tr.time r ≤ b)
    (hz : z ∈ H (tr.time q)) (hv : SA.VoteAt tr.projAC z q e)
    (hqb : tr.time q ≤ b) (hs : e.msg.slot = l) (hml : m < l)
    (hB : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨HO, hHO, hOr, hOO⟩ :=
    hp.high_origin_votes_before_at q hqb x r m O ho hrb z ell e hz hc (by omega)
  obtain ⟨HB, hHB, hBr, hBB⟩ := hB
  have hcoh := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain rfl : HO = HB := hcoh.1 hHO hHB (hOr.trans hBr.symm)
  exact SA.anc_total hcoh hBB hOO

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end

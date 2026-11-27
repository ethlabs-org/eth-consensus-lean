module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources

public section

/-! # Comparing a supported target with an older high origin

The supporter is honest at its vote, not at the origin's write or at a later read.
The high-origin vote guarantee remains the explicit kernel boundary.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- An own-cut honest supporter compares its target with an older bounded origin. -/
theorem target_compatible_older_origin_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x z : Fin sp.n} {r m q l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    {e : AC.Em sp (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hrb : tr.time r ≤ b)
    (hz : z ∈ H (tr.time q)) (hv : AC.VoteAt tr.projAC z q e)
    (hqb : tr.time q ≤ b) (hs : e.msg.slot = l) (hml : m < l)
    (hB : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨HO, hHO, hOr, hOO⟩ :=
    hp.high_origin_votes_before_at q hqb x r m O ho hrb z ell e hz hc (by omega)
  obtain ⟨HB, hHB, hBr, hBB⟩ := hB
  have hcoh := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain rfl : HO = HB := hcoh.1 hHO hHB (hOr.trans hBr.symm)
  exact AC.anc_total hcoh hBB hOO

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end

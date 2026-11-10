module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.CountedSupporters

public section

/-! # Counted result supporters at a later independently honest vote -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- Carrying a result carries support for each ancestor of that result. -/
theorem counted_ancestor_supporters (hrun : ACRun proposer tr H U)
    {X y : Fin sp.n} {i₀ i s : Nat} (hX : X ∈ H (tr.time i₀)) (hy : y ∈ H (tr.time i))
    {B C : Blk sp.n FGP} {ℓX ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hcX : tr.CallAt X i₀ ℓX) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hBC : Anc U B C)
    (hcarry : CarryAt tr U y i e s (fastCounted sp (tr.state X i₀) ℓX.frame s C))
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame s C, v.val = w} ⊆
      supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B :=
  carried_counted_supporters hrun hX hy hcX hc hs hBC hcarry hviab hd

end Consensus.Goldilocks.SA.Growing

end

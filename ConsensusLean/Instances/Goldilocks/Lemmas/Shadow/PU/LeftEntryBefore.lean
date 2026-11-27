module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry

public section

/-! # Shadow P-U: left-entry provenance before the cut

`ResetPremisesUpTo.left_entry_origin_or_covered_before_at` over the shadow run: the shared proof
over the reset core (`ResetRunCore.left_entry_origin_or_covered_before_at`, `Clean/LeftEntry`)
at `ResetPremisesUpTo'.toCore`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {g ΔF a b hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- **Left-entry provenance, with the cover read before the cut**, over the shadow run
(`ResetPremisesUpTo.left_entry_origin_or_covered_before_at`). -/
theorem ResetPremisesUpTo'.left_entry_origin_or_covered_before_at'
    (hp : ResetPremisesUpTo' tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state y k).fg.tree) (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v d, v ∈ H t ∧ d < k ∧
      tr.SignAt v d att ∧ att.T = E.root ∧
        ((∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ Anc (tr.HonestBlocksAt H) E O) ∨
          (v ∈ H (max (cutZ sp.toParams g) t) ∧ CoveredBefore tr H g a b (sp.slot t) k E)) :=
  hp.toCore.left_entry_origin_or_covered_before_at ht hle hy htb hE hET hEh hEC hlt

end Consensus.Goldilocks.Healing.Growing

end

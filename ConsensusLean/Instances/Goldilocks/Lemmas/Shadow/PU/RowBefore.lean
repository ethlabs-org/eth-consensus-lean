module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry

public section

/-! # Shadow signed rows covered before their signing -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {g : Time}

/-- The signed row's healed member was written before the shadow signing. -/
theorem signed_row_lock_member_before_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧ ∃ r < d, ∃ s C D,
      HealedMemberBefore tr H g a b C s d ∧
      Anc (tr.HonestBlocksAt H) E C ∧ Anc (tr.HonestBlocksAt H) C D ∧ v ∈ H (tr.time r) ∧
      ((∃ CV, AC.FastLockAt tr.projAC v r s D CV) ∨ AC.SlowLockAt tr.projAC v r s D) :=
  signed_row_lock_member_before_at_core hrun.toCore hnc hvz hs hh hsnap hc hdb

/-- The shadow signed row is covered by a member written before its signing. -/
theorem signed_row_covered_before_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧
      CoveredBefore tr H g a b (sp.slot (tr.time d)) d E :=
  signed_row_covered_before_at_core hrun.toCore hnc hvz hs hh hsnap hc hdb

end Consensus.Goldilocks.Healing.Growing.Outcome

end

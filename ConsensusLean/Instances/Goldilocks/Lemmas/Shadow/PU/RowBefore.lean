module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry

public section

/-! # Shadow signed rows covered before their signing -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp} {g : Time}

/-- The signed row's healed member was written before the shadow signing. -/
theorem signed_row_lock_member_before_at'
    {ini : Fin sp.n → (goldilocksNode' sp).State}
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
    {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d))) (hs : tr.SignAt v d att)
    (hh : HZ tr H g + 1 ≤ att.h) (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (hdb : tr.time d ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = att.T ∧
      CoveredBefore tr H g a b (sp.slot (tr.time d)) d E :=
  signed_row_covered_before_at_core hrun.toCore hnc hvz hs hh hsnap hc hdb

/-- A held shadow left entry is covered by a member written before the reader's cut. -/
theorem left_entry_covered_before_at'
    {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {a b : Time} {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hq : (H (max (cutZ sp.toParams g) t))ᶜ.ncard < sp.toParams.fg.q)
    {E C : AC.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h)
    (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h)
    (hsnap : ∃ k, FirstCutAfter tr k (cutZ sp.toParams g))
    (hc : HighSourceCover tr H g a b) (htb : t ≤ b) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H (max (cutZ sp.toParams g) t),
      ∃ d < k, tr.SignAt v d att ∧ att.T = E.root ∧ CoveredBefore tr H g a b (sp.slot t) k E :=
  left_entry_covered_before_at_core hrun.toCore hnc ht hle hy hq hE hET hEh hEC hlt hsnap hc htb

end Consensus.Goldilocks.Healing.Growing.Outcome

end

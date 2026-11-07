module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource

public section

/-! # Vote specialization of the duty-independent floor crossing

The causal row bound is left explicit here until its own-cut exclusion proof is
available. The shared floor transport retains its exact frozen statement.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Specialize the shared floor source to the vote's slot with an explicit causal row bound. -/
theorem high_floor_source_core_of_row_bound_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H (tr.time k)) (hkb : tr.time k ≤ b)
    {e : SA.Em sp (List (FG.Att sp.n))}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v d, v ∈ H (tr.time d) → tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < e.msg.slot)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < e.msg.slot ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocksAt H) E O ∧
      Anc (tr.HonestBlocksAt H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h := by
  obtain ⟨v, r, l, O, E, hr, hO, hl, hE, hEO, hBO, hf, -⟩ :=
    hp.high_floor_signed_source_of_row_bound_at ho (hp.run.time_nonneg k)
      (fun _ hq => hp.run.time_mono hq.le) hy hkb hrow hpair hcomp hfloor
  exact ⟨v, r, l, O, E, hr, hO, hl, hE, hEO, hBO, hf⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

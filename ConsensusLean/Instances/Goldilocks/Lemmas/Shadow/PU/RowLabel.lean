module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLabel

public section

/-! # Shadow instantiations of the shared causal row labels

The signer and voter are each read on their own honest prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b hold : Time}

/-- A held honest row cannot originate in a same-slot optimistic write. -/
theorem row_origin_not_current_at'
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    {r : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} : ¬ AC.OptimisticLockAt tr.projAC v r e.msg.slot D CV :=
  row_origin_not_current_at_core hp.toCore hy hc hW ha hv hs hrd

/-- The source label of a held honest row strictly precedes the vote's slot. -/
theorem row_origin_label_lt_at'
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O) : l < e.msg.slot :=
  row_origin_label_lt_at_core hp.toCore hy hc hW ha hv hs hdk hrd ho

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

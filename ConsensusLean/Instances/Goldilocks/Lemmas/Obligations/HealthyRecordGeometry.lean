module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record

/-! # Retained-record lookup

`record_lookup_of_later`: an unchanged record cannot reenter the filtered frame after its
finalized floor advances.
-/

public section
namespace Consensus.Goldilocks.Obligations

/-- An unchanged record cannot reenter the filtered frame after its finalized floor advances. -/
theorem record_lookup_of_later
    {sp : AC.ACParams}
    {tr : GoldilocksTrace sp} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i j : Nat} (hij : i ≤ j)
    (heq : (tr.state y j).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed)
    {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed = some R) :
    AC.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed = some R := by
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  obtain ⟨hRm, hroot⟩ := AC.lookup_eq_some hR
  obtain ⟨L, hL, hLroot, _⟩ := Compose.record_origin hrun hnc hy i
  have hLR : L = R := hU.1 ⟨y, hy, i, hL⟩ ⟨y, hy, j, hRm.1⟩
    (hLroot.trans (heq.symm.trans hroot.symm))
  subst L
  have hFR : Anc (tr.HonestBlocks H) (tr.state y i).fg.F R :=
    (Anc.mono (Compose.fg_tree_subset_honest hy j)
      (Regimes.finalized_monotone_from hrun hy hij)).trans
      (Anc.mono (Compose.fg_tree_subset_honest hy j) hRm.2)
  have hm : R ∈ (Node.frame (tr.state y i)).tree :=
    ⟨hL, Compose.honest_held_anc hrun hnc hy hFR hL⟩
  cases hk : AC.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
  | none => exact False.elim (AC.lookup_eq_none hk ⟨R, hm, hLroot⟩)
  | some B =>
    obtain ⟨hB, hrB⟩ := AC.lookup_eq_some hk
    congr 1
    exact hU.1 ⟨y, hy, i, hB.1⟩ ⟨y, hy, i, hL⟩ (hrB.trans hLroot.symm)

namespace UpTo

variable {sp : AC.ACParams}
  {tr : GoldilocksTrace sp} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g ΔF a : Time}

end UpTo
end Consensus.Goldilocks.Obligations

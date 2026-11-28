module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Witness.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Node.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.FloorHead

public section

/-! # Finalized observations below warm shadow vote heads -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- A primed viable witness puts a separate finalized observation below every viable head. -/
theorem finalized_anc_head_at_cast_at {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {z y : Fin sp.n} {c i : Nat}
    (hz : z ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    (hf : (H (max (tr.time c) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {Y : AC.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i))
      (tr.state z c).fg.F) :
    Anc (tr.HonestBlocksAt H) (tr.state z c).fg.F
      (AC.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hri := (hac.upTo (hrun.time_nonneg i)).localRun
  have hPhi := AC.frameIn_of_callAt hri hy hci
  have hfloor : ∀ Q ∈ ell.frame.viableHeads,
      ell.frame.Anc (tr.state z c).fg.F Q := by
    intro Q hQ
    have hwit := Consensus.Goldilocks.Shadow.PU.Growing.early_witness_viable
      hrun hframe hy hilo hihi hc.1 hQ
    have hQt : Q ∈ (tr.state y i).fg.tree := by
      have hv := hQ
      rw [Consensus.Goldilocks.Shadow.PU.Growing.frame_of_projAC_at hrun hy hc.1, Node.frame_eq,
        Store.toFrame_viableHeads] at hv
      exact hv.1
    have hFQ := hframe.finalized_below_descendant_at hrun hnc hz hy hy hf hclo hchi
      hQt hwit hQt .refl
    have hFt := AC.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2
      (hPhi.1.viableHeads_subset hQ) hFQ
      (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans
        (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))) |>.trans haF)
    exact AC.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hFt hFQ
      (hPhi.1.viableHeads_subset hQ)
  have hFt := AC.mem_of_anc (hfloor Y hvY) (hPhi.1.viableHeads_subset hvY)
  have hat : AC.getAnchor sp e.readPoint ell.frame (tr.time i) ∈ ell.frame.tree := by
    by_cases he : ell.frame.fcRoot = AC.getAnchor sp e.readPoint ell.frame (tr.time i)
    · exact he ▸ hPhi.1.fcRoot_mem
    · exact (Anc.mem (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)) he).2
  have hcast : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  exact Anc.mono hPhi.2 (AC.finalized_floor_anc_getHead hPhi.1 (fun _ h => h.1)
    (AC.voterBlockTree_ancU hri.toU hrun.vstart hy hcast) hfloor hY hvY (hfloor Y hvY)
    e.readPoint (tr.time i) _ _ (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))
    (AC.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hat haF hFt))

/-- The primed frame root is F, so a separate root observation uses finalized ancestry. -/
theorem fcRoot_anc_head_at_cast_at {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {z y : Fin sp.n} {c i : Nat}
    (hz : z ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    (hf : (H (max (tr.time c) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ellz ell : ACLabel (goldilocksNode sp)} (hcz : tr.projAC.CallAt z c ellz)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    {Y : AC.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i))
      ellz.frame.fcRoot) :
    Anc (tr.HonestBlocksAt H) ellz.frame.fcRoot
      (AC.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hroot : ellz.frame.fcRoot = (tr.state z c).fg.F := by
    rw [Consensus.Goldilocks.Shadow.PU.Growing.frame_of_projAC_at hrun hz hcz,
      Node.frame_eq, Store.toFrame_fcRoot]
  rw [hroot] at haF ⊢
  exact finalized_anc_head_at_cast_at hframe hrun hnc hz hy hf hclo hchi hilo hihi hc
    hY hvY haF

end Consensus.Goldilocks.Healing.Growing.Shadow

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesPath
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.FloorHead

public section

/-! # Finalized prefixes at independently honest casts -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A separately honest finalized observation lies below the cast head when it lies above
the cast anchor. The quorum bound is at the later of the two observations. -/
theorem FrameWindow.finalized_anc_head_at_cast_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {z y : Fin sp.n} {c i : Nat}
    (hz : z ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    (hf : (H (max (tr.time c) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    {Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i))
      (tr.state z c).fg.F) :
    Anc (tr.HonestBlocksAt H) (tr.state z c).fg.F
      (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hri := (hac.upTo (hrun.time_nonneg i)).localRun
  have hPhi := SA.frameIn_of_callAt hri hy hci
  have hfr := (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1
  have hfloor : ∀ Q ∈ ell.frame.viableHeads,
      ell.frame.Anc (tr.state z c).fg.F Q := by
    intro Q hQ
    have hV := hQ
    rw [hfr] at hV
    have hFQ := hframe.finalized_below_descendant_at hrun hnc hz hy hy hf hclo hchi
      hV.1 (by rw [← hframe.floor_eq y i hy hilo hihi]; exact hV.2.2.2)
      (fun hk => by
        rw [← hframe.root_eq y i hy hilo hihi hk]
        have hroot : (tr.state y i).fg.fcRoot = (tr.state y i).fg.J :=
          ite_eq_left ((hframe.kind_iff y i hy hilo hihi).mpr hk)
        have hanc := hV.2.2.1
        rw [hroot] at hanc
        exact hanc.mono (fun B hB =>
          ⟨y, i, tr.time i, hrun.time_nonneg i, (fun q hq => hrun.time_mono hq.le), hy, hB⟩))
      hV.1 .refl
    have hFt := SA.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2
      (hPhi.1.viableHeads_subset hQ) hFQ
      (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans
        (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))) |>.trans haF)
    exact SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hFt hFQ
      (hPhi.1.viableHeads_subset hQ)
  have hFt := SA.mem_of_anc (hfloor Y hvY) (hPhi.1.viableHeads_subset hvY)
  have hat : SA.getAnchor sp e.readPoint ell.frame (tr.time i) ∈ ell.frame.tree := by
    by_cases he : ell.frame.fcRoot = SA.getAnchor sp e.readPoint ell.frame (tr.time i)
    · exact he ▸ hPhi.1.fcRoot_mem
    · exact (Anc.mem (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)) he).2
  have hcast : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  exact Anc.mono hPhi.2 (SA.finalized_floor_anc_getHead hPhi.1 (fun _ h => h.1)
    (SA.voterBlockTree_anc hri hy hcast) hfloor hY hvY (hfloor Y hvY)
    e.readPoint (tr.time i) _ _ (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))
    (SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hat haF hFt))

/-- A cast reaches another honest frame's root: common J roots agree, and an F root
uses the separately observed finalized prefix. -/
theorem FrameWindow.fcRoot_anc_head_at_cast_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {z y : Fin sp.n} {c i : Nat}
    (hz : z ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    (hf : (H (max (tr.time c) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ellz ell : ACLabel (goldilocksNode sp ro)} (hcz : tr.projAC.CallAt z c ellz)
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ell e)
    {Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i))
      ellz.frame.fcRoot) :
    Anc (tr.HonestBlocksAt H) ellz.frame.fcRoot
      (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := SA.frameIn_of_callAt (hac.upTo (hrun.time_nonneg i)).localRun hy hci
  have hfr := (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1
  have hfrz := (hrun.cutLaw z c _ (Compose.projAC_callAt.mp hcz) hz).1
  by_cases hk : kindJ
  · have hroots : ellz.frame.fcRoot = ell.frame.fcRoot := by
      rw [hfrz, hfr]
      change (tr.state z c).fg.fcRoot = (tr.state y i).fg.fcRoot
      rw [show (tr.state z c).fg.fcRoot = (tr.state z c).fg.J from
        ite_eq_left ((hframe.kind_iff z c hz hclo hchi).mpr hk),
        show (tr.state y i).fg.fcRoot = (tr.state y i).fg.J from
        ite_eq_left ((hframe.kind_iff y i hy hilo hihi).mpr hk),
        hframe.root_eq z c hz hclo hchi hk, hframe.root_eq y i hy hilo hihi hk]
    rw [hroots]
    exact Anc.mono hPhi.2 (SA.anc_getHead_of_compat hPhi.1 (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi.1 hL).elim
        (fun h => Or.inr h.2.1) Or.inl) (fun _ h => h.1.1)
      _ _ (.refl : ell.frame.Anc ell.frame.fcRoot ell.frame.fcRoot))
  · have hroot : ellz.frame.fcRoot = (tr.state z c).fg.F := by
      rw [hfrz]
      exact ite_eq_right (fun h => hk ((hframe.kind_iff z c hz hclo hchi).mp h))
    rw [hroot] at haF ⊢
    exact hframe.finalized_anc_head_at_cast_at hrun hnc hz hy hf hclo hchi hilo hihi hc
      hY hvY haF

end Consensus.Goldilocks.Healing.Growing

end

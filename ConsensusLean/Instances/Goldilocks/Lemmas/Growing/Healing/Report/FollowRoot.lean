module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality

public section

/-! # Historical frame roots below actual proposal heads -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

/-- A common window root follows an actual proposal without retaining either reader's honesty. -/
theorem FrameWindow.fcRoot_anc_proposal_head_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    {lo hi : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y z : Fin sp.n} {i c s : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time i) (tr.time c)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z c ell)
    (hcall : ell.call = .proposal) (hti : tr.time c = sp.ts s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state z c) ell.frame (tr.time c)).2 =
      some (d, pay)) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot d.head := by
  have hfc : (H (tr.time c))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n :=
    lt_of_le_of_lt (Set.ncard_le_ncard (Set.compl_subset_compl.mpr
      (hrun.antitone (le_max_right _ _)))) hf
  have hv := proposal_parent_viable_full_frame_at hrun hnc hz hfc hc hcall
    (by rwa [sp.slotTime_eq]) hd
  have he : ell.frame = Node.frame (tr.state z c) :=
    (hrun.cutLaw z c (.ac ell) (Compose.projAC_callAt.mp hc) hz).1
  rw [he] at hv
  have hroot := honest_anc_of_store_anc_at (hrun.time_nonneg c)
    (fun q hq => hrun.time_mono hq.le) hz hv.2.2.1
  have hJ : kindJ → Anc (tr.HonestBlocksAt H) J d.head := by
    intro hk
    have hkc := (hframe.kind_iff z c hz hclo hchi).mpr hk
    change Anc _ (tr.state z c).fg.fcRoot d.head at hroot
    rwa [show (tr.state z c).fg.fcRoot = (tr.state z c).fg.J from ite_eq_left hkc,
      hframe.root_eq z c hz hclo hchi hk] at hroot
  by_cases hk : kindJ
  · have hki := (hframe.kind_iff y i hy hilo hihi).mpr hk
    rw [show (tr.state y i).fg.fcRoot = (tr.state y i).fg.J from ite_eq_left hki,
      hframe.root_eq y i hy hilo hihi hk]
    exact hJ hk
  · have hki := (hframe.kind_iff y i hy hilo hihi).not.mpr hk
    rw [show (tr.state y i).fg.fcRoot = (tr.state y i).fg.F from ite_eq_right hki]
    exact hframe.finalized_below_descendant_at hrun hnc hy hz hz hf hilo hihi hv.1
      (by rw [← hframe.floor_eq z c hz hclo hchi]; exact hv.2.2.2) hJ hv.1 .refl

end Consensus.Goldilocks.Healing.Growing

end

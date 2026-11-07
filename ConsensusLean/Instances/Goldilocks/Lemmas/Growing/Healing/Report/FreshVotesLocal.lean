module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal

public section

/-! # Local warm-vote walk geometry

These facts inspect one cast before its voter is compromised. Retaining that node's
execution through the cast suffices; no common honest cohort or frame invariant is used.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A cast whose anchor is the slot's proposal cannot walk to a later-slot child. -/
theorem vote_head_eq_of_anchor_eq_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = e.msg.slot)
    (hPt : P ∈ ell.frame.tree)
    (haP : SA.getAnchor sp e.readPoint ell.frame (tr.time i) = P) :
    e.msg.head = P.root := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg i
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ell e := by
    refine ⟨?_, hc.2⟩
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  exact Healing.vote_head_eq_of_anchor_eq (hrun.upTo hd) (hnc.upTo (tr.time i))
    hy hc' hPs hPt haP

/-- A point on the anchor-to-proposal path is in the voter's frozen viable domain.
Historical ancestry is pulled into this reader's prefix, not a shared honest cohort. -/
theorem frozen_viable_of_anchor_path_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    {X P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (haX : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXP : Anc (tr.HonestBlocksAt H) X P) :
    X ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg i
  have hc' : SA.CastAt (tr.upTo (tr.time i)).projAC y i ell e := by
    refine ⟨?_, hc.2⟩
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hac := Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
    (tr.upTo (tr.time i)) proposer (hrun.upTo hd) (hnc.upTo (tr.time i))
  have hPh := SA.frameIn_of_callAt hac.localRun hy hc'.1
  have hP' := hPh.2 hP.1.1
  have hXP' := RunTrace.anc_upTo_of_right hr hnc hd hP' hXP
  have hX' : X ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) := by
    rcases eq_or_ne X P with he | he
    · exact he ▸ hP'
    · exact (Anc.mem hXP' he).1
  exact Healing.frozen_viable_of_anchor_path (hrun.upTo hd) (hnc.upTo (tr.time i))
    hy hc' hP (RunTrace.anc_upTo_of_right hr hnc hd hX' haX) hXP'

/-- The actual proposal walk is finite and ends at the emitted duty head. -/
theorem proposal_walk_end_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {ip : Nat}
    (hz : z ∈ H (tr.time ip))
    {ellp : ACLabel (goldilocksNode sp ro)} (hcp : tr.projAC.CallAt z ip ellp)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) :
    d.start ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot d.start ∧
      SA.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) ((sp.slot (tr.time ip) : Int) - 1))
        (SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay)
          ((sp.slot (tr.time ip) : Int) - 1)) d.start d.head := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg ip
  have hc' : (tr.upTo (tr.time ip)).projAC.CallAt z ip ellp := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hs := Trace.upTo_state tr.projAC z (d := tr.time ip) (i := ip)
    (fun k hk => hr.time_mono hk.le)
  have hp' : (SA.acProposal sp ((tr.upTo (tr.time ip)).projAC.state z ip)
      ellp.frame ((tr.upTo (tr.time ip)).time ip)).2 = some (d, pay) := by
    simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hp
  exact Healing.proposal_walk_end (hrun.upTo hd) (hnc.upTo (tr.time ip)) hz hc' hp'

end Consensus.Goldilocks.Healing.Growing

end

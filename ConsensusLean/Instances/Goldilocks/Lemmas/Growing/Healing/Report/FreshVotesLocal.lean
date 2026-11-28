module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock

public section

/-! # Local warm-vote walk geometry

These facts inspect one cast before its voter is compromised. Retaining that node's
execution through the cast suffices; no common honest cohort or frame invariant is used.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

namespace Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- A cast anchored at its slot's proposal has no later eligible child, independently of the
node's frame implementation. -/
theorem vote_head_eq_of_anchor_eq_at
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = e.msg.slot)
    (hPt : P ∈ ell.frame.tree)
    (haP : AC.getAnchor sp e.readPoint ell.frame (tr.time i) = P) :
    e.msg.head = P.root := by
  have hr := (rc.acRun_upTo hnc (rc.time_nonneg i)).localRun
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  have hPhi := (AC.frameIn_of_callAt hr hy hc'.1).1
  have hslot := AC.frame_slot_leU sp hr.toU hy hc'.1
  have hs := (AC.castAt_specU hr.toU hy hc').2.1
  have hstop : ¬ ∃ C, AC.IsBest sp
      (AC.headScore sp ell.frame (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot)
        ((e.msg.slot : Int) - 1))
      (AC.eligibleChildren
        (ell.frame.viableTree (AC.voteDomain sp e.readPoint ell.frame e.msg.slot))
        (AC.headEligible sp ell.frame (tr.time i)
          (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) P)
      C := by
    rintro ⟨C, ⟨⟨hC, hCP, -⟩, -⟩⟩
    have hlt := hPhi.coherent.2 P hPt C (AC.voteDomain_subset_tree hC.1) hCP
    have hle := hslot C (AC.voteDomain_subset_tree hC.1)
    omega
  have heq : AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voteDomain sp e.readPoint ell.frame e.msg.slot))
      (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1) = P := by
    unfold AC.getHead
    rw [haP]
    exact AC.ghost_fuel_stable (Nat.zero_le _) hstop
  exact (rc.castAt_spec_at hnc hy hc).2.2.2.trans (congrArg Block.root heq)

/-- Frozen viability is closed along the path from the cast anchor to a frozen viable block. -/
theorem frozen_viable_of_anchor_path_at
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {X P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (haX : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXP : Anc (tr.HonestBlocksAt H) X P) :
    X ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have hr := (rc.acRun_upTo hnc (rc.time_nonneg i)).localRun
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  have hPhi := rc.frameIn_at hnc hy hc.1
  have hrootX := (Anc.mono hPhi.2
    (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))).trans haX
  have hXt := AC.frame_mem_of_between sp (rc.coherent hnc) hPhi.1 hPhi.2 hP.1.1 hXP
    ((Anc.mono hPhi.2 hPhi.1.F_anc_fcRoot).trans hrootX)
  have hXPf := AC.anc_tree_of_anc_U (rc.coherent hnc) hPhi.1 hPhi.2 hXt hXP hP.1.1
  have hrootXf := AC.anc_tree_of_anc_U (rc.coherent hnc) hPhi.1 hPhi.2
    hPhi.1.fcRoot_mem hrootX hXt
  obtain ⟨Y, hY, hvY, hPY⟩ := hP.2.2
  exact ⟨AC.voterBlockTree_ancU hr.toU rc.vstart hy hc' P hP.1 X hXPf, hrootXf,
    Y, hY, hvY, hXPf.trans hPY⟩

/-- The proposal's duty head is the end of its finite walk in any core's call frame. -/
theorem proposal_walk_end_at
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {ip : Nat}
    (hz : z ∈ H (tr.time ip))
    {ellp : ACLabel (goldilocksNode sp)} (hcp : tr.projAC.CallAt z ip ellp)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) :
    d.start ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot d.start ∧
      AC.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (AC.headScore sp ellp.frame (AC.View.ofLists pay) ((sp.slot (tr.time ip) : Int) - 1))
        (AC.headEligible sp ellp.frame (tr.time ip) (AC.View.ofLists pay)
          ((sp.slot (tr.time ip) : Int) - 1)) d.start d.head := by
  have hPhi := (rc.frameIn_at hnc hz hcp).1
  have key (A : AC.ACState sp.n) (V : AC.View sp.n) (σ : Int) :
      AC.getAnchor sp A ellp.frame (tr.time ip) ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot (AC.getAnchor sp A ellp.frame (tr.time ip)) ∧
      AC.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (AC.headScore sp ellp.frame V σ)
        (AC.headEligible sp ellp.frame (tr.time ip) V σ)
        (AC.getAnchor sp A ellp.frame (tr.time ip))
        (AC.getHead sp A ellp.frame (tr.time ip) (ellp.frame.viableTree ellp.frame.tree) V σ) := by
    have hroot := AC.fcRoot_anc_getAnchor hPhi A (tr.time ip)
    have hstart : AC.getAnchor sp A ellp.frame (tr.time ip) ∈ ellp.frame.tree := by
      rcases eq_or_ne ellp.frame.fcRoot (AC.getAnchor sp A ellp.frame (tr.time ip)) with he | he
      · exact he ▸ hPhi.fcRoot_mem
      · exact (Anc.mem hroot he).2
    refine ⟨hstart, hroot, ?_⟩
    exact AC.walkEnd_ghost hPhi.coherent (fun X hX => hX.1)
      (hPhi.finite.subset fun X hX => hX.1)
      (Set.ncard_le_ncard (fun X hX => hX.1) hPhi.finite) _
  unfold AC.acProposal at hp
  split_ifs at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact key _ _ _

end Core

/-- A cast whose anchor is the slot's proposal cannot walk to a later-slot child. -/
theorem vote_head_eq_of_anchor_eq_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = e.msg.slot)
    (hPt : P ∈ ell.frame.tree)
    (haP : AC.getAnchor sp e.readPoint ell.frame (tr.time i) = P) :
    e.msg.head = P.root := by
  exact Core.vote_head_eq_of_anchor_eq_at hrun.toCore hnc hy hc hPs hPt haP

/-- A point on the anchor-to-proposal path is in the voter's frozen viable domain.
Historical ancestry is pulled into this reader's prefix, not a shared honest cohort. -/
theorem frozen_viable_of_anchor_path_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {X P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (haX : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXP : Anc (tr.HonestBlocksAt H) X P) :
    X ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  exact Core.frozen_viable_of_anchor_path_at hrun.toCore hnc hy hc hP haX hXP

/-- The actual proposal walk is finite and ends at the emitted duty head. -/
theorem proposal_walk_end_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} {ip : Nat}
    (hz : z ∈ H (tr.time ip))
    {ellp : ACLabel (goldilocksNode sp)} (hcp : tr.projAC.CallAt z ip ellp)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) :
    d.start ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot d.start ∧
      AC.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (AC.headScore sp ellp.frame (AC.View.ofLists pay) ((sp.slot (tr.time ip) : Int) - 1))
        (AC.headEligible sp ellp.frame (tr.time ip) (AC.View.ofLists pay)
          ((sp.slot (tr.time ip) : Int) - 1)) d.start d.head := by
  exact Core.proposal_walk_end_at hrun.toCore hnc hz hcp hp

end Consensus.Goldilocks.Healing.Growing

end

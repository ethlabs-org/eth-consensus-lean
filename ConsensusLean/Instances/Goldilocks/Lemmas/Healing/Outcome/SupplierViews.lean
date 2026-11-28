module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ParentStop
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SuffixTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal viability and view selection

Viable proposals, reflected competitors and the stop-at-parent argument used by unanimity. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-- Viability passes to a store descendant of at least the same height. -/
private theorem isViable_of_anc {P : Params} {ACP : Type} {st : Store P ACP}
    {X B : NodeBlock P ACP} (hv : st.IsViable X) (hXB : st.Anc X B)
    (hh : (st.σ X.root).h ≤ (st.σ B.root).h) : st.IsViable B := by
  rcases hv with hm | ⟨hX, hgap | hJX⟩
  · exact Or.inl (hm.trans hh)
  · by_cases hm : st.hmax ≤ (st.σ B.root).h
    · exact Or.inl hm
    · exact Or.inr ⟨by omega, Or.inl hgap⟩
  · by_cases hm : st.hmax ≤ (st.σ B.root).h
    · exact Or.inl hm
    · exact Or.inr ⟨by omega, Or.inr (hJX.trans hXB)⟩

/-- A voter competitor other than the proposal, below a predecessor of its parent, reflects into the
proposer's viable tree. Frozen candidates use guarded relay; current-slot candidates use the
actual proposal's uniqueness. -/
theorem reset_competitor_reflect
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {Q X B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQt : Q ∈ ellp.frame.tree) (hPQ : P.parent = some Q.root)
    (hXQ : ellp.frame.Anc X Q) (hBP : B ≠ P)
    (hXv : X ∈ ellp.frame.viableHeads)
    (hBX : B.parent = some X.root)
    (hB : B ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hP.1 hci
  obtain ⟨-, hPsiU⟩ := AC.frameIn_of_callAt hr hy hcy.1
  have hXt : X ∈ ellp.frame.tree := AC.mem_of_anc hXQ hQt
  have hXB : Anc (tr.HonestBlocks H) X B := .single ⟨hPhiU hXt, hPsiU hB.1.1, hBX⟩
  have hFB := ((hPhi.rooted.2 X hXt).mono hPhiU).trans hXB
  have hBt : B ∈ ellp.frame.tree := by
    rcases hB.1.2 with hfz | ⟨P', hP't, hP's, hBP'⟩
    · exact reset_frozen_frame hp hc hP.1 hy hci hti hcy hg hjoin hB.1.1 hfz hFB
    · obtain rfl := reset_proposal_frame_unique hp hP (by omega) hy hcy.1 hP't hP's
      have hBQ : Anc (tr.HonestBlocks H) B Q := by
        rcases Relation.ReflTransGen.cases_tail (hBP'.mono hPsiU) with heq | ⟨Y, hBY, hY⟩
        · exact absurd heq.symm hBP
        obtain rfl : Y = Q := hr.coherent.1 hY.1 (hPhiU hQt)
          (Option.some_injective _ (hY.2.2.symm.trans hPQ))
        exact hBY
      exact AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hQt hBQ hFB
  have hfB := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.rooted.1
    (((hPhi.rooted.2 X (hPhi.viableHeads_subset hXv)).mono hPhiU).trans hXB) hBt
  refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
  rw [Compose.frame_of_projAC hp.run hP.1 hci] at hXv hBt ⊢
  have hXBs := Compose.honest_held_anc hp.run hp.noColl hP.1 hXB hBt.1
  exact ⟨hBt.1, hBt.2, isViable_of_anc hXv.2.2 hXBs
    (Compose.honest_held_height hp.run hp.noColl hP.1 hXBs).1⟩

/-- Finite winner transport along the viable proposal chain. -/
theorem ResetPremisesUpTo.reset_winner_voter_tree {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u)
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocks H) C P)
    (haC : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u) := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc.1
  have hfC := ((AC.fcRoot_anc_getAnchor hPhi e.readPoint (tr.time j)).mono hPhiU).trans haC
  have hFC := hfC
  have hCt := AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hP.1.1 hCP hFC
  have hCP' := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hCt hCP hP.1.1
  have hfC' := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.rooted.1 hfC hCt
  obtain ⟨W, hW, hWv, hPW⟩ := hP.2.2
  have hCs : C ∈ AC.voterBlockTree sp e.readPoint ell.frame u := by
    rw [← hes] at hP ⊢
    exact AC.voterBlockTree_ancU hr.toU hp.run.vstart hy hc P hP.1 C hCP'
  exact ⟨hCs, hfC', W, hW, hWv, hCP'.trans hPW⟩

/-- Any ancestor of a viable current proposal above the voter's anchor is in its viable tree.
This is the winner-domain transport used by suffix comparison. -/
theorem reset_winner_voter_tree
    (hp : ResetPremises tr H K proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u)
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocks H) C P)
    (haC : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u) :=
  (hp.toUpTo tr H le_rfl).reset_winner_voter_tree hy hc hes hP hCP haC

/-- Finite competitor reflection uses only guarded frozen transport and actual uniqueness. -/
theorem ResetPremisesUpTo.reset_competitor_reflect {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hib : tr.time i ≤ b)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {Q X B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQt : Q ∈ ellp.frame.tree) (hPQ : P.parent = some Q.root)
    (hXQ : ellp.frame.Anc X Q) (hBP : B ≠ P)
    (hXv : X ∈ ellp.frame.viableHeads) (hBX : B.parent = some X.root)
    (hB : B ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci
  obtain ⟨_, hPsiU⟩ := AC.frameIn_of_callAt hr hy hcy.1
  have hXt : X ∈ ellp.frame.tree := AC.mem_of_anc hXQ hQt
  have hXB : Anc (tr.HonestBlocks H) X B := .single ⟨hPhiU hXt, hPsiU hB.1.1, hBX⟩
  have hFB := ((hPhi.rooted.2 X hXt).mono hPhiU).trans hXB
  have hBt : B ∈ ellp.frame.tree := by
    rcases hB.1.2 with hfz | ⟨P', hP't, hP's, hBP'⟩
    · exact hp.reset_frozen_frame hc hpH hy hci hti hcy hib hg hjoin hB.1.1 hfz hFB
    · obtain rfl := hp.reset_proposal_frame_unique hpH hdesignated hactual hPs
        (by omega) hy hcy.1 hP't hP's
      have hBQ : Anc (tr.HonestBlocks H) B Q := by
        rcases Relation.ReflTransGen.cases_tail (hBP'.mono hPsiU) with heq | ⟨Y, hBY, hY⟩
        · exact absurd heq.symm hBP
        obtain rfl : Y = Q := hr.coherent.1 hY.1 (hPhiU hQt)
          (Option.some_injective _ (hY.2.2.symm.trans hPQ))
        exact hBY
      exact AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hQt hBQ hFB
  have hfB := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.rooted.1
    (((hPhi.rooted.2 X (hPhi.viableHeads_subset hXv)).mono hPhiU).trans hXB) hBt
  refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
  rw [Compose.frame_of_projAC hp.run hpH hci] at hXv hBt ⊢
  have hXBs := Compose.honest_held_anc hp.run hp.noColl hpH hXB hBt.1
  exact ⟨hBt.1, hBt.2, isViable_of_anc hXv.2.2 hXBs
    (Compose.honest_held_height hp.run hp.noColl hpH hXBs).1⟩

/-- A best child on the proposal-parent path stays best at the voter. The winner is
transported through the viable proposal, while competitors reflect through guarded relay. -/
theorem reset_suffix_best
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPv : P ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : AC.gbar g ≤ sp.ts s)
    (hgi : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {X C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQt : d.head ∈ ellp.frame.tree) (hXQ : ellp.frame.Anc X d.head)
    (hne : X ≠ d.head) (hXv : X ∈ ellp.frame.viableHeads)
    (hCQ : ellp.frame.Anc C d.head)
    (haX : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint elly.frame (tr.time j)) X)
    (hC : AC.IsBest sp (AC.headScore sp ellp.frame (AC.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        AC.headEligible sp ellp.frame (tr.time i) (AC.View.ofLists pay) s B} C) :
    AC.IsBest sp (AC.headScore sp elly.frame
      (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some X.root ∧ AC.headEligible sp elly.frame (tr.time j)
          (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hP.1 hci
  obtain ⟨-, hPsiU⟩ := AC.frameIn_of_callAt hr hy hcy.1
  exact suffix_best_of_views hr.coherent hPhi hPhiU hPsiU (fun _ hB => hB.1.1) hti
    (reset_views_agree hp hc hP hci hcall hd hti hpay hy hcy hes hPv.1.1 hg hgi hgj hjoi hjoj)
    hQt hPQ hP.2.2.2.2.1 hPv.1.1 hXQ hne hXv hCQ
    (fun hCP hXC => reset_winner_voter_tree hp hy hcy hes hPv hCP (haX.trans hXC))
    (fun B hB hBP hBX => reset_competitor_reflect hp hc hP hci hti hy hcy hgi hjoi hQt hPQ hXQ
      hBP hXv hBX hB) hC

/-- Finite best-child transfer along the proposal-parent suffix. -/
theorem ResetPremisesUpTo.reset_suffix_best {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPv : P ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : AC.gbar g ≤ sp.ts s)
    (hgi : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {X C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQt : d.head ∈ ellp.frame.tree) (hXQ : ellp.frame.Anc X d.head)
    (hne : X ≠ d.head) (hXv : X ∈ ellp.frame.viableHeads)
    (hCQ : ellp.frame.Anc C d.head)
    (haX : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint elly.frame (tr.time j)) X)
    (hC : AC.IsBest sp (AC.headScore sp ellp.frame (AC.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        AC.headEligible sp ellp.frame (tr.time i) (AC.View.ofLists pay) s B} C) :
    AC.IsBest sp (AC.headScore sp elly.frame
      (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some X.root ∧ AC.headEligible sp elly.frame (tr.time j)
          (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci
  obtain ⟨_, hPsiU⟩ := AC.frameIn_of_callAt hr hy hcy.1
  exact suffix_best_of_views hr.coherent hPhi hPhiU hPsiU (fun _ hB => hB.1.1) hti
    (hp.reset_views_agree hc hpH hdesignated hactual hPs hci hcall hd hti hpay hy hcy hes hib
      hjb hPv.1.1 hg hgi hgj hjoi hjoj)
    hQt hPQ hPs hPv.1.1 hXQ hne hXv hCQ
    (fun hCP hXC => hp.reset_winner_voter_tree hy hcy hes hPv hCP (haX.trans hXC))
    (fun B hB hBP hBX => hp.reset_competitor_reflect hc hpH hdesignated hactual hPs hci hti hy
      hcy hib hgi hjoi hQt hPQ hXQ hBP hXv hBX hB) hC

end Consensus.Goldilocks.Healing

end

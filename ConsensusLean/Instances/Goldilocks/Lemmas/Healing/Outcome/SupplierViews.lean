module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore

public section

/-! # Goldilocks Healing: proposal viability and view selection

Viable proposals, reflected competitors and the stop-at-parent argument used by unanimity. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- At a first-disagreement cut, a frame-held proposal is a viable voter-tree candidate. -/
theorem reset_proposal_viable
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u)
    (hPy : P ∈ elly.frame.tree)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root) :
    P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame u) := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hroot := reset_vote_root_below_proposal hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
  have hroot' := SA.anc_tree_of_anc_U hr.coherent hPsi hPsiU hPsi.fcRoot_mem hroot hPy
  have hPt : P ∈ SA.voterBlockTree sp e.readPoint elly.frame u :=
    ⟨hPy, Or.inr ⟨P, hPy, hP.2.2.2.2.1, .refl⟩⟩
  have hPyStore : P ∈ (tr.state y j).fg.tree := by
    rw [Compose.frame_of_projAC hp.run hy hcy.1] at hPy
    exact hPy.1
  have hfloor := reset_vote_floor_above_old hp hy hR hcy hes hPyStore (fun x r l O ho ht => by
    have hOQ := crossing_below_proposal_parent hp hc hP hR hci hcall hd hti hPQ ho ht
      (show Anc (tr.HonestBlocks H) O O from .refl)
    obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    have hQt : d.head ∈ ellp.frame.tree := by
      rcases eq_or_ne d.start d.head with he | he
      · exact he ▸ hst
      · exact (Anc.mem hsQ he).2
    exact hOQ.trans (.single ⟨hPhiU hQt, hPsiU hPy, hPQ⟩))
  refine ⟨hPt, hroot', P, hPt, ?_, .refl⟩
  rw [Compose.frame_of_projAC hp.run hy hcy.1] at hPy hroot' ⊢
  exact ⟨hPy.1, hPy.2, hroot'.mono (fun X hX => hX.1), hfloor⟩

/-- A held actual proposal is viable at a bounded post-drain cast. -/
theorem ResetPremisesUpTo.reset_proposal_viable {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) {k i j u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) :
    P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame u) := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hroot := hp.reset_vote_root_below_proposal hc hpH hactual hR hci hcall hd hti hib hPQ
    hy hcy hes hjb
  have hroot' := SA.anc_tree_of_anc_U hr.coherent hPsi hPsiU hPsi.fcRoot_mem hroot hPy
  have hPt : P ∈ SA.voterBlockTree sp e.readPoint elly.frame u :=
    ⟨hPy, Or.inr ⟨P, hPy, hPs, .refl⟩⟩
  have hPyStore : P ∈ (tr.state y j).fg.tree := by
    rw [Compose.frame_of_projAC hp.run hy hcy.1] at hPy
    exact hPy.1
  have hfloor := hp.reset_vote_floor_above_old hy hR hcy hes hjb hPyStore
    (fun x r l O ho ht _ => by
      have hOQ := hp.reset_proposal_passes hc hpH hR hci hcall hd hti hib O ⟨x, r, l, ho, ht⟩
      obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
      have hQt : d.head ∈ ellp.frame.tree := by
        rcases eq_or_ne d.start d.head with he | he
        · exact he ▸ hst
        · exact (Anc.mem hsQ he).2
      exact hOQ.trans (.single ⟨hPhiU hQt, hPsiU hPy, hPQ⟩))
  refine ⟨hPt, hroot', P, hPt, ?_, .refl⟩
  rw [Compose.frame_of_projAC hp.run hy hcy.1] at hPy hroot' ⊢
  exact ⟨hPy.1, hPy.2, hroot'.mono (fun X hX => hX.1), hfloor⟩

/-- Any ancestor of a viable current proposal above the voter's anchor is in its viable tree.
This is the winner-domain transport used by suffix comparison. -/
theorem reset_winner_voter_tree
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u)
    {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocks H) C P)
    (haC : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hfC := ((SA.fcRoot_anc_getAnchor hPhi e.readPoint (tr.time j)).mono hPhiU).trans haC
  have hFC := (hPhi.F_anc_fcRoot.mono hPhiU).trans hfC
  have hCt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hP.1.1 hCP hFC
  have hCP' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hCt hCP hP.1.1
  have hfC' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hfC hCt
  obtain ⟨W, hW, hWv, hPW⟩ := hP.2.2
  have hCs : C ∈ SA.voterBlockTree sp e.readPoint ell.frame u := by
    rw [← hes] at hP ⊢
    exact SA.voterBlockTree_anc hr hy hc P hP.1 C hCP'
  exact ⟨hCs, hfC', W, hW, hWv, hCP'.trans hPW⟩

/-- A voter competitor other than the proposal, below a predecessor of its parent, reflects into the
proposer's viable tree. Frozen candidates use guarded relay; current-slot candidates use the
actual proposal's uniqueness. -/
theorem reset_competitor_reflect
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    {Q X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : Q ∈ ellp.frame.tree) (hPQ : P.parent = some Q.root)
    (hXQ : ellp.frame.Anc X Q) (hBP : B ≠ P)
    (hXv : X ∈ ellp.frame.viableHeads)
    (hBX : B.parent = some X.root)
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  obtain ⟨-, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hXt : X ∈ ellp.frame.tree := SA.mem_of_anc hXQ hQt
  have hXB : Anc (tr.HonestBlocks H) X B := .single ⟨hPhiU hXt, hPsiU hB.1.1, hBX⟩
  have hFB := ((hPhi.rooted.2 X hXt).mono hPhiU).trans hXB
  have hBt : B ∈ ellp.frame.tree := by
    rcases hB.1.2 with hfz | ⟨P', hP't, hP's, hBP'⟩
    · exact reset_frozen_frame hp hc hP.1 hy hci hti hcy hg hB.1.1 hfz hFB
    · obtain rfl := reset_proposal_frame_unique hp hP (by omega) hy hcy.1 hP't hP's
      have hBQ : Anc (tr.HonestBlocks H) B Q := by
        rcases Relation.ReflTransGen.cases_tail (hBP'.mono hPsiU) with heq | ⟨Y, hBY, hY⟩
        · exact absurd heq.symm hBP
        obtain rfl : Y = Q := hr.coherent.1 hY.1 (hPhiU hQt)
          (Option.some_injective _ (hY.2.2.symm.trans hPQ))
        exact hBY
      exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hQt hBQ hFB
  have hfB := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem
    (((hPhi.fcRoot_anc_viableHeads X hXv).mono hPhiU).trans hXB) hBt
  refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
  rw [Compose.frame_of_projAC hp.run hP.1 hci] at hXv hBt ⊢
  have hXBs := Compose.honest_held_anc hp.run hp.noColl hP.1 hXB hBt.1
  exact ⟨hBt.1, hBt.2, hXv.2.2.1.trans hXBs,
    le_trans hXv.2.2.2 (Compose.honest_held_height hp.run hp.noColl hP.1 hXBs).1⟩

/-- Finite winner transport along the viable proposal chain. -/
theorem ResetPremisesUpTo.reset_winner_voter_tree {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u)
    {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocks H) C P)
    (haC : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hfC := ((SA.fcRoot_anc_getAnchor hPhi e.readPoint (tr.time j)).mono hPhiU).trans haC
  have hFC := (hPhi.F_anc_fcRoot.mono hPhiU).trans hfC
  have hCt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hP.1.1 hCP hFC
  have hCP' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hCt hCP hP.1.1
  have hfC' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hfC hCt
  obtain ⟨W, hW, hWv, hPW⟩ := hP.2.2
  have hCs : C ∈ SA.voterBlockTree sp e.readPoint ell.frame u := by
    rw [← hes] at hP ⊢
    exact SA.voterBlockTree_anc hr hy hc P hP.1 C hCP'
  exact ⟨hCs, hfC', W, hW, hWv, hCP'.trans hPW⟩

/-- Finite competitor reflection uses only guarded frozen transport and actual uniqueness. -/
theorem ResetPremisesUpTo.reset_competitor_reflect {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hib : tr.time i ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {Q X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : Q ∈ ellp.frame.tree) (hPQ : P.parent = some Q.root)
    (hXQ : ellp.frame.Anc X Q) (hBP : B ≠ P)
    (hXv : X ∈ ellp.frame.viableHeads) (hBX : B.parent = some X.root)
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨_, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hXt : X ∈ ellp.frame.tree := SA.mem_of_anc hXQ hQt
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
      exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hQt hBQ hFB
  have hfB := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem
    (((hPhi.fcRoot_anc_viableHeads X hXv).mono hPhiU).trans hXB) hBt
  refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
  rw [Compose.frame_of_projAC hp.run hpH hci] at hXv hBt ⊢
  have hXBs := Compose.honest_held_anc hp.run hp.noColl hpH hXB hBt.1
  exact ⟨hBt.1, hBt.2, hXv.2.2.1.trans hXBs,
    le_trans hXv.2.2.2 (Compose.honest_held_height hp.run hp.noColl hpH hXBs).1⟩

/-- A best child on the proposal-parent path stays best at the voter. The winner is
transported through the viable proposal, while competitors reflect through guarded relay. -/
theorem reset_suffix_best
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPv : P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : d.head ∈ ellp.frame.tree) (hXQ : ellp.frame.Anc X d.head)
    (hne : X ≠ d.head) (hXv : X ∈ ellp.frame.viableHeads)
    (hCQ : ellp.frame.Anc C d.head)
    (haX : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X)
    (hC : SA.IsBest sp (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s B} C) :
    SA.IsBest sp (SA.goldfishScore sp elly.frame
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some X.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  obtain ⟨-, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨heq, hvot, hsup⟩ := reset_views_agree hp hc hP hci hcall hd hti hpay hy hcy hes
    hPv.1.1 hg hgi hgj
  have hQP : Anc (tr.HonestBlocks H) d.head P :=
    .single ⟨hPhiU hQt, hPsiU hPv.1.1, hPQ⟩
  have hXC : Anc (tr.HonestBlocks H) X C :=
    .single ⟨hPhiU (SA.mem_of_anc hXQ hQt), hPhiU hC.1.1.1, hC.1.2.1⟩
  have hCy := reset_winner_voter_tree hp hy hcy hes hPv
    ((hCQ.mono hPhiU).trans hQP) (haX.trans hXC)
  have hCs : C.slot < s + 1 := by
    have h1 := (Anc.slot_le hPhi.coherent hCQ).1
    have h2 := hr.coherent.2 d.head (hPhiU hQt) P (hPsiU hPv.1.1) hPQ
    have hPs := hP.2.2.2.2.1
    omega
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  apply SA.isBest_transfer hXv (by omega) hvot ?_ (fun B hB => hB.1)
    (fun B hB => hB.1.1) hCy ?_ hC
  · intro B hBp hBy
    simp only [SA.goldfishScore, heq, hsup B hBp hBy]
  · intro B hB hBX
    have hBP : B ≠ P := by
      rintro rfl
      exact hne (hr.coherent.1 (hPhiU (SA.mem_of_anc hXQ hQt)) (hPhiU hQt)
        (Option.some_injective _ (hBX.symm.trans hPQ)))
    exact reset_competitor_reflect hp hc hP hci hti hy hcy hgi hQt hPQ hXQ hBP hXv hBX hB

/-- Finite best-child transfer along the proposal-parent suffix. -/
theorem ResetPremisesUpTo.reset_suffix_best {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPv : P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : d.head ∈ ellp.frame.tree) (hXQ : ellp.frame.Anc X d.head)
    (hne : X ≠ d.head) (hXv : X ∈ ellp.frame.viableHeads)
    (hCQ : ellp.frame.Anc C d.head)
    (haX : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X)
    (hC : SA.IsBest sp (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s B} C) :
    SA.IsBest sp (SA.goldfishScore sp elly.frame
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some X.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨_, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨heq, hvot, hsup⟩ := hp.reset_views_agree hc hpH hdesignated hactual hPs
    hci hcall hd hti hpay hy hcy hes hib hjb hPv.1.1 hg hgi hgj hjoi hjoj
  have hQP : Anc (tr.HonestBlocks H) d.head P :=
    .single ⟨hPhiU hQt, hPsiU hPv.1.1, hPQ⟩
  have hXC : Anc (tr.HonestBlocks H) X C :=
    .single ⟨hPhiU (SA.mem_of_anc hXQ hQt), hPhiU hC.1.1.1, hC.1.2.1⟩
  have hCy := hp.reset_winner_voter_tree hy hcy hes hPv
    ((hCQ.mono hPhiU).trans hQP) (haX.trans hXC)
  have hCs : C.slot < s + 1 := by
    have h1 := (Anc.slot_le hPhi.coherent hCQ).1
    have h2 := hr.coherent.2 d.head (hPhiU hQt) P (hPsiU hPv.1.1) hPQ
    omega
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  apply SA.isBest_transfer hXv (by omega) hvot ?_ (fun B hB => hB.1)
    (fun B hB => hB.1.1) hCy ?_ hC
  · intro B hBp hBy
    simp only [SA.goldfishScore, heq, hsup B hBp hBy]
  · intro B hB hBX
    have hBP : B ≠ P := by
      rintro rfl
      exact hne (hr.coherent.1 (hPhiU (SA.mem_of_anc hXQ hQt)) (hPhiU hQt)
        (Option.some_injective _ (hBX.symm.trans hPQ)))
    exact hp.reset_competitor_reflect hc hpH hdesignated hactual hPs hci hti hy hcy
      hib hgi hjoi hQt hPQ hXQ hBP hXv hBX hB

/-- Once the proposal parent is viable in both frames, an old child cannot become eligible
at the voter: guarded view agreement preserves its lack of a strict majority. -/
theorem reset_old_child_ineligible
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hQt : d.head ∈ ellp.frame.tree) (hQv : d.head ∈ ellp.frame.viableHeads)
    (hQvy : d.head ∈ elly.frame.viableHeads)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s + 1) :
    ¬ SA.goldfishEligible sp elly.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  have hPhi := (SA.frameIn_of_callAt hr hP.1 hci).1
  have hBP : B ≠ P := by
    have hPs := hP.2.2.2.2.1
    rintro rfl
    omega
  have hBv := reset_competitor_reflect hp hc hP hci hti hy hcy hgi hQt hPQ
    .refl hBP hQv hBQ hB
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  set T := ellp.frame.viableTree ellp.frame.tree
  have hT : T ⊆ ellp.frame.tree := fun _ h => h.1
  have hhead : d.head = SA.ghost sp T
      (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      (SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
      ellp.frame.tree.ncard d.start := by
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot, hcast]
    rfl
  have hstop := SA.ghost_stopped hPhi.coherent hT (hPhi.finite.subset hT)
    (sc := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
    (el := SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
    (Set.ncard_le_ncard hT hPhi.finite) d.start
  rw [← hhead] at hstop
  obtain ⟨heq, hvot, hsup⟩ := reset_views_agree hp hc hP hci hcall hd hti hpay hy hcy hes
    hPy hg hgi hgj
  have hsj : sp.slot (tr.time j) = s + 1 :=
    ((SA.castAt_spec hr hy hcy).2.1).symm.trans hes
  rintro (h | h | h)
  · exact h ⟨d.head, hQvy, hBQ⟩
  · omega
  · have hmaj : (SA.voters (SA.View.ofLists pay).votes).ncard <
        2 * SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s B := by
      simpa only [SA.goldfishScore, hvot, heq, hsup B hBv.1 hB.1.1] using h
    exact hstop (SA.exists_isBest hPhi
      (S := {X | X ∈ T ∧ X.parent = some d.head.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s X})
      (fun X hX => hT hX.1) ⟨B, hBv, hBQ, Or.inr (Or.inr hmaj)⟩ _)

/-- Finite old-child exclusion preserves the proposal call's strict-majority test. -/
theorem ResetPremisesUpTo.reset_old_child_ineligible {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hQt : d.head ∈ ellp.frame.tree) (hQv : d.head ∈ ellp.frame.viableHeads)
    (hQvy : d.head ∈ elly.frame.viableHeads)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s + 1) :
    ¬ SA.goldfishEligible sp elly.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  have hPhi := (SA.frameIn_of_callAt hr hpH hci).1
  have hBP : B ≠ P := by rintro rfl; omega
  have hBv := hp.reset_competitor_reflect hc hpH hdesignated hactual hPs hci hti hy hcy
    hib hgi hjoi hQt hPQ .refl hBP hQv hBQ hB
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  set T := ellp.frame.viableTree ellp.frame.tree
  have hT : T ⊆ ellp.frame.tree := fun _ h => h.1
  have hhead : d.head = SA.ghost sp T
      (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      (SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
      ellp.frame.tree.ncard d.start := by
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot, hcast]
    rfl
  have hstop := SA.ghost_stopped hPhi.coherent hT (hPhi.finite.subset hT)
    (sc := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
    (el := SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
    (Set.ncard_le_ncard hT hPhi.finite) d.start
  rw [← hhead] at hstop
  obtain ⟨heq, hvot, hsup⟩ := hp.reset_views_agree hc hpH hdesignated hactual hPs
    hci hcall hd hti hpay hy hcy hes hib hjb hPy hg hgi hgj hjoi hjoj
  have hsj : sp.slot (tr.time j) = s + 1 :=
    ((SA.castAt_spec hr hy hcy).2.1).symm.trans hes
  rintro (h | h | h)
  · exact h ⟨d.head, hQvy, hBQ⟩
  · omega
  · have hmaj : (SA.voters (SA.View.ofLists pay).votes).ncard <
        2 * SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s B := by
      simpa only [SA.goldfishScore, hvot, heq, hsup B hBv.1 hB.1.1] using h
    exact hstop (SA.exists_isBest hPhi
      (S := {X | X ∈ T ∧ X.parent = some d.head.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s X})
      (fun X hX => hT hX.1) ⟨B, hBv, hBQ, Or.inr (Or.inr hmaj)⟩ _)

/-- Two distinct viable children force the voter's root below their parent. If that parent
extends every pre-slot high origin, it also reaches the voter's height floor. -/
theorem reset_parent_viable_of_children
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    {Q P B : SA.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocks H)
    (hPQ : P.parent = some Q.root) (hBQ : B.parent = some Q.root) (hBP : B ≠ P)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hBv : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hQold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) O Q) : Q ∈ ell.frame.viableHeads := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hQP : Anc (tr.HonestBlocks H) Q P := .single ⟨hQU, hPhiU hPv.1.1, hPQ⟩
  have hnBP : ¬ Anc (tr.HonestBlocks H) B P := by
    intro h
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hBY, hY⟩
    · exact hBP heq.symm
    obtain rfl : Y = Q := hr.coherent.1 hY.1 hQU
      (Option.some_injective _ (hY.2.2.symm.trans hPQ))
    have h1 := (Anc.slot_le hr.coherent hBY).1
    have h2 := hr.coherent.2 Y hQU B (hPhiU hBv.1.1) hBQ
    omega
  have below : ∀ X, Anc (tr.HonestBlocks H) X B → Anc (tr.HonestBlocks H) X P →
      Anc (tr.HonestBlocks H) X Q := by
    intro X hXB hXP
    rcases Relation.ReflTransGen.cases_tail hXB with heq | ⟨Y, hXY, hY⟩
    · exact False.elim (hnBP (heq ▸ hXP))
    obtain rfl : Y = Q := hr.coherent.1 hY.1 hQU
      (Option.some_injective _ (hY.2.2.symm.trans hBQ))
    exact hXY
  have hfQ := below _ (hBv.2.1.mono hPhiU) (hPv.2.1.mono hPhiU)
  have hQt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hPv.1.1 hQP
    ((hPhi.F_anc_fcRoot.mono hPhiU).trans hfQ)
  have hfQ' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hfQ hQt
  rw [Compose.frame_of_projAC hp.run hy hc.1] at hQt hfQ' ⊢
  exact ⟨hQt.1, hQt.2, hfQ'.mono (fun X hX => hX.1),
    reset_vote_floor_above_old hp hy hR hc hes hQt.1 hQold⟩

/-- Finite sibling viability places their parent above the voter's root and height floor. -/
theorem ResetPremisesUpTo.reset_parent_viable_of_children {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {Q P B : SA.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocks H)
    (hPQ : P.parent = some Q.root) (hBQ : B.parent = some Q.root) (hBP : B ≠ P)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hBv : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hQold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O Q) : Q ∈ ell.frame.viableHeads := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hQP : Anc (tr.HonestBlocks H) Q P := .single ⟨hQU, hPhiU hPv.1.1, hPQ⟩
  have hnBP : ¬ Anc (tr.HonestBlocks H) B P := by
    intro h
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hBY, hY⟩
    · exact hBP heq.symm
    obtain rfl : Y = Q := hr.coherent.1 hY.1 hQU
      (Option.some_injective _ (hY.2.2.symm.trans hPQ))
    have h1 := (Anc.slot_le hr.coherent hBY).1
    have h2 := hr.coherent.2 Y hQU B (hPhiU hBv.1.1) hBQ
    omega
  have below : ∀ X, Anc (tr.HonestBlocks H) X B → Anc (tr.HonestBlocks H) X P →
      Anc (tr.HonestBlocks H) X Q := by
    intro X hXB hXP
    rcases Relation.ReflTransGen.cases_tail hXB with heq | ⟨Y, hXY, hY⟩
    · exact False.elim (hnBP (heq ▸ hXP))
    obtain rfl : Y = Q := hr.coherent.1 hY.1 hQU
      (Option.some_injective _ (hY.2.2.symm.trans hBQ))
    exact hXY
  have hfQ := below _ (hBv.2.1.mono hPhiU) (hPv.2.1.mono hPhiU)
  have hQt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hPv.1.1 hQP
    ((hPhi.F_anc_fcRoot.mono hPhiU).trans hfQ)
  have hfQ' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hfQ hQt
  rw [Compose.frame_of_projAC hp.run hy hc.1] at hQt hfQ' ⊢
  exact ⟨hQt.1, hQt.2, hfQ'.mono (fun X hX => hX.1),
    hp.reset_vote_floor_above_old hy hR hc hes hjb hQt.1 hQold⟩

/-- At the proposal parent, the actual proposal is the only eligible child and its own
children are ineligible. Parent viability is derived separately for each old competitor. -/
theorem reset_stop_at_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPv : P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hQt : d.head ∈ ellp.frame.tree) (hQv : d.head ∈ ellp.frame.viableHeads) :
    (P ∈ {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ elly.frame.viableTree
          (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp (SA.goldfishScore sp elly.frame
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun
  have hPhiU := (SA.frameIn_of_callAt hr hP.1 hci).2
  have hPsiU := (SA.frameIn_of_callAt hr hy hcy.1).2
  have hng : ∀ B ∈ elly.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hpar hgen
    have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
    have he := hr.coherent.1 (hPsiU hB) ⟨y, hy, j, hG⟩ hgen
    rw [he] at hpar
    exact hpar (by simp [Params.genesisBlock])
  have hprop : P.proposer ∈ H := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hprop, -⟩ :=
      honestProposalRun_of_ready hp.run hp.noColl hP
    rw [hprop, ← hP.2.1]
    exact hP.1
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  rw [← hcast]
  apply SA.stop_core hac hy hcy hes hP.2.2.2.2.1 hPQ hprop hng hPv
  intro B hB hBQ hBs
  have hBP : B ≠ P := by
    have hPs := hP.2.2.2.2.1
    rintro rfl
    omega
  have hQvy := reset_parent_viable_of_children hp hy hR hcy hes (hPhiU hQt) hPQ hBQ hBP
    hPv hB (fun x r l O ho ht => crossing_below_proposal_parent hp hc hP hR hci hcall hd
      hti hPQ ho ht .refl)
  rw [hcast]
  exact reset_old_child_ineligible hp hc hP hci hcall hd hti hpay hPQ hy hcy hes hPv.1.1
    hg hgi hgj hQt hQv hQvy hB hBQ hBs

/-- Finite stopping at the actual proposal after excluding every old sibling. -/
theorem ResetPremisesUpTo.reset_stop_at_parent {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1) (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPv : P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hQt : d.head ∈ ellp.frame.tree) (hQv : d.head ∈ ellp.frame.viableHeads) :
    (P ∈ {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ elly.frame.viableTree
          (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp (SA.goldfishScore sp elly.frame
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun
  have hPhiU := (SA.frameIn_of_callAt hr hpH hci).2
  have hPsiU := (SA.frameIn_of_callAt hr hy hcy.1).2
  have hng : ∀ B ∈ elly.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hpar hgen
    have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
    have he := hr.coherent.1 (hPsiU hB) ⟨y, hy, j, hG⟩ hgen
    rw [he] at hpar
    exact hpar (by simp [Params.genesisBlock])
  have hprop : P.proposer ∈ H := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hprop, _⟩ :=
      honestProposalRun_of_proposesAt hp.run hp.noColl hpH hdesignated hactual hPs
    rw [hprop, ← hdesignated]
    exact hpH
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  rw [← hcast]
  apply SA.stop_core hac hy hcy hes hPs hPQ hprop hng hPv
  intro B hB hBQ hBs
  have hBP : B ≠ P := by rintro rfl; omega
  have hQvy := hp.reset_parent_viable_of_children hy hR hcy hes hjb (hPhiU hQt) hPQ hBQ
    hBP hPv hB (fun x r l O ho ht _ => hp.reset_proposal_passes hc hpH hR hci hcall hd
      hti hib O ⟨x, r, l, ho, ht⟩)
  rw [hcast]
  exact hp.reset_old_child_ineligible hc hpH hdesignated hactual hPs hci hcall hd hti
    hpay hPQ hy hcy hes hib hjb hPv.1.1 hg hgi hgj hjoi hjoj hQt hQv hQvy hB hBQ hBs

end Consensus.Goldilocks.Healing

end

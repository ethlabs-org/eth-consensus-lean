module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree

public section

/-! # Goldilocks Healing: post-reset duty suppliers

The source and transport facts are in `Outcome.Foundation`; the proposal pivot is in
`Outcome.Pivot`. The duty conclusions here may use both without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- Actual honest proposals are unique in honest frames at their positive slot.
This uses no payload-support clause of `ReadyProposal`. -/
theorem reset_proposal_frame_unique
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hPprop, -, ja, -, hacc, -⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hPprop hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hr hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hQf : SA.HonestFrameBlock tr.projAC H Q := ⟨y, hy, j, ell, hcall, hQ⟩
  have hroot : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
    obtain rfl := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcall).2 hQ)
      ⟨y, hy, j, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block P Q ⟨p, hP.1, ja, ellp, hcp, hPm⟩ hQf (hPprop ▸ hP.1)
    (by rw [hPprop, hac.honest.proposer Q hQf hroot, hQu, hP.2.1])
    (by rw [hP.2.2.2.2.1, hQu])).symm

/-- The actual proposal reaches a voter's frame above its finalization root. -/
theorem reset_proposal_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k j u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F P) : P ∈ ell.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts u + sp.Δ
  · obtain ⟨Q, hQ, hQs, -⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs
    exact (reset_proposal_frame_unique hp hP hu hy hcy.1 hQ hQs) ▸ hQ
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ja, -, hacc, hta⟩ :=
      honestProposalRun_of_ready hp.run hp.noColl hP
    rw [← hP.2.1] at hacc
    exact reset_accept_frame hp hc hP.1 hy hacc hcy.1 hg
      (by change tr.time ja = sp.ts u at hta; rw [hta]; exact not_lt.mp hearly) hF

/-- Payload support is transported only above the receiver's `F`. Early votes use their
actual readiness witness; deadline votes use guarded relay, not ready-proposal support. -/
theorem reset_support_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    {v : SA.Vote sp.n} (hv : v ∈ pay.2) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ellp.frame.tree) (hBr : B.root = v.head)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs hsup
    obtain rfl := reset_proposal_frame_unique hp hP (by omega) hy hcy.1 hQ hQs
    have hslot : sp.slot (tr.time i) = s + 1 := by
      rw [hti]; exact SA.slot_of_mem sp _ le_rfl ((SA.ts_lt_iff sp).mpr (by omega))
    have hpay' : pay = SA.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
      unfold SA.acProposal at hd
      split_ifs at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rw [← hd.2, hslot]
      congr 1
      push_cast
      ring
    have hvs : v.slot + 1 = s + 1 := by
      rw [hpay'] at hv
      simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
        List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [SA.state_pool_slot sp hr hP.1 i s v hv.1]
    obtain ⟨B', hB', hBr', -⟩ := hsup v (by rw [SA.blockSupport, hpay]; exact hv) hvs
    rwa [hr.coherent.1 ((SA.frameIn_of_callAt hr hP.1 hci).2 hB)
      ((SA.frameIn_of_callAt hr hy hcy.1).2 hB') (hBr.trans hBr'.symm)]
  · exact reset_frame_relay hp hc hP.1 hy hci hcy.1 hB hg
      (by rw [hti]; exact not_lt.mp hearly) hF

/-- A pre-freeze voter block reaches the proposal frame under the proposer's `F` guard. -/
theorem reset_frozen_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) (hy : y ∈ H) {i j s : Nat}
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : SA.CastAt tr.projAC y j elly e)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < SA.ETime.of (SA.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocks H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  rw [SA.readPoint_blockStamp_eq hr hy hcy] at hst
  rcases stamp_origin hr hy j elly hcy.1 B hB with hgen | ⟨q, -, ellq, hcq, hBq, hstamp⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH i ellp hci
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcy.1).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hpH hci).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < SA.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    apply reset_frame_relay hp hc hy hpH hcq hci hBq hg ?_ hF
    rw [hti]
    simp only [SA.freeze, SA.SAParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith

/-- Guarded incidence gives view agreement on common held targets. Proposal heldness at the
voter remains explicit; this lemma does not supply viable-tree membership. -/
theorem reset_views_agree
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (sp.ts s) (sp.ts (s + 1 : Nat)) hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 ((SA.le_gbar g).trans hg))
  apply SA.view_agree hac hP.1 hy hP.2.1 ⟨hci, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hP.2.2.2.2.1, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact reset_frozen_frame hp hc hP.1 hy hci hti hcy hgi hB hstamp hF
  · intro v hv B hB hBr hF
    exact reset_support_frame hp hc hP hci hd hti hpay hy hcy hes hgj hv hB hBr hF

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

/-- **The joined duty, unanimity** (§23; phase-service §10, "Join with RN/RU"): under the reset
premises and `Catch(2Δ)`, every honest vote of the slot `u` of an honest ready proposal `P` with
`t_u ≥ R` is `P`. -/
theorem ready_unanimous (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) : Unanimous tr H u P := by
  sorry

/-- **The joined duty at the update** (§23, §17 "Exact remaining premise"; phase-service §10;
restated with the healing orb, workbench#30-style): under the reset premises and `Catch(2Δ)`, for
an honest ready proposal `P` of slot `u` with `t_u ≥ R` and every honest node `z` running its
update of slot `u` (at `t_u + 6Δ`, joined, cut `kz`): either the result is `P`, not vetoed, its
fast test selects `P`, and every FG source `z` returns at a cut at or after the update, at its
time, extends `P`; or some honest node has an actual `ac_to_fg` report `C` by then that extends
`P` with a greater state height than `P` in the reporter's state (a higher source; `P` need not
be an entry). -/
theorem ready_update (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) {z : Fin sp.n} (hz : z ∈ H) {kz : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC z kz u ℓ) :
    (SA.getConfirmation sp (tr.projAC.state z kz) ℓ.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state z kz).locks ℓ.frame (tr.time kz) P ∧
      SA.fastSelect sp (tr.projAC.state z kz) ℓ.frame u P = some P ∧
      ∀ k' ℓ' C, kz ≤ k' → SA.ToFGAt tr.projAC z k' ℓ' C → tr.time k' = tr.time kz →
        Anc (tr.HonestBlocks H) P C) ∨
    ∃ z' ∈ H, ∃ r ℓ' C, SA.ToFGAt tr.projAC z' r ℓ' C ∧ tr.time r ≤ tr.time kz ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z' r).fg.σ P.root).h < ((tr.state z' r).fg.σ C.root).h := by
  sorry

/-- **Report coverage** (workbench#30 `entry-rows-exact.md` §2, the exact acquisition supplier
of `entry_rows`): for an honest ready proposal `P` of slot `u` with `t_u ≥ R`, by
`d = t_u + 6Δ` either every honest node has an actual `ac_to_fg` report `C` extending `P` (a
report that suppresses a later one counts at its own cut), or some honest node has an actual
report `C` extending `P` of a greater state height than `P` (a higher source). (`ready_update`'s
returned-source clause is vacuous when nothing is returned; this supplier quantifies over every
honest node's actual reports.) -/
theorem report_cover (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) :
    (∀ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  sorry

end Consensus.Goldilocks.Healing

end

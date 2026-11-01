module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireSources
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
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun
  have hDelta := sp.toParams.hΔ
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  have hcut := lt_cutZ (sp := sp) g
  have hga0 := SA.gbar_nonneg g
  have ha0 : 0 ≤ a := by linarith
  have ha : sp.ts (sp.slot a) ≤ a := by
    exact (SA.ts_le_iff_le_slot sp ha0 _).2 (by omega)
  have hu : sp.slot a + 2 * sp.k + 5 ≤ u := by
    rw [drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hg : SA.gbar g ≤ sp.ts s := by
    have hle : sp.ts (sp.slot a) + 4 * sp.Δ ≤ sp.ts s := by
      have hs : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts s :=
        (SA.ts_le_iff sp).2 (by omega)
      simpa only [SAParams.ts, mul_add, mul_one] using hs
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have he : sp.ts ((sp.slot a : Int) + 1) = sp.ts (sp.slot a) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    rw [he] at ha'
    linarith
  have hgu : SA.gbar g + 2 * sp.Δ ≤ sp.ts (s + 1 : Nat) := by
    have hs : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith
  obtain ⟨-, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, -, -, hpay, -⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := reset_pivot hp hc hP hR hci hcall hd hti hPQ
  have hPhi := (SA.frameIn_of_callAt hr hP.1 hci).1
  have hPhiU := (SA.frameIn_of_callAt hr hP.1 hci).2
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  set W₁ := SA.ghost sp (ellp.frame.viableTree ellp.frame.tree)
    (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
    (SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s) with hW₁
  have hTp : ellp.frame.viableTree ellp.frame.tree ⊆ ellp.frame.tree := fun _ h => h.1
  have hQ : d.head = W₁ ellp.frame.tree.ncard d.start := by
    rw [hW₁]
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot, hcast]
    rfl
  have hstop₀ := SA.ghost_stopped hPhi.coherent hTp (hPhi.finite.subset hTp)
    (sc := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
    (el := SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
    (Set.ncard_le_ncard hTp hPhi.finite) d.start
  rw [← hW₁] at hstop₀
  have hstop₁ := hstop₀
  rw [← hQ] at hstop₁
  have hW₁add : ∀ a b x, W₁ (a + b) x = W₁ b (W₁ a x) := fun a b x => by
    rw [hW₁]; exact SA.ghost_add a b x
  have hstopQ : ∀ m, W₁ m d.head = d.head := fun m => by
    have h0 : W₁ 0 d.head = d.head := rfl
    rw [hW₁] at h0 ⊢
    exact (SA.ghost_fuel_stable (f := 0) (Nat.zero_le m)
      (by rw [h0]; exact hstop₁)).trans h0
  have hXQend : ∀ {X}, ellp.frame.Anc D X → ellp.frame.Anc X d.head →
      W₁ ellp.frame.tree.ncard X = d.head := by
    intro X hDX hXQ
    obtain ⟨kx, -, hkx⟩ := SA.ghost_visits hPhi.coherent hTp _ (hsD.trans hDX) (hQ ▸ hXQ)
    rw [← hW₁] at hkx
    have hadd := hW₁add kx ellp.frame.tree.ncard d.start
    rw [hkx] at hadd
    rw [← hadd, add_comm, hW₁add, ← hQ, hstopQ]
  intro y hy j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hv hes
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : SA.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x hx j' hj' e' hv' hs' => ih j' hj' x hx e' hv' hs'
    have hPsi := (SA.frameIn_of_callAt hr hy hcy.1).1
    have hPsiU := (SA.frameIn_of_callAt hr hy hcy.1).2
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
      have := (SA.castAt_spec hr hy hcy).2.1
      rw [hes] at this
      exact_mod_cast this.le
    have hgj := hgu.trans hjt
    have hroot := reset_vote_root_below_proposal hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
    have hPy := reset_proposal_frame hp hc hP (by omega) hy hcy hes hgj
      ((hPsi.F_anc_fcRoot.mono hPsiU).trans hroot)
    have hPv := reset_proposal_viable hp hc hP hR hci hcall hd hti hPQ hy hcy hes hPy hE
    obtain ⟨hstep₀, hP₀⟩ := reset_stop_at_parent hp hc hP hR hci hcall hd hti hpay hPQ hy
      hcy hes hPv hg (hti ▸ hgu) hgj hQt (hviab _ hDQ .refl)
    obtain ⟨X, hXc, haX, hXend⟩ := hvot y hy j elly e hcy hes hE
    rw [hcast] at hXend
    set W₂ := SA.ghost sp
      (elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
      (SA.goldfishScore sp elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      (SA.goldfishEligible sp elly.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s) with hW₂
    have hTy : elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ⊆
        elly.frame.tree := fun _ h => h.1.1
    have hXP : ∃ fX, W₂ fX X = P := by
      rcases hXc with rfl | ⟨hDX, hXQ⟩
      · exact ⟨0, rfl⟩
      refine ⟨ellp.frame.tree.ncard + 1, SA.ghost_follow _ X (hXQend hDX hXQ) hstop₁ ?_
        hstep₀ hP₀⟩
      intro m hm hne C hC
      by_cases hXe : X = d.head
      · exact absurd (by rw [hXe]; exact hstopQ m) hne
      have hXt := (Anc.mem hXQ hXe).1
      have hXm : ellp.frame.Anc X (W₁ m X) := SA.anc_ghost hTp m hXt
      have hmem : W₁ m X ∈ ellp.frame.tree := by
        rcases eq_or_ne (W₁ m X) X with he | he
        · rw [he]; exact hXt
        · exact (Anc.mem hXm (Ne.symm he)).2
      have hend : W₁ (ellp.frame.tree.ncard - m) (W₁ m X) = d.head := by
        rw [← hW₁add, Nat.add_sub_cancel' hm.le]
        exact hXQend hDX hXQ
      have hQm : ellp.frame.Anc (W₁ m X) d.head :=
        hend ▸ SA.anc_ghost hTp _ hmem
      have hCQ : ellp.frame.Anc C d.head := by
        have hw := SA.walkEnd_ghost
          (sc := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
          (el := SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s)
          hPhi.coherent hTp (hPhi.finite.subset hTp)
          (Set.ncard_le_ncard hTp hPhi.finite) d.start
        rw [← hW₁, ← hQ] at hw
        obtain ⟨f, hf, -⟩ := SA.walkEnd_iff.1
          (hw.of_anc hPhi.coherent hTp (hsD.trans (hDX.trans hXm)) hQm)
        cases f with
        | zero => exact absurd hf hne
        | succ f =>
          have h1 : W₁ 1 (W₁ m X) = C := SA.ghost_succ_of_best 0 _ hC
          rw [hW₁] at h1
          rw [show f + 1 = 1 + f by omega, SA.ghost_add, h1] at hf
          exact hf ▸ SA.anc_ghost hTp f (hTp hC.1.1)
      exact reset_suffix_best hp hc hP hci hcall hd hti hpay hPQ hy hcy hes hPv hg
        (hti ▸ hgu) hgj hQt hQm hne (hviab _ (hDX.trans hXm) hQm) hCQ
        ((haX.mono hPsiU).trans (hXm.mono hPhiU)) hC
    obtain ⟨fX, hfX⟩ := hXP
    have hspec := (SA.castAt_spec hr hy hcy).2.2.2
    rw [hes, hcast] at hspec
    rw [hspec]
    congr 1
    change W₂ elly.frame.tree.ncard (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) = P
    obtain ⟨ky, -, hky⟩ := SA.ghost_visits hPsi.coherent hTy _ haX hXend
    have hP₂ : W₂ (ky + fX) (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) = P := by
      rw [hW₂, SA.ghost_add, ← hW₂]
      rw [← hW₂] at hky
      rw [hky]; exact hfX
    have hstop₂ := SA.ghost_stopped hPsi.coherent hTy (hPsi.finite.subset hTy)
      (sc := SA.goldfishScore sp elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      (el := SA.goldfishEligible sp elly.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      (Set.ncard_le_ncard hTy hPsi.finite) (SA.getAnchor sp e.readPoint elly.frame (tr.time j))
    rw [← hW₂] at hstop₂
    have hmax₁ := SA.ghost_fuel_stable (le_max_left elly.frame.tree.ncard (ky + fX)) hstop₂
    have hmax₂ := SA.ghost_fuel_stable (le_max_right elly.frame.tree.ncard (ky + fX)) (hP₂ ▸ hP₀)
    rw [← hW₂] at hmax₁ hmax₂
    rw [← hmax₁, hmax₂, hP₂]

/-- Every honest node executes the joined update and immediately following joined to-FG call
at the coverage deadline. This supplies calls, not a nonempty returned report. -/
theorem reset_update_toFG_calls
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat} (hu : SA.gbar g ≤ sp.ts u) :
    ∃ j ell ell', SA.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  have hS := healthy_base_of_reset_catch hp hc
  have hDelta := sp.toParams.hΔ
  have hg0 := SA.gbar_nonneg g
  obtain ⟨j, x, hg⟩ := hp.run.tick_of_awake y hy (sp.ts u + 6 * sp.Δ)
    (by linarith) ⟨4 * (u : Int) + 6, by simp only [SAParams.ts]; ring⟩
    (hp.healthy.2.1 y hy _ (by change SA.gbar g ≤ _; linarith))
  have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
    SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith)
      (by simp only [SAParams.ts]; push_cast; linarith)
  have hnP : ¬ Node.Proposes proposer y (sp.ts u + 6 * sp.Δ) := by
    rintro ⟨-, h, -⟩
    rw [show sp.toParams.slotOf (sp.ts u + 6 * sp.Δ) = u + 1 from hslot,
      sp.slotTime_eq] at h
    simp only [SAParams.ts] at h
    push_cast at h
    linarith
  obtain ⟨hcj, htj⟩ := tick_first_cut hg
  have h1 : (Node.exec proposer dg y (tr.state y j) (sp.ts u + 6 * sp.Δ) (.tick x)).2[1]? =
      some (Node.acToFG
        (Node.tickStep proposer dg y (tr.state y j) (sp.ts u + 6 * sp.Δ) x .acTick).1
        (sp.ts u + 6 * sp.Δ)).2.1 := by
    change (Node.onTick proposer dg y (tr.state y j) (sp.ts u + 6 * sp.Δ) x).2[1]? = _
    rw [onTick_eq]
    simp only [Node.tickStep, hnP, ↓reduceIte]
    split <;> simp [Node.acToFG, Node.acCall]
  obtain ⟨hk', hlabel⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 1 hk'
  obtain ⟨ell', hcj1, hcall', htj1⟩ : ∃ ell' : ACLabel (goldilocksNode sp ro),
      tr.CallAt y (j + 1) (.ac ell') ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ :=
    ⟨_, ⟨hn, hl.trans (congrArg some hlabel)⟩, rfl, ht⟩
  obtain ⟨ell, hcjAC, hcall⟩ : ∃ ell : ACLabel (goldilocksNode sp ro),
      tr.projAC.CallAt y j ell ∧ ell.call = .tick :=
    ⟨_, Compose.projAC_callAt.2 hcj, rfl⟩
  have hjoin : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      SA.joined sp (tr.projAC.state y i) (tr.time i) := by
    intro i hi
    apply hS.joined_state hy i
    change SA.gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
    rw [hi, hslot]
    simpa using hu
  refine ⟨j, ell, ell', ⟨hcjAC, hcall, htj, hjoin j htj⟩,
    Compose.projAC_callAt.2 hcj1, hcall', htj1, ?_, hjoin (j + 1) htj1⟩
  rw [(hp.run.cutLaw y hy (j + 1) _ hcj1).1,
    Compose.frame_of_projAC hp.run hy hcjAC, tr.state_succ_of_call hcj]
  unfold Node.frame
  rw [(hp.run.cutLaw y hy j _ hcj).2.2.1]

/-- A deepest candidate extending a non-genesis block gives an actual report by this call's
time, including the historical report that suppresses a new return. -/
theorem report_of_deepest_candidate
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : SA.joined sp (tr.projAC.state y j) (tr.time j))
    {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPg : P.root ≠ sp.genesisRoot)
    (hC : SA.deepest ell.frame (SA.toFGCandidates sp (tr.projAC.state y j)
      ell.frame (tr.time j)) = some C) (hPC : ell.frame.Anc P C) :
    ∃ r ell' R, SA.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  by_cases hrep : SA.AncR ell.frame C (tr.projAC.state y j).fgReported
  · obtain ⟨R, hRt, hRr, hCR⟩ := hrep
    have hPR : ell.frame.Anc P R := hPC.trans hCR
    rcases fgReported_origin hr hy j with hgen | ⟨r, hrj, ell', R', hto, hR'r⟩
    · have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
      have he := hr.coherent.1 (hPhiU hRt) ⟨y, hy, j, hG⟩ (hRr.trans hgen)
      rw [he] at hPR
      rcases Relation.ReflTransGen.cases_tail hPR with heq | ⟨Y, _, hY⟩
      · exact False.elim (hPg (by rw [← heq]; rfl))
      · exact False.elim (Option.some_ne_none _ (hY.2.2.symm.trans rfl))
    have hR't := toFG_mem_tree hp.run hy hto
    obtain rfl : R' = R := hr.coherent.1 ⟨y, hy, r, hR't⟩ (hPhiU hRt)
      (hR'r.trans hRr.symm)
    exact ⟨r, ell', R', hto, hp.run.time_mono hrj.le, hPR.mono hPhiU⟩
  · refine ⟨j, ell, C, ⟨hc, hcall, ?_⟩, le_rfl, hPC.mono hPhiU⟩
    change (SA.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2.1 = some C
    unfold SA.acToFG
    simp only [hjoin, not_true_eq_false, ↓reduceIte, hC, hrep]

/-- Every sufficiently clean older fast or slow source is below the unanimous proposal.
The source need not precede the chosen vote cut: clean-source transfer budgets both times. -/
theorem clean_source_below_ready
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthy_base_of_reset_catch hp hc
  obtain ⟨j, e, hv, hes⟩ := SA.honest_votes_in_slot hS hgu p hP.1
  obtain ⟨ell, hcast⟩ := hv
  obtain ⟨Hd, hHd, hHdr, hBH⟩ := clean_source_votes_before hp hc
    (max (tr.time r) (tr.time j)) hx horig hs (le_max_left _ _) j (le_max_right _ _)
    p hP.1 ell e hcast (hes ▸ hsu)
  have hhead := ready_unanimous hp hc hP hR p hP.1 j e ⟨ell, hcast⟩ hes
  have hPU := (SA.frameIn_of_callAt hS.run.localRun hP.1 hcast.1).2
  obtain ⟨X, hXt, hXr, -⟩ := (Compose.cast_head_fcRoot hS.run.localRun hP.1 hcast).1
  have hXP : X = P := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ja, -, hacc, -⟩ :=
      honestProposalRun_of_ready hp.run hp.noColl hP
    rw [← hP.2.1] at hacc
    obtain ⟨ellp, hcp, hblock⟩ := hacc
    have hPm := (SA.accept_new sp hS.run.localRun hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
    exact hS.run.localRun.coherent.1 (hPU hXt)
      ((SA.frameIn_of_callAt hS.run.localRun hP.1 hcp).2 hPm) (hXr.trans hhead)
  have hDP : Hd = P := hS.run.localRun.coherent.1 hHd (hXP ▸ hPU hXt)
    (hHdr.trans hhead)
  exact hDP ▸ hBH

/-- A fast or slow lock source of the proposal's own label is below the unanimous proposal.
This uses an actual counted honest vote, not the fast lock sought at a later update. -/
theorem same_slot_source_below_ready
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {r : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r u B CV) ∨ SA.SlowLockAt tr.projAC x r u B) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthy_base_of_reset_catch hp hc
  have hU := hS.run.localRun.coherent
  obtain ⟨-, -, _, _, _, _, _, _, _, _, _, _, _, ja, _, hacc, _⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hS.run.localRun hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hPU := (SA.frameIn_of_callAt hS.run.localRun hP.1 hcp).2 hPm
  have below : ∀ z ∈ H, ∀ j e, SA.VoteAt tr.projAC z j e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B → Anc (tr.HonestBlocks H) B P := by
    rintro z hz j e hv hes ⟨Hd, hHd, hHdr, hBH⟩
    have he := hU.1 hHd hPU (hHdr.trans (ready_unanimous hp hc hP hR z hz j e hv hes))
    exact he ▸ hBH
  rcases horig with ⟨CV, hf⟩ | ⟨ell, C, hupd, hC, _, hD, _⟩
  · obtain ⟨z, hz, j, e, hv, hes, hB⟩ := SA.fastLock_honest_vote hS.run hS.two_faulty_lt hx hf
    exact below z hz j e hv hes hB
  · obtain ⟨z, hz, j, e, hv, hes, Hd, hHd, hHdr, hCH⟩ := SA.result_extended hS hgu hx
      hupd.1 (by rw [hupd.2.2.1]; linarith [sp.toParams.hΔ]) hC
    have hPhiU := (SA.frameIn_of_callAt hS.run.localRun hx hupd.1).2
    exact below z hz j e hv hes
      ⟨Hd, hHd, hHdr, ((SA.deepest_mem hD).1.1.2.2.mono hPhiU).trans hCH⟩

/-- At any post-drain call, the viable image of a stored live lock of an older label lies
below the ready proposal. This covers both slow locks and fast locks. -/
theorem ready_old_lock_below
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : drainTime sp a ≤ tr.time j)
    {l : SA.Lock} (hl : l ∈ (tr.projAC.state y j).locks) (hlu : l.slot < u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) P := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hs := drain_live_locks ht _
    ⟨l, hl, L, hL, hLr, hlive, rfl⟩
  change cleanLabel sp a + sp.k + 2 ≤ l.slot at hs
  obtain ⟨r, _, B, horig, X, hX, hXr, hXB⟩ : ∃ r < j, ∃ B,
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot B CV) ∨ SA.SlowLockAt tr.projAC y r l.slot B) ∧
      ∃ X ∈ tr.HonestBlocks H, X.root = l.block ∧ Anc (tr.HonestBlocks H) X B := by
    cases hf : l.fast with
    | false =>
      obtain ⟨r, hrj, B, hslow, hX⟩ := SA.slow_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, B, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, B, CV, hfast, hX⟩ := SA.fast_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, B, Or.inl ⟨CV, hfast⟩, hX⟩
  have hXL : X = L := hr.coherent.1 hX (hPhiU hL) (hXr.trans hLr.symm)
  rw [hXL] at hXB
  exact ((SA.anc_viableAncestor ell.frame L).mono hPhiU).trans
    (hXB.trans (clean_source_below_ready hp hc hP hR hgu hy horig hs hlu))

/-- At the deadline, only next-slot optimistic sources remain beyond the proved old and
same-slot cases. Their compatibility is an explicit obligation, not inferred from unanimity. -/
theorem ready_update_locks_compatible
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y j u ell)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hu.1
  have hDelta := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  have he : L = ell.frame.viableAncestor B := hPhi.coherent.1 hLt
    (SA.viableAncestor_anc hPhi hB).1 hLr.symm
  rw [he]
  by_cases hlu : l.slot < u
  · exact Or.inl (ready_old_lock_below hp hc hP hR hgu hy hu.1
      (by rw [ht]; linarith) hl hlu hlive hB hBr)
  obtain ⟨r, hrj, D, horig, X, hX, hXr, hXD⟩ : ∃ r < j, ∃ D,
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨ SA.SlowLockAt tr.projAC y r l.slot D) ∧
      ∃ X ∈ tr.HonestBlocks H, X.root = l.block ∧ Anc (tr.HonestBlocks H) X D := by
    cases hf : l.fast with
    | false =>
      obtain ⟨r, hrj, D, hs, hX⟩ := SA.slow_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, D, Or.inr hs, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hf, hX⟩ := SA.fast_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hf⟩, hX⟩
  have hXB : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  rw [hXB] at hXD
  have hLD := ((SA.anc_viableAncestor ell.frame B).mono hPhiU).trans hXD
  have hrt : tr.time r ≤ sp.ts u + 6 * sp.Δ := ht ▸ hp.run.time_mono hrj.le
  have hDP : Compatible (tr.HonestBlocks H) D P := by
    by_cases heq : l.slot = u
    · exact Or.inl (same_slot_source_below_ready hp hc hP hR hgu hy (heq ▸ horig))
    have hgt : u < l.slot := by omega
    rcases horig with ⟨CV, ⟨ellr, C, hupd, _⟩ | hop⟩ | ⟨ellr, C, hupd, _⟩
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hts := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith
    · have hsl : sp.slot (tr.time r) = l.slot := hop.choose_spec.choose_spec.2.1
      have hbound : l.slot ≤ u + 1 := by
        have hmono := SA.slot_mono sp (hr.time_nonneg r) hrt
        change sp.slot (tr.time r) ≤ sp.slot (sp.ts u + 6 * sp.Δ) at hmono
        have hs : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
          SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith)
            (by simp only [SAParams.ts]; push_cast; linarith)
        rw [hsl, hs] at hmono
        exact hmono
      exact hnext r hrj D CV (show l.slot = u + 1 by omega ▸ hop)
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hts := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith
  rcases hDP with hDP | hPD
  · exact Or.inl (hLD.trans hDP)
  · exact SA.anc_total hr.coherent hLD hPD

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

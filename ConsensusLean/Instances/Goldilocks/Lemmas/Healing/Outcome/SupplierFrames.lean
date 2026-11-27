module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal and recipient frames

Frame uniqueness, relay and view agreement for the post-reset duty suppliers. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF a : Time}

/-- Same-label raw sources lie below the unanimous operational head via an actual
honest supporter, not via an assumed later successful update. -/
theorem ResetPremisesUpTo.same_slot_source_below_unanimous {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x : Fin sp.n} (hx : x ∈ H) {r u : Nat}
    {B P : AC.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, AC.FastLockAt tr.projAC x r u B CV) ∨ AC.SlowLockAt tr.projAC x r u B)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts u)
    (hPU : P ∈ tr.HonestBlocks H)
    (hun : ∀ z ∈ H, ∀ q e, AC.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root) : Anc (tr.HonestBlocks H) B P := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have below : ∀ z ∈ H, ∀ q ≤ r, ∀ e, AC.VoteAt tr.projAC z q e → e.msg.slot = u →
      AC.VoteExtends (tr.HonestBlocks H) e.msg B → Anc (tr.HonestBlocks H) B P := by
    rintro z hz q hqr e hv hes ⟨D, hD, hDr, hBD⟩
    obtain rfl : D = P := hr.coherent.1 hD hPU
      (hDr.trans (hun z hz q e hv ((hp.run.time_mono hqr).trans hrb) hes))
    exact hBD
  rcases horig with ⟨CV, ⟨ell, C, hupd, hC, hD, _⟩ | hop⟩ | ⟨ell, C, hupd, hC, hD⟩
  · obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := hp.result_supporter hx
      ⟨ell, hupd, hC, rfl⟩ ((AC.deepest_mem hD).1.1.2.2.mono
        (AC.frameIn_of_callAt hr hx hupd.1).2) hrb hts
    exact below z hz q hqr.le e hv hes he
  · obtain ⟨_, z, hz, q, hqr, e, hv, hes, he⟩ :=
      hp.optimistic_supporter hx (slot_gbar_lt_of_cutZ_le hts) hop
    exact below z hz q hqr e hv hes he
  · obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := hp.result_supporter hx
      ⟨ell, hupd, hC, rfl⟩ ((AC.deepest_mem hD).1.1.2.2.mono
        (AC.frameIn_of_callAt hr hx hupd.1).2) hrb hts
    exact below z hz q hqr.le e hv hes he

/-- Held-only finite update selection from actual early-resolved votes of the honest members of
the slot-`u` committee, for a slot `u` after the slot of `ḡ` (CS2 there). The receipt/unanimity
and normalized-lock comparison obligations are explicit; neither full viability nor whole-run
health is used. Only the pool's voters are counted: they are committee members (P). The
post-state records the actual raw write. -/
theorem ResetPremisesUpTo.ready_update_selection_of_pool {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hu1 : sp.slot (AC.gbar g) + 1 ≤ u)
    (hu : AC.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot)
    (hpool : ∀ v ∈ H, v ∈ K.committee u → ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame vote < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P) :
    AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (AC.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hu.1
  let A := tr.projAC.state y j
  have hVK : (AC.voters {v | v ∈ A.pool u}) ⊆ K.committee u := by
    rintro w ⟨v, hv, rfl⟩
    exact hp.hP.1 y hy j u v hv
  have hKvot : K.committee u ∩ H ⊆ (AC.voters {v | v ∈ A.pool u}) ∩ H := fun v hv => by
    obtain ⟨vote, hm, he, -⟩ := hpool v hv.2 hv.1
    exact ⟨⟨vote, hm, he⟩, hv.2⟩
  have hsplitK : (K.committee u ∩ H).ncard + (K.committee u ∩ Hᶜ).ncard = sp.committeeSize := by
    rw [← hp.hsize u]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hsplitV : ((AC.voters {v | v ∈ A.pool u}) ∩ H).ncard +
      (Hᶜ ∩ (AC.voters {v | v ∈ A.pool u})).ncard = (AC.voters {v | v ∈ A.pool u}).ncard := by
    rw [← Set.sdiff_eq_compl_inter]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hKle := Set.ncard_le_ncard hKvot
  have hcs2 := hp.cs2 hu1
  have hFle := Set.ncard_le_ncard (s := Hᶜ ∩ (AC.voters {v | v ∈ A.pool u}))
    (t := K.committee u ∩ Hᶜ) fun w hw => ⟨hVK hw.2, hw.1⟩
  have hVHle := Set.ncard_le_ncard (s := (AC.voters {v | v ∈ A.pool u}) ∩ H)
    (t := K.committee u ∩ H) fun w hw => ⟨hVK hw.1, hw.2⟩
  have hscore : (K.committee u ∩ H).ncard ≤ AC.confirmationScore sp A ell.frame u P := by
    unfold AC.confirmationScore
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro v hv
    obtain ⟨vote, hm, he, hh, hres, huniq⟩ := hpool v hv.2 hv.1
    refine ⟨?_, vote, ⟨hm, hres⟩, he, ?_, P, hPt, hh.symm, .refl⟩
    · rintro ⟨x, hx, z, hz, hne, hxv, hzv⟩
      exact hne ((huniq x hx hxv).trans (huniq z hz hzv).symm)
    · exact_mod_cast AC.state_pool_slotU sp hr.toU hp.run.vstart hy j u vote hm
  have hconf : AC.getConfirmation sp A ell.frame u = some P := by
    unfold AC.getConfirmation
    have hPS : P ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (AC.voters {v | v ∈ A.pool u}).ncard < 2 * AC.confirmationScore sp A ell.frame u B} :=
      ⟨hPt, hPhi.rooted.2 P hPt, by omega⟩
    have hall : ∀ B ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (AC.voters {v | v ∈ A.pool u}).ncard < 2 * AC.confirmationScore sp A ell.frame u B},
        ell.frame.Anc B P := by
      rintro B ⟨hBt, -, hmaj⟩
      by_contra hBP
      unfold AC.confirmationScore at hmaj
      dsimp only at hmaj
      refine absurd hmaj (not_lt.2 (le_trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (t := Hᶜ ∩ (AC.voters {v | v ∈ A.pool u})) ?_)) (by omega)))
      rintro v ⟨-, x, ⟨hx, -⟩, rfl, -, R, hR, hRr, hBR⟩
      refine ⟨fun hv => ?_, x, hx, rfl⟩
      obtain ⟨vote, -, -, hh, -, huniq⟩ := hpool _ hv (hp.hP.1 y hy j u x hx)
      obtain rfl := huniq x hx rfl
      obtain rfl : R = P := hPhi.coherent.1 hR hPt (hRr.trans hh)
      exact hBP hBR
    obtain ⟨D, hD⟩ := AC.exists_deepest hPhi (fun B hB => hB.1) ⟨P, hPS⟩
    have hDP := hall D (AC.deepest_mem hD).1
    have hPD := AC.anc_deepest hPhi (fun B hB => hB.1)
      (fun B hB C hC => AC.anc_total hPhi.coherent (hall B hB) (hall C hC)) hD P hPS
    rw [hD, Anc.antisymm hPhi.coherent hDP hPD]
  have hnv : ¬ AC.conflictsWithLock sp A.locks ell.frame (tr.time j) P := by
    apply AC.not_conflictsWithLock_of_forall
    intro L hL
    rcases hlocks L hL with h | h
    · exact Or.inr (AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hL.1 h hPt)
    · exact Or.inl (AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPt h hL.1)
  have hfast : AC.fastSelect sp A ell.frame u P = some P :=
    AC.fastSelect_eq_result hPhi hPt hPg (by unfold AC.FastTest; omega)
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    exact AC.slot_of_mem sp (u + 1)
      (by simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
      (by simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  have hpost : tr.projAC.post j = AC.updateConfirmation sp A ell.frame (tr.time j) u := by
    have he := hr.exec j ell hu.1.2 (hu.1.1 ▸ hy)
    rw [hu.1.1, hu.2.1] at he
    have h1 : tr.projAC.post j = (AC.acOnTick sp y A ell.frame (tr.time j)).1 :=
      (congrArg Prod.fst he).symm
    rw [h1]
    unfold AC.acOnTick
    dsimp only
    have hn1 : ¬ tr.time j = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [ht]; simp only [ACParams.ts]; push_cast; linarith only [sp.toParams.hΔ]
    have h2 : tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [ht]; simp only [ACParams.ts]; push_cast; ring
    have hj : AC.joined sp A (tr.time j) := hu.2.2.2
    have hc2 : (tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧ 0 < u + 1) = True :=
      eq_true ⟨h2, Nat.succ_pos u⟩
    rw [hslot]
    simp only [hj, not_true_eq_false, hn1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  refine ⟨hconf, hnv, hfast, hpost, ?_⟩
  rw [hpost]
  unfold AC.updateConfirmation
  simp only [hconf, hnv, ↓reduceIte]
  unfold AC.updateLatestConfirmed
  split <;> rfl

/-- An honest designated actual proposal is the unique block of its positive slot
in every honest frame, without reset or readiness premises. -/
theorem proposal_frame_unique
    {ini} (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hac.localRun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hPprop, _, ja, _, hacc, _⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hpH hdesignated hactual hPs
  rw [← hdesignated] at hPprop hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (AC.accept_new sp hr hpH ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hQf : AC.HonestFrameBlock tr.projAC H Q := ⟨y, hy, j, ell, hcall, hQ⟩
  have hroot : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hy j)
    obtain rfl := hr.coherent.1 ((AC.frameIn_of_callAt hr hy hcall).2 hQ)
      ⟨y, hy, j, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block P Q ⟨p, hpH, ja, ellp, hcp, hPm⟩ hQf (hPprop ▸ hpH)
    (by rw [hPprop, hac.honest.proposer Q hQf hroot, hQu, hdesignated])
    (by rw [hPs, hQu])).symm

/-- Actual honest proposals are unique in honest frames at their positive slot.
This uses no payload-support clause of `ReadyProposal`. -/
theorem reset_proposal_frame_unique
    (hp : ResetPremises tr H K proposer dg g ΔF a)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P :=
  proposal_frame_unique hp.run hp.noColl hP.1 hP.2.1 hP.2.2.2.1 hP.2.2.2.2.1 hu hy hcall
    hQ hQu

/-- Actual proposal uniqueness in a bounded run needs no readiness/support predicate. -/
theorem ResetPremisesUpTo.reset_proposal_frame_unique {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P :=
  proposal_frame_unique hp.run hp.noColl hpH hdesignated hactual hPs hu hy hcall hQ hQu

/-- Finite relay of an acceptance at or after `ḡ`: a receiver whose finality is below the block
accepts it before `max(t, g') + Δ`, `g' = t_{slot(ḡ)+1}`, at a call `Δ` after the acceptance time
`t` (the causal reset restart bound). -/
theorem ResetPremisesUpTo.reset_relay_accept {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    (hnew : AC.gbar g ≤ tr.time q)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (hjb : tr.time j ≤ b)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧
      tr.time k < max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + sp.Δ := by
  have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
    (fun k hkj hk => restart_le_before hp hy (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hkj).trans hjb)) (tr.time q)
  have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
    apply hd.trans
    change max (tr.time q) (sp.ts (sp.slot (AC.gbar g) + 1 : Nat)) + sp.Δ ≤ tr.time j
    rw [← max_add_add_right]
    exact max_le hq hjoin
  obtain ⟨k, hkj, hak, hkt⟩ := (sync_window_of_service hp.run hp.sync).relay
    x hx q B ha hnew y hy j ell hcall (hdl.trans hjb) hdl hF
  refine ⟨k, hkj, hak, hkt.trans_le ?_⟩
  exact Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := k)
    (fun k' hk' hk => restart_le_before hp hy (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono (hk'.trans hkj)).trans hjb)) (tr.time q)

/-- Finite guarded acceptance transport uses the causal reset restart bound. -/
theorem ResetPremisesUpTo.reset_accept_frame {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (hjb : tr.time j ≤ b) (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  by_cases hnew : AC.gbar g ≤ tr.time q
  · obtain ⟨k, hkj, hak, -⟩ := hp.reset_relay_accept hx hy ha hnew hcall hjb hjoin hq hF
    exact AC.mem_tree_of_acceptAtU sp hr.toU hy hak hkj hcall hF
  · obtain ⟨k, hkj, hak, _⟩ := (catch_window_of_run hp.run hc).relay x hx q B ha
      (not_le.mp hnew) y hy j ell hcall hg hjb hF
    exact AC.mem_tree_of_acceptAtU sp hr.toU hy hak hkj hcall hF

/-- Finite relay of held blocks retains the receiver's finalization guard. -/
theorem ResetPremisesUpTo.reset_frame_relay {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hjb : tr.time j ≤ b) (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  rcases Compose.frame_anc_acceptedU hr.toU hx q ellx hcx B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((AC.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (AC.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · exact hp.reset_accept_frame hc hx hy ha hcy hjb hg hjoin
      (by have := hp.run.time_mono hk; change tr.time k ≤ tr.time q at this
          linarith only [hq, this]) hF

/-- The actual proposal reaches a voter's frame above its finalization root. -/
theorem reset_proposal_frame
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k j u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F P) : P ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  by_cases hearly : tr.time j < sp.ts u + sp.Δ
  · obtain ⟨Q, hQ, hQs, -⟩ := (AC.cast_readyU hr.toU hy hcy (by rw [hes]; exact hearly)).1
    rw [hes] at hQs
    exact (reset_proposal_frame_unique hp hP hu hy hcy.1 hQ hQs) ▸ hQ
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ja, -, hacc, hta⟩ :=
      honestProposalRun_of_ready hp.run hp.noColl hP
    rw [← hP.2.1] at hacc
    exact reset_accept_frame hp hc hP.1 hy hacc hcy.1 hg hjoin
      (by change tr.time ja = sp.ts u at hta; rw [hta]; exact not_lt.mp hearly) hF

/-- Bounded actual casts hold the operational proposal above their finalized root. -/
theorem ResetPremisesUpTo.reset_proposal_frame {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k j u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F P) : P ∈ ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  by_cases hearly : tr.time j < sp.ts u + sp.Δ
  · obtain ⟨Q, hQ, hQs, _⟩ := (AC.cast_readyU hr.toU hy hcy (by rw [hes]; exact hearly)).1
    rw [hes] at hQs
    exact (hp.reset_proposal_frame_unique hpH hdesignated hactual hPs hu hy hcy.1 hQ hQs) ▸ hQ
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ja, _, hacc, hta⟩ :=
      honestProposalRun_of_proposesAt hp.run hp.noColl hpH hdesignated hactual hPs
    rw [← hdesignated] at hacc
    exact hp.reset_accept_frame hc hpH hy hacc hcy.1 hjb hg hjoin
      (by change tr.time ja = sp.ts u at hta; rw [hta]; exact not_lt.mp hearly) hF

/-- Payload support is transported only above the receiver's `F`. Early votes use their
actual readiness witness; deadline votes use guarded relay, not ready-proposal support. -/
theorem reset_support_frame
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {v : AC.Vote sp.n} (hv : v ∈ pay.2) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ellp.frame.tree) (hBr : B.root = v.head)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := (AC.cast_readyU hr.toU hy hcy (by rw [hes]; exact hearly)).1
    rw [hes] at hQs hsup
    obtain rfl := reset_proposal_frame_unique hp hP (by omega) hy hcy.1 hQ hQs
    have hslot : sp.slot (tr.time i) = s + 1 := by
      rw [hti]; exact AC.slot_of_mem sp _ le_rfl ((AC.ts_lt_iff sp).mpr (by omega))
    have hpay' : pay = AC.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
      unfold AC.acProposal at hd
      split_ifs at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rw [← hd.2, hslot]
      congr 1
      push_cast
      ring
    have hvs : v.slot + 1 = s + 1 := by
      rw [hpay'] at hv
      simp only [AC.voteViewList, AC.ACState.poolAt, Int.toNat_natCast, List.filter_filter,
        List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [AC.state_pool_slotU sp hr.toU hp.run.vstart hP.1 i s v hv.1]
    obtain ⟨B', hB', hBr', -⟩ := hsup v (by rw [AC.declaredSupportVotes, hpay]; exact hv) hvs
    rwa [hr.coherent.1 ((AC.frameIn_of_callAt hr hP.1 hci).2 hB)
      ((AC.frameIn_of_callAt hr hy hcy.1).2 hB') (hBr.trans hBr'.symm)]
  · exact reset_frame_relay hp hc hP.1 hy hci hcy.1 hB hg hjoin
      (by rw [hti]; exact not_lt.mp hearly) hF

/-- A pre-freeze voter block reaches the proposal frame under the proposer's `F` guard. -/
theorem reset_frozen_frame
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) (hy : y ∈ H) {i j s : Nat}
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : AC.CastAt tr.projAC y j elly e)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < AC.ETime.of (AC.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocks H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  rw [AC.readPoint_blockStamp_eqU hr.toU hy hcy] at hst
  rcases stamp_origin hr hy j elly hcy.1 B hB with hgen | ⟨q, -, ellq, hcq, hBq, hstamp⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hpH i ellp hci
    obtain rfl : B = G := hr.coherent.1 ((AC.frameIn_of_callAt hr hy hcy.1).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (AC.frameIn_of_callAt hr hpH hci).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < AC.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    apply reset_frame_relay hp hc hy hpH hcq hci hBq hg hjoin ?_ hF
    rw [hti]
    simp only [AC.freeze, AC.ACParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith only [ht]

/-- Guarded incidence gives view agreement on common held targets. Proposal heldness at the
voter remains explicit; this lemma does not supply viable-tree membership. -/
theorem reset_views_agree
    (hp : ResetPremises tr H K proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPy : P ∈ elly.frame.tree) (hg : AC.gbar g ≤ sp.ts s)
    (hgi : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j) :
    AC.equivocators (AC.View.ofLists pay).votes =
        AC.equivocators (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      AC.voters (AC.View.ofLists pay).votes =
        AC.voters (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        AC.supporters ellp.frame (AC.View.ofLists pay) s X =
          AC.supporters elly.frame (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (sp.ts s) (sp.ts (s + 1 : Nat)) hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 ((AC.le_gbar g).trans hg))
  apply AC.view_agree hac hP.1 hy hP.2.1 ⟨hci, hcall, d, hd⟩ hti hcy hes
    ⟨P, hPy, hP.2.2.2.2.1, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact reset_frozen_frame hp hc hP.1 hy hci hti hcy hgi hjoi hB hstamp hF
  · intro v hv B hB hBr hF
    exact reset_support_frame hp hc hP hci hd hti hpay hy hcy hes hgj hjoj hv hB hBr hF

/-- Finite payload support uses early cast readiness or guarded deadline relay. -/
theorem ResetPremisesUpTo.reset_support_frame {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1) (hjb : tr.time j ≤ b)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {v : AC.Vote sp.n} (hv : v ∈ pay.2) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ellp.frame.tree) (hBr : B.root = v.head)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := (AC.cast_readyU hr.toU hy hcy (by rw [hes]; exact hearly)).1
    rw [hes] at hQs hsup
    obtain rfl := hp.reset_proposal_frame_unique hpH hdesignated hactual hPs
      (by omega) hy hcy.1 hQ hQs
    have hslot : sp.slot (tr.time i) = s + 1 := by
      rw [hti]; exact AC.slot_of_mem sp _ le_rfl ((AC.ts_lt_iff sp).mpr (by omega))
    have hpay' : pay = AC.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
      unfold AC.acProposal at hd
      split_ifs at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rw [← hd.2, hslot]
      congr 1
      push_cast
      ring
    have hvs : v.slot + 1 = s + 1 := by
      rw [hpay'] at hv
      simp only [AC.voteViewList, AC.ACState.poolAt, Int.toNat_natCast, List.filter_filter,
        List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [AC.state_pool_slotU sp hr.toU hp.run.vstart hpH i s v hv.1]
    obtain ⟨B', hB', hBr', _⟩ := hsup v (by rw [AC.declaredSupportVotes, hpay]; exact hv) hvs
    rwa [hr.coherent.1 ((AC.frameIn_of_callAt hr hpH hci).2 hB)
      ((AC.frameIn_of_callAt hr hy hcy.1).2 hB') (hBr.trans hBr'.symm)]
  · exact hp.reset_frame_relay hc hpH hy hci hcy.1 hB hjb hg hjoin
      (by rw [hti]; exact not_lt.mp hearly) hF

/-- A bounded pre-freeze competitor reaches the proposal under its finalized guard. -/
theorem ResetPremisesUpTo.reset_frozen_frame {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) (hy : y ∈ H) {i j s : Nat}
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : AC.CastAt tr.projAC y j elly e) (hib : tr.time i ≤ b)
    (hg : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < AC.ETime.of (AC.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocks H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  rw [AC.readPoint_blockStamp_eqU hr.toU hy hcy] at hst
  rcases stamp_origin hr hy j elly hcy.1 B hB with hgen | ⟨q, _, ellq, hcq, hBq, hstamp⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hpH i ellp hci
    obtain rfl : B = G := hr.coherent.1 ((AC.frameIn_of_callAt hr hy hcy.1).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (AC.frameIn_of_callAt hr hpH hci).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < AC.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    apply hp.reset_frame_relay hc hy hpH hcq hci hBq hib hg hjoin ?_ hF
    rw [hti]
    simp only [AC.freeze, AC.ACParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith only [ht]

/-- Finite operational proposal and voter views agree on common held targets. -/
theorem ResetPremisesUpTo.reset_views_agree {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) (hg : AC.gbar g ≤ sp.ts s)
    (hgi : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j) :
    AC.equivocators (AC.View.ofLists pay).votes =
        AC.equivocators (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      AC.voters (AC.View.ofLists pay).votes =
        AC.voters (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        AC.supporters ellp.frame (AC.View.ofLists pay) s X =
          AC.supporters elly.frame (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hac := Compose.goldilocks_ac_projection_from hp.run hp.noColl
  have hsync := hp.sync.syncAC (hi := sp.ts (s + 1 : Nat)) hp.run ((AC.le_gbar g).trans hg)
  apply AC.view_agree hac hpH hy hdesignated ⟨hci, hcall, d, hd⟩ hti hcy hes
    ⟨P, hPy, hPs, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact hp.reset_frozen_frame hc hpH hy hci hti hcy hib hgi hjoi hB hstamp hF
  · intro v hv B hB hBr hF
    exact hp.reset_support_frame hc hpH hdesignated hactual hPs hci hd hti hpay hy hcy hes
      hjb hgj hjoj hv hB hBr hF

end Consensus.Goldilocks.Healing

end

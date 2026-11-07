module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree

public section

/-! # Proposer agreement with honesty through the consuming vote -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

private theorem anc_of_slot_le {S S' : Set (Blk sp.n FGP)} (hS : Coherent S) {s : Nat}
    (heq : {X | X ∈ S ∧ X.slot ≤ s} = {X | X ∈ S' ∧ X.slot ≤ s}) {X Y : Blk sp.n FGP}
    (h : Anc S X Y) (hY : Y.slot ≤ s) : Anc S' X Y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail Z Y _ hZY ih =>
    have hlt := hS.2 _ hZY.1 _ hZY.2.1 hZY.2.2
    have hZ : Z ∈ {X | X ∈ S' ∧ X.slot ≤ s} := by rw [← heq]; exact ⟨hZY.1, by omega⟩
    have hY' : Y ∈ {X | X ∈ S' ∧ X.slot ≤ s} := by rw [← heq]; exact ⟨hZY.2.1, hY⟩
    exact (ih (by omega)).tail ⟨hZ.1, hY'.1, hZY.2.2⟩

private theorem compatible_of_slot_le {S S' : Set (Blk sp.n FGP)} (hS : Coherent S) {s : Nat}
    (heq : {X | X ∈ S ∧ X.slot ≤ s} = {X | X ∈ S' ∧ X.slot ≤ s}) {X Y : Blk sp.n FGP}
    (hX : X.slot ≤ s) (hY : Y.slot ≤ s) (h : Compatible S X Y) : Compatible S' X Y :=
  h.imp (fun h => anc_of_slot_le hS heq h hY) fun h => anc_of_slot_le hS heq h hX

private theorem resolved_head {A : SAState sp.n} {Φ : Frm sp.n FGP} {v : Vote sp.n}
    (h : resolutionTime A Φ v ≠ ⊤) : ∃ Hd ∈ Φ.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot := by
  unfold resolutionTime at h
  split at h
  · exact absurd rfl h
  · rename_i Hd hl
    obtain ⟨hHd, hr⟩ := lookup_eq_some hl
    split_ifs at h with hlt
    · exact absurd rfl h
    · exact ⟨Hd, hHd, hr, by omega⟩

/-- The repaired A1.1 form: proposer honesty covers both frame-reading cuts (#154). -/
theorem proposer_voters_agree_of_honest_max
    {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U)
    {s : Nat} {p y : Fin sp.n} {i j : Nat} {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)}
    {pay : Payload sp.n} {e : Em sp FGP}
    (hpmax : p ∈ H (max (tr.time i) (tr.time j))) (hy : y ∈ H (tr.time j))
    (hpp : p = proposer (s + 1)) (hprop : ProposalAt tr p i ℓp pay)
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hc : CastAt tr y j ℓy e)
    (hs : e.msg.slot = s + 1)
    (hPy : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat)) tr)
    (heq : {X | X ∈ ℓp.frame.tree ∧ X.slot ≤ s} = {X | X ∈ ℓy.frame.tree ∧ X.slot ≤ s})
    (B : Blk sp.n FGP) (_hB : B ∈ ℓp.frame.tree) (hBs : B.slot ≤ s) :
    opponents sp ℓp.frame (View.ofLists pay) s B =
      opponents sp ℓy.frame (mergedVoteView sp e.readPoint ℓy.frame (s + 1)) s B := by
  have hr := hrun.localRun
  have hm := hr.time_mono
  have hp := hr.antitone (le_max_left _ _) hpmax
  have hpr := hrun.upTo (hr.time_nonneg i)
  have hyr := hrun.upTo (hr.time_nonneg j)
  have statep : (tr.upTo (tr.time i)).state p i = tr.state p i :=
    Trace.upTo_state tr p fun _ hk => hm hk.le
  have statey : (tr.upTo (tr.time j)).state y (j + 1) = tr.state y (j + 1) :=
    Trace.upTo_state tr y fun _ hk => hm (Nat.le_of_lt_succ hk)
  obtain ⟨hcp, hcall, d, hpay⟩ := hprop
  have hcp' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, hcp⟩
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_call hpr.localRun hp hcp'
  obtain ⟨hΦy, hΦyU⟩ := frameIn_of_call hyr.localRun hy hc'.1
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  have hsi : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; exact slot_of_mem sp (s + 1) le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  obtain ⟨hjp, hpay', hrt⟩ := proposal_payload hpay
  rw [hsi, hcast] at hpay'
  subst hpay'
  have hrsp : ∀ k ≤ i, tr.RestartAt p k → tr.time k ≤ sp.ts s := by
    have he := hpr.localRun.exec i ℓp hcp'.2 (hcp'.1 ▸ hp)
    rw [hcp'.1, hcall] at he
    have hj' : joined sp ((tr.upTo (tr.time i)).post i) (tr.time i) := by
      have hpost : (tr.upTo (tr.time i)).post i =
          (acProposal sp ((tr.upTo (tr.time i)).state p i) ℓp.frame (tr.time i)).1 :=
        (congrArg Prod.fst he).symm
      unfold joined; rw [hpost, statep, hrt]; exact hjp
    intro k hk hrk
    have hh := (SA.joined_awake sp FGP ro _ U _ hpr.localRun p hp i ℓp hcp' hj').2 k hk
      ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hk, hrk⟩)
    simpa only [Trace.upTo_time, hsi, hcast] using hh
  obtain ⟨_, hys, hyj, _⟩ := castAt_spec hyr.localRun hy hc'
  have hsj : sp.slot (tr.time j) = s + 1 := by change e.msg.slot = sp.slot (tr.time j) at hys; omega
  have hrsy : ∀ k ≤ j, tr.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hj' : joined sp ((tr.upTo (tr.time j)).post j) (tr.time j) := by
      unfold joined; rw [restartTime_of_castAt hyr.localRun hy hc']; exact hyj
    intro k hk hrk
    have hh := (SA.joined_awake sp FGP ro _ U _ hyr.localRun y hy j ℓy hc'.1 hj').2 k hk
      ((ACTrace.upTo_restartAt (A := goldilocksSA sp FGP ro)).mpr ⟨hm hk, hrk⟩)
    simpa only [Trace.upTo_time, hsj, hcast] using hh
  obtain ⟨P, hP, hPs, hPpay⟩ := hPy
  have hPv : blockVotes P = (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).1 := by
    simp only [blockVotes, hPpay]
  have hPsup : blockSupport P = (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).2 := by
    simp only [blockSupport, hPpay]
  have huniq : ∀ k ℓk, k ≤ j → tr.CallAt y k ℓk → ∀ X ∈ ℓk.frame.tree,
      X.slot = s + 1 → X = P := by
    intro k ℓk hkj hck X hX hXs
    have hkt := hm hkj
    have hyk := hr.antitone hkt hy
    have hpj := hr.antitone (le_max_right _ _) hpmax
    have hpk := hr.antitone hkt hpj
    have hck' := (Trace.upTo_callAt tr).mpr ⟨hkt, hck⟩
    have hXp := hrun.honest.proposer X ⟨y, k, ℓk, hyk, hck, hX⟩ (by
      intro hroot
      obtain ⟨G, hG, hGr, hGs⟩ := SA.genesis_mem hyr.localRun hy k hck'
      have he := hr.coherent.1 ((frameIn_of_call hyr.localRun hy hck').2 hX) hG
        (hroot.trans hGr.symm)
      rw [he, hGs] at hXs
      omega)
    have hPp := hrun.honest.proposer P ⟨y, j, ℓy, hy, hc.1, hP⟩ (by
      intro hroot
      obtain ⟨G, hG, hGr, hGs⟩ := SA.genesis_mem hyr.localRun hy j hc'.1
      have he := hr.coherent.1 (hΦyU hP) hG (hroot.trans hGr.symm)
      rw [he, hGs] at hPs
      omega)
    rw [hXs, ← hpp] at hXp
    rw [hPs, ← hpp] at hPp
    exact hrun.honest.one_block y k ℓk X y j ℓy P hyk hck hX hy hc.1 hP
      (hXp ▸ hr.antitone (max_le hkt le_rfl) hpj) (hXp.trans hPp.symm) (hXs.trans hPs.symm)
  have hpool : ∀ w ∈ (tr.state p i).pool s, (tr.state p i).voteStamp w < ⊤ := by
    intro w hw
    have hw' : w ∈ ((tr.upTo (tr.time i)).state p i).pool s := statep.symm ▸ hw
    have hws := state_pool_slot sp hpr.localRun hp i s w hw'
    rcases pool_origin hpr.localRun hp i w (hws ▸ hw') with
      ⟨k, _, _, h, _⟩ | ⟨k, _, ℓ, _, _, h, _⟩ <;>
      rw [statep] at h <;> exact h ▸ etime_of_lt_top _
  have hset : {w | w ∈ (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).1} =
      {w | w ∈ (tr.state p i).pool s} :=
    Set.ext fun w => mem_voteViewList_fst.trans ⟨And.left, fun h => ⟨h, hpool w h⟩⟩
  have hstar : ∀ x ∈ e.readPoint.pool s, e.readPoint.voteStamp x < ETime.of (sp.ts s + 3 * sp.Δ) →
      x ∈ (tr.state p i).pool s ∨ x.val ∈ equivocators {w | w ∈ (tr.state p i).pool s} := by
    intro x hx hxt
    obtain ⟨hx1, hx2⟩ := readPoint_pool hyr.localRun hy hc' hx
    have hxs := state_pool_slot sp hyr.localRun hy (j + 1) s x hx1
    rcases pool_origin hyr.localRun hy (j + 1) x (hxs ▸ hx1) with
      ⟨k, hk, hsend, hst, hsl⟩ | ⟨k, hk, ℓk, hck, _, _, X, hX, hxX⟩
    · rw [hx2 hxs] at hst
      have htk : tr.time k < sp.ts s + 3 * sp.Δ := etime_of_lt_of.1 (hst ▸ hxt)
      have hsk : sp.ts s ≤ tr.time k :=
        (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by rw [← hxs]; exact_mod_cast hsl)
      obtain ⟨hkt, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
      have hh := sync_forward hr hsync (hr.antitone hkt hy) hsend hsk
        (by rw [hts]; linarith) hp hcp
        (fun k' hk' hr' => (hrsp k' hk' hr').trans hsk) (by rw [hti, hts]; linarith)
        fun t h₁ h₂ => by
          rw [slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith), hxs]; omega
      rwa [hxs] at hh
    · have hvp := (frame_validPayload sp hyr.localRun hy hck X hX).1 x hxX
      obtain ⟨_, hck⟩ := (Trace.upTo_callAt tr).mp hck
      rw [huniq k ℓk (Nat.le_of_lt_succ hk) hck X hX (by omega)] at hxX
      exact Or.inl (mem_voteViewList_fst.1 (hPv ▸ hxX)).1
  have hblk : ∀ X ∈ ℓy.frame.tree, X.slot = s + 1 → X = P :=
    huniq j ℓy le_rfl hc.1
  have hvotes : ∀ v ∈ (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes,
      v ∈ (tr.state p i).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state p i).pool s} := by
    rintro v (hv | ⟨X, hX, hXs, hv⟩)
    · change v ∈ (voteViewList _ _ _ _).1 at hv
      rw [hcast, mem_voteViewList_fst] at hv
      exact hstar v hv.1 (by simpa [freeze, hcast] using hv.2)
    · rw [hblk X hX hXs] at hv
      exact Or.inl (mem_voteViewList_fst.1 (hPv ▸ hv)).1
  have hmem : ∀ X : Blk sp.n FGP, X.slot ≤ s → (X ∈ ℓp.frame.tree ↔ X ∈ ℓy.frame.tree) := by
    intro X hX
    have hh := Set.ext_iff.1 heq X
    exact ⟨fun h => (hh.mp ⟨h, hX⟩).1, fun h => (hh.mpr ⟨h, hX⟩).1⟩
  have hcomp : ∀ Hd : Blk sp.n FGP, Hd.slot ≤ s →
      (Compatible ℓp.frame.tree Hd B ↔ Compatible ℓy.frame.tree Hd B) := fun Hd hHd =>
    ⟨compatible_of_slot_le hΦp.coherent heq hHd hBs,
      compatible_of_slot_le hΦy.coherent heq.symm hHd hBs⟩
  change opponents sp ℓp.frame ⟨{w | w ∈ (voteViewList _ _ _ _).1}, _⟩ s B = _
  rw [hset]
  ext w
  constructor
  · rintro (⟨a, ha, b, hb, hab, rfl, hbv⟩ | ⟨x, hx, rfl, hxs, Hd, hHd, hHdr, hnc⟩)
    · have hv : ∀ v ∈ (tr.state p i).pool s,
          v ∈ (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes := fun v hv =>
        Or.inr ⟨P, hP, hPs, hPv ▸ mem_voteViewList_fst.2 ⟨hv, hpool v hv⟩⟩
      exact Or.inl ⟨a, hv a ha, b, hv b hb, hab, rfl, hbv⟩
    · obtain ⟨⟨_, hst⟩, hres⟩ := mem_voteViewList_snd.1 hx
      obtain ⟨Hd', hHd', hHd'r, hHd's⟩ := resolved_head hres.ne
      have hh : Hd' = Hd := hΦp.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
      subst hh
      have hHds : Hd'.slot ≤ s := by omega
      exact Or.inr ⟨x, Or.inr ⟨P, hP, hPs, hPsup ▸ hx, by omega, Hd', (hmem _ hHds).1 hHd,
        hHdr, by omega⟩, rfl, hxs, Hd', (hmem _ hHds).1 hHd, hHdr,
        fun h => hnc ((hcomp _ hHds).2 h)⟩
  · rintro (⟨a, ha, b, hb, hab, rfl, hbv⟩ | ⟨x, hx, rfl, hxs, Hd, hHd, hHdr, hnc⟩)
    · rcases hvotes a ha with ha' | ha'
      · rcases hvotes b hb with hb' | hb'
        · exact Or.inl ⟨a, ha', b, hb', hab, rfl, hbv⟩
        · exact Or.inl (hbv ▸ hb')
      · exact Or.inl ha'
    · rcases hx with hx | ⟨X, hX, hXs, hx, _, Hd', hHd', hHd'r, hHd's⟩
      · change x ∈ (voteViewList _ _ _ _).2 at hx
        rw [hcast, mem_voteViewList_snd] at hx
        obtain ⟨⟨hxp, hxt⟩, hres⟩ := hx
        obtain ⟨Hd', hHd', hHd'r, hHd's⟩ := resolved_head (hres.trans (etime_of_lt_top _)).ne
        have hh : Hd' = Hd := hΦy.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
        subst hh
        have hHds : Hd'.slot ≤ s := by omega
        have hHdp := (hmem _ hHds).2 hHd
        rcases hstar x hxp (by simpa [freeze, hcast] using hxt) with hxP | hxP
        · have hbs : (tr.state p i).blockStamp x.head ≠ ⊤ := by
            have hh := blockStamp_lt_of_acceptedBefore sp hpr.localRun hp hcp' hHdp
              (T := tr.time i + 1) (by
                rcases frame_accepted hpr.localRun hp i hcp' Hd' hHdp with h | ⟨k, hk, h⟩
                · exact Or.inl h
                · exact Or.inr ⟨k, h, by change tr.time k < tr.time i + 1; linarith [hm hk]⟩)
              (fun k hk hrk => by
                have ht := hrsp k hk ((ACTrace.upTo_restartAt
                  (A := goldilocksSA sp FGP ro)).mp hrk).2
                change tr.time k < tr.time i + 1
                rw [hti, hts]; linarith only [ht, hΔ])
              (Or.inr (by rw [hcall]; simp))
            rw [statep] at hh
            exact hHdr ▸ (hh.trans (etime_of_lt_top _)).ne
          refine Or.inr ⟨x, mem_voteViewList_snd.2 ⟨⟨hxP, hpool x hxP⟩,
            lt_top_iff_ne_top.2 (resolutionTime_ne_top hΦp hHdp hHdr hHd's (hpool x hxP).ne hbs)⟩,
            rfl, hxs, Hd', hHdp, hHdr, fun h => hnc ((hcomp _ hHds).1 h)⟩
        · exact Or.inl hxP
      · rw [hblk X hX hXs] at hx
        have hh : Hd' = Hd := hΦy.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
        subst hh
        have hHds : Hd'.slot ≤ s := by omega
        exact Or.inr ⟨x, hPsup ▸ hx, rfl, hxs, Hd', (hmem _ hHds).2 hHd, hHdr,
          fun h => hnc ((hcomp _ hHds).1 h)⟩

/-- Finite service survives retention for validators honest at the horizon. -/
theorem ServiceWindowBefore.upTo
    {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hr : Goldilocks.Growing.ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {a b d : Time} (h : ServiceWindowBefore H U a b tr) :
    SA.ServiceWindowBefore (H d) U a b (tr.upTo d) := by
  have hm := hr.time_mono
  refine ⟨?_, ?_⟩
  · intro x hx i v hsend hai y hy j ℓ hc hdb hdj
    obtain ⟨hid, hsend⟩ := (ACTrace.upTo_sendOrAdmit hm).mp hsend
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt tr).mp hc
    rw [ACTrace.upTo_deadline hm hjd] at hdb hdj
    exact (upTo_messageServedBefore hm hjd).mpr
      (h.message x i v (hr.antitone hid hx) hsend hai y j ℓ
        (hr.antitone hjd hy) hc hdb hdj)
  · intro x hx i B hi hai y hy j ℓ hc hdb hdj hanc
    obtain ⟨hid, hi⟩ := (ACTrace.upTo_acceptAt (A := goldilocksSA sp FGP ro)).mp hi
    obtain ⟨hjd, hc⟩ := (Trace.upTo_callAt tr).mp hc
    rw [ACTrace.upTo_deadline hm hjd] at hdb hdj
    obtain ⟨k, hk, hacc, ht⟩ := h.relay x i B (hr.antitone hid hx) hi hai y j ℓ
      (hr.antitone hjd hy) hc hdb hdj hanc
    have hkd := (hm hk).trans hjd
    exact ⟨k, hk, (ACTrace.upTo_acceptAt (A := goldilocksSA sp FGP ro)).mpr ⟨hkd, hacc⟩,
      by rwa [ACTrace.upTo_deadline hm hkd]⟩

theorem view_agree_window_before
    {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U)
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H (max (tr.time i) (tr.time j))) (hy : y ∈ H (tr.time j))
    (hpp : p = proposer (s + 1)) (hprop : ProposalAt tr p i ℓp pay)
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hc : CastAt tr y j ℓy e)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    {a b : Time} (hsync : ServiceWindowBefore H U a b tr) (ha : a ≤ sp.ts s) (hb : tr.time i ≤ b)
    (hyp : ∀ Hd ∈ ℓy.frame.tree, Hd.slot ≤ s →
      e.readPoint.blockStamp Hd.root < ETime.of (freeze sp (s + 1)) → Anc U ℓp.frame.F Hd →
        Hd ∈ ℓp.frame.tree)
    (hpy : ∀ x ∈ pay.2, ∀ Hd ∈ ℓp.frame.tree, Hd.root = x.head → Anc U ℓy.frame.F Hd →
      Hd ∈ ℓy.frame.tree) :
    equivocators (View.ofLists pay).votes =
        equivocators (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes ∧
      voters (View.ofLists pay).votes =
        voters (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        supporters ℓp.frame (View.ofLists pay) s X =
          supporters ℓy.frame (mergedVoteView sp e.readPoint ℓy.frame (s + 1)) s X := by
  have hr := hrun.localRun
  have hd := hr.time_nonneg j
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hjt : tr.time i ≤ tr.time j := by
    obtain ⟨P, hP, hPs, _⟩ := hP
    have hslot := frame_slot_le sp (hr.upTo hd) hy hc'.1 P hP
    rw [hPs] at hslot
    rw [hti]
    exact (ts_le_iff_le_slot sp hd (s + 1 : Nat)).mpr (by exact_mod_cast hslot)
  have hprop' : ProposalAt (tr.upTo (tr.time j)) p i ℓp pay := by
    obtain ⟨hc, hcall, d, hp⟩ := hprop
    refine ⟨(Trace.upTo_callAt tr).mpr ⟨hjt, hc⟩, hcall, d, ?_⟩
    have hstate : (tr.upTo (tr.time j)).state p i = tr.state p i :=
      Trace.upTo_state tr p fun _ hk => (hr.time_mono hk.le).trans hjt
    simpa only [hstate, Trace.upTo_time] using hp
  exact SA.view_agree_window_before (hrun.upTo hd) (hr.antitone (le_max_right _ _) hp) hy
    hpp hprop' hti hc' hP (hsync.upTo hr) ha hb hyp hpy

theorem view_agree_before
    {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U)
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H (max (tr.time i) (tr.time j))) (hy : y ∈ H (tr.time j))
    (hpp : p = proposer (s + 1)) (hprop : ProposalAt tr p i ℓp pay)
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hc : CastAt tr y j ℓy e)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    {b : Time} (hsync : ServiceBefore H U b tr) (hb : tr.time i ≤ b)
    (hyp : ∀ Hd ∈ ℓy.frame.tree, Hd.slot ≤ s →
      e.readPoint.blockStamp Hd.root < ETime.of (freeze sp (s + 1)) → Anc U ℓp.frame.F Hd →
        Hd ∈ ℓp.frame.tree)
    (hpy : ∀ x ∈ pay.2, ∀ Hd ∈ ℓp.frame.tree, Hd.root = x.head → Anc U ℓy.frame.F Hd →
      Hd ∈ ℓy.frame.tree) :
    equivocators (View.ofLists pay).votes =
        equivocators (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes ∧
      voters (View.ofLists pay).votes =
        voters (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        supporters ℓp.frame (View.ofLists pay) s X =
          supporters ℓy.frame (mergedVoteView sp e.readPoint ℓy.frame (s + 1)) s X :=
  view_agree_window_before hrun hp hy hpp hprop hti hc hP hsync
    (by have := sp.toParams.hΔ; simp only [SAParams.ts]; positivity) hb hyp hpy

theorem view_agree
    {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U)
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H (max (tr.time i) (tr.time j))) (hy : y ∈ H (tr.time j))
    (hpp : p = proposer (s + 1)) (hprop : ProposalAt tr p i ℓp pay)
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hc : CastAt tr y j ℓy e)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    (hsync : SyncACAt (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat)) tr)
    (hyp : ∀ Hd ∈ ℓy.frame.tree, Hd.slot ≤ s →
      e.readPoint.blockStamp Hd.root < ETime.of (freeze sp (s + 1)) → Anc U ℓp.frame.F Hd →
        Hd ∈ ℓp.frame.tree)
    (hpy : ∀ x ∈ pay.2, ∀ Hd ∈ ℓp.frame.tree, Hd.root = x.head → Anc U ℓy.frame.F Hd →
      Hd ∈ ℓy.frame.tree) :
    equivocators (View.ofLists pay).votes =
        equivocators (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes ∧
      voters (View.ofLists pay).votes =
        voters (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        supporters ℓp.frame (View.ofLists pay) s X =
          supporters ℓy.frame (mergedVoteView sp e.readPoint ℓy.frame (s + 1)) s X := by
  have hr := hrun.localRun
  have hd := hr.time_nonneg j
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hjt : tr.time i ≤ tr.time j := by
    obtain ⟨P, hP, hPs, _⟩ := hP
    have hslot := frame_slot_le sp (hr.upTo hd) hy hc'.1 P hP
    rw [hPs] at hslot
    rw [hti]
    exact (ts_le_iff_le_slot sp hd (s + 1 : Nat)).mpr (by exact_mod_cast hslot)
  have hprop' : ProposalAt (tr.upTo (tr.time j)) p i ℓp pay := by
    obtain ⟨hc, hcall, d, hp⟩ := hprop
    refine ⟨(Trace.upTo_callAt tr).mpr ⟨hjt, hc⟩, hcall, d, ?_⟩
    have hstate : (tr.upTo (tr.time j)).state p i = tr.state p i :=
      Trace.upTo_state tr p fun _ hk => (hr.time_mono hk.le).trans hjt
    simpa only [hstate, Trace.upTo_time] using hp
  have hsync' : SyncAC (goldilocksSA sp FGP ro) (H (tr.time j)) U
      (sp.ts s) (sp.ts (s + 1 : Nat)) (tr.upTo (tr.time j)) := by
    refine ⟨?_, ?_⟩
    · intro x hx k v hsend ha hb y hy c ℓ hcc hdl
      obtain ⟨hkd, hsend⟩ := (ACTrace.upTo_sendOrAdmit hr.time_mono).mp hsend
      obtain ⟨hcd, hcc⟩ := (Trace.upTo_callAt tr).mp hcc
      rw [ACTrace.upTo_deadline hr.time_mono hcd] at hdl
      obtain ⟨r, hrc, hkr, hproc, ht⟩ := hsync.1 x k v (hr.antitone hkd hx) hsend ha hb
        y c ℓ (hr.antitone hcd hy) hcc hdl
      have hrd := (hr.time_mono hrc).trans hcd
      exact ⟨r, hrc, hkr, (ACTrace.upTo_processAt (A := goldilocksSA sp FGP ro)).mpr ⟨hrd, hproc⟩,
        by rwa [ACTrace.upTo_deadline hr.time_mono hrd]⟩
    · intro x hx k B hacc ha hb y hy c ℓ hcc hdl hanc
      obtain ⟨hkd, hacc⟩ := (ACTrace.upTo_acceptAt (A := goldilocksSA sp FGP ro)).mp hacc
      obtain ⟨hcd, hcc⟩ := (Trace.upTo_callAt tr).mp hcc
      rw [ACTrace.upTo_deadline hr.time_mono hcd] at hdl
      obtain ⟨r, hrc, hacc, ht⟩ := hsync.2 x k B (hr.antitone hkd hx) hacc ha hb
        y c ℓ (hr.antitone hcd hy) hcc hdl hanc
      have hrd := (hr.time_mono hrc).trans hcd
      exact ⟨r, hrc, (ACTrace.upTo_acceptAt (A := goldilocksSA sp FGP ro)).mpr ⟨hrd, hacc⟩,
        by rwa [ACTrace.upTo_deadline hr.time_mono hrd]⟩
  exact SA.view_agree (hrun.upTo hd) (hr.antitone (le_max_right _ _) hp) hy
    hpp hprop' hti hc' hP hsync' hyp hpy

end Consensus.Goldilocks.SA.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: the proposal's view and a voter's merged view agree

For an honest proposer `p` of slot `s + 1` proposing at `t_{s+1}` and an honest voter `y` of slot
`s + 1` that holds that proposal `P` (the only slot-`(s+1)` block of the honest frames), under
`Sync[t_s, t_{s+1}]`: the proposal's view (`p`'s slot-`s` pool, the resolved votes as support)
and `y`'s merged view give the same equivocators and the same voters, and the same supporters to
every block of both trees, provided the blocks that resolve a support vote at one node are in the
other's tree when they extend its `Φ.F`: the voter's blocks stamped before the vote freeze are in
`p`'s tree, and the heads of `P`'s support entries are in `y`'s tree. The trees may differ
otherwise (late faulty blocks, different finalized tips).
This is A1.1's agreement (`proposer_voters_agree`) for the Goldfish score, without its premise
that the two trees agree up to slot `s`. Used by H.1 (`proposal_votes`) and by the service
statements (`honest_votes_eq_proposal_before`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- The genesis block of an honest node's initial frame is in `U`, with slot `0`. -/
theorem genesis_mem (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksSA sp FGP ro)}, tr.CallAt y i ℓ →
      ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.slot = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, hslot, -⟩, ⟨-, hsub⟩, -⟩ | ⟨j, ℓ', hj, hc', -⟩
    · exact ⟨Φ₀.F, hsub (htree ▸ rfl), hroot, hslot⟩
    · exact ih j hj hc'

/-- A resolved vote has its head in the tree, of slot at most the vote's, and the head's stamp
is at most the resolution time. -/
private theorem resolved_head {A : SAState sp.n} {Φ : Frm sp.n FGP} {v : Vote sp.n}
    (h : resolutionTime A Φ v ≠ ⊤) : ∃ Hd ∈ Φ.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot ∧
      A.blockStamp v.head ≤ resolutionTime A Φ v := by
  unfold resolutionTime at h ⊢
  rcases hl : lookup Φ v.head with _ | Hd
  · rw [hl] at h; exact absurd rfl h
  · obtain ⟨hHd, hr⟩ := lookup_eq_some hl
    rw [hl] at h
    dsimp only at h ⊢
    split_ifs at h ⊢ with hlt
    · exact absurd rfl h
    · exact ⟨Hd, hHd, hr, by omega, le_max_right _ _⟩

/-- A block of a frame's tree extending a block `X` of another frame's tree extends, in `U`,
that other frame's `F`. -/
private theorem anc_F {Φ Ψ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (hΨU : Ψ.tree ⊆ U) {X R : Blk sp.n FGP} (hX : X ∈ Φ.tree) (h : Ψ.Anc X R) :
    Anc U Φ.F R :=
  Relation.ReflTransGen.trans ((hΦ.rooted.2 X hX).mono hΦU) (h.mono hΨU)

/-- `X ⪯ r` moves to another frame of `U` holding `X` and a block with root `r`. -/
private theorem ancR_transfer (hU : Coherent U) {Φ Ψ : Frm sp.n FGP} (hΦU : Φ.tree ⊆ U)
    (hΨ : FrameOK Ψ) (hΨU : Ψ.tree ⊆ U) {X Hd : Blk sp.n FGP} {r : Nat} (hX : X ∈ Ψ.tree)
    (hHd : Hd ∈ Ψ.tree) (hr : Hd.root = r) (h : AncR Φ X r) : AncR Ψ X r := by
  obtain ⟨R, hR, rfl, hanc⟩ := h
  obtain rfl : R = Hd := hU.1 (hΦU hR) (hΨU hHd) hr.symm
  exact ⟨R, hHd, rfl, anc_tree_of_anc_U hU hΨ hΨU hX (hanc.mono hΦU) hHd⟩

/-- **The proposal's view and the merged view agree** (equivocators, voters, and supporters of
every block of both trees). -/
private theorem view_agree_of_forward (hrun : ACRun proposer tr H U)
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H) (hpp : p = proposer (s + 1))
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    (hforward : ∀ k v, tr.SendOrAdmit y k v → sp.ts s ≤ tr.time k →
      tr.time k < sp.ts s + 3 * sp.Δ → v.slot = s →
      (∀ k' ≤ i, tr.RestartAt p k' → tr.time k' ≤ sp.ts s) →
      v ∈ (tr.state p i).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state p i).pool s})
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
  have hU : Coherent U := hr.coherent
  obtain ⟨hcp, hcall, d, hpay⟩ := hprop
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_call hr hp hcp
  obtain ⟨hΦy, hΦyU⟩ := frameIn_of_call hr hy hc.1
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  have hsi : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; exact slot_of_mem sp (s + 1) le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  obtain ⟨hjp, hpay', hrt⟩ := proposal_payload hpay
  rw [hsi, hcast] at hpay'
  subst hpay'
  -- the restarts of the proposer are at or before `t_s`
  have hrsp : ∀ k ≤ i, tr.RestartAt p k → tr.time k ≤ sp.ts s := by
    have he := hr.exec i ℓp hcp.2 (hcp.1 ▸ hp)
    rw [hcp.1, hcall] at he
    have hj' : joined sp (tr.post i) (tr.time i) := by
      have hpost : tr.post i = (acProposal sp (tr.state p i) ℓp.frame (tr.time i)).1 :=
        (congrArg Prod.fst he).symm
      unfold joined; rw [hpost, hrt]; exact hjp
    intro k hk hrk
    have := ((joined_awake sp) FGP ro H U tr hr p hp i ℓp hcp hj').2 k hk hrk
    rwa [hsi, hcast] at this
  -- the only slot-`(s+1)` block of the honest frames is the proposal
  obtain ⟨P, hP, hPs, hPpay⟩ := hP
  have hPv : blockVotes P = (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).1 := by
    simp only [blockVotes, hPpay]
  have hPsup : blockSupport P = (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).2 := by
    simp only [blockSupport, hPpay]
  have huniq : ∀ X, HonestFrameBlock tr H X → X.slot = s + 1 → X = P := fun X hX hXs =>
    frameBlock_unique hrun (by omega) (hpp ▸ hp) hX ⟨y, hy, j, ℓy, hc.1, hP⟩ hXs hPs
  -- the proposal's votes are the proposer's slot-`s` pool
  have hpool : ∀ w ∈ (tr.state p i).pool s, (tr.state p i).voteStamp w < ⊤ := by
    intro w hw
    have hws := state_pool_slot sp hr hp i s w hw
    rcases pool_origin hr hp i w (hws ▸ hw) with ⟨k, -, -, h, -⟩ | ⟨k, -, ℓ, -, -, h, -⟩ <;>
      exact h ▸ etime_of_lt_top _
  have hset : {w | w ∈ (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).1} =
      {w | w ∈ (tr.state p i).pool s} :=
    Set.ext fun w => mem_voteViewList_fst.trans ⟨And.left, fun h => ⟨h, hpool w h⟩⟩
  -- **every early vote of the voter reaches the proposer**
  have hstar : ∀ x ∈ e.readPoint.pool s, e.readPoint.voteStamp x < ETime.of (sp.ts s + 3 * sp.Δ) →
      x ∈ (tr.state p i).pool s ∨ x.val ∈ equivocators {w | w ∈ (tr.state p i).pool s} := by
    intro x hx hxt
    obtain ⟨hx1, hx2⟩ := readPoint_pool hr hy hc hx
    have hxs : x.slot = s := state_pool_slot sp hr hy (j + 1) s x hx1
    rcases pool_origin hr hy (j + 1) x (hxs ▸ hx1) with
      ⟨k, -, hsend, hst, hsl⟩ | ⟨k, -, ℓk, hck, -, -, X, hX, hxX⟩
    · rw [hx2 hxs] at hst
      have htk : tr.time k < sp.ts s + 3 * sp.Δ := etime_of_lt_of.1 (hst ▸ hxt)
      have hsk : sp.ts s ≤ tr.time k :=
        (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by rw [← hxs]; exact_mod_cast hsl)
      exact hforward k x hsend hsk htk hxs hrsp
    · -- a restart put it there, from a block of slot `s + 1`: the proposal
      have hvp := (frame_validPayload sp hr hy hck X hX).1 x hxX
      rw [huniq X ⟨y, hy, k, ℓk, hck, hX⟩ (by omega)] at hxX
      exact Or.inl (mem_voteViewList_fst.1 (hPv ▸ hxX)).1
  -- the votes of the merged view are the proposal's or make their validator an equivocator there
  have hblk : ∀ X ∈ ℓy.frame.tree, X.slot = s + 1 → X = P := fun X hX hXs =>
    huniq X ⟨y, hy, j, ℓy, hc.1, hX⟩ hXs
  have hvotes : ∀ v ∈ (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes,
      v ∈ (tr.state p i).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state p i).pool s} := by
    rintro v (hv | ⟨X, hX, hXs, hv⟩)
    · change v ∈ (voteViewList _ _ _ _).1 at hv
      rw [hcast, mem_voteViewList_fst] at hv
      exact hstar v hv.1 (by simpa [freeze, hcast] using hv.2)
    · rw [hblk X hX hXs] at hv
      exact Or.inl (mem_voteViewList_fst.1 (hPv ▸ hv)).1
  -- the proposal's votes are merged votes
  have hm : ∀ v ∈ (tr.state p i).pool s,
      v ∈ (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes := fun v hv =>
    Or.inr ⟨P, hP, hPs, hPv ▸ mem_voteViewList_fst.2 ⟨hv, hpool v hv⟩⟩
  have hpe : equivocators {w | w ∈ (tr.state p i).pool s} =
      equivocators (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes := by
    ext w
    constructor
    · rintro ⟨a, ha, b, hb, hab, rfl, hbv⟩
      exact ⟨a, hm a ha, b, hm b hb, hab, rfl, hbv⟩
    · rintro ⟨a, ha, b, hb, hab, rfl, hbv⟩
      rcases hvotes a ha with ha' | ha'
      · rcases hvotes b hb with hb' | hb'
        · exact ⟨a, ha', b, hb', hab, rfl, hbv⟩
        · exact hbv ▸ hb'
      · exact ha'
  have heqv : equivocators (View.ofLists (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤)).votes
      = equivocators (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes := by
    change equivocators {w | w ∈ (voteViewList _ _ _ _).1} = _
    rw [hset, hpe]
  refine ⟨heqv, ?_, fun X hXp hXy => ?_⟩
  · change voters {w | w ∈ (voteViewList _ _ _ _).1} = _
    rw [hset]
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, hm a ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases hvotes a ha with ha' | ⟨b, hb, -, -, -, hb', -⟩
      · exact ⟨a, ha', rfl⟩
      · exact ⟨b, hb, hb'⟩
  ext w
  constructor
  · rintro ⟨hw, x, hx, rfl, hxs, R, hR, hRr, hXR⟩
    obtain ⟨-, hres⟩ := mem_voteViewList_snd.1 hx
    obtain ⟨Hd, hHd, hHdr, hHds, -⟩ := resolved_head hres.ne
    obtain rfl : R = Hd := hΦp.coherent.1 hR hHd (hRr.trans hHdr.symm)
    have hRy := hpy x hx R hR hRr (anc_F hΦy hΦyU hΦpU hXy hXR)
    exact ⟨heqv ▸ hw, x, Or.inr ⟨P, hP, hPs, hPsup ▸ hx, by omega, R, hRy, hRr, by omega⟩, rfl,
      hxs, R, hRy, hRr, anc_tree_of_anc_U hU hΦy hΦyU hXy (hXR.mono hΦpU) hRy⟩
  · rintro ⟨hw, x, hx, rfl, hxs, hXR⟩
    suffices h : x ∈ (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).2 by
      obtain ⟨-, hres⟩ := mem_voteViewList_snd.1 h
      obtain ⟨Hd, hHd, hHdr, -⟩ := resolved_head hres.ne
      exact ⟨heqv ▸ hw, x, h, rfl, hxs, ancR_transfer hU hΦyU hΦp hΦpU hXp hHd hHdr hXR⟩
    rcases hx with hx | ⟨Q, hQ, hQs, hx, -⟩
    · -- an early support vote of the voter
      change x ∈ (voteViewList _ _ _ _).2 at hx
      rw [hcast, mem_voteViewList_snd] at hx
      obtain ⟨⟨hxp, hxt⟩, hres⟩ := hx
      obtain ⟨Hd, hHd, hHdr, hHds, hHdt⟩ :=
        resolved_head (hres.trans (etime_of_lt_top _)).ne
      obtain ⟨R, hR, hRr, hXR⟩ := hXR
      obtain rfl : R = Hd := hΦy.coherent.1 hR hHd (hRr.trans hHdr.symm)
      have hRp := hyp R hR (by omega) (by rw [hHdr]; exact hHdt.trans_lt hres)
        (anc_F hΦp hΦpU hΦyU hXp hXR)
      rcases hstar x hxp (by simpa [freeze, hcast] using hxt) with hxP | hxP
      · -- the proposer holds it, resolved
        have hbs : (tr.state p i).blockStamp x.head ≠ ⊤ := by
          refine hRr ▸ (blockStamp_lt_of_acceptedBefore sp hr hp hcp hRp
            (T := tr.time i + 1) ?_ (fun k hk hrk => ?_)
            (Or.inr (by rw [hcall]; simp))).trans (etime_of_lt_top _) |>.ne
          · rcases frame_accepted hr hp i hcp R hRp with h | ⟨k, hk, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨k, h, (hr.time_mono hk).trans_lt (lt_add_one _)⟩
          · have htime := hrsp k hk hrk
            rw [hti, hts]
            linarith only [htime, hΔ]
        exact mem_voteViewList_snd.2 ⟨⟨hxP, hpool x hxP⟩,
          lt_top_iff_ne_top.2 (resolutionTime_ne_top hΦp hRp hRr hHds (hpool x hxP).ne hbs)⟩
      · exact absurd (hpe ▸ hxP) hw
    · -- a support entry of the proposal
      rw [hblk Q hQ hQs] at hx
      exact hPsup ▸ hx

/-- View agreement needs service only from the previous slot through the
proposal deadline. The two block-delivery premises are exactly the relay/Catch
obligations; no settled phase or equality of the frame trees is assumed. -/
theorem view_agree_window_before (hrun : ACRun proposer tr H U)
    {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H) (hpp : p = proposer (s + 1))
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    {a b : Time} (hsync : ServiceWindowBefore H U a b tr)
    (ha : a ≤ sp.ts s) (hb : tr.time i ≤ b)
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
  refine view_agree_of_forward hrun hp hy hpp hprop hti hc hP ?_ hyp hpy
  intro k v hsend hsk htk hvs hrs
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hdl : tr.time k + sp.Δ ≤ tr.time i := by
    rw [hti, hts]; linarith only [htk, hΔ]
  have h := sync_window_before_forward hrun.localRun hsync hy hsend (ha.trans hsk)
    (hdl.trans hb) hp hprop.1
    (fun k' hk' hr' => (hrs k' hk' hr').trans hsk) hdl fun t h₁ h₂ => by
      rw [slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith only [h₂, htk, hΔ]), hvs]
      omega
  simpa only [hvs] using h

/-- View agreement needs service only through the proposal cut. -/
theorem view_agree_before (hrun : ACRun proposer tr H U) {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H) (hpp : p = proposer (s + 1))
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e)
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
  view_agree_window_before hrun hp hy hpp hprop hti hc hP
    ⟨hsync.message, hsync.relay⟩
    (by have := sp.toParams.hΔ; simp only [SAParams.ts]; positivity) hb hyp hpy

/-- The original source-window service also suffices for view agreement. -/
theorem view_agree (hrun : ACRun proposer tr H U) {s : Nat} {p y : Fin sp.n} {i j : Nat}
    {ℓp ℓy : ACLabel (goldilocksSA sp FGP ro)} {pay : Payload sp.n} {e : Em sp FGP}
    (hp : p ∈ H) (hy : y ∈ H) (hpp : p = proposer (s + 1))
    (hprop : ProposalAt tr p i ℓp pay) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hc : CastAt tr y j ℓy e)
    (hP : ∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat)) tr)
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
  refine view_agree_of_forward hrun hp hy hpp hprop hti hc hP ?_ hyp hpy
  intro k v hsend hsk htk hvs hrs
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have h := sync_forward hrun.localRun hsync hy hsend hsk
    (by rw [hts]; linarith only [htk, hΔ]) hp hprop.1
    (fun k' hk' hr' => (hrs k' hk' hr').trans hsk)
    (by rw [hti, hts]; linarith only [htk, hΔ])
    fun t h₁ h₂ => by
      rw [slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith only [h₂, htk, hΔ]), hvs]
      omega
  simpa only [hvs] using h

end Consensus.Goldilocks.SA

end

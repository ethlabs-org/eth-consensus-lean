module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

public section

/-! # Goldilocks SA: proposer and voters agree on unlocking (A1.1)

The proposal's view and an honest voter's merged view give the same opponents to every block of
slot at most `s`, under `Sync[t_s, t_{s+1}]`, when both frames hold the same blocks of slot at
most `s`.

The merged view is the voter's slot-`s` votes held before the freeze `t_s + 3Δ` and the votes of
the slot-`(s+1)` proposals of its tree; the proposer is honest, so its proposal is the only one
(`HonestObjects.one_block`), and the proposal view is the proposer's slot-`s` pool. Each early
vote of the voter was admitted at a time in `[t_s, t_s + 3Δ)` (or put there by a restart from a
block of slot `s + 1`, which is the proposal), so under `Sync` the proposer, joined at `t_{s+1}`,
processed it before `t_{s+1}`: it holds the vote, or two other votes of its validator. Heads of
slot at most `s` are in both trees, ancestry below slot `s` is the same in both, and the
proposer has stamped the blocks of its tree, so a resolved vote at the voter is resolved at the
proposer. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

private theorem frameIn_of_call (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- Every block of an honest node's frame is genesis or was accepted by the node. -/
private theorem frame_accepted (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksSA sp FGP ro)}, tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k X := by
  have step : ∀ (Φ Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call),
      (goldilocksSA sp FGP ro).CallOK U Φ t c Φ' → ∀ X ∈ Φ'.tree, X ∈ Φ.tree ∨ c = .block X := by
    intro Φ Φ' t c hok X hX
    obtain ⟨-, hc⟩ := hok
    cases c with
    | block B =>
      obtain ⟨hs, -, -⟩ := hc
      rw [hs.tree_eq] at hX
      rcases hX.1 with rfl | hX
      · exact Or.inr rfl
      · exact Or.inl hX
    | message m => exact Or.inl (hc.1 ▸ hX)
    | tick => exact Or.inl (hc ▸ hX)
    | proposal => exact Or.inl (hc ▸ hX)
    | toFG => exact Or.inl (hc ▸ hX)
    | restart => exact Or.inl (hc ▸ hX)
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc X hX
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · rcases step _ _ _ _ hok X hX with h | h
      · rw [htree, Set.mem_singleton_iff] at h
        exact Or.inl (h ▸ hroot)
      · exact Or.inr ⟨i, le_rfl, ℓ, hc, h⟩
    · rcases step _ _ _ _ hok X hX with h | h
      · exact (ih j hj hc' X h).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩
      · exact Or.inr ⟨i, le_rfl, ℓ, hc, h⟩

/-- The genesis block of an honest node's initial frame is in `U`, with slot `0`. -/
private theorem genesis_mem (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
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

/-- An honest proposer of a slot `σ > 0` has one block of slot `σ` in the honest frames. -/
private theorem frameBlock_unique (hrun : ACRun proposer tr H U) {σ : Nat} (hσ : σ ≠ 0)
    (hp : proposer σ ∈ H) {B B' : Blk sp.n FGP} (hB : HonestFrameBlock tr H B)
    (hB' : HonestFrameBlock tr H B') (hs : B.slot = σ) (hs' : B'.slot = σ) : B = B' := by
  have hr := hrun.localRun
  have hprop : ∀ X, HonestFrameBlock tr H X → X.slot = σ → X.proposer = proposer σ := by
    rintro X ⟨y, hy, i, ℓ, hc, hX⟩ hXs
    obtain ⟨G, hG, hGr, hGs⟩ := genesis_mem hr hy i hc
    refine hXs ▸ hrun.honest.proposer X ⟨y, hy, i, ℓ, hc, hX⟩ fun hXr => hσ ?_
    rw [← hXs, hr.coherent.1 ((frameIn_of_call hr hy hc).2 hX) hG (hXr.trans hGr.symm), hGs]
  exact hrun.honest.one_block B B' hB hB' (hprop B hB hs ▸ hp)
    ((hprop B hB hs).trans (hprop B' hB' hs').symm) (hs.trans hs'.symm)

/-- Ancestry below a block of slot at most `s` only reads the blocks of slot at most `s`. -/
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

/-- A resolved vote has its head in the tree, of slot at most the vote's. -/
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

/-- A vote with a finite stamp whose head is a stamped block of the tree of slot at most the
vote's is resolved. -/
private theorem resolutionTime_ne_top {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {v : Vote sp.n} {Hd : Blk sp.n FGP} (hHd : Hd ∈ Φ.tree) (hr : Hd.root = v.head)
    (hs : Hd.slot ≤ v.slot) (hv : A.voteStamp v ≠ ⊤) (hb : A.blockStamp v.head ≠ ⊤) :
    resolutionTime A Φ v ≠ ⊤ := by
  unfold resolutionTime
  split
  · rename_i hl
    exact absurd ⟨Hd, hHd, hr⟩ (lookup_eq_none hl)
  · rename_i Hd' hl
    obtain ⟨hHd', hr'⟩ := lookup_eq_some hl
    have : Hd' = Hd := hΦ.coherent.1 hHd' hHd (hr'.trans hr.symm)
    subst this
    split_ifs with hlt
    · omega
    · exact (max_lt (lt_top_iff_ne_top.2 hv) (lt_top_iff_ne_top.2 hb)).ne

private theorem mem_voteViewList_fst {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).1 ↔ v ∈ A.pool s ∧ A.voteStamp v < c := by
  simp [voteViewList, SAState.poolAt]

private theorem mem_voteViewList_snd {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).2 ↔
      (v ∈ A.pool s ∧ A.voteStamp v < c) ∧ resolutionTime A Φ v < c := by
  simp [voteViewList, SAState.poolAt]
  tauto

private theorem etime_of_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

private theorem etime_of_lt_of {a b : Time} : ETime.of a < ETime.of b ↔ a < b := by
  simp [ETime.of]

/-- The payload of a proposal is the proposer's view of the previous slot's pool, and the
proposer is joined. -/
private theorem proposal_payload {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposal sp A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ pay = voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ ∧
      (acProposal sp A Φ t).1.restartTime = A.restartTime := by
  unfold acProposal at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hj
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hj, h.2.symm, rfl⟩

variable (sp) in
/-- **A1.1.** -/
theorem proposer_voters_agree : ProposerVotersAgree sp := by
  intro FGP ro H U tr proposer hrun s p y i j ℓp ℓy pay e hp hy hpp hprop hti hc hs
    hPy hsync heq B hB hBs
  have hr := hrun.localRun
  obtain ⟨hcp, hcall, d, hpay⟩ := hprop
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_call hr hp hcp
  obtain ⟨hΦy, -⟩ := frameIn_of_call hr hy hc.1
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcast : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  have hsi : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; exact slot_of_mem sp (s + 1) le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  obtain ⟨hjp, hpay', hrt⟩ := proposal_payload hpay
  rw [hsi, hcast] at hpay'
  subst hpay'
  -- the restarts of the proposer and of the voter are at or before `t_s`
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
  obtain ⟨-, hys, hyj, -⟩ := castAt_spec hr hy hc
  have hsj : sp.slot (tr.time j) = s + 1 := by omega
  have hrsy : ∀ k ≤ j, tr.RestartAt y k → tr.time k ≤ sp.ts s := by
    have hj' : joined sp (tr.post j) (tr.time j) := by
      unfold joined; rw [restartTime_of_castAt hr hy hc]; exact hyj
    intro k hk hrk
    have := ((joined_awake sp) FGP ro H U tr hr y hy j ℓy hc.1 hj').2 k hk hrk
    rwa [hsj, hcast] at this
  -- the only slot-`(s+1)` block of the honest frames is the proposal
  obtain ⟨P, hP, hPs, hPpay⟩ := hPy
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
      have := sync_forward hr hsync hy hsend hsk (by rw [hts]; linarith) hp hcp
        (fun k' hk' hr' => (hrsp k' hk' hr').trans hsk) (by rw [hti, hts]; linarith)
        fun t h₁ h₂ => by
          rw [slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith), hxs]; omega
      rwa [hxs] at this
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
  have hmem : ∀ X : Blk sp.n FGP, X.slot ≤ s → (X ∈ ℓp.frame.tree ↔ X ∈ ℓy.frame.tree) := by
    intro X hX
    have := Set.ext_iff.1 heq X
    simp only [Set.mem_ofPred_eq] at this
    tauto
  have hcomp : ∀ Hd : Blk sp.n FGP, Hd.slot ≤ s →
      (Compatible ℓp.frame.tree Hd B ↔ Compatible ℓy.frame.tree Hd B) := fun Hd hHd =>
    ⟨compatible_of_slot_le hΦp.coherent heq hHd hBs,
      compatible_of_slot_le hΦy.coherent heq.symm hHd hBs⟩
  change opponents sp ℓp.frame ⟨{w | w ∈ (voteViewList _ _ _ _).1}, _⟩ s B = _
  rw [hset]
  ext w
  constructor
  · rintro (⟨a, ha, b, hb, hab, rfl, hbv⟩ | ⟨x, hx, rfl, hxs, Hd, hHd, hHdr, hnc⟩)
    · have hm : ∀ v ∈ (tr.state p i).pool s,
          v ∈ (mergedVoteView sp e.readPoint ℓy.frame (s + 1)).votes := fun v hv =>
        Or.inr ⟨P, hP, hPs, hPv ▸ mem_voteViewList_fst.2 ⟨hv, hpool v hv⟩⟩
      exact Or.inl ⟨a, hm a ha, b, hm b hb, hab, rfl, hbv⟩
    · obtain ⟨⟨-, hst⟩, hres⟩ := mem_voteViewList_snd.1 hx
      obtain ⟨Hd', hHd', hHd'r, hHd's⟩ := resolved_head hres.ne
      have : Hd' = Hd := hΦp.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
      subst this
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
    · rcases hx with hx | ⟨X, hX, hXs, hx, -, Hd', hHd', hHd'r, hHd's⟩
      · -- an early support vote of the voter
        change x ∈ (voteViewList _ _ _ _).2 at hx
        rw [hcast, mem_voteViewList_snd] at hx
        obtain ⟨⟨hxp, hxt⟩, hres⟩ := hx
        obtain ⟨Hd', hHd', hHd'r, hHd's⟩ := resolved_head (hres.trans (etime_of_lt_top _)).ne
        have : Hd' = Hd := hΦy.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
        subst this
        have hHds : Hd'.slot ≤ s := by omega
        have hHdp := (hmem _ hHds).2 hHd
        rcases hstar x hxp (by simpa [freeze, hcast] using hxt) with hxP | hxP
        · -- the proposer holds it, resolved
          have hbs : (tr.state p i).blockStamp x.head ≠ ⊤ := by
            refine hHdr ▸ (blockStamp_lt_of_acceptedBefore sp hr hp hcp hHdp
              (T := tr.time i + 1) ?_ (fun k hk hrk => ?_)
              (Or.inr (by rw [hcall]; simp))).trans (etime_of_lt_top _) |>.ne
            · rcases frame_accepted hr hp i hcp Hd' hHdp with h | ⟨k, hk, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨k, h, by linarith [hr.time_mono hk]⟩
            · have := hrsp k hk hrk
              rw [hti, hts] at *
              linarith
          refine Or.inr ⟨x, mem_voteViewList_snd.2 ⟨⟨hxP, hpool x hxP⟩,
            lt_top_iff_ne_top.2 (resolutionTime_ne_top hΦp hHdp hHdr hHd's (hpool x hxP).ne hbs)⟩,
            rfl, hxs, Hd', hHdp, hHdr, fun h => hnc ((hcomp _ hHds).1 h)⟩
        · exact Or.inl hxP
      · -- a support entry of the proposal
        rw [hblk X hX hXs] at hx
        have : Hd' = Hd := hΦy.coherent.1 hHd' hHd (hHd'r.trans hHdr.symm)
        subst this
        have hHds : Hd'.slot ≤ s := by omega
        exact Or.inr ⟨x, hPsup ▸ hx, rfl, hxs, Hd', (hmem _ hHds).2 hHd, hHdr,
          fun h => hnc ((hcomp _ hHds).1 h)⟩

end Consensus.Goldilocks.SA

end

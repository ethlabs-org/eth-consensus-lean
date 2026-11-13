module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.MergedOpponents
import ConsensusLean.Lemmas.Tactic.Linarith

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

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → SAState sp.n}

/-- `frameIn_of_call` with the unlock given. -/
theorem frameIn_of_callU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

theorem frameIn_of_call (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U :=
  frameIn_of_callU (hr := hr.toU) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)

/-- `frame_accepted` with the unlock given. -/
theorem frame_acceptedU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
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

/-- Every block of an honest node's frame is genesis or was accepted by the node. -/
theorem frame_accepted (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksSA sp FGP ro)}, tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k X :=
  frame_acceptedU (hr := hr.toU) (y := y) (hy := hy) (i := i)

/-- The genesis block of an honest node's initial frame is in `U`, with slot `0`. -/
private theorem genesis_memU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
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

/-- `frameBlock_unique` with the unlock given. -/
theorem frameBlock_uniqueU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {σ : Nat} (hσ : σ ≠ 0)
    (hp : proposer σ ∈ H) {B B' : Blk sp.n FGP} (hB : HonestFrameBlock tr H B)
    (hB' : HonestFrameBlock tr H B') (hs : B.slot = σ) (hs' : B'.slot = σ) : B = B' := by
  have hr := hrun.localRun
  have hprop : ∀ X, HonestFrameBlock tr H X → X.slot = σ → X.proposer = proposer σ := by
    rintro X ⟨y, hy, i, ℓ, hc, hX⟩ hXs
    obtain ⟨G, hG, hGr, hGs⟩ := genesis_memU hr hy i hc
    refine hXs ▸ hrun.honest.proposer X ⟨y, hy, i, ℓ, hc, hX⟩ fun hXr => hσ ?_
    rw [← hXs, hr.coherent.1 ((frameIn_of_callU hr hy hc).2 hX) hG (hXr.trans hGr.symm), hGs]
  exact hrun.honest.one_block B B' hB hB' (hprop B hB hs ▸ hp)
    ((hprop B hB hs).trans (hprop B' hB' hs').symm) (hs.trans hs'.symm)

/-- An honest proposer of a slot `σ > 0` has one block of slot `σ` in the honest frames. -/
theorem frameBlock_unique (hrun : ACRun proposer tr H U) {σ : Nat} (hσ : σ ≠ 0)
    (hp : proposer σ ∈ H) {B B' : Blk sp.n FGP} (hB : HonestFrameBlock tr H B)
    (hB' : HonestFrameBlock tr H B') (hs : B.slot = σ) (hs' : B'.slot = σ) : B = B' :=
  frameBlock_uniqueU (hrun := hrun.toU) (σ := σ) (hσ := hσ) (hp := hp) (B := B) (B' := B')
      (hB := hB) (hB' := hB') (hs := hs) (hs' := hs')

/-- A vote with a finite stamp whose head is a stamped block of the tree of slot at most the
vote's is resolved. -/
theorem resolutionTime_ne_top {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
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

theorem mem_voteViewList_fst {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).1 ↔ v ∈ A.pool s ∧ A.voteStamp v < c := by
  simp [voteViewList, SAState.poolAt]

theorem mem_voteViewList_snd {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).2 ↔
      (v ∈ A.pool s ∧ A.voteStamp v < c) ∧ resolutionTime A Φ v < c := by
  simp [voteViewList, SAState.poolAt]
  tauto

theorem etime_of_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

/-- `proposal_payload` with the unlock given. -/
theorem proposal_payloadWith
    {L : Set Lock} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposalWith sp L A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ pay = voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ ∧
      (acProposalWith sp L A Φ t).1.restartTime = A.restartTime := by
  unfold acProposalWith at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hj
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hj, h.2.symm, rfl⟩

/-- The payload of a proposal is the proposer's view of the previous slot's pool, and the
proposer is joined. -/
theorem proposal_payload {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposal sp A Φ t).2 = some (d, pay)) :
    joined sp A t ∧ pay = voteViewList A Φ ((sp.slot t : Int) - 1) ⊤ ∧
      (acProposal sp A Φ t).1.restartTime = A.restartTime :=
  proposal_payloadWith (A := A) (Φ := Φ) (t := t) (d := d) (pay := pay) (h := h)

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
  -- the proposer has stamped the blocks of its tree
  have hbs : ∀ Hd ∈ ℓp.frame.tree, (tr.state p i).blockStamp Hd.root ≠ ⊤ := fun Hd hHd =>
    (blockStamp_lt_of_acceptedBefore sp hr hp hcp hHd (T := tr.time i + 1)
      (by
        rcases frame_accepted hr hp i hcp Hd hHd with h | ⟨k, hk, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, h, by linarith [hr.time_mono hk]⟩)
      (fun k hk hrk => by
        have := hrsp k hk hrk
        rw [hti, hts]
        linarith only [this, hΔ])
      (Or.inr (by rw [hcall]; simp))).trans (etime_of_lt_top _) |>.ne
  exact opponents_eq_of_merged hΦp hΦy heq hP hPs hPv hPsup
    (fun X hX hXs => huniq X ⟨y, hy, j, ℓy, hc.1, hX⟩ hXs) hpool
    (fun x hx Hd hHd hHdr hHds =>
      resolutionTime_ne_top hΦp hHd hHdr hHds (hpool x hx).ne (hHdr ▸ hbs Hd hHd))
    hstar hBs

end Consensus.Goldilocks.SA

end

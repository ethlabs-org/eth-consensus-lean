module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.MergedOpponents
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks AC: proposer and voters agree on unlocking (A1.1)

The proposal's view and an honest voter's merged view give the same opponents to every block of
slot at most `s`, under `Sync[t_s, t_{s+1}]`, when both frames hold the same blocks of slot at
most `s`. The same synchrony window ensures that the voter's read point backs each declared vote
of the honest proposer.

The merged view is the voter's slot-`s` votes held before the freeze `t_s + 3Δ` and the votes of
the slot-`(s+1)` proposals of its tree; the proposer is honest, so its proposal is the only one
(`HonestObjects.one_block`), and the proposal view is the proposer's slot-`s` pool. Each early
vote of the voter was admitted at a time in `[t_s, t_s + 3Δ)`; under `Sync` the proposer,
joined at `t_{s+1}`, processed it before `t_{s+1}`: it holds the vote, or two other votes of its
validator. Heads of slot at most `s` are in both trees, ancestry below slot `s` is the same, and the
proposer has stamped the blocks of its tree, so a resolved vote at the voter is resolved at the
proposer. -/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → ACState sp.n}

/-- `frameIn_of_callU` with the unlock given. -/
theorem frameIn_of_callU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- Every block of an honest node's frame is genesis or was accepted by the node. With the unlock
given. -/
theorem frame_acceptedU
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksAC sp FGP ro)}, tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      X.root = sp.genesisRoot ∨ ∃ k ≤ i, tr.AcceptAt y k X := by
  have step : ∀ (Φ Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksAC sp FGP ro).Call),
      (goldilocksAC sp FGP ro).CallOK U Φ t c Φ' → ∀ X ∈ Φ'.tree, X ∈ Φ.tree ∨ c = .block X := by
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
private theorem genesis_memU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksAC sp FGP ro)}, tr.CallAt y i ℓ →
      ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.slot = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, hslot, -⟩, ⟨-, hsub⟩, -⟩ | ⟨j, ℓ', hj, hc', -⟩
    · exact ⟨Φ₀.F, hsub (htree ▸ rfl), hroot, hslot⟩
    · exact ih j hj hc'

/-- An honest proposer of a slot `σ > 0` has at most one block of slot `σ` in the honest frames.
With the unlock given. -/
theorem frameBlock_uniqueU
    {ini} {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U ini) {σ : Nat} (hσ : σ ≠ 0)
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

/-- A vote with a finite stamp whose head is a stamped block of the tree of slot at most the
vote's is resolved. -/
theorem resolutionTime_ne_top {A : ACState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
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

theorem mem_voteViewList_fst {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).1 ↔ v ∈ A.pool s ∧ A.voteStamp v < c := by
  simp [voteViewList, ACState.poolAt]

theorem mem_voteViewList_snd {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {c : ETime} {v : Vote sp.n} :
    v ∈ (voteViewList A Φ (s : Int) c).2 ↔
      (v ∈ A.pool s ∧ A.voteStamp v < c) ∧ resolutionTime A Φ v < c := by
  simp [voteViewList, ACState.poolAt]
  tauto

theorem etime_of_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

/-- `proposal_payload` with the unlock given. -/
theorem proposal_payloadWith
    {L : Set Lock} {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
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
theorem proposal_payload {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
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
  have hcount := count_declared_of_syncU hr.toU (fun _ => voteStart_initial _) hp hy
    hprop hti hc hs hPy hsync
  obtain ⟨hcp, hcall, d, hpay⟩ := hprop
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callU hr.toU hp hcp
  obtain ⟨hΦy, -⟩ := frameIn_of_callU hr.toU hy hc.1
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
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
  -- the only slot-`(s+1)` block of the honest frames is the proposal
  obtain ⟨P, hP, hPs, hPpay⟩ := hPy
  have hPv : declaredHeadVotes P = (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).1 := by
    simp only [declaredHeadVotes, hPpay]
  have hPsup : declaredSupportVotes P = (voteViewList (tr.state p i) ℓp.frame (s : Int) ⊤).2 := by
    simp only [declaredSupportVotes, hPpay]
  have huniq : ∀ X, HonestFrameBlock tr H X → X.slot = s + 1 → X = P := fun X hX hXs =>
    frameBlock_uniqueU hrun.toU (by omega) (hpp ▸ hp) hX ⟨y, hy, j, ℓy, hc.1, hP⟩ hXs hPs
  -- the proposal's votes are the proposer's slot-`s` pool
  have hpool : ∀ w ∈ (tr.state p i).pool s, (tr.state p i).voteStamp w < ⊤ := by
    intro w hw
    have hws := state_pool_slotU sp hr.toU (fun _ => voteStart_initial _) hp i s w hw
    obtain ⟨k, -, -, h, -⟩ :=
      pool_origin_sentU hr.toU (fun _ => voteStart_initial _) hp i w (hws ▸ hw)
    exact h ▸ etime_of_lt_top _
  -- **every early vote of the voter reaches the proposer**
  have hstar : ∀ x ∈ e.readPoint.pool s, e.readPoint.voteStamp x < ETime.of (sp.ts s + 3 * sp.Δ) →
      x ∈ (tr.state p i).pool s ∨ x.val ∈ equivocators {w | w ∈ (tr.state p i).pool s} := by
    intro x hx hxt
    obtain ⟨hx1, hx2⟩ := readPoint_poolU hr.toU hy hc hx
    have hxs : x.slot = s := state_pool_slotU sp hr.toU (fun _ => voteStart_initial _) hy (j + 1) s
        x hx1
    obtain ⟨k, -, hsend, hst, hsl⟩ :=
      pool_origin_sentU hr.toU (fun _ => voteStart_initial _) hy (j + 1) x (hxs ▸ hx1)
    rw [hx2 hxs] at hst
    have htk : tr.time k < sp.ts s + 3 * sp.Δ := etime_of_lt_of.1 (hst ▸ hxt)
    have hsk : sp.ts s ≤ tr.time k :=
      (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by rw [← hxs]; exact_mod_cast hsl)
    have := sync_forward hr hsync hy hsend hsk (by rw [hts]; linarith) hp hcp
      (fun k' hk' hr' => (hrsp k' hk' hr').trans hsk) (by rw [hti, hts]; linarith)
      fun t h₁ h₂ => by
        rw [slot_of_mem sp s (hsk.trans h₁) (by rw [hts]; linarith), hxs]; omega
    rwa [hxs] at this
  -- the proposer has stamped the blocks of its tree
  have hbs : ∀ Hd ∈ ℓp.frame.tree, (tr.state p i).blockStamp Hd.root ≠ ⊤ := fun Hd hHd =>
    (blockStamp_lt_of_acceptedBeforeU sp hr.toU (fun _ => voteStart_initial _) hp hcp hHd
      (T := tr.time i + 1)
      (by
        rcases frame_acceptedU hr.toU hp i hcp Hd hHd with h | ⟨k, hk, h⟩
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
    hstar hcount hBs

end Consensus.Goldilocks.AC

end

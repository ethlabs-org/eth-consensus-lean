module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: what a result carries to a voter (A1.8 (c), (d))

For an update result `C` of an honest `X` in slot `s` with counted votes `CV`, and an honest
`y`'s slot-`(s+1)` vote with `Carry_y(s, ·, C)` and the writer-pool condition (d):
* the merged view's support is among its votes (support entries are votes of the block,
  `validPayload`);
* the validators of `CV` are supporters of `C` in `y`'s merged view: `y` holds each counted vote
  (two other votes of a validator would be in `X`'s pool by (d) and make it an equivocator
  there), received and resolved before the vote freeze (its head accepted before
  `t_s + 3Δ`, in `y`'s tree since it extends `C`), and none of them equivocates at `y` (by (d),
  again);
* the merged view's voters are participants at `X` (by (d));
* the counted validators are a strict majority of `X`'s participants (`get_confirmation`). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

theorem mem_admitVote_pool {A : SAState sp.n} {t : Time} {v x : Vote sp.n} {σ : Nat}
    (h : x ∈ A.pool σ) : x ∈ (admitVote sp A t v).pool σ := by
  unfold admitVote
  split_ifs
  · exact h
  · exact h
  · simp only [Function.update_apply]
    split_ifs with he
    · subst he; exact List.mem_append_left _ h
    · exact h

/-- `merged_vote_slot` with the unlock given. -/
theorem merged_vote_slotUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s := by
  rintro v (hv | ⟨B, hB, hBs, hv⟩)
  · have hv : v ∈ e.readPoint.poolAt ((s + 1 : Nat) - 1 : Int) := (List.mem_filter.1 hv).1
    simp only [SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    have hpost : v ∈ (tr.post i).pool s := by
      rw [post_of_castAtUS hr hst hy hc, optimisticConfirmationM_keep _ optimistic_pool]
      exact mem_admitVote_pool (by simpa using hv)
    refine state_pool_slotUS sp hr hy (i + 1) s v ?_
    rw [Trace.state]
    split_ifs with h
    · exact hpost
    · exact absurd ⟨hc.1.1, by simp [hc.1.2]⟩ h
  · have := (frame_validPayloadUS sp hr hy hc.1 B hB).1 v hv
    exact Nat.succ_injective (this.trans hBs)

/-- Merged vote slots at the parent's walk start. -/
theorem merged_vote_slotU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s :=
  merged_vote_slotUS (st := fun _ => parentWalkStartFn sp) hr
    (fun _ => walkStartLaw_parentWalkStartFn) hy hc

/-- Every vote of an honest voter's merged view of slot `s + 1` has slot `s`. -/
theorem merged_vote_slot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s :=
  merged_vote_slotU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)
      (s := s)

/-- `merged_support_subset` with the unlock given. -/
theorem merged_support_subsetUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (σ : Nat) :
    (mergedVoteView sp e.readPoint ℓ.frame σ).support ⊆
      (mergedVoteView sp e.readPoint ℓ.frame σ).votes := by
  rintro v (hv | ⟨B, hB, hBs, hv, -⟩)
  · exact Or.inl (List.mem_of_mem_filter hv)
  · exact Or.inr ⟨B, hB, hBs, (frame_validPayloadUS sp hr hy hc.1 B hB).2 v hv⟩

/-- Merged support inclusion at the parent's walk start. -/
theorem merged_support_subsetU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (σ : Nat) :
    (mergedVoteView sp e.readPoint ℓ.frame σ).support ⊆
      (mergedVoteView sp e.readPoint ℓ.frame σ).votes :=
  merged_support_subsetUS (st := fun _ => parentWalkStartFn sp) hr hy hc σ

/-- The support of an honest voter's merged view is among its votes. -/
theorem merged_support_subset (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (σ : Nat) :
    (mergedVoteView sp e.readPoint ℓ.frame σ).support ⊆
      (mergedVoteView sp e.readPoint ℓ.frame σ).votes :=
  merged_support_subsetU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)
      (σ := σ)

/-- The validators counted for an update result are a strict majority of the update's
participants. -/
theorem result_majority {X : Fin sp.n} {i₀ s : Nat} {C : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hres : ResultAt tr X i₀ s C CV) :
    (voters {v | v ∈ (tr.state X i₀).pool s}).ncard < 2 * {w | ∃ v ∈ CV, v.val = w}.ncard := by
  obtain ⟨ℓ, -, hC, rfl⟩ := hres
  have hmaj := ((deepest_mem hC).1).2.2
  refine lt_of_lt_of_le hmaj (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
  rintro w ⟨hw, x, ⟨hx, hres⟩, hval, -, hanc⟩
  exact ⟨x, ⟨hx, hval ▸ hw, hres, hanc⟩, hval⟩

/-- `merged_voters_subset` with the unlock given. -/
theorem merged_voters_subsetUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} {P : List (Vote sp.n)}
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ P ∨ v.val ∈ equivocators {w | w ∈ P}) :
    voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ voters {v | v ∈ P} := by
  rintro w ⟨v, hv, rfl⟩
  rcases hd v hv (merged_vote_slotUS hr hst hy hc v hv) with h | ⟨x, hx, -, -, -, hxv, -⟩
  · exact ⟨v, h, rfl⟩
  · exact ⟨x, hx, hxv⟩

/-- Merged voter inclusion at the parent's walk start. -/
theorem merged_voters_subsetU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} {P : List (Vote sp.n)}
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ P ∨ v.val ∈ equivocators {w | w ∈ P}) :
    voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ voters {v | v ∈ P} :=
  merged_voters_subsetUS (st := fun _ => parentWalkStartFn sp) hr
    (fun _ => walkStartLaw_parentWalkStartFn) hy hc hd

/-- Under the writer-pool condition (d), the voters of `y`'s merged view are participants at
`X`. -/
theorem merged_voters_subset (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {s : Nat} {P : List (Vote sp.n)}
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ P ∨ v.val ∈ equivocators {w | w ∈ P}) :
    voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ voters {v | v ∈ P} :=
  merged_voters_subsetU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)
      (s := s) (P := P) (hd := hd)

/-- In a well-formed frame, `lookup` finds every block of the tree by its root. -/
theorem lookup_of_mem {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {B : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) : lookup Φ B.root = some B := by
  cases h : lookup Φ B.root with
  | none => exact absurd ⟨B, hB, rfl⟩ (lookup_eq_none h)
  | some B' =>
    obtain ⟨hB', hr⟩ := lookup_eq_some h
    exact congrArg some (hΦ.coherent.1 hB' hB hr)

private theorem admitVote_fields (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).blockStamp = A.blockStamp ∧
      (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem optimistic_fields (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmationM sp wm A Φ t).blockStamp = A.blockStamp ∧
      (optimisticConfirmationM sp wm A Φ t).restartTime = A.restartTime := by
  refine optimisticConfirmationM_of (P := fun X => X.blockStamp = A.blockStamp ∧
    X.restartTime = A.restartTime) ?_ ⟨rfl, rfl⟩
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> exact ⟨rfl, rfl⟩

private theorem blockReceipt_blockStamp (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).blockStamp = Function.update A.blockStamp B.root (ETime.of t) := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').blockStamp = A'.blockStamp from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => exact fun A' => (ih _).trans (admitVote_fields _ _ _).1

private theorem tryVote_readPoint
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : ∀ e ∈ (tryVoteWithM sp wm x L A Φ t).2, e.readPoint.blockStamp = A.blockStamp := by
  unfold tryVoteWithM
  dsimp only
  split_ifs <;> simp

private theorem onTick_readPoint
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    ∀ e ∈ (acOnTickWithM sp wm x L A Φ t).2, e.readPoint.blockStamp = A.blockStamp := by
  unfold acOnTickWithM
  dsimp only
  split_ifs
  all_goals first | exact tryVote_readPoint x A Φ t | simp

/-- `readPoint_blockStamp` with the unlock given. -/
theorem readPoint_blockStampU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {r : Nat}
    (hrB : ∀ B, ℓ.call = .block B → r ≠ B.root) :
    e.readPoint.blockStamp r = (tr.state y i).blockStamp r := by
  obtain ⟨hc, he⟩ := hc
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have he' : e ∈ (stepWithM sp ro wm y (u i) (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by
    rw [hx]; exact he
  clear hx he
  generalize tr.state y i = A at he' ⊢
  revert hrB he'
  cases ℓ.call with
  | tick => exact fun _ he' => by rw [onTick_readPoint (L := u i) y A _ _ e he']
  | proposal => intro _ he'; simp at he'
  | toFG => intro _ he'; simp at he'
  | message m =>
    intro _ he'
    rw [tryVote_readPoint (L := u i) y _ _ _ e he', (optimistic_fields _ _ _).1, (admitVote_fields
        _ _ _).1]
  | block B =>
    intro hrB he'
    rw [tryVote_readPoint (L := u i) y _ _ _ e he', (optimistic_fields _ _ _).1,
        blockReceipt_blockStamp,
      Function.update_of_ne (hrB B rfl)]
  | restart =>
    intro _ he'
    change e ∈ (acRestart sp ro y A ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- The read point of an honest vote has the block stamps of the state before its call, except
for the block that an `on_block` call receives. -/
theorem readPoint_blockStamp (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {r : Nat}
    (hrB : ∀ B, ℓ.call = .block B → r ≠ B.root) :
    e.readPoint.blockStamp r = (tr.state y i).blockStamp r :=
  readPoint_blockStampU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)
      (r := r) (hrB := hrB)

/-- An early accepted block retained in the frame has a strictly early stamp at the
emission read point, including through restart replay. Unique acceptance excludes a
late `block` call overwriting that stamp. -/
theorem readPoint_blockStamp_lt_of_acceptedBefore
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ell e) {B : Blk sp.n FGP}
    (hB : B ∈ ell.frame.tree) (hacc : AcceptedBefore tr y B (freeze sp e.msg.slot))
    (hrs : ∀ k ≤ i, tr.RestartAt y k → tr.time k < freeze sp e.msg.slot)
    (ht : freeze sp e.msg.slot ≤ tr.time i) :
    e.readPoint.blockStamp B.root < ETime.of (freeze sp e.msg.slot) := by
  have hPhiU : ell.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ell hc.1 with ⟨-, _, -, -, h⟩ | ⟨_, _, -, -, -, h⟩ <;>
      exact h.1.2
  have hstamp := blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hB hacc hrs (Or.inl ht)
  rw [readPoint_blockStamp hr hy hc ?_]
  · exact hstamp
  intro C hcall hroot
  have hC := (accept_new sp hr hy ⟨ell, hc.1, hcall⟩).1 ell hc.1
  have heq : C = B := hr.coherent.1 (hPhiU hC) (hPhiU hB) hroot.symm
  subst C
  rcases hacc with hg | ⟨k, hk, hkt⟩
  · exact accept_ne_genesis sp hr hy ⟨ell, hc.1, hcall⟩ hg
  · obtain rfl := accept_unique sp hr hy hk ⟨ell, hc.1, hcall⟩
    exact (not_lt_of_ge ht) hkt

/-- A block accepted before the freeze belongs to an honest vote's frozen domain,
including genesis. -/
theorem voterBlockTree_of_acceptedBefore (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ell e) {B : Blk sp.n FGP}
    (hB : B ∈ ell.frame.tree) (hacc : AcceptedBefore tr y B (freeze sp e.msg.slot))
    (hrs : ∀ k ≤ i, tr.RestartAt y k → tr.time k < freeze sp e.msg.slot)
    (ht : freeze sp e.msg.slot ≤ tr.time i) :
    B ∈ voterBlockTree sp e.readPoint ell.frame e.msg.slot :=
  ⟨hB, Or.inl (readPoint_blockStamp_lt_of_acceptedBefore hr hy hc hB hacc hrs ht)⟩

/-- `carried_supporter` with the unlock given. -/
theorem carried_supporterU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {s : Nat}
    (hs : e.msg.slot = s + 1) {C : Blk sp.n FGP} (hC : C ∈ ℓ.frame.tree) {v : Vote sp.n}
    (hvs : v.slot = s) (hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ))
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Hv.slot ≤ s ∧ Anc U C Hv ∧
      AcceptedBefore tr y Hv (sp.ts s + 3 * sp.Δ))
    (hneq : v.val ∉ equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes) :
    v.val ∈ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨Hv, hHvU, hHvr, hHvs, hCHv, hacc⟩ := hhead
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  obtain ⟨-, hslot, hjoin, -⟩ := castAt_specU hr hy hc
  have hti : sp.slot (tr.time i) = s + 1 := hslot ▸ hs
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  -- the vote is cast after the freeze `t_s + 3Δ`
  have hT : sp.ts s + 3 * sp.Δ < tr.time i := by
    have h := (ts_le_iff_le_slot sp (hr.time_nonneg i) ((s : Int) + 1)).2
      (by rw [hti]; push_cast; rfl)
    simp only [SAParams.ts] at h ⊢
    linarith
  obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_callU sp hr hy _ _ hc.1
  -- the head is in the voter's tree
  have hF : Anc U ℓ.frame.F Hv := ((hΦ.rooted.2 C hC).mono hΦU).trans hCHv
  have hHvt : Hv ∈ ℓ.frame.tree := by
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · obtain rfl : Hv = G := hU.1 hHvU hGU (hg.trans hGr.symm)
      obtain h | ⟨c, -, hcp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hF
      · exact h ▸ hΦ.rooted.1
      · exact absurd (hcp.2.2.symm.trans hGp) (Option.some_ne_none _)
    · have hki : k ≤ i := by
        by_contra h
        have := hr.time_mono (le_of_not_ge h)
        exact lt_irrefl _ (lt_trans (hT.trans_le this) hkt)
      exact mem_tree_of_acceptAtU sp hr hy hk hki hc.1 hF
  -- the voter's restarts were before `t_s`
  have hjp : joined sp (tr.post i) (tr.time i) := by
    rw [post_of_castAtU hr hy hc]
    unfold joined at hjoin ⊢
    rwa [(optimistic_fields _ _ _).2, (admitVote_fields _ _ _).2]
  have hrs : ∀ k ≤ i, tr.RestartAt y k → tr.time k < sp.ts s + 3 * sp.Δ := by
    intro k hk hrk
    have h := (joined_awakeU sp FGP ro H U tr hr y hy i ℓ hc.1 hjp).2 k hk hrk
    rw [hti] at h
    have : sp.ts (((s + 1 : Nat) : Int) - 1) = sp.ts s := by congr 1; push_cast; ring
    exact (h.trans_eq this).trans_lt (lt_add_of_pos_right _ (mul_pos (by decide) hΔ))
  -- the head is not the block that this very call receives
  have hne : ∀ B, ℓ.call = .block B → v.head ≠ B.root := by
    intro B₀ hcall hB
    have key : ∀ Φ, (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call ℓ.frame →
        FrameStep Φ B₀ ℓ.frame := by
      intro Φ hok
      rw [hcall] at hok
      exact hok.2.1
    have hB₀ : ∀ Φ, FrameStep Φ B₀ ℓ.frame → B₀ = Hv := fun Φ hst =>
      hU.1 (hΦU (hst.tree_eq ▸ ⟨Set.mem_insert _ _, hst.F'_anc_B⟩)) hHvU
        (hB.symm.trans hHvr.symm)
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, hok⟩ | ⟨j, ℓ', -, -, -, hok⟩ <;>
      · have hst := key _ hok
        obtain rfl := hB₀ _ hst
        obtain rfl : B₀ = G := hU.1 hHvU hGU (hg.trans hGr.symm)
        obtain ⟨P, -, hP⟩ := hst.parent_mem
        exact absurd (hP.symm.trans hGp) (Option.some_ne_none _)
    · have hki : k < i := by
        by_contra h
        have := hr.time_mono (not_lt.1 h)
        exact lt_irrefl _ (lt_trans (hT.trans_le this) hkt)
      obtain ⟨ℓk, hck, hkB⟩ := hk
      rcases hr.frameLaw y hy i ℓ hc.1 with ⟨hnc, -⟩ | ⟨j, ℓ', hj, hc', hnc, hok⟩
      · exact hnc k (Nat.zero_le _) hki ℓk hck
      have hkj : k ≤ j := by
        by_contra h
        exact hnc k (Nat.lt_of_not_le h) hki ℓk hck
      have hst := key _ hok
      obtain rfl := hB₀ _ hst
      obtain ⟨-, hΦ'U⟩ : FrameOK ℓ'.frame ∧ ℓ'.frame.tree ⊆ U := by
        rcases hr.frameLaw y hy j ℓ' hc' with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
          exact h.1
      have hanc : Anc U ℓ'.frame.F B₀ :=
        Anc.mono (Set.insert_subset_iff.2 ⟨hHvU, hΦ'U⟩) (hst.F_anc_F'.trans hst.F'_anc_B)
      exact hst.new (mem_tree_of_acceptAtU sp hr hy ⟨ℓk, hck, hkB⟩ hkj hc' hanc)
  -- the vote is resolved before the freeze
  have hbs := blockStamp_lt_of_acceptedBeforeU sp hr hy hc.1 hHvt hacc hrs (Or.inl hT.le)
  rw [hHvr, ← readPoint_blockStampU hr hy hc hne] at hbs
  have hfz : freeze sp (s + 1) = sp.ts s + 3 * sp.Δ := by simp [freeze]
  have hres : resolutionTime e.readPoint ℓ.frame v < ETime.of (freeze sp (s + 1)) := by
    unfold resolutionTime
    rw [← hHvr, lookup_of_mem hΦ hHvt]
    simp only [not_lt.2 (hHvs.trans_eq hvs.symm), ite_false, hfz]
    exact max_lt hheld.2 (hHvr ▸ hbs)
  refine ⟨hneq, v, Or.inl ?_, rfl, by simp [hvs], Hv, hHvt, hHvr,
    anc_tree_of_anc_U hU hΦ hΦU hC hCHv hHvt⟩
  refine List.mem_filter.2 ⟨List.mem_filter.2 ⟨?_, ?_⟩, by simpa using hres⟩
  · simp only [SAState.poolAt, ite_false, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) from
      not_lt.2 (sub_nonneg.2 (Int.ofNat_le.2 (Nat.le_add_left 1 s)))]
    simpa [hvs] using hheld.1
  · simpa [hfz] using hheld.2

/-- **A carried vote is a supporter.** A slot-`s` vote that an honest voter of slot `s + 1`
holds, received before the vote freeze `t_s + 3Δ`, whose head (of slot at most `s`) extends a
block `C` of the voter's tree and was accepted by the voter before the freeze, and whose
validator does not equivocate in the voter's merged view, makes that validator a supporter of
`C` there (the head is still in the voter's tree, and the vote is resolved before the freeze:
the voter is joined, so its restarts were before `t_s`). -/
theorem carried_supporter (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {s : Nat}
    (hs : e.msg.slot = s + 1) {C : Blk sp.n FGP} (hC : C ∈ ℓ.frame.tree) {v : Vote sp.n}
    (hvs : v.slot = s) (hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ))
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Hv.slot ≤ s ∧ Anc U C Hv ∧
      AcceptedBefore tr y Hv (sp.ts s + 3 * sp.Δ))
    (hneq : v.val ∉ equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes) :
    v.val ∈ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C :=
  carried_supporterU (hrun := hrun.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)
      (s := s) (hs := hs) (C := C) (hC := hC) (v := v) (hvs := hvs) (hheld := hheld)
          (hhead := hhead) (hneq := hneq)

/-- `carried_cover` with the unlock given. -/
theorem carried_coverU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {s : Nat}
    (hs : e.msg.slot = s + 1) {C : Blk sp.n FGP} (hC : C ∈ ℓ.frame.tree) {CV : Set (Vote sp.n)}
    (hcarry : CarryAt tr U y i e s CV) {v : Vote sp.n} (hv : v ∈ CV) (hvs : v.slot = s)
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Hv.slot ≤ s ∧ Anc U C Hv) :
    v.val ∈ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C ∪
      equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
  have hU := hrun.localRun.coherent
  have hm : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
      u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
    intro u hus hu
    refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
    · simp only [SAState.poolAt, ite_false, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) from
        not_lt.2 (sub_nonneg.2 (Int.ofNat_le.2 (Nat.le_add_left 1 s)))]
      simpa [hus] using hu.1
    · simpa [freeze] using hu.2
  rcases hcarry.holds v hv with hheld | ⟨v₁, v₂, h12, -, -, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
  · by_cases heq : v.val ∈ equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes
    · exact Or.inr heq
    obtain ⟨Hv, hHv, hHvr, hHvs, hCHv⟩ := hhead
    obtain ⟨Hv', hHv', hHv'r, hacc⟩ := hcarry.heads v hv
    obtain rfl : Hv' = Hv := hU.1 hHv' hHv (hHv'r.trans hHvr.symm)
    exact Or.inl (carried_supporterU hrun hy hc hs hC hvs hheld
      ⟨Hv', hHv', hHv'r, hHvs, hCHv, hacc Hv' Relation.ReflTransGen.refl⟩ heq)
  · exact Or.inr ⟨v₁, hm v₁ hs₁ hh₁, v₂, hm v₂ hs₂ hh₂, h12, hv₁, hv₂⟩

/-- **A carried vote covers its validator.** The validator of a slot-`s` vote that `Carry_y`
covers, whose head (of slot at most `s`) extends a block `C` of the voter's tree, is a supporter of
`C` in the voter's merged view or an equivocator there (two other held votes of it, or a second
vote beside the held one). -/
theorem carried_cover (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {s : Nat}
    (hs : e.msg.slot = s + 1) {C : Blk sp.n FGP} (hC : C ∈ ℓ.frame.tree) {CV : Set (Vote sp.n)}
    (hcarry : CarryAt tr U y i e s CV) {v : Vote sp.n} (hv : v ∈ CV) (hvs : v.slot = s)
    (hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ Hv.slot ≤ s ∧ Anc U C Hv) :
    v.val ∈ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C ∪
      equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes :=
  carried_coverU (hrun := hrun.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e) (hc := hc)
      (s := s) (hs := hs) (C := C) (hC := hC) (CV := CV) (hcarry := hcarry) (v := v) (hv := hv)
          (hvs := hvs) (hhead := hhead)

/-- `counted_supporters` with the unlock given. -/
theorem counted_supportersU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {X y : Fin sp.n} (hX : X ∈ H)
        (hy : y ∈ H)
    {i₀ i s : Nat} {C D : Blk sp.n FGP} {ℓX ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hcX : tr.CallAt X i₀ ℓX) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) (hCD : Anc U C D)
    (hcarry : CarryAt tr U y i e s (fastCounted sp (tr.state X i₀) ℓX.frame s D))
    (hviab : ViableAtVote ℓ e (s + 1) C)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame s D, v.val = w} ⊆
      supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦX, hΦXU⟩ : FrameOK ℓX.frame ∧ ℓX.frame.tree ⊆ U := by
    rcases hr.frameLaw X hX i₀ ℓX hcX with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hCt : C ∈ ℓ.frame.tree := by
    obtain ⟨hΦ, -⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
      rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
        exact h.1
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  -- a validator that is not an equivocator at `X` has at most one vote in `y`'s merged view
  have hone : ∀ w ∉ equivocators {x | x ∈ (tr.state X i₀).pool s}, ∀ v₁ v₂,
      v₁ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₂ ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes →
      v₁.val = w → v₂.val = w → v₁ = v₂ := by
    intro w hw v₁ v₂ h₁ h₂ hv₁ hv₂
    by_contra hne
    rcases hd v₁ h₁ (merged_vote_slotU hr hy hc v₁ h₁) with h₁' | h₁'
    · rcases hd v₂ h₂ (merged_vote_slotU hr hy hc v₂ h₂) with h₂' | h₂'
      · exact hw ⟨v₁, h₁', v₂, h₂', hne, hv₁, hv₂⟩
      · exact hw (hv₂ ▸ h₂')
    · exact hw (hv₁ ▸ h₁')
  rintro w ⟨v, ⟨hvp, hvw, hvres, hvanc⟩, rfl⟩
  have hvs : v.slot = s := state_pool_slotU sp hr hX i₀ s v hvp
  -- the head is the block of `X`'s tree that the vote resolves on, of slot at most `s`
  obtain ⟨Hd, hHd, hHdr, hHds⟩ : ∃ Hd ∈ ℓX.frame.tree, Hd.root = v.head ∧ Hd.slot ≤ v.slot := by
    unfold resolutionTime at hvres
    split at hvres
    · exact absurd hvres (by simp [ETime.of])
    · rename_i Hd hl
      obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
      split_ifs at hvres with hlt
      · exact absurd hvres (by simp [ETime.of])
      · exact ⟨Hd, hHd, hHdr, Nat.le_of_not_lt hlt⟩
  have hCHd : Anc U C Hd := by
    obtain ⟨R, hR, hRr, hCR⟩ := hvanc
    have : R = Hd := hΦXU hR |> fun h => hU.1 h (hΦXU hHd) (hRr.trans hHdr.symm)
    subst this
    exact hCD.trans (Anc.mono hΦXU hCR)
  -- `y` holds `v` itself: two other votes of its validator would make it an equivocator at `X`
  have hheld : HeldBefore e.readPoint v (sp.ts s + 3 * sp.Δ) := by
    rcases hcarry.holds v ⟨hvp, hvw, hvres, hvanc⟩ with h | ⟨v₁, v₂, h12, h1, -, hv₁, hv₂, hs₁, hs₂,
      hh₁, hh₂⟩
    · exact h
    · exfalso
      have hm : ∀ u, u.slot = s → HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
          u ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
        intro u hus hu
        refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
        · simp only [SAState.poolAt, ite_false, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) from
            not_lt.2 (sub_nonneg.2 (Int.ofNat_le.2 (Nat.le_add_left 1 s)))]
          simpa [hus] using hu.1
        · simpa [freeze] using hu.2
      exact h12 (hone _ hvw v₁ v₂ (hm v₁ hs₁ hh₁) (hm v₂ hs₂ hh₂) hv₁ hv₂)
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v ⟨hvp, hvw, hvres, hvanc⟩
  have hHvd : Hv = Hd := hU.1 hHv (hΦXU hHd) (hHvr.trans hHdr.symm)
  subst hHvd
  refine carried_supporterU hrun hy hc hs hCt hvs hheld
    ⟨Hv, hHv, hHvr, hvs ▸ hHds, hCHd, hacc Hv Relation.ReflTransGen.refl⟩ fun hq => ?_
  obtain ⟨x, hx, x', hx', hne, hxv, hx'v⟩ := hq
  exact hne (hone _ hvw x x' hx hx' hxv hx'v)

/-- The validators that an honest `X`'s update counts for a block `D` (`fastCounted`, at a call of
`X`) are supporters of every `C ⪯ D` in an honest voter's merged view of the next slot, under
`Carry_y` for the counted votes, `C` viable at the vote, and the writer-pool condition (A1.8 (a),
(c), (d)). -/
theorem counted_supporters (hrun : ACRun proposer tr H U) {X y : Fin sp.n} (hX : X ∈ H) (hy : y ∈ H)
    {i₀ i s : Nat} {C D : Blk sp.n FGP} {ℓX ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hcX : tr.CallAt X i₀ ℓX) (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) (hCD : Anc U C D)
    (hcarry : CarryAt tr U y i e s (fastCounted sp (tr.state X i₀) ℓX.frame s D))
    (hviab : ViableAtVote ℓ e (s + 1) C)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    {w | ∃ v ∈ fastCounted sp (tr.state X i₀) ℓX.frame s D, v.val = w} ⊆
      supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s C :=
  counted_supportersU (hrun := hrun.toU) (X := X) (y := y) (hX := hX) (hy := hy) (i₀ := i₀)
      (i := i) (s := s) (C := C) (D := D) (ℓX := ℓX) (ℓ := ℓ) (e := e) (hcX := hcX) (hc := hc)
          (hs := hs) (hCD := hCD) (hcarry := hcarry) (hviab := hviab) (hd := hd)

end Consensus.Goldilocks.SA

end

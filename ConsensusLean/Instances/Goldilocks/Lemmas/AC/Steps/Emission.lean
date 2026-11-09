module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: an honest vote

Every emission of an honest node's call is the vote of `try_vote` (a restart's replay sends
nothing, A0.7): it is the node's own vote of the slot of the call's time, cast while joined, and
its head is the walk from the anchor over the viable tree of the vote domain (the voter block
tree, or the whole tree when the voter block tree has no viable block) with the merged view
against the previous slot, all read at the emission's read point (the unlocking and `voted_slot`
change nothing the walk reads but the locks). -/

namespace Consensus.Goldilocks.SA

variable {wm : WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- The vote emitted by a call whose head walk starts at `st`. -/
private def VoteSpecS (st : WalkStartFn sp FGP) (x : Fin sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (e : Em sp FGP) : Prop :=
  e.msg.val = x ∧ e.msg.slot = sp.slot t ∧ joined sp e.readPoint t ∧
    e.msg.head = (getHeadFrom sp
      (st e.readPoint Φ t (mergedVoteView sp e.readPoint Φ e.msg.slot) ((e.msg.slot : Int) - 1))
      Φ t (Φ.viableTree (voteDomain sp e.readPoint Φ e.msg.slot))
      (mergedVoteView sp e.readPoint Φ e.msg.slot) ((e.msg.slot : Int) - 1)).root

private def EmitsVotesS (m : WriteMode) (st : WalkStartFn sp FGP) (x : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (r : SAState sp.n × List (Em sp FGP)) : Prop :=
  ∀ e ∈ r.2, VoteSpecS st x Φ t e ∧
    r.1 = optimisticConfirmationM sp m (admitVote sp e.readPoint t e.msg) Φ t

private theorem tryVote_emitsS {st : WalkStartFn sp FGP} (hst : WalkStartLaw st)
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    EmitsVotesS wm st x Φ t (tryVoteWithMS sp wm st x L A Φ t) := by
  unfold tryVoteWithMS
  dsimp only
  split_ifs with h1
  · simp [EmitsVotesS]
  · simp [EmitsVotesS]
  all_goals
    simp only [EmitsVotesS, List.mem_singleton, forall_eq, and_true]
    refine ⟨rfl, rfl, not_not.1 (not_or.1 h1).1, ?_⟩
    dsimp only
    congr 2
    exact (hst.votedSlot _ Φ t _ _ _).symm

private theorem onTick_emitsS {st : WalkStartFn sp FGP} (hst : WalkStartLaw st)
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    EmitsVotesS wm st x Φ t (acOnTickWithMS sp wm st x L A Φ t) := by
  unfold acOnTickWithMS
  dsimp only
  split_ifs with _ ht hu hu
  · have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · simp [EmitsVotesS]
  · exact tryVote_emitsS hst x A Φ t
  · simp [EmitsVotesS]
  · simp [EmitsVotesS]

private theorem step_emitsS {st : WalkStartFn sp FGP} (hst : WalkStartLaw st)
    {L : Set Lock} (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    EmitsVotesS wm st y Φ t (stepWithMS sp ro wm st y L A Φ t c) := by
  cases c with
  | tick => exact onTick_emitsS hst y A _ _
  | proposal => simp [EmitsVotesS]
  | toFG => simp [EmitsVotesS]
  | message m => exact tryVote_emitsS hst y _ _ _
  | block B => exact tryVote_emitsS hst y _ _ _
  | restart =>
    intro e he
    change e ∈ (acRestart sp ro y A Φ t).2 at he
    rw [((restart_state sp) FGP ro y A Φ t hΦ ht).1] at he
    simp at he

private theorem cast_emitsUS {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    VoteSpecS (st i) y ℓ.frame (tr.time i) e ∧ tr.post i =
      optimisticConfirmationM sp wm (admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
        (tr.time i) := by
  obtain ⟨hc, he⟩ := hc
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have h := step_emitsS (wm := wm) (hst i) (L := u i) y (tr.state y i) ℓ.frame (tr.time i) ℓ.call hΦ
    (hr.time_nonneg i)
  rw [hx] at h
  exact h e he

/-- The vote of a run from `st`, read at its emission's read point. -/
theorem castAt_specUS {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i))
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHeadFrom sp
        (st i e.readPoint ℓ.frame (tr.time i)
          (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1))
        ℓ.frame (tr.time i) (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  (cast_emitsUS hr hst hy hc).1

/-- The vote of `x` at frame `Φ` and time `t`, as `castAt_spec` states it. -/
private def VoteSpec (x : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time) (e : Em sp FGP) : Prop :=
  e.msg.val = x ∧ e.msg.slot = sp.slot t ∧ joined sp e.readPoint t ∧
    e.msg.head = (getHead sp e.readPoint Φ t
      (Φ.viableTree (voteDomain sp e.readPoint Φ e.msg.slot))
      (mergedVoteView sp e.readPoint Φ e.msg.slot) ((e.msg.slot : Int) - 1)).root

/-- Every emission of a call is a vote of `VoteSpec`, and the call leaves the state of the
vote's own receipt. -/
private def EmitsVotes (m : WriteMode) (x : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (r : SAState sp.n × List (Em sp FGP)) : Prop :=
  ∀ e ∈ r.2, VoteSpec x Φ t e ∧
    r.1 = optimisticConfirmationM sp m (admitVote sp e.readPoint t e.msg) Φ t

private theorem updateLatestConfirmed_blockStamp (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).blockStamp = A.blockStamp := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

theorem optimistic_blockStamp (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_blockStamp _ _ _

private theorem tryVote_emits
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    EmitsVotes wm x Φ t (tryVoteWithM sp wm x L A Φ t) :=
  tryVote_emitsS walkStartLaw_parentWalkStartFn x A Φ t

private theorem onTick_emits
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    EmitsVotes wm x Φ t (acOnTickWithM sp wm x L A Φ t) := by
  unfold acOnTickWithM
  dsimp only
  split_ifs with _ ht hu hu
  · have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · simp [EmitsVotes]
  · exact tryVote_emits x A Φ t
  · simp [EmitsVotes]
  · simp [EmitsVotes]

private theorem step_emits
    {L : Set Lock} (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    EmitsVotes wm y Φ t (stepWithM sp ro wm y L A Φ t c) := by
  cases c with
  | tick => exact onTick_emits y A _ _
  | proposal => simp [EmitsVotes]
  | toFG => simp [EmitsVotes]
  | message m => exact tryVote_emits y _ _ _
  | block B => exact tryVote_emits y _ _ _
  | restart =>
    intro e he
    change e ∈ (acRestart sp ro y A Φ t).2 at he
    rw [((restart_state sp) FGP ro y A Φ t hΦ ht).1] at he
    simp at he

/-- A single call emits only its own signer's vote, without a coherent-universe premise. -/
theorem step_emission_signer (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    {e : Em sp FGP} (he : e ∈ ((goldilocksSA sp FGP ro).step y A Φ t c).2) :
    e.msg.val = y :=
  (step_emits (wm := WriteMode.parent sp) (L := parentUnlock sp A Φ t c) y A Φ t c hΦ ht e
    (by rwa [step_eq_stepWith] at he)).1.1

/-- An honest vote, and the state its call leaves. -/
private theorem cast_emitsU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    VoteSpec y ℓ.frame (tr.time i) e ∧ tr.post i =
      optimisticConfirmationM sp wm (admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
        (tr.time i) :=
  cast_emitsUS (st := fun _ => parentWalkStartFn sp) hr
    (fun _ => walkStartLaw_parentWalkStartFn) hy hc

/-- `castAt_spec` with the unlock given. -/
theorem castAt_specU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  castAt_specUS (st := fun _ => parentWalkStartFn sp) hr
    (fun _ => walkStartLaw_parentWalkStartFn) hy hc

/-- **An honest vote.** -/
theorem castAt_spec (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  apply castAt_specU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- Ancestor closure of the voter block tree is independent of the walk start. -/
theorem voterBlockTree_ancUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  intro B hB X hX
  have hsp := stamp_parentUS sp FGP ro y U hr.coherent _ _ _
    (localRun_reachableUS sp hr hy i ℓ hc.1)
  have hle : (tr.post i).blockStamp X.root ≤ (tr.post i).blockStamp B.root := by
    clear hB
    induction hX with
    | refl => exact le_rfl
    | tail _ hp ih => exact ih.trans (hsp _ hp.2.1 _ hp.1 hp.2.2)
  rw [(cast_emitsUS hr hst hy hc).2, optimisticConfirmationM_keep _ optimistic_blockStamp,
    admitVote_blockStamp] at hle
  exact ⟨mem_of_anc hX hB.1, hB.2.imp hle.trans_lt
    fun ⟨P, hP, hPs, hBP⟩ => ⟨P, hP, hPs, hX.trans hBP⟩⟩

/-- `voterBlockTree_anc` with the unlock given. -/
theorem voterBlockTree_ancU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot :=
  voterBlockTree_ancUS (st := fun _ => parentWalkStartFn sp) hr
    (fun _ => walkStartLaw_parentWalkStartFn) hy hc

/-- The voter block tree of an honest vote is closed under ancestors in the frame (block stamps
grow along parent edges, A0.1, at the state the call leaves, whose stamps are the read
point's). -/
theorem voterBlockTree_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  apply voterBlockTree_ancU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- `castAt_head_of_viable` with the unlock given. -/
theorem castAt_head_of_viableU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e)
    (hne : (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)).Nonempty) :
    e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot))
      (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  rw [← viableTree_voteDomain_eq_of_viable hne]
  exact (castAt_specU hr hy hc).2.2.2

/-- **An honest vote whose voter block tree has a viable block**: its head is the walk over the
viable voter block tree (the vote domain is the voter block tree, `voteDomain_eq_of_viable`). -/
theorem castAt_head_of_viable (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e)
    (hne : (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)).Nonempty) :
    e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot))
      (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  apply castAt_head_of_viableU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- Viability at a vote in the voter block tree gives viability in the vote domain. -/
theorem ViableAtVote.voteDomain {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} {σ : Nat}
    {B : Blk sp.n FGP} (h : ViableAtVote ℓ e σ B) :
    B ∈ ℓ.frame.viableTree (SA.voteDomain sp e.readPoint ℓ.frame σ) ∨
      ℓ.frame.Anc B ℓ.frame.fcRoot :=
  h.imp_left fun h => viableTree_voterBlockTree_subset_voteDomain h

/-- The domain of a vote from a structural start is ancestor-closed. -/
theorem voteDomain_ancUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot :=
  voteDomain_anc_closed (voterBlockTree_ancUS hr hst hy hc)

/-- `voteDomain_anc` with the unlock given. -/
theorem voteDomain_ancU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot :=
  voteDomain_anc_closed (voterBlockTree_ancU hr hy hc)

/-- The vote domain of an honest vote is closed under ancestors in the frame. -/
theorem voteDomain_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot := by
  apply voteDomain_ancU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- The post-state of a vote from a structural start. -/
theorem post_of_castAtUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) (hst : ∀ i, WalkStartLaw (st i)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    tr.post i = optimisticConfirmationM sp wm (admitVote sp e.readPoint (tr.time i) e.msg)
      ℓ.frame (tr.time i) :=
  (cast_emitsUS hr hst hy hc).2

/-- `post_of_castAt` with the unlock given, the optimistic check at the writes of `wm`. -/
theorem post_of_castAtU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    tr.post i = optimisticConfirmationM sp wm (admitVote sp e.readPoint (tr.time i) e.msg)
      ℓ.frame (tr.time i) :=
  (cast_emitsU hr hy hc).2

/-- The call that casts an honest vote leaves the state of the vote's own receipt: the read
point with the own vote admitted and the optimistic check run. -/
theorem post_of_castAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    tr.post i = optimisticConfirmation sp (admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
      (tr.time i) := by
  apply post_of_castAtU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

private theorem tryVote_timeS (st : WalkStartFn sp FGP)
    {L : Set Lock} {x : Fin sp.n} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {e : Em sp FGP} (he : e ∈ (tryVoteWithMS sp wm st x L A Φ t).2) :
    t ≤ sp.ts (sp.slot t) + sp.Δ := by
  by_contra ht
  have hguard : ¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨
      sp.ts (sp.slot t) + sp.Δ < t := Or.inr (Or.inr (lt_of_not_ge ht))
  simp only [tryVoteWithMS, hguard, ite_true] at he
  exact List.not_mem_nil he

private theorem tryVote_time
    {L : Set Lock} {x : Fin sp.n} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {e : Em sp FGP} (he : e ∈ (tryVoteWithM sp wm x L A Φ t).2) : t ≤ sp.ts (sp.slot t) + sp.Δ :=
  tryVote_timeS (parentWalkStartFn sp) he

/-- A `try_vote` emission is the caster's own vote of the slot of the call's time. The walk's
domain is carried but not read. -/
private theorem tryVote_emits_slot {x : Fin sp.n} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {e : Em sp FGP} (he : e ∈ (tryVote sp x A Φ t).2) :
    e.msg.val = x ∧ e.msg.slot = sp.slot t := by
  have h := (tryVote_emits (wm := WriteMode.parent sp) x A Φ t e he).1
  exact ⟨h.1, h.2.1⟩

/-- `vote_time_le` with the unlock given. -/
theorem vote_time_leUS
    {u : Nat → Set Lock} {st : Nat → WalkStartFn sp FGP}
    (hr : ACLocalRunUS wm u st H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ := by
  obtain ⟨ℓ, hc, he⟩ := hv
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw x hx j ℓ hc with ⟨-, _, -, -, hok⟩ | ⟨_, _, -, -, -, hok⟩ <;>
      exact hok.1.1
  have hx' := hr.exec j ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at hx'
  have he' : e ∈ (stepWithMS sp ro wm (st j) x (u j) (tr.state x j) ℓ.frame (tr.time j)
      ℓ.call).2 := by
    rw [hx']; exact he
  clear hx' he
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at he'
    change e ∈ (acOnTickWithMS sp wm (st j) x (u j) _ ℓ.frame _).2 at he'
    unfold acOnTickWithMS at he'
    dsimp only at he'
    split at he'
    · exact absurd he' List.not_mem_nil
    · change e ∈ (if tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ then
        tryVoteWithMS sp wm (st j) x (u j) (tr.state x j) ℓ.frame (tr.time j)
        else (tr.state x j, [])).2 at he'
      split at he'
      · exact le_of_eq ‹_›
      · exact absurd he' List.not_mem_nil
  | proposal => rw [hcall] at he'; simp at he'
  | toFG => rw [hcall] at he'; simp at he'
  | message m => rw [hcall] at he'; exact tryVote_timeS (st j) he'
  | block B => rw [hcall] at he'; exact tryVote_timeS (st j) he'
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro x _ ℓ.frame (tr.time j)).2 at he'
    rw [((restart_state sp) FGP ro x _ ℓ.frame (tr.time j) hΦ (hr.time_nonneg j)).1] at he'
    simp at he'

/-- Vote timing at the parent's walk start. -/
theorem vote_time_leU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ :=
  vote_time_leUS (st := fun _ => parentWalkStartFn sp) hr hx hv

/-- An honest vote is cast by `t_s + Δ` of its slot `s`. -/
theorem vote_time_le (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ := by
  apply vote_time_leU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- An honest vote is its caster's, of the slot of its cast time. -/
theorem vote_signer_slot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    e.msg.val = x ∧ e.msg.slot = sp.slot (tr.time j) := by
  obtain ⟨ℓ, hc, he⟩ := hv
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw x hx j ℓ hc with ⟨-, _, -, -, hok⟩ | ⟨_, _, -, -, -, hok⟩ <;>
      exact hok.1.1
  have hx' := hr.exec j ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at hx'
  have he' : e ∈ ((goldilocksSA sp FGP ro).step x (tr.state x j) ℓ.frame (tr.time j)
      ℓ.call).2 := by
    rw [hx']; exact he
  clear hx' he
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at he'
    change e ∈ (acOnTick sp x _ ℓ.frame _).2 at he'
    unfold acOnTick at he'
    dsimp only at he'
    split at he'
    · exact absurd he' List.not_mem_nil
    · change e ∈ (if tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ then
        tryVote sp x (tr.state x j) ℓ.frame (tr.time j) else (tr.state x j, [])).2 at he'
      split at he'
      · exact tryVote_emits_slot he'
      · exact absurd he' List.not_mem_nil
  | proposal => rw [hcall] at he'; simp [ACInterface.step] at he'
  | toFG => rw [hcall] at he'; simp [ACInterface.step] at he'
  | message m => rw [hcall] at he'; exact tryVote_emits_slot he'
  | block B => rw [hcall] at he'; exact tryVote_emits_slot he'
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro x _ ℓ.frame (tr.time j)).2 at he'
    rw [((restart_state sp) FGP ro x _ ℓ.frame (tr.time j) hΦ (hr.time_nonneg j)).1] at he'
    simp at he'

end Consensus.Goldilocks.SA

end

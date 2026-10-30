module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps

public section

/-! # Goldilocks SA: an honest vote

Every emission of an honest node's call is the vote of `try_vote` (a restart's replay sends
nothing, A0.7): it is the node's own vote of the slot of the call's time, cast while joined, and
its head is the walk from the anchor over the viable tree of the voter block tree with the
merged view against the previous slot, all read at the emission's read point (the unlocking and
`voted_slot` change nothing the walk reads but the locks). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- The vote of `x` at frame `Φ` and time `t`, as `castAt_spec` states it. -/
private def VoteSpec (x : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time) (e : Em sp FGP) : Prop :=
  e.msg.val = x ∧ e.msg.slot = sp.slot t ∧ joined sp e.readPoint t ∧
    e.msg.head = (getHead sp e.readPoint Φ t
      (Φ.viableTree (voterBlockTree sp e.readPoint Φ e.msg.slot))
      (mergedVoteView sp e.readPoint Φ e.msg.slot) ((e.msg.slot : Int) - 1)).root

/-- Every emission of a call is a vote of `VoteSpec`, and the call leaves the state of the
vote's own receipt. -/
private def EmitsVotes (x : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (r : SAState sp.n × List (Em sp FGP)) : Prop :=
  ∀ e ∈ r.2, VoteSpec x Φ t e ∧
    r.1 = optimisticConfirmation sp (admitVote sp e.readPoint t e.msg) Φ t

private theorem admitVote_blockStamp (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).blockStamp = A.blockStamp := by
  unfold admitVote
  split_ifs <;> rfl

private theorem updateLatestConfirmed_blockStamp (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).blockStamp = A.blockStamp := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

private theorem optimistic_blockStamp (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_blockStamp _ _ _

private theorem tryVote_emits (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    EmitsVotes x Φ t (tryVote sp x A Φ t) := by
  unfold tryVote
  dsimp only
  split_ifs with h1
  · simp [EmitsVotes]
  · simp [EmitsVotes]
  all_goals
    simp only [EmitsVotes, List.mem_singleton, forall_eq, and_true]
    exact ⟨rfl, rfl, not_not.1 (not_or.1 h1).1, rfl⟩

private theorem onTick_emits (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    EmitsVotes x Φ t (acOnTick sp x A Φ t) := by
  unfold acOnTick
  dsimp only
  split_ifs with _ ht hu hu
  · have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · simp [EmitsVotes]
  · exact tryVote_emits x A Φ t
  · simp [EmitsVotes]
  · simp [EmitsVotes]

/-- An honest vote, and the state its call leaves. -/
private theorem cast_emits (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    VoteSpec y ℓ.frame (tr.time i) e ∧ tr.post i =
      optimisticConfirmation sp (admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
        (tr.time i) := by
  obtain ⟨hc, he⟩ := hc
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  generalize tr.state y i = A at hx
  suffices h : EmitsVotes y ℓ.frame (tr.time i)
      ((goldilocksSA sp FGP ro).step y A ℓ.frame (tr.time i) ℓ.call) by
    rw [hx] at h
    exact h e he
  cases ℓ.call with
  | tick => exact onTick_emits y A _ _
  | proposal => simp [EmitsVotes, ACInterface.step]
  | toFG => simp [EmitsVotes, ACInterface.step]
  | message m => exact tryVote_emits y _ _ _
  | block B => exact tryVote_emits y _ _ _
  | restart =>
    intro e he
    change e ∈ (acRestart sp ro y A ℓ.frame (tr.time i)).2 at he
    rw [((restart_state sp) FGP ro y A ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he
    simp at he

/-- **An honest vote.** -/
theorem castAt_spec (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root :=
  (cast_emits hr hy hc).1

/-- The voter block tree of an honest vote is closed under ancestors in the frame (block stamps
grow along parent edges, A0.1, at the state the call leaves, whose stamps are the read
point's). -/
theorem voterBlockTree_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  intro B hB X hX
  have hsp := stamp_parent sp FGP ro y U hr.coherent _ _ _
    (localRun_reachable _ _ _ _ _ _ hr y hy i ℓ hc.1)
  have hle : (tr.post i).blockStamp X.root ≤ (tr.post i).blockStamp B.root := by
    clear hB
    induction hX with
    | refl => exact le_rfl
    | tail _ hp ih => exact ih.trans (hsp _ hp.2.1 _ hp.1 hp.2.2)
  rw [(cast_emits hr hy hc).2, optimistic_blockStamp, admitVote_blockStamp] at hle
  exact ⟨mem_of_anc hX hB.1, hB.2.imp hle.trans_lt
    fun ⟨P, hP, hPs, hBP⟩ => ⟨P, hP, hPs, hX.trans hBP⟩⟩

/-- The call that casts an honest vote leaves the state of the vote's own receipt: the read
point with the own vote admitted and the optimistic check run. -/
theorem post_of_castAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    tr.post i = optimisticConfirmation sp (admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
      (tr.time i) :=
  (cast_emits hr hy hc).2

end Consensus.Goldilocks.SA

end

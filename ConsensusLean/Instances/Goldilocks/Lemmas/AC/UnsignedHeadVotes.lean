module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Actions

public section

/-! # Goldilocks SA, unsigned head votes in proposals: the voter's handlers equal today's when covered

A candidate variant of the slot-`s` vote (work branch, not a protocol change). A slot-`s` block
carries the same payload as today, read as *unsigned head votes*: an entry `(v, s−1, H)` names the
previous-slot head of seat `v` (the Lean SA abstracts signatures, so an unsigned head vote and a vote are the
same triple). A voter never admits the entries into its pool, and counts an entry only when it is
**held**: its pool holds the exact vote, or holds two distinct votes of that seat for that slot
(`ShouldCountDeclaredVote`). The voter casts early only when every entry of every slot-`s` proposal in its tree is
held (`UnsignedHeadVotesHeld`); at the timeout it counts the held entries and omits the others.

* `heldMergedVoteView`: the frozen base of today's `mergedVoteView`, with the held entries of the
  slot-`s` proposals in place of all of them;
* `tryVoteUnsigned`, `blockReceiptUnsigned`, `acOnBlockUnsigned`: the unsigned-vote handlers (the receipt only
  stamps the block);
* `heldMergedVoteView_eq`: when covered, the unsigned-vote view **is** today's merged view;
* `tryVoteUnsigned_eq_tryVote`: when covered at the call, the unsigned-vote handler returns today's
  state and emissions (the same vote, read point, duty head and unlocked locks);
* `unsignedHeld_of_tryVoteUnsigned_early`, `tryVoteUnsigned_early_eq`: an early unsigned-vote cast is covered,
  so every early cast is today's cast;
* `blockReceipt_eq_unsigned`: when every entry of the block is held at the receipt, today's receipt
  (stamp, then admission of the entries) is the unsigned-vote receipt: each admission is a no-op
  (exact vote already pooled, or the seat's two-vote cap already full). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- An entry is **held** by a state: its pool holds the exact vote, or the seat of the entry is an
equivocator of the entry's slot pool (two distinct held votes of that seat for that slot). -/
def ShouldCountDeclaredVote (A : SAState sp.n) (v : Vote sp.n) : Prop :=
  v ∈ A.poolAt v.slot ∨ v.val ∈ equivocators {x | x ∈ A.poolAt v.slot}

/-- Every entry (vote or support entry) of every slot-`s` proposal of the tree is held. -/
def UnsignedHeadVotesHeld (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : Prop :=
  ∀ B ∈ Φ.tree, B.slot = s → ∀ v, v ∈ blockVotes B ∨ v ∈ blockSupport B → ShouldCountDeclaredVote sp A v

/-- The unsigned-vote merged view: today's frozen base, plus the **held** entries of the slot-`s`
proposals of the tree (support entries also with today's resolution condition). -/
noncomputable def heldMergedVoteView (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : View sp.n :=
  let base := voteView A Φ ((s : Int) - 1) (ETime.of (freeze sp s))
  { votes := base.votes ∪ {v | ∃ B ∈ Φ.tree, B.slot = s ∧ v ∈ blockVotes B ∧ ShouldCountDeclaredVote sp A v}
    support := base.support ∪ {v | ∃ B ∈ Φ.tree, B.slot = s ∧ v ∈ blockSupport B ∧
      ShouldCountDeclaredVote sp A v ∧ v.slot + 1 = s ∧ ∃ H ∈ Φ.tree, H.root = v.head ∧ H.slot + 1 ≤ s} }

open Classical in
/-- `try_vote` with unsigned head votes: early only when ready **and covered**; the walk and the unlock
read `heldMergedVoteView`. Otherwise today's `tryVote` line by line. -/
noncomputable def tryVoteUnsigned (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s ∨ ¬ UnsignedHeadVotesHeld sp A Φ s) then (A, [])
  else
    let V := heldMergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := unlock sp A.locks Φ t ((s : Int) - 1) V } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := if A.mayVote s then optimisticConfirmation sp (admitVote sp A₂ t vote) Φ t else A₂
    (A₃, if A.mayVote s then
      [{ msg := vote, readPoint := A₂,
         head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }] else [])

/-- The unsigned-vote receipt of a block: its stamp only (the entries are never admitted). -/
def blockReceiptUnsigned (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) : SAState sp.n :=
  { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }

/-- `ac_on_block` with unsigned head votes. -/
noncomputable def acOnBlockUnsigned (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : SAState sp.n × List (Em sp FGP) :=
  tryVoteUnsigned sp self (optimisticConfirmation sp (blockReceiptUnsigned sp A t B) Φ t) Φ t

variable {sp}

/-- **Covered, the unsigned-vote view is today's merged view.** -/
theorem heldMergedVoteView_eq {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    (h : UnsignedHeadVotesHeld sp A Φ s) : heldMergedVoteView sp A Φ s = mergedVoteView sp A Φ s := by
  simp only [heldMergedVoteView, mergedVoteView]
  congr 1
  · ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (hv | ⟨B, hB, hBs, hv, -⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨B, hB, hBs, hv⟩
    · rintro (hv | ⟨B, hB, hBs, hv⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨B, hB, hBs, hv, h B hB hBs v (Or.inl hv)⟩
  · ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (hv | ⟨B, hB, hBs, hv, -, hrest⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨B, hB, hBs, hv, hrest⟩
    · rintro (hv | ⟨B, hB, hBs, hv, hrest⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨B, hB, hBs, hv, h B hB hBs v (Or.inr hv), hrest⟩

/-- The unsigned-vote view is always contained in today's merged view (an omitted entry only
shrinks it). -/
theorem heldMergedVoteView_votes_subset (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) :
    (heldMergedVoteView sp A Φ s).votes ⊆ (mergedVoteView sp A Φ s).votes ∧
      (heldMergedVoteView sp A Φ s).support ⊆ (mergedVoteView sp A Φ s).support := by
  simp only [heldMergedVoteView, mergedVoteView]
  constructor
  · rintro v (hv | ⟨B, hB, hBs, hv, -⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨B, hB, hBs, hv⟩
  · rintro v (hv | ⟨B, hB, hBs, hv, -, hrest⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨B, hB, hBs, hv, hrest⟩

/-- **Covered at the call, the unsigned-vote handler is today's**: the same state and the same
emissions (vote, read point, duty head). -/
theorem tryVoteUnsigned_eq_tryVote (self : Fin sp.n) {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (h : UnsignedHeadVotesHeld sp A Φ (sp.slot t)) : tryVoteUnsigned sp self A Φ t = tryVote sp self A Φ t := by
  unfold tryVoteUnsigned tryVote
  dsimp only
  rw [heldMergedVoteView_eq h]
  have hn : ¬ ¬ UnsignedHeadVotesHeld sp A Φ (sp.slot t) := not_not.2 h
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- **An early unsigned-vote cast is covered**: when the handler emits before `t_s + Δ`, every entry
of every slot-`s` proposal of the frame is held. -/
theorem unsignedHeld_of_tryVoteUnsigned_early (self : Fin sp.n) {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} (hlt : t < sp.ts (sp.slot t) + sp.Δ) (hem : (tryVoteUnsigned sp self A Φ t).2 ≠ []) :
    UnsignedHeadVotesHeld sp A Φ (sp.slot t) := by
  by_contra hc
  apply hem
  simp only [tryVoteUnsigned]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- **Every early unsigned-vote cast is today's cast** at the same state and frame. -/
theorem tryVoteUnsigned_early_eq (self : Fin sp.n) {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (hlt : t < sp.ts (sp.slot t) + sp.Δ) (hem : (tryVoteUnsigned sp self A Φ t).2 ≠ []) :
    tryVoteUnsigned sp self A Φ t = tryVote sp self A Φ t :=
  tryVoteUnsigned_eq_tryVote self (unsignedHeld_of_tryVoteUnsigned_early self hlt hem)

/-- A held entry is a no-op for today's admission: the pool already holds it, or the seat's
two-vote cap for that slot is full. -/
theorem admitVote_of_shouldCountDeclaredVote {A : SAState sp.n} {t : Time} {v : Vote sp.n}
    (h : ShouldCountDeclaredVote sp A v) : admitVote sp A t v = A := by
  have hpool : A.poolAt v.slot = A.pool v.slot := by simp [SAState.poolAt]
  unfold admitVote
  rcases h with hv | ⟨x, hx, y, hy, hxy, hxv, hyv⟩
  · rw [hpool] at hv
    simp [hv]
  · rw [hpool] at hx hy
    have hcap : 2 ≤ ((A.pool v.slot).filter (fun x => x.val = v.val)).dedup.length := by
      rw [← List.card_toFinset]
      apply Finset.one_lt_card.2
      refine ⟨x, ?_, y, ?_, hxy⟩ <;> simp_all
    split_ifs <;> rfl

/-- Admitting a list of held entries leaves the state unchanged. -/
theorem foldl_admitVote_of_held {A : SAState sp.n} {t : Time} :
    ∀ {l : List (Vote sp.n)}, (∀ v ∈ l, ShouldCountDeclaredVote sp A v) →
      l.foldl (fun A v => admitVote sp A t v) A = A
  | [], _ => rfl
  | v :: l, h => by
    rw [List.foldl_cons, admitVote_of_shouldCountDeclaredVote (h v List.mem_cons_self)]
    exact foldl_admitVote_of_held (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-- **Covered at the receipt, today's block receipt is the unsigned-vote receipt**: stamping the
block and admitting its entries leaves the pool and vote stamps unchanged. -/
theorem blockReceipt_eq_unsigned {A : SAState sp.n} {t : Time} {B : Blk sp.n FGP}
    (h : ∀ v ∈ blockVotes B, ShouldCountDeclaredVote sp A v) :
    blockReceipt sp A t B = blockReceiptUnsigned sp A t B :=
  foldl_admitVote_of_held (A := { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) })
    (fun v hv => h v hv)

end Consensus.Goldilocks.SA

end

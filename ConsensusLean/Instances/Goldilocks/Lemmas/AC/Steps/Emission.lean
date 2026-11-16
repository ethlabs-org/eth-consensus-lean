module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps

public section

/-! # Goldilocks SA: an honest vote

Every emission of an honest node's call is the vote of `try_vote`'s vote branch (a restart's
replay sends nothing, A0.7; `voteBranchAt_of_castAtU`): it is the node's own vote of the slot of
the call's time, cast while joined, and its head is the walk from the anchor over the viable tree
of the vote domain (the voter block tree, or the whole tree when the voter block tree has no viable
block) with the merged view against the previous slot, all read at the emission's read point (the
unlocking and `voted_slot` change nothing the walk reads but the locks). The branch's read point
and the state it leaves (`voteBranchAt_spec`, `post_of_voteBranchAt`) hold for a node that may
not vote in the slot too. -/

namespace Consensus.Goldilocks.SA

variable {wm : WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {ini : Fin sp.n → SAState sp.n}

/-- The vote of `x` at frame `Φ` and time `t`, as `castAt_spec` states it. -/
private def VoteSpec (x : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time) (e : Em sp FGP) : Prop :=
  e.msg.val = x ∧ e.msg.slot = sp.slot t ∧
    e.msg.head = (getHead sp e.readPoint Φ t
      (Φ.viableTree (voteDomain sp e.readPoint Φ e.msg.slot))
      (mergedVoteView sp e.readPoint Φ e.msg.slot) ((e.msg.slot : Int) - 1)).root

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

/-- Every emission of `try_vote` is a vote of `VoteSpec`. -/
private theorem tryVote_emits
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ∀ e ∈ (tryVoteWithM sp wm x L A Φ t).2, VoteSpec x Φ t e := by
  unfold tryVoteWithM
  dsimp only
  split_ifs
  all_goals first
    | (intro e he; simp at he; done)
    | simp only [List.mem_singleton, forall_eq]
      exact ⟨rfl, rfl, rfl⟩

/-- A single call emits only its own signer's vote, without a coherent-universe premise. -/
theorem step_emission_signer (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    {e : Em sp FGP} (he : e ∈ ((goldilocksSA sp FGP ro).step y A Φ t c).2) :
    e.msg.val = y := by
  rw [step_eq_stepWith, ← stepWithM_parent] at he
  rcases stepWithM_voteBranch (L := parentUnlock sp A Φ t c) y hΦ ht c
      (A' := (stepWithM sp ro (WriteMode.parent sp) y (parentUnlock sp A Φ t c) A Φ t c).1)
      (es := (stepWithM sp ro (WriteMode.parent sp) y (parentUnlock sp A Φ t c) A Φ t c).2) rfl with
    ⟨hn, -⟩ | ⟨-, -, -, -, -, -, htv⟩
  · rw [hn] at he
    exact absurd he List.not_mem_nil
  · exact (tryVote_emits y _ Φ t e (by rw [htv]; exact he)).1

/-- `castAt_spec` with the unlock given: the joined read point is the vote branch's
(`voteBranchAt_specU`); the signer, slot and head are the emission's. -/
theorem castAt_specU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  obtain ⟨-, -, htv⟩ := voteBranchAt_inputU hr hy (voteBranchAt_of_castAtU hr hy hc)
  obtain ⟨hval, hsl, hhead⟩ := tryVote_emits y _ ℓ.frame (tr.time i) e (by rw [htv]; exact hc.2)
  exact ⟨hval, hsl, (voteBranchAt_specU hr hy (voteBranchAt_of_castAtU hr hy hc)).2.1, hhead⟩

/-- **An honest vote.** -/
theorem castAt_spec (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time i) ∧ joined sp e.readPoint (tr.time i) ∧
      e.msg.head = (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot))
        (mergedVoteView sp e.readPoint ℓ.frame e.msg.slot) ((e.msg.slot : Int) - 1)).root := by
  apply castAt_specU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- **The read point of a vote branch** (`voteBranchAt_specU`): `voted_slot` is the slot of the
call's time, the node is joined there, and the call is by the slot's vote deadline. -/
theorem voteBranchAt_spec (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {R : SAState sp.n}
    (hb : VoteBranchAt tr y j ℓ R) :
    R.votedSlot = sp.slot (tr.time j) ∧ joined sp R (tr.time j) ∧
      tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ :=
  voteBranchAt_specU hr.toU hy hb

/-- `post_of_castAt` with the unlock given, the optimistic check at the writes of `wm`: the cast
is the emitting arm of `post_of_voteBranchAtU`. -/
theorem post_of_castAtU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    tr.post i = optimisticConfirmationM sp wm (admitVote sp e.readPoint (tr.time i) e.msg)
      ℓ.frame (tr.time i) := by
  rcases post_of_voteBranchAtU hr hy (voteBranchAt_of_castAtU hr hy hc) with
    ⟨-, hn, -⟩ | ⟨-, e', he', -, -, -, hpost⟩
  · exact absurd (hn ▸ hc.2) List.not_mem_nil
  · obtain rfl : e = e' := List.mem_singleton.1 (he' ▸ hc.2)
    exact hpost

/-- The call that casts an honest vote leaves the state of the vote's own receipt: the read
point with the own vote admitted and the optimistic check run. -/
theorem post_of_castAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    tr.post i = optimisticConfirmation sp (admitVote sp e.readPoint (tr.time i) e.msg) ℓ.frame
      (tr.time i) := by
  apply post_of_castAtU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- **The state a vote branch leaves** (`post_of_voteBranchAtU`): a node that may not vote in the
slot emits nothing and leaves the read point `R`; one that may emits its own vote of the slot,
read at `R`, and leaves that vote's receipt. -/
theorem post_of_voteBranchAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {R : SAState sp.n} (hb : VoteBranchAt tr y j ℓ R) :
    ((tr.state y j).mayVote (sp.slot (tr.time j)) = false ∧ ℓ.emits = [] ∧ tr.post j = R) ∨
      ((tr.state y j).mayVote (sp.slot (tr.time j)) = true ∧ ∃ e, ℓ.emits = [e] ∧
        e.readPoint = R ∧ e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time j) ∧
        tr.post j = optimisticConfirmation sp (admitVote sp R (tr.time j) e.msg) ℓ.frame
          (tr.time j)) :=
  post_of_voteBranchAtU hr.toU hy hb

/-- `voterBlockTree_anc` with the unlock given, from starts up to the vote permission. -/
theorem voterBlockTree_ancU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot := by
  intro B hB X hX
  have hsp := stamp_parentU sp FGP ro y U hr.coherent (hini y) _ _ _
    (localRun_reachableU sp hr hy i ℓ hc.1)
  have hle : (tr.post i).blockStamp X.root ≤ (tr.post i).blockStamp B.root := by
    clear hB
    induction hX with
    | refl => exact le_rfl
    | tail _ hp ih => exact ih.trans (hsp _ hp.2.1 _ hp.1 hp.2.2)
  rw [post_of_castAtU hr hy hc, optimisticConfirmationM_keep _ optimistic_blockStamp,
    admitVote_blockStamp] at hle
  exact ⟨mem_of_anc hX hB.1, hB.2.imp hle.trans_lt
    fun ⟨P, hP, hPs, hBP⟩ => ⟨P, hP, hPs, hX.trans hBP⟩⟩

/-- The voter block tree of an honest vote is closed under ancestors in the frame (block stamps
grow along parent edges, A0.1, at the state the call leaves, whose stamps are the read
point's), from starts up to the vote permission. -/
theorem voterBlockTree_anc_from (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot :=
  voterBlockTree_ancU (wm := WriteMode.parent sp) hr.toU hini hy hc

/-- The voter block tree of an honest vote is closed under ancestors in the frame:
`voterBlockTree_anc_from` at the initial starts. -/
theorem voterBlockTree_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voterBlockTree sp e.readPoint ℓ.frame e.msg.slot :=
  voterBlockTree_anc_from hr (fun _ => voteStart_initial _) hy hc

/-- `castAt_head_of_viable` with the unlock given. -/
theorem castAt_head_of_viableU
    {ini} {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
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
theorem castAt_head_of_viable {ini}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n}
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

/-- `voteDomain_anc` with the unlock given, from starts up to the vote permission. -/
theorem voteDomain_ancU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot :=
  voteDomain_anc_closed (voterBlockTree_ancU hr hini hy hc)

/-- The vote domain of an honest vote is closed under ancestors in the frame, from starts up to
the vote permission. -/
theorem voteDomain_anc_from (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot :=
  voteDomain_ancU (wm := WriteMode.parent sp) hr.toU hini hy hc

/-- The vote domain of an honest vote is closed under ancestors in the frame:
`voteDomain_anc_from` at the initial starts. -/
theorem voteDomain_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∀ B ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot, ∀ X, ℓ.frame.Anc X B →
      X ∈ voteDomain sp e.readPoint ℓ.frame e.msg.slot :=
  voteDomain_anc_from hr (fun _ => voteStart_initial _) hy hc

/-- `vote_time_le` with the unlock given: the deadline of the vote branch
(`voteBranchAt_specU`). -/
theorem vote_time_leU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ := by
  obtain ⟨ℓ, hc, he⟩ := hv
  exact (voteBranchAt_specU hr hx (voteBranchAt_of_castAtU hr hx ⟨hc, he⟩)).2.2

/-- An honest vote is cast by `t_s + Δ` of its slot `s`. -/
theorem vote_time_le (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ := by
  apply vote_time_leU (wm := WriteMode.parent sp) <;>
    first | assumption | exact ACLocalRun.toU ‹_›

/-- An honest vote is its caster's, of the slot of its cast time. -/
theorem vote_signer_slot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini)
    {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {e : Em sp FGP} (hv : VoteAt tr x j e) :
    e.msg.val = x ∧ e.msg.slot = sp.slot (tr.time j) := by
  obtain ⟨ℓ, hc, he⟩ := hv
  obtain ⟨hval, hsl, -⟩ := castAt_spec hr hx ⟨hc, he⟩
  exact ⟨hval, hsl⟩

end Consensus.Goldilocks.SA

end

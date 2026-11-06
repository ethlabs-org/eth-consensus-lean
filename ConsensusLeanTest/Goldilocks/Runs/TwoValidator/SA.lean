module
public import ConsensusLeanTest.Goldilocks.Runs.TwoValidator.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
@[expose] public section

/-! # The healthy two-validator run: the client record and the SA on the chain

* **The record** (`RecGood Λ n`) after the rows of heights `1, …, n`; `attest_new`: the node signs
  its row of the height of its source when it has not signed it yet; `attest_old`: otherwise it
  signs nothing.
* **The SA on a chain frame** (`ChainFrame`): deepest blocks, viable ancestors, live locks,
  anchors and head walks along the chain. -/

namespace Consensus.Goldilocks.Witness.TwoRun

open SA Node

/-! ## The record -/

/-- The anti-slashing record after the rows of heights `1, …, n`. -/
structure RecGood (Λ : FG.Record) (n : Nat) : Prop where
  target : ∀ h, Λ.target h = if 1 ≤ h ∧ h ≤ n then some (blk (ent h)).root else none
  timeout : ∀ h, Λ.timeout h = ∅
  lock : ∀ h, Λ.lock h = if 1 ≤ h ∧ h + 1 ≤ n then some (blk (ent h)).root else none
  sent : ∀ c ∈ Λ.sent, c.1 ≤ n
  sent_top : 1 ≤ n → ∃ c ∈ Λ.sent, c.1 = n

theorem recGood_empty : RecGood FG.Record.empty 0 :=
  ⟨fun _ => by simp [FG.Record.empty]; omega, fun _ => rfl,
    fun _ => by simp [FG.Record.empty], fun _ h => by simp [FG.Record.empty] at h,
    fun h => absurd h (by omega)⟩

theorem ent_ent_hgt {q : Nat} (hq : 1 ≤ q) : ent (hgt (ent q)) = ent q := by rw [hgt_ent hq]

/-- The entry state of the source `blk s` at height `q`: the chain state of the entry block. -/
theorem entry_state {fg : Store sp.toParams N.Payload} {τ s : Nat} (h : FGGood fg τ)
    (hs : s ≤ τ) : fg.σ (fg.σ (blk s).root).Th = csN (ent (hgt s)) := by
  rw [h.sigma s hs, csN_eq, cs_Th]
  exact h.sigma _ (le_trans (ent_hgt_le s) hs)

/-- **A new row**: the node signs its row of the height of its source. -/
theorem attest_new {fg : Store sp.toParams N.Payload} {τ s : Nat} (h : FGGood fg τ)
    (hs : s ≤ τ) (y : Fin sp.n) {Λ : FG.Record} (hΛ : RecGood Λ (hgt s - 1)) :
    ∃ Λ', fg.attest Λ y (blk s) = some (row y (hgt s), Λ') ∧ RecGood Λ' (hgt s) := by
  have hq := hgt_pos s
  set q := hgt s with hqd
  have hent := entry_state h hs
  rw [← hqd] at hent
  have he_h : (csN (ent q)).h = q := by rw [csN_eq, cs_h, hgt_ent hq]
  have he_Th : (csN (ent q)).Th = (blk (ent q)).root := by rw [csN_eq, cs_Th, hgt_ent hq]
  have he_hj : (csN (ent q)).hj = q - 1 := by rw [csN_eq, cs_hj, hgt_ent hq]
  have he_J : (csN (ent q)).J = (blk (ent (q - 1))).root := by rw [csN_eq, cs_J, hgt_ent hq]
  have hfin : Λ.finalityPair (csN (ent q)) = (row y q).fin := by
    unfold FG.Record.finalityPair
    rw [row_fin]
    rcases Nat.lt_or_ge q 2 with h2 | h2
    · have hb : ¬ (csN (ent q)).previousHeightJustified := by
        unfold FG.ChainState.previousHeightJustified; rw [he_hj]; omega
      rw [ite_eq_right hb, ite_eq_left (by omega)]
      have hp : (csN (ent q)).pending = [] := by
        rw [csN_eq, cs_pending, hgt_ent hq, ite_eq_left (by omega)]
      rw [hp]; rfl
    · have hb : (csN (ent q)).previousHeightJustified := by
        unfold FG.ChainState.previousHeightJustified; rw [he_hj, he_h]; omega
      have hperm : Λ.permits (csN (ent q)).hj (csN (ent q)).J := by
        rw [he_hj, he_J]
        refine ⟨Or.inr ?_, by rw [hΛ.timeout]; simp, Or.inl ?_⟩
        · rw [hΛ.target, ite_eq_left ⟨by omega, le_rfl⟩]
        · rw [hΛ.lock, ite_eq_right (by omega)]
      rw [ite_eq_left hb, ite_eq_left hperm, he_hj, he_J, ite_eq_right (by omega)]
  have hhp : Λ.heightPair q (blk (ent q)).root = some (q, (blk (ent q)).root, false) := by
    unfold FG.Record.heightPair
    rw [ite_eq_right (by rw [hΛ.lock, ite_eq_right (by omega)]; simp),
      ite_eq_right (by rw [hΛ.timeout]; simp),
      ite_eq_left (Or.inl (by rw [hΛ.target, ite_eq_right (by omega)]))]
  have hsent : ¬ (Λ.sent.any fun b =>
      decide (b.1 = q ∧ ((!false) = true ∨ b.2.1 = (blk (ent q)).root))) = true := by
    rw [List.any_eq_true]
    rintro ⟨b, hb, hb'⟩
    have := hΛ.sent b hb
    simp at hb'; omega
  refine ⟨Λ.recordAtt (row y q), ?_, ?_⟩
  · unfold Store.attest FG.Record.createAtt
    rw [hent, he_h, he_Th, hhp]
    dsimp only
    rw [ite_eq_right hsent, hfin]
    rfl
  · refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun c hc => ?_, fun _ => ?_⟩
    · unfold FG.Record.recordAtt
      dsimp only
      rw [ite_eq_left ⟨by simp [row_timeout], by rw [row_h, hΛ.target, ite_eq_right (by omega)]⟩,
        Function.update_apply, row_h, row_T, hΛ.target]
      split_ifs with h1 h2 h3 <;> (try subst h1) <;> first | rfl | omega
    · unfold FG.Record.recordAtt
      dsimp only
      rw [row_timeout]
      exact hΛ.timeout h'
    · unfold FG.Record.recordAtt
      dsimp only
      rw [row_fin]
      rcases Nat.lt_or_ge q 2 with h2 | h2
      · rw [ite_eq_left (by omega)]
        dsimp only
        rw [hΛ.lock]
        split_ifs <;> first | rfl | omega
      · rw [ite_eq_right (by omega)]
        dsimp only
        rw [Function.update_apply, hΛ.lock]
        split_ifs with h1 h3 h4 <;> (try subst h1) <;> first | rfl | omega
    · unfold FG.Record.recordAtt at hc
      dsimp only at hc
      rcases List.mem_append.1 hc with hc | hc
      · have := hΛ.sent c hc; omega
      · rw [List.mem_singleton] at hc; subst hc
        change (row y q).h ≤ q
        rw [row_h]
    · exact ⟨(row y q).content, by unfold FG.Record.recordAtt; simp, rfl⟩

/-- **An old row**: once the row of the height of its source is signed, the node signs
nothing. -/
theorem attest_old {fg : Store sp.toParams N.Payload} {τ s : Nat} (h : FGGood fg τ)
    (hs : s ≤ τ) (y : Fin sp.n) {Λ : FG.Record} (hΛ : RecGood Λ (hgt s)) :
    fg.attest Λ y (blk s) = none := by
  have hq := hgt_pos s
  set q := hgt s with hqd
  have hent := entry_state h hs
  rw [← hqd] at hent
  have he_h : (csN (ent q)).h = q := by rw [csN_eq, cs_h, hgt_ent hq]
  have he_Th : (csN (ent q)).Th = (blk (ent q)).root := by rw [csN_eq, cs_Th, hgt_ent hq]
  have hhp : Λ.heightPair q (blk (ent q)).root = some (q, (blk (ent q)).root, false) := by
    unfold FG.Record.heightPair
    rw [ite_eq_right (by rw [hΛ.lock, ite_eq_right (by omega)]; simp),
      ite_eq_right (by rw [hΛ.timeout]; simp),
      ite_eq_left (Or.inr (by rw [hΛ.target, ite_eq_left ⟨hq, le_rfl⟩]))]
  obtain ⟨c, hc, hc1⟩ := hΛ.sent_top hq
  have hsent : (Λ.sent.any fun b =>
      decide (b.1 = q ∧ ((!false) = true ∨ b.2.1 = (blk (ent q)).root))) = true :=
    List.any_eq_true.2 ⟨c, hc, by simp [hc1]⟩
  unfold Store.attest FG.Record.createAtt
  rw [hent, he_h, he_Th, hhp]
  dsimp only
  rw [ite_eq_left hsent]

/-! ## The SA on a chain frame -/

theorem etime_of_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)


namespace ChainFrame

variable {Φ : N.Frm} {f j τ : Nat}

theorem fcRoot_mem' (h : ChainFrame Φ f j τ) : Φ.fcRoot ∈ Φ.tree := by
  rw [h.fcRoot]; exact h.mem h.fj h.jτ

theorem eq_of_mem (h : ChainFrame Φ f j τ) {B : N.Blk} (hB : B ∈ Φ.tree) :
    ∃ m, f ≤ m ∧ m ≤ τ ∧ B = blk m := (h.tree B).1 hB

theorem eq_of_root (h : ChainFrame Φ f j τ) {B : N.Blk} (hB : B ∈ Φ.tree) {m : Nat}
    (hr : B.root = (blk m).root) : B = blk m ∧ f ≤ m ∧ m ≤ τ := by
  obtain ⟨m', h1, h2, rfl⟩ := h.eq_of_mem hB
  obtain rfl := blk_root_inj hr
  exact ⟨rfl, h1, h2⟩

theorem ancs (h : ChainFrame Φ f j τ) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) :
    {A | Φ.Anc A (blk m)} = blk '' Set.Icc f m := by
  ext A
  constructor
  · intro hA
    obtain ⟨a, ha, rfl, hor⟩ := anc_blk_inv h.onChain hA
    rcases hor with rfl | hmem
    · exact ⟨a, ⟨h1, le_rfl⟩, rfl⟩
    · exact ⟨a, ⟨(h.mem_iff.1 hmem).1, ha⟩, rfl⟩
  · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    exact h.anc ha1 ha2 h2

theorem depth_eq (h : ChainFrame Φ f j τ) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) :
    depth Φ (blk m) = m + 1 - f := by
  unfold depth
  rw [h.ancs h1 h2, Set.ncard_image_of_injective _ blk_injective, ← Finset.coe_Icc,
    Set.ncard_coe_finset, Nat.card_Icc]

theorem isDeepest_unique {S : Set N.Blk} {B C : N.Blk} (hB : IsDeepest Φ S B)
    (hC : IsDeepest Φ S C) : B = C := by
  by_contra hne
  rcases hB.2 C hC.1 (Ne.symm hne) with h | ⟨h, h'⟩ <;>
    rcases hC.2 B hB.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

/-- The deepest block of a set of chain blocks of the tree is the latest one. -/
theorem deepest_eq (h : ChainFrame Φ f j τ) {S : Set N.Blk} (hS : S ⊆ Φ.tree) {M : Nat}
    (hM : blk M ∈ S) (hle : ∀ B ∈ S, ∃ m ≤ M, B = blk m) : deepest Φ S = some (blk M) := by
  have hMt := h.mem_iff.1 (hS hM)
  have hd : IsDeepest Φ S (blk M) := by
    refine ⟨hM, fun C hC hne => Or.inl ?_⟩
    obtain ⟨m, hm, rfl⟩ := hle C hC
    have hmt := h.mem_iff.1 (hS hC)
    have hlt : m < M := lt_of_le_of_ne hm (fun he => hne (by rw [he]))
    rw [h.depth_eq hmt.1 hmt.2, h.depth_eq hMt.1 hMt.2]
    omega
  unfold deepest
  rw [dite_eq_left ⟨_, hd⟩]
  exact congrArg some (isDeepest_unique (Exists.choose_spec ⟨_, hd⟩) hd)

theorem viableAncestor_eq (h : ChainFrame Φ f j τ) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) :
    Φ.viableAncestor (blk m) = blk m := by
  have hcand : Φ.AncestorCandidate (blk m) := by
    rcases Nat.lt_or_ge m j with hm | hm
    · left; rw [h.fcRoot]; exact h.anc h1 hm.le h.jτ
    · right; exact h.mem_viableTree (h.mem (le_trans h.fj h.jτ) le_rfl) hm h2 (h.mem h1 h2)
  have hv : Φ.IsViableAncestor (blk m) (blk m) :=
    ⟨Relation.ReflTransGen.refl, hcand, fun _ hA' _ => hA'⟩
  unfold Frame.viableAncestor
  rw [dite_eq_left ⟨_, hv⟩]
  have hs := Exists.choose_spec (⟨_, hv⟩ : ∃ A, Φ.IsViableAncestor (blk m) A)
  obtain ⟨a, ha, he, -⟩ := anc_blk_inv h.onChain hs.1
  rw [he] at hs ⊢
  have := h.le_of_anc (hs.2.2 (blk m) Relation.ReflTransGen.refl hcand)
  rw [show a = m by omega]

theorem mem_liveLocks (h : ChainFrame Φ f j τ) {L : Set Lock} {t : Time} {l : Lock} (hl : l ∈ L)
    {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) (hr : l.block = (blk m).root)
    (hlive : sp.slot t ≤ l.expiry) : l ∈ liveLocks sp L Φ t :=
  ⟨l, hl, blk m, h.mem h1 h2, hr.symm, hlive, by rw [h.viableAncestor_eq h1 h2, ← hr]⟩

theorem liveLocks_sub (h : ChainFrame Φ f j τ) {L : Set Lock} {t : Time} {l : Lock}
    (hl : l ∈ liveLocks sp L Φ t) :
    l ∈ L ∧ (∃ m, f ≤ m ∧ m ≤ τ ∧ l.block = (blk m).root) ∧ sp.slot t ≤ l.expiry := by
  obtain ⟨l₀, hl₀, B, hB, hr, hlive, rfl⟩ := hl
  obtain ⟨m, h1, h2, rfl⟩ := h.eq_of_mem hB
  rw [h.viableAncestor_eq h1 h2, hr]
  exact ⟨hl₀, ⟨m, h1, h2, hr.symm⟩, hlive⟩

/-- Locks on chain blocks up to `b`. -/
def LocksLe (L : Set Lock) (b : Nat) : Prop := ∀ l ∈ L, ∃ m ≤ b, l.block = (blk m).root

theorem liveLockBlocks_le (h : ChainFrame Φ f j τ) {L : Set Lock} {b : Nat} (hL : LocksLe L b)
    {t : Time} {B : N.Blk} (hB : B ∈ liveLockBlocks sp L Φ t) : ∃ m ≤ b, B = blk m := by
  obtain ⟨hBt, l, hl, hr⟩ := hB
  obtain ⟨hlL, -, -⟩ := h.liveLocks_sub hl
  obtain ⟨m, hm, hr'⟩ := hL l hlL
  exact ⟨m, hm, (h.eq_of_root hBt (hr.symm.trans hr')).1⟩

/-- The anchor is the latest live lock block (or `fc_root`). -/
theorem getAnchor_eq (h : ChainFrame Φ f j τ) {A : SAState sp.n} {t : Time} {b : Nat}
    (hL : LocksLe A.locks b) (hjb : j ≤ b) (hb : blk b ∈ liveLockBlocks sp A.locks Φ t ∨ b = j) :
    getAnchor sp A Φ t = blk b := by
  unfold getAnchor
  rw [h.deepest_eq (M := b)]
  · rfl
  · rintro B (hB | hB)
    · exact hB.1
    · rw [Set.mem_singleton_iff.1 hB]; exact h.fcRoot_mem'
  · rcases hb with hb | rfl
    · exact Or.inl hb
    · exact Or.inr h.fcRoot.symm
  · rintro B (hB | hB)
    · exact h.liveLockBlocks_le hL hB
    · rw [Set.mem_singleton_iff.1 hB, h.fcRoot]; exact ⟨j, hjb, rfl⟩

end ChainFrame

/-! ## The SA's steps on a chain frame -/

theorem ghost_tip {T : Set N.Blk} {b : Nat} (hT : ∀ B ∈ T, ∃ m ≤ b, B = blk m)
    (sc : N.Blk → Nat) (el : N.Blk → Prop) : ∀ n, ghost sp T sc el n (blk b) = blk b
  | 0 => rfl
  | n + 1 => by
    rw [ghost, dite_eq_right]
    rintro ⟨C, ⟨hCT, hpar, -⟩, -⟩
    obtain ⟨m, hm, rfl⟩ := hT C hCT
    rcases m with _ | m
    · rw [blk_parent_zero] at hpar; cases hpar
    · rw [blk_parent_succ] at hpar
      have := blk_root_inj (Option.some.inj hpar); omega

theorem ghost_step {T : Set N.Blk} {b : Nat} (hT : ∀ B ∈ T, ∃ m, B = blk m)
    (hmem : blk (b + 1) ∈ T) {sc : N.Blk → Nat} {el : N.Blk → Prop} (hel : el (blk (b + 1)))
    (n : Nat) : ghost sp T sc el (n + 1) (blk b) = ghost sp T sc el n (blk (b + 1)) := by
  have hbest : IsBest sp sc {B | B ∈ T ∧ B.parent = some (blk b).root ∧ el B} (blk (b + 1)) := by
    refine ⟨⟨hmem, blk_parent_succ b, hel⟩, fun D hD' hne => absurd ?_ hne⟩
    obtain ⟨hD, hpar, -⟩ := hD'
    obtain ⟨m, rfl⟩ := hT D hD
    rcases m with _ | m
    · rw [blk_parent_zero] at hpar; cases hpar
    · rw [blk_parent_succ] at hpar
      rw [blk_root_inj (Option.some.inj hpar)]
  rw [ghost, dite_eq_left ⟨_, hbest⟩]
  congr 1
  have hc := Exists.choose_spec (⟨_, hbest⟩ : ∃ C, IsBest sp sc
    {B | B ∈ T ∧ B.parent = some (blk b).root ∧ el B} C)
  by_contra hne
  rcases hc.2 _ hbest.1 (Ne.symm hne) with h | ⟨h, h'⟩ <;>
    rcases hbest.2 _ hc.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

open ChainFrame in
theorem compatible_chain {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {B C : N.Blk}
    (hB : B ∈ Φ.tree) (hC : C ∈ Φ.tree) : Compatible Φ.tree B C := by
  obtain ⟨b, hb1, hb2, rfl⟩ := h.eq_of_mem hB
  obtain ⟨c, hc1, hc2, rfl⟩ := h.eq_of_mem hC
  rcases le_total b c with hbc | hbc
  · exact Or.inl (h.anc hb1 hbc hc2)
  · exact Or.inr (h.anc hc1 hbc hb2)

/-- The SA state apart from locks, the record of the confirmed block and the saved results. -/
structure Same (A A' : SAState sp.n) : Prop where
  pool : A'.pool = A.pool
  voteStamp : A'.voteStamp = A.voteStamp
  blockStamp : A'.blockStamp = A.blockStamp
  votedSlot : A'.votedSlot = A.votedSlot
  fgReported : A'.fgReported = A.fgReported
  restartTime : A'.restartTime = A.restartTime

theorem Same.refl (A : SAState sp.n) : Same A A := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {A A' A'' : SAState sp.n} (h : Same A A') (h' : Same A' A'') : Same A A'' :=
  ⟨h'.pool.trans h.pool, h'.voteStamp.trans h.voteStamp, h'.blockStamp.trans h.blockStamp,
    h'.votedSlot.trans h.votedSlot, h'.fgReported.trans h.fgReported,
    h'.restartTime.trans h.restartTime⟩

/-- With `k = 2` every new fast lock of slot `s` expires after `s + 2`. -/
theorem fastExpiry_eq (L : Set Lock) (Φ : N.Frm) (t : Time) (s : Nat) :
    fastExpiry sp L Φ t s = s + 2 :=
  le_antisymm (fastExpiry_le sp L Φ t s) (le_fastExpiry sp L Φ t s)

theorem updateLatestConfirmed_eq (A : SAState sp.n) (Φ : N.Frm) (C : N.Blk) :
    ∃ c, updateLatestConfirmed sp A Φ C = { A with latestConfirmed := c } := by
  unfold updateLatestConfirmed
  split_ifs
  · exact ⟨A.latestConfirmed, rfl⟩
  · exact ⟨_, rfl⟩

theorem optimisticConfirmation_cases (A : SAState sp.n) (Φ : N.Frm) (t : Time) :
    Same A (optimisticConfirmation sp A Φ t) ∧
      ((optimisticConfirmation sp A Φ t).locks = A.locks ∨ ∃ B,
        optimisticSelect sp A Φ t = some B ∧ (optimisticConfirmation sp A Φ t).locks =
          addLocks sp A.locks Φ t (sp.slot t) {(B.root, true, sp.slot t + 2)}) := by
  unfold optimisticConfirmation
  split
  · exact ⟨Same.refl A, Or.inl rfl⟩
  · rename_i B hB
    rw [fastExpiry_eq]
    obtain ⟨c, hc⟩ := updateLatestConfirmed_eq
      { A with locks := (addLocks sp A.locks Φ t (sp.slot t)
        {(B.root, true, sp.slot t + 2)}) } Φ B
    rw [hc]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inr ⟨B, hB, rfl⟩⟩

theorem optimisticConfirmation_of_none {A : SAState sp.n} {Φ : N.Frm} {t : Time}
    (h : optimisticSelect sp A Φ t = none) : optimisticConfirmation sp A Φ t = A := by
  unfold optimisticConfirmation; rw [h]

theorem deepest_empty (Φ : N.Frm) : deepest Φ (∅ : Set N.Blk) = none := by
  unfold deepest; rw [dite_eq_right]; rintro ⟨B, hB, -⟩; exact hB

theorem optimisticSelect_of_pool_nil {A : SAState sp.n} {Φ : N.Frm} {t : Time}
    (h : A.pool (sp.slot t) = []) : optimisticSelect sp A Φ t = none := by
  unfold optimisticSelect
  dsimp only
  split_ifs
  · rfl
  · convert deepest_empty Φ
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h3 _
    have : optimisticVoters sp A Φ (sp.slot t) B = ∅ := by
      ext i; simp [optimisticVoters, h]
    rw [this, Set.ncard_empty] at h3
    change 3 * 2 ≤ 4 * 0 at h3
    omega

theorem updateConfirmation_cases (A : SAState sp.n) (Φ : N.Frm) (t : Time) (s : Nat) :
    Same A (updateConfirmation sp A Φ t s) ∧
      ((updateConfirmation sp A Φ t s).locks = A.locks ∨ ∃ N : Set (Nat × Bool × Nat),
        (∀ p ∈ N, ∃ B ∈ Φ.tree, p.1 = B.root) ∧
        (updateConfirmation sp A Φ t s).locks = addLocks sp A.locks Φ t s N) := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
  · rename_i C hC
    obtain ⟨c, hc⟩ := updateLatestConfirmed_eq
      { A with saved := Function.update A.saved s ((getConfirmation sp A Φ s).map Block.root) }
      Φ C
    split_ifs
    all_goals
      try rw [hc]
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inr ⟨_, ?_, rfl⟩⟩
      rintro p (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
      · exact ⟨B, (deepest_mem hB).1.1.1.1, rfl⟩
      · exact ⟨B, (deepest_mem hB).1.1.1.1, rfl⟩

open ChainFrame in
theorem liveLocks_le {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock}
    {b : Nat} (hL : LocksLe L b) (t : Time) : LocksLe (liveLocks sp L Φ t) b :=
  fun l hl => hL l (h.liveLocks_sub hl).1

open ChainFrame in
theorem addLocks_le {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock}
    {b : Nat} (hL : LocksLe L b) (hb : τ ≤ b) (t : Time) (s : Nat) {N : Set (Nat × Bool × Nat)}
    (hN : ∀ p ∈ N, ∃ B ∈ Φ.tree, p.1 = B.root) : LocksLe (addLocks sp L Φ t s N) b := by
  intro l hl
  obtain ⟨hl', -, -⟩ := h.liveLocks_sub hl
  rcases hl' with hl' | ⟨p, hp, rfl⟩
  · exact hL l hl'
  · obtain ⟨B, hB, hr⟩ := hN p hp
    obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB
    exact ⟨m, by omega, hr⟩

open ChainFrame in
theorem unlock_le {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock}
    {b : Nat} (hL : LocksLe L b) (t : Time) (s : Int) (V : View sp.n) :
    LocksLe (unlock sp L Φ t s V) b := by
  rintro l' ⟨l, hl, B, hB, hr, rfl⟩
  obtain ⟨hlL, ⟨m, h1, h2, hm⟩, -⟩ := h.liveLocks_sub hl
  obtain ⟨m', hm', hm'r⟩ := hL l hlL
  obtain rfl := blk_root_inj (hm.symm.trans hm'r)
  obtain ⟨rfl, -, -⟩ := h.eq_of_root hB (hr.trans hm)
  split_ifs
  · unfold unlockTarget
    rcases hd : deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' (blk m) ∧
        2 * (opponents sp Φ V s B').ncard < sp.n} with _ | D
    · exact ⟨f, by omega, by rw [Option.getD_none, h.F]⟩
    · obtain ⟨⟨hD, hDa, -⟩, -⟩ := deepest_mem hd
      obtain ⟨d, -, -, rfl⟩ := h.eq_of_mem hD
      exact ⟨d, le_trans (h.le_of_anc hDa) hm', rfl⟩
  · exact ⟨m, hm', hm⟩

open ChainFrame in
theorem mem_unlock {Φ : N.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock} {l : Lock}
    (hl : l ∈ L) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) (hr : l.block = (blk m).root) {t : Time}
    (hlive : sp.slot t ≤ l.expiry) {s : Int} (hs : ¬ (l.slot : Int) < s) (V : View sp.n) :
    l ∈ unlock sp L Φ t s V :=
  ⟨l, h.mem_liveLocks hl h1 h2 hr hlive, blk m, h.mem h1 h2, hr.symm, by rw [ite_eq_right hs]⟩

theorem admitVote_old {A : SAState sp.n} {t : Time} {v : Vote sp.n} (h : v ∈ A.pool v.slot) :
    admitVote sp A t v = A := by
  unfold admitVote; rw [ite_eq_left (Or.inr (Or.inr h))]

/-! ## The SA's calls of the tick run -/

theorem delta1 : sp.Δ = 1 := rfl

theorem slotOf_nat (t : Nat) : sp.toParams.slotOf (t : Int) = t / 4 := by
  unfold Params.slotOf
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by simp; omega, fun _ => ?_, fun n hn _ h => ?_⟩
  · change 4 * ((t / 4 : Nat) : Int) ≤ t; omega
  · change 4 * (n : Int) ≤ t at h; omega

theorem slot_nat (n : Nat) : sp.slot (n : Int) = n / 4 := slotOf_nat n

theorem ts_nat (s : Nat) : sp.ts (s : Int) = 4 * (s : Int) := by
  simp only [SAParams.ts]; change 4 * 1 * (s : Int) = _; ring

theorem joined_of_bot {A : SAState sp.n} (h : A.restartTime = ⊥) (t : Time) : joined sp A t := by
  unfold joined; rw [h]; exact bot_le

namespace ChainFrame

variable {Φ : N.Frm} {f j τ : Nat}

theorem tree_eq (h : ChainFrame Φ f j τ) : Φ.tree = blk '' Set.Icc f τ := by
  ext B
  rw [h.tree]
  constructor
  · rintro ⟨m, h1, h2, rfl⟩; exact ⟨m, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, h1, h2, rfl⟩

theorem tree_ncard (h : ChainFrame Φ f j τ) : Φ.tree.ncard = τ + 1 - f := by
  rw [h.tree_eq, Set.ncard_image_of_injective _ blk_injective, ← Finset.coe_Icc,
    Set.ncard_coe_finset, Nat.card_Icc]

theorem lookup_blk (h : ChainFrame Φ f j τ) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) :
    lookup Φ (blk m).root = some (blk m) := by
  have hin : InTree Φ (blk m).root := ⟨blk m, h.mem h1 h2, rfl⟩
  unfold lookup
  rw [dite_eq_left hin]
  have hs := hin.choose_spec
  rw [(h.eq_of_root hs.1 hs.2).1]

theorem voterBlockTree_sub (A : SAState sp.n) (s : Nat) :
    voterBlockTree sp A Φ s ⊆ Φ.tree := fun _ hB => hB.1

theorem mem_voterBlockTree (h : ChainFrame Φ f j τ) (A : SAState sp.n) {m : Nat} (h1 : f ≤ m)
    (h2 : m ≤ τ) : blk m ∈ voterBlockTree sp A Φ τ :=
  ⟨h.mem h1 h2, Or.inr ⟨blk τ, h.mem (by omega) le_rfl, blk_slot τ, h.anc h1 h2 le_rfl⟩⟩

end ChainFrame

open ChainFrame


end Consensus.Goldilocks.Witness.TwoRun

end

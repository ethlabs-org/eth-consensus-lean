module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # The one-validator tick run: the SA's calls and the ticks

The SA on a chain frame (`ChainFrame`): the deepest block of a set of chain blocks is the latest,
every block is its own viable ancestor, live locks keep their blocks, and a head walk stops at the
tip. With this, each tick of the run is computed (`Good st t`, the node state before the tick of
time `t`, with `tip t` the latest accepted slot):

* `tick_A` (`t = t_{k+1}`): `ac_proposal` returns the tip `k` (the anchor: the fast lock of the
  previous slot) and the slot-`k` vote; the own block is `blk (k + 1)`; its `ac_on_block` casts the
  vote of slot `k + 1` (`tryVote_blk`) and writes its optimistic fast lock; `ac_to_fg` returns
  `blk (k + 1)` and the node signs `att (k + 1)`.
* `tick_B0` (`t = 1`): the vote of slot `0` on genesis.
* `tick_C` (`t = t_s + 2Δ`): the confirmation update, which keeps the locks on chain blocks.
* `tick_noop`: the other ticks change nothing; `ac_to_fg` returns `⊥` once the tip is reported. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node

/-! ## The SA on a chain frame -/

theorem etime_of_lt_top (t : Time) : ETime.of t < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top t)

theorem blk_injective : Function.Injective blk := fun _ _ h => blk_inj h

namespace ChainFrame

variable {Φ : N1.Frm} {f j τ : Nat}

theorem fcRoot_mem' (h : ChainFrame Φ f j τ) : Φ.fcRoot ∈ Φ.tree := by
  rw [h.fcRoot]; exact h.mem h.fj h.jτ

theorem eq_of_mem (h : ChainFrame Φ f j τ) {B : N1.Blk} (hB : B ∈ Φ.tree) :
    ∃ m, f ≤ m ∧ m ≤ τ ∧ B = blk m := (h.tree B).1 hB

theorem eq_of_root (h : ChainFrame Φ f j τ) {B : N1.Blk} (hB : B ∈ Φ.tree) {m : Nat}
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

theorem isDeepest_unique {S : Set N1.Blk} {B C : N1.Blk} (hB : IsDeepest Φ S B)
    (hC : IsDeepest Φ S C) : B = C := by
  by_contra hne
  rcases hB.2 C hC.1 (Ne.symm hne) with h | ⟨h, h'⟩ <;>
    rcases hC.2 B hB.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

/-- The deepest block of a set of chain blocks of the tree is the latest one. -/
theorem deepest_eq (h : ChainFrame Φ f j τ) {S : Set N1.Blk} (hS : S ⊆ Φ.tree) {M : Nat}
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
  rw [dite_pos' ⟨_, hd⟩]
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
  rw [dite_pos' ⟨_, hv⟩]
  have hs := Exists.choose_spec (⟨_, hv⟩ : ∃ A, Φ.IsViableAncestor (blk m) A)
  obtain ⟨a, ha, he, -⟩ := anc_blk_inv h.onChain hs.1
  rw [he] at hs ⊢
  have := h.le_of_anc (hs.2.2 (blk m) Relation.ReflTransGen.refl hcand)
  rw [show a = m by omega]

theorem mem_liveLocks (h : ChainFrame Φ f j τ) {L : Set Lock} {t : Time} {l : Lock} (hl : l ∈ L)
    {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) (hr : l.block = (blk m).root)
    (hlive : sp1.slot t ≤ l.expiry) : l ∈ liveLocks sp1 L Φ t :=
  ⟨l, hl, blk m, h.mem h1 h2, hr.symm, hlive, by rw [h.viableAncestor_eq h1 h2, ← hr]⟩

theorem liveLocks_sub (h : ChainFrame Φ f j τ) {L : Set Lock} {t : Time} {l : Lock}
    (hl : l ∈ liveLocks sp1 L Φ t) :
    l ∈ L ∧ (∃ m, f ≤ m ∧ m ≤ τ ∧ l.block = (blk m).root) ∧ sp1.slot t ≤ l.expiry := by
  obtain ⟨l₀, hl₀, B, hB, hr, hlive, rfl⟩ := hl
  obtain ⟨m, h1, h2, rfl⟩ := h.eq_of_mem hB
  rw [h.viableAncestor_eq h1 h2, hr]
  exact ⟨hl₀, ⟨m, h1, h2, hr.symm⟩, hlive⟩

/-- Locks on chain blocks up to `b`. -/
def LocksLe (L : Set Lock) (b : Nat) : Prop := ∀ l ∈ L, ∃ m ≤ b, l.block = (blk m).root

theorem liveLockBlocks_le (h : ChainFrame Φ f j τ) {L : Set Lock} {b : Nat} (hL : LocksLe L b)
    {t : Time} {B : N1.Blk} (hB : B ∈ liveLockBlocks sp1 L Φ t) : ∃ m ≤ b, B = blk m := by
  obtain ⟨hBt, l, hl, hr⟩ := hB
  obtain ⟨hlL, -, -⟩ := h.liveLocks_sub hl
  obtain ⟨m, hm, hr'⟩ := hL l hlL
  exact ⟨m, hm, (h.eq_of_root hBt (hr.symm.trans hr')).1⟩

/-- The anchor is the latest live lock block (or `fc_root`). -/
theorem getAnchor_eq (h : ChainFrame Φ f j τ) {A : SAState sp1.n} {t : Time} {b : Nat}
    (hL : LocksLe A.locks b) (hjb : j ≤ b) (hb : blk b ∈ liveLockBlocks sp1 A.locks Φ t ∨ b = j) :
    getAnchor sp1 A Φ t = blk b := by
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

theorem ghost_tip {T : Set N1.Blk} {b : Nat} (hT : ∀ B ∈ T, ∃ m ≤ b, B = blk m)
    (sc : N1.Blk → Nat) (el : N1.Blk → Prop) : ∀ n, ghost sp1 T sc el n (blk b) = blk b
  | 0 => rfl
  | n + 1 => by
    rw [ghost, dite_neg']
    rintro ⟨C, ⟨hCT, hpar, -⟩, -⟩
    obtain ⟨m, hm, rfl⟩ := hT C hCT
    rcases m with _ | m
    · rw [blk_parent_zero] at hpar; cases hpar
    · rw [blk_parent_succ] at hpar
      have := blk_root_inj (Option.some.inj hpar); omega

theorem ghost_step {T : Set N1.Blk} {b : Nat} (hT : ∀ B ∈ T, ∃ m, B = blk m)
    (hmem : blk (b + 1) ∈ T) {sc : N1.Blk → Nat} {el : N1.Blk → Prop} (hel : el (blk (b + 1)))
    (n : Nat) : ghost sp1 T sc el (n + 1) (blk b) = ghost sp1 T sc el n (blk (b + 1)) := by
  have hbest : IsBest sp1 sc {B | B ∈ T ∧ B.parent = some (blk b).root ∧ el B} (blk (b + 1)) := by
    refine ⟨⟨hmem, blk_parent_succ b, hel⟩, fun D hD' hne => absurd ?_ hne⟩
    obtain ⟨hD, hpar, -⟩ := hD'
    obtain ⟨m, rfl⟩ := hT D hD
    rcases m with _ | m
    · rw [blk_parent_zero] at hpar; cases hpar
    · rw [blk_parent_succ] at hpar
      rw [blk_root_inj (Option.some.inj hpar)]
  rw [ghost, dite_pos' ⟨_, hbest⟩]
  congr 1
  have hc := Exists.choose_spec (⟨_, hbest⟩ : ∃ C, IsBest sp1 sc
    {B | B ∈ T ∧ B.parent = some (blk b).root ∧ el B} C)
  by_contra hne
  rcases hc.2 _ hbest.1 (Ne.symm hne) with h | ⟨h, h'⟩ <;>
    rcases hbest.2 _ hc.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

open ChainFrame in
theorem compatible_chain {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {B C : N1.Blk}
    (hB : B ∈ Φ.tree) (hC : C ∈ Φ.tree) : Compatible Φ.tree B C := by
  obtain ⟨b, hb1, hb2, rfl⟩ := h.eq_of_mem hB
  obtain ⟨c, hc1, hc2, rfl⟩ := h.eq_of_mem hC
  rcases le_total b c with hbc | hbc
  · exact Or.inl (h.anc hb1 hbc hc2)
  · exact Or.inr (h.anc hc1 hbc hb2)

/-- The SA state apart from locks, the record of the confirmed block and the saved results. -/
structure Same (A A' : SAState sp1.n) : Prop where
  pool : A'.pool = A.pool
  voteStamp : A'.voteStamp = A.voteStamp
  blockStamp : A'.blockStamp = A.blockStamp
  votedSlot : A'.votedSlot = A.votedSlot
  fgReported : A'.fgReported = A.fgReported
  restartTime : A'.restartTime = A.restartTime

theorem Same.refl (A : SAState sp1.n) : Same A A := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {A A' A'' : SAState sp1.n} (h : Same A A') (h' : Same A' A'') : Same A A'' :=
  ⟨h'.pool.trans h.pool, h'.voteStamp.trans h.voteStamp, h'.blockStamp.trans h.blockStamp,
    h'.votedSlot.trans h.votedSlot, h'.fgReported.trans h.fgReported,
    h'.restartTime.trans h.restartTime⟩

/-- With `k = 2` every new fast lock of slot `s` expires after `s + 2`. -/
theorem fastExpiry_eq (L : Set Lock) (Φ : N1.Frm) (t : Time) (s : Nat) :
    fastExpiry sp1 L Φ t s = s + 2 :=
  le_antisymm (fastExpiry_le sp1 L Φ t s) (le_fastExpiry sp1 L Φ t s)

theorem updateLatestConfirmed_eq (A : SAState sp1.n) (Φ : N1.Frm) (C : N1.Blk) :
    ∃ c, updateLatestConfirmed sp1 A Φ C = { A with latestConfirmed := c } := by
  unfold updateLatestConfirmed
  split_ifs
  · exact ⟨A.latestConfirmed, rfl⟩
  · exact ⟨_, rfl⟩

theorem optimisticConfirmation_cases (A : SAState sp1.n) (Φ : N1.Frm) (t : Time) :
    Same A (optimisticConfirmation sp1 A Φ t) ∧
      ((optimisticConfirmation sp1 A Φ t).locks = A.locks ∨ ∃ B,
        optimisticSelect sp1 A Φ t = some B ∧ (optimisticConfirmation sp1 A Φ t).locks =
          addLocks sp1 A.locks Φ t (sp1.slot t) {(B.root, true, sp1.slot t + 2)}) := by
  unfold optimisticConfirmation
  split
  · exact ⟨Same.refl A, Or.inl rfl⟩
  · rename_i B hB
    rw [fastExpiry_eq]
    obtain ⟨c, hc⟩ := updateLatestConfirmed_eq
      { A with locks := (addLocks sp1 A.locks Φ t (sp1.slot t)
        {(B.root, true, sp1.slot t + 2)}) } Φ B
    rw [hc]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inr ⟨B, hB, rfl⟩⟩

theorem optimisticConfirmation_of_none {A : SAState sp1.n} {Φ : N1.Frm} {t : Time}
    (h : optimisticSelect sp1 A Φ t = none) : optimisticConfirmation sp1 A Φ t = A := by
  unfold optimisticConfirmation; rw [h]

theorem deepest_empty (Φ : N1.Frm) : deepest Φ (∅ : Set N1.Blk) = none := by
  unfold deepest; rw [dite_neg']; rintro ⟨B, hB, -⟩; exact hB

theorem optimisticSelect_of_pool_nil {A : SAState sp1.n} {Φ : N1.Frm} {t : Time}
    (h : A.pool (sp1.slot t) = []) : optimisticSelect sp1 A Φ t = none := by
  unfold optimisticSelect
  dsimp only
  split_ifs
  · rfl
  · convert deepest_empty Φ
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h3 _
    have : optimisticVoters sp1 A Φ (sp1.slot t) B = ∅ := by
      ext i; simp [optimisticVoters, h]
    rw [this, Set.ncard_empty] at h3
    change 3 * 1 ≤ 4 * 0 at h3
    omega

theorem optimisticSelect_vote {Φ : N1.Frm} {f j s : Nat} (h : ChainFrame Φ f j s) (hs : 1 ≤ s)
    {A : SAState sp1.n} {t : Time} (hst : sp1.slot t = s) (ht : t < sp1.ts s + 2 * sp1.Δ)
    (hjn : joined sp1 A t) (hpool : A.pool s = [cv s]) :
    optimisticSelect sp1 A Φ t = some (blk s) := by
  unfold optimisticSelect
  rw [ite_neg (by rw [hst]; push Not; exact ⟨hjn, by omega, ht⟩)]
  have htip := h.mem (le_trans h.fj h.jτ) le_rfl
  apply h.deepest_eq (fun B hB => hB.1)
  · refine ⟨htip, ?_, ?_⟩
    · have : optimisticVoters sp1 A Φ (sp1.slot t) (blk s) = Set.univ := by
        ext i
        simp only [optimisticVoters, Set.mem_ofPred_eq, Set.mem_univ, iff_true, hst, hpool,
          List.mem_singleton, exists_eq_left]
        exact ⟨Subsingleton.elim _ _, blk s, htip, rfl, Relation.ReflTransGen.refl⟩
      rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    · rintro ⟨B, hB, hnc⟩; exact hnc (compatible_chain h htip hB.1)
  · rintro B ⟨hB, -⟩
    obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB
    exact ⟨m, hm, rfl⟩

theorem updateConfirmation_cases (A : SAState sp1.n) (Φ : N1.Frm) (t : Time) (s : Nat) :
    Same A (updateConfirmation sp1 A Φ t s) ∧
      ((updateConfirmation sp1 A Φ t s).locks = A.locks ∨ ∃ N : Set (Nat × Bool × Nat),
        (∀ p ∈ N, ∃ B ∈ Φ.tree, p.1 = B.root) ∧
        (updateConfirmation sp1 A Φ t s).locks = addLocks sp1 A.locks Φ t s N) := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inl rfl⟩
  · rename_i C hC
    obtain ⟨c, hc⟩ := updateLatestConfirmed_eq
      { A with saved := Function.update A.saved s ((getConfirmation sp1 A Φ s).map Block.root) }
      Φ C
    split_ifs
    all_goals
      try rw [hc]
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, Or.inr ⟨_, ?_, rfl⟩⟩
      rintro p (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
      · exact ⟨B, (deepest_mem hB).1.1.1.1, rfl⟩
      · exact ⟨B, (deepest_mem hB).1.1.1.1, rfl⟩

open ChainFrame in
theorem liveLocks_le {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock}
    {b : Nat} (hL : LocksLe L b) (t : Time) : LocksLe (liveLocks sp1 L Φ t) b :=
  fun l hl => hL l (h.liveLocks_sub hl).1

open ChainFrame in
theorem addLocks_le {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock}
    {b : Nat} (hL : LocksLe L b) (hb : τ ≤ b) (t : Time) (s : Nat) {N : Set (Nat × Bool × Nat)}
    (hN : ∀ p ∈ N, ∃ B ∈ Φ.tree, p.1 = B.root) : LocksLe (addLocks sp1 L Φ t s N) b := by
  intro l hl
  obtain ⟨hl', -, -⟩ := h.liveLocks_sub hl
  rcases hl' with hl' | ⟨p, hp, rfl⟩
  · exact hL l hl'
  · obtain ⟨B, hB, hr⟩ := hN p hp
    obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB
    exact ⟨m, by omega, hr⟩

open ChainFrame in
theorem unlock_le {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock}
    {b : Nat} (hL : LocksLe L b) (t : Time) (s : Int) (V : View sp1.n) :
    LocksLe (unlock sp1 L Φ t s V) b := by
  rintro l' ⟨l, hl, B, hB, hr, rfl⟩
  obtain ⟨hlL, ⟨m, h1, h2, hm⟩, -⟩ := h.liveLocks_sub hl
  obtain ⟨m', hm', hm'r⟩ := hL l hlL
  obtain rfl := blk_root_inj (hm.symm.trans hm'r)
  obtain ⟨rfl, -, -⟩ := h.eq_of_root hB (hr.trans hm)
  split_ifs
  · unfold unlockTarget
    rcases hd : deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' (blk m) ∧
        2 * (opponents sp1 Φ V s B').ncard < sp1.n} with _ | D
    · exact ⟨f, by omega, by rw [Option.getD_none, h.F]⟩
    · obtain ⟨⟨hD, hDa, -⟩, -⟩ := deepest_mem hd
      obtain ⟨d, -, -, rfl⟩ := h.eq_of_mem hD
      exact ⟨d, le_trans (h.le_of_anc hDa) hm', rfl⟩
  · exact ⟨m, hm', hm⟩

open ChainFrame in
theorem mem_unlock {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ) {L : Set Lock} {l : Lock}
    (hl : l ∈ L) {m : Nat} (h1 : f ≤ m) (h2 : m ≤ τ) (hr : l.block = (blk m).root) {t : Time}
    (hlive : sp1.slot t ≤ l.expiry) {s : Int} (hs : ¬ (l.slot : Int) < s) (V : View sp1.n) :
    l ∈ unlock sp1 L Φ t s V :=
  ⟨l, h.mem_liveLocks hl h1 h2 hr hlive, blk m, h.mem h1 h2, hr.symm, by rw [ite_neg hs]⟩

theorem admitVote_old {A : SAState sp1.n} {t : Time} {v : Vote sp1.n} (h : v ∈ A.pool v.slot) :
    admitVote sp1 A t v = A := by
  unfold admitVote; rw [ite_pos (Or.inr (Or.inr h))]

theorem admitVote_cv {A : SAState sp1.n} {t : Time} {s : Nat} (hst : sp1.slot t = s)
    (h : A.pool s = []) :
    admitVote sp1 A t (cv s) =
      { A with pool := Function.update A.pool s [cv s],
               voteStamp := Function.update A.voteStamp (cv s) (ETime.of t) } := by
  unfold admitVote
  change (if ((s : Nat) : Int) < (sp1.slot t : Int) - 1 ∨ sp1.slot t < s ∨ cv s ∈ A.pool s then A
    else if 2 ≤ ((A.pool s).filter (fun x => x.val = (cv s).val)).dedup.length then A
    else { A with pool := Function.update A.pool s (A.pool s ++ [cv s]),
                  voteStamp := Function.update A.voteStamp (cv s) (ETime.of t) }) = _
  rw [h, hst, ite_neg (by simp), ite_neg (by simp)]
  rfl

theorem blockReceipt_blk {A : SAState sp1.n} {t : Time} {s : Nat}
    (h : cv s ∈ A.pool s) :
    blockReceipt sp1 A t (blk (s + 1)) =
      { A with blockStamp := Function.update A.blockStamp (blk (s + 1)).root (ETime.of t) } := by
  unfold blockReceipt
  rw [show blockVotes (blk (s + 1)) = [cv s] from rfl, List.foldl_cons, List.foldl_nil]
  exact admitVote_old h

/-! ## The SA's calls of the tick run -/

theorem delta1 : sp1.Δ = 1 := rfl

theorem slot_nat (n : Nat) : sp1.slot (n : Int) = n / 4 := slotOf_nat n

theorem ts_nat (s : Nat) : sp1.ts (s : Int) = 4 * (s : Int) := by
  simp only [SAParams.ts]; change 4 * 1 * (s : Int) = _; ring

theorem joined_of_bot {A : SAState sp1.n} (h : A.restartTime = ⊥) (t : Time) : joined sp1 A t := by
  unfold joined; rw [h]; exact bot_le

namespace ChainFrame

variable {Φ : N1.Frm} {f j τ : Nat}

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
  rw [dite_pos' hin]
  have hs := hin.choose_spec
  rw [(h.eq_of_root hs.1 hs.2).1]

theorem voterBlockTree_sub (A : SAState sp1.n) (s : Nat) :
    voterBlockTree sp1 A Φ s ⊆ Φ.tree := fun _ hB => hB.1

theorem mem_voterBlockTree (h : ChainFrame Φ f j τ) (A : SAState sp1.n) {m : Nat} (h1 : f ≤ m)
    (h2 : m ≤ τ) : blk m ∈ voterBlockTree sp1 A Φ τ :=
  ⟨h.mem h1 h2, Or.inr ⟨blk τ, h.mem (by omega) le_rfl, blk_slot τ, h.anc h1 h2 le_rfl⟩⟩

end ChainFrame

open ChainFrame

theorem optimisticSelect_slot_zero {A : SAState sp1.n} {Φ : N1.Frm} {t : Time}
    (h : sp1.slot t = 0) : optimisticSelect sp1 A Φ t = none := by
  unfold optimisticSelect
  dsimp only
  rw [ite_pos (Or.inr (Or.inl h))]

theorem optimisticConfirmation_of_some {A : SAState sp1.n} {Φ : N1.Frm} {t : Time} {B : N1.Blk}
    (h : optimisticSelect sp1 A Φ t = some B) :
    Same A (optimisticConfirmation sp1 A Φ t) ∧ (optimisticConfirmation sp1 A Φ t).locks =
      addLocks sp1 A.locks Φ t (sp1.slot t) {(B.root, true, sp1.slot t + 2)} := by
  unfold optimisticConfirmation
  rw [h]
  dsimp only
  rw [fastExpiry_eq]
  obtain ⟨c, hc⟩ := updateLatestConfirmed_eq
    { A with locks := (addLocks sp1 A.locks Φ t (sp1.slot t)
      {(B.root, true, sp1.slot t + 2)}) } Φ B
  rw [hc]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `ac_on_tick` by the residue of the time modulo a slot. -/
theorem acOnTick_eq (A : SAState sp1.n) (Φ : N1.Frm) (n : Nat) (hj : A.restartTime = ⊥) :
    acOnTick sp1 v0 A Φ n =
      if n % 4 = 2 ∧ 4 ≤ n then (updateConfirmation sp1 A Φ n (n / 4 - 1), [])
      else if n % 4 = 1 then tryVote sp1 v0 A Φ n else (A, []) := by
  unfold acOnTick
  rw [ite_neg (not_not.2 (joined_of_bot hj _))]
  dsimp only
  rw [slot_nat, ts_nat]
  have e1 : ((n : Int) = 4 * ((n / 4 : Nat) : Int) + sp1.Δ) ↔ n % 4 = 1 := by
    change _ = _ + 1 ↔ _; omega
  have e2 : ((n : Int) = 4 * ((n / 4 : Nat) : Int) + 2 * sp1.Δ ∧ 0 < n / 4) ↔
      (n % 4 = 2 ∧ 4 ≤ n) := by
    change _ = _ + 2 * 1 ∧ _ ↔ _; omega
  by_cases h1 : n % 4 = 1
  · have h2 : ¬ (n % 4 = 2 ∧ 4 ≤ n) := by omega
    rw [ite_pos (e1.2 h1), ite_neg (fun h => h2 (e2.1 h)), ite_neg h2, ite_pos h1]
  · rw [ite_neg (fun h => h1 (e1.1 h))]
    by_cases h2 : n % 4 = 2 ∧ 4 ≤ n
    · rw [ite_pos (e2.2 h2), ite_pos h2]
    · rw [ite_neg (fun h => h2 (e2.1 h)), ite_neg h2, ite_neg h1]

theorem tryVote_voted {A : SAState sp1.n} {Φ : N1.Frm} {t : Time}
    (h : A.votedSlot = (sp1.slot t : Int)) : tryVote sp1 v0 A Φ t = (A, []) := by
  unfold tryVote
  dsimp only
  rw [ite_pos (Or.inr (Or.inl h))]

/-- The vote of slot `0`, at time `1`. -/
theorem tryVote_zero {A : SAState sp1.n} {Φ : N1.Frm} (h : ChainFrame Φ 0 0 0)
    (hj : A.restartTime = ⊥) (hvs : A.votedSlot = -1)
    (hL : LocksLe A.locks 0) :
    ∃ d, tryVote sp1 v0 A Φ 1 = (admitVote sp1 { A with votedSlot := 0 } 1 (cv 0),
      [⟨cv 0, { A with votedSlot := 0 }, some d⟩]) := by
  have hs : sp1.slot (1 : Int) = 0 := slot_nat 1
  unfold tryVote
  dsimp only
  rw [hs, ite_neg (by rw [ts_nat, hvs]; push Not; exact ⟨joined_of_bot hj _, by decide, by decide⟩),
    ite_neg (by rw [ts_nat]; change ¬ ((1 : Int) < 4 * 0 + 1 ∧ _); omega), ite_neg (lt_irrefl 0)]
  have hanc : getAnchor sp1 A Φ 1 = blk 0 := h.getAnchor_eq hL le_rfl (Or.inr rfl)
  have hhead : getHead sp1 A Φ 1 (Φ.viableTree (voteDomain sp1 A Φ 0))
      (mergedVoteView sp1 A Φ 0) ((0 : Nat) - 1) = blk 0 := by
    unfold getHead
    rw [hanc]
    refine ghost_tip (fun B hB => ?_) _ _ _
    obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem (voteDomain_subset_tree hB.1)
    exact ⟨m, hm, rfl⟩
  rw [hhead, optimisticConfirmation_of_none (optimisticSelect_slot_zero hs)]
  exact ⟨_, rfl⟩

theorem voteReady_blk {Φ : N1.Frm} {f k : Nat} (h : ChainFrame Φ f (jexp (k + 1)) (k + 1)) :
    voteReady sp1 Φ (k + 1) := by
  have hf : f ≤ k := by have := h.fj; have := jexp_le k; unfold jexp at *; split_ifs at * <;> omega
  refine ⟨blk (k + 1), h.mem (by omega) le_rfl, blk_slot _, fun x hx _ => ?_⟩
  rw [show blockSupport (blk (k + 1)) = [cv k] from rfl, List.mem_singleton] at hx
  subst hx
  exact ⟨blk k, h.mem hf (by omega), rfl, by rw [blk_slot]⟩

theorem jexp_succ_le (k : Nat) : jexp (k + 1) ≤ k := by unfold jexp; split_ifs <;> omega

/-- The vote of slot `k + 1`, inside `ac_on_block` of the own block at `t_{k+1}`. -/
theorem tryVote_blk {A : SAState sp1.n} {Φ : N1.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jexp (k + 1)) (k + 1)) (hj : A.restartTime = ⊥)
    (hvs : A.votedSlot = (k : Int)) (hpool : A.pool (k + 1) = []) (hL : LocksLe A.locks k)
    (htip : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ A.locks) :
    ∃ L₁ d, tryVote sp1 v0 A Φ ((4 * (k + 1) : Nat) : Int) =
      (optimisticConfirmation sp1 (admitVote sp1 { A with locks := L₁, votedSlot := (k + 1 : Nat) }
        ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ ((4 * (k + 1) : Nat) : Int),
        [⟨cv (k + 1), { A with locks := L₁, votedSlot := (k + 1 : Nat) }, some d⟩]) ∧
      LocksLe L₁ k ∧ (1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁) := by
  have hs : sp1.slot (((4 * (k + 1) : Nat) : Int)) = k + 1 := by rw [slot_nat]; omega
  have hf : f ≤ k := le_trans h.fj (jexp_succ_le k)
  unfold tryVote
  dsimp only
  rw [hs, ite_neg (by
      rw [ts_nat, hvs]; push Not
      exact ⟨joined_of_bot hj _, by push_cast; omega, by rw [delta1]; push_cast; linarith⟩),
    ite_neg (fun hc => hc.2.elim (by omega) (fun hn => hn (voteReady_blk h))),
    ite_pos (by omega : 0 < k + 1)]
  set V := mergedVoteView sp1 A Φ (k + 1)
  set L₁ := unlock sp1 A.locks Φ ((4 * (k + 1) : Nat) : Int) (((k + 1 : Nat) : Int) - 1) V
  have hL₁ : LocksLe L₁ k := unlock_le h hL _ _ _
  have htip₁ : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁ := fun hk =>
    mem_unlock h (htip hk) hf (by omega) rfl (by rw [hs]; change k + 1 ≤ k + 2; omega)
      (by push_cast; omega) V
  have hanc : getAnchor sp1 { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int) = blk k := by
    refine h.getAnchor_eq hL₁ (jexp_succ_le k) ?_
    rcases Nat.lt_or_ge k 1 with hk | hk
    · right; obtain rfl : k = 0 := by omega
      rfl
    · left
      exact ⟨h.mem hf (by omega), _, h.mem_liveLocks (htip₁ hk) hf (by omega) rfl
        (by rw [hs]; change k + 1 ≤ k + 2; omega), rfl⟩
  have hncard : Φ.tree.ncard = (k + 1 - f) + 1 := by rw [h.tree_ncard]; omega
  have hhead : getHead sp1 { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int)
      (Φ.viableTree (voteDomain sp1 { A with locks := L₁ } Φ (k + 1))) V
      (((k + 1 : Nat) : Int) - 1) = blk (k + 1) := by
    unfold getHead
    rw [hanc, hncard]
    have hT : ∀ B ∈ Φ.viableTree (voteDomain sp1 { A with locks := L₁ } Φ (k + 1)),
        ∃ m ≤ k + 1, B = blk m := fun B hB => by
      obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem (voteDomain_subset_tree hB.1)
      exact ⟨m, hm, rfl⟩
    rw [ghost_step (fun B hB => (hT B hB).imp fun _ h => h.2)
      (viableTree_voterBlockTree_subset_voteDomain
        (h.mem_viableTree (mem_voterBlockTree h _ (by omega) le_rfl) (jexp_le _) le_rfl
          (mem_voterBlockTree h _ (by omega) le_rfl)))
      (Or.inr (Or.inl (by rw [blk_slot, hs])))]
    exact ghost_tip hT _ _ _
  rw [hhead]
  exact ⟨L₁, _, rfl, hL₁, htip₁⟩

/-- `ac_proposal` at `t_{k+1}`: the tip `k` as the parent, the slot-`k` vote as the payload. -/
theorem acProposal_tick {A : SAState sp1.n} {Φ : N1.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jexp k) k) (hj : A.restartTime = ⊥) (hpool : A.pool k = [cv k])
    (hvst : A.voteStamp (cv k) < ⊤) (hbst : A.blockStamp (blk k).root < ⊤)
    (hL : LocksLe A.locks k) (htip : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ A.locks) :
    ∃ L₁ d, SA.acProposal sp1 A Φ ((4 * (k + 1) : Nat) : Int) =
        ({ A with locks := L₁ }, some (d, ([cv k], [cv k]))) ∧ d.head = blk k ∧
      LocksLe L₁ k ∧ (1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁) := by
  have hs : sp1.slot (((4 * (k + 1) : Nat) : Int)) = k + 1 := by rw [slot_nat]; omega
  have hf : f ≤ k := le_trans h.fj (jexp_le k)
  unfold SA.acProposal
  rw [ite_neg (not_not.2 (joined_of_bot hj _))]
  dsimp only
  rw [hs]
  have hk : (((k + 1 : Nat) : Int) - 1) = (k : Int) := by push_cast; ring
  rw [hk]
  have hp : voteViewList A Φ (k : Int) ⊤ = ([cv k], [cv k]) := by
    have hres : resolutionTime A Φ (cv k) < ⊤ := by
      unfold resolutionTime
      rw [show (cv k).head = (blk k).root from rfl, h.lookup_blk hf le_rfl]
      dsimp only
      rw [ite_neg (by rw [blk_slot]; exact lt_irrefl k)]
      exact max_lt hvst hbst
    unfold voteViewList SAState.poolAt
    rw [ite_neg (by omega), Int.toNat_natCast, hpool]
    simp [hvst, hres]
  rw [hp]
  set L₁ := unlock sp1 A.locks Φ ((4 * (k + 1) : Nat) : Int) (k : Int)
    (View.ofLists ([cv k], [cv k]))
  have hL₁ : LocksLe L₁ k := unlock_le h hL _ _ _
  have htip₁ : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ L₁ := fun hk1 =>
    mem_unlock h (htip hk1) hf le_rfl rfl (by rw [hs]; change k + 1 ≤ k + 2; omega)
      (lt_irrefl _) _
  have hanc : getAnchor sp1 { A with locks := L₁ } Φ ((4 * (k + 1) : Nat) : Int) = blk k := by
    refine h.getAnchor_eq hL₁ (jexp_le k) ?_
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · right; obtain rfl : k = 0 := by omega
      rfl
    · left
      exact ⟨h.mem hf le_rfl, _, h.mem_liveLocks (htip₁ hk1) hf le_rfl rfl
        (by rw [hs]; change k + 1 ≤ k + 2; omega), rfl⟩
  refine ⟨L₁, _, rfl, ?_, hL₁, htip₁⟩
  change ghost sp1 _ _ _ _ (getAnchor sp1 { A with locks := L₁ } Φ _) = _
  rw [hanc]
  refine ghost_tip (fun B hB => ?_) _ _ _
  obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB.1
  exact ⟨m, hm, rfl⟩

/-- The own vote of slot `k + 1`, admitted, and its optimistic fast lock. -/
theorem vote_admitted {A' : SAState sp1.n} {Φ : N1.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jexp (k + 1)) (k + 1)) (hj : A'.restartTime = ⊥)
    (hpool : A'.pool (k + 1) = []) (hL : LocksLe A'.locks k) :
    (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).restartTime = ⊥ ∧
    (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).votedSlot = A'.votedSlot ∧
    (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).pool = Function.update A'.pool (k + 1) [cv (k + 1)] ∧
    (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).voteStamp =
      Function.update A'.voteStamp (cv (k + 1)) (ETime.of ((4 * (k + 1) : Nat) : Int)) ∧
    (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).blockStamp = A'.blockStamp ∧
    (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).fgReported = A'.fgReported ∧
    LocksLe (optimisticConfirmation sp1 (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int)
        (cv (k + 1))) Φ ((4 * (k + 1) : Nat) : Int)).locks (k + 1) ∧
    (⟨(blk (k + 1)).root, k + 1, true, k + 1 + 2⟩ : Lock) ∈ (optimisticConfirmation sp1
      (admitVote sp1 A' ((4 * (k + 1) : Nat) : Int) (cv (k + 1))) Φ
        ((4 * (k + 1) : Nat) : Int)).locks := by
  have hs : sp1.slot (((4 * (k + 1) : Nat) : Int)) = k + 1 := by rw [slot_nat]; omega
  rw [admitVote_cv hs hpool]
  have hsel := optimisticSelect_vote
    (A := { A' with pool := Function.update A'.pool (k + 1) [cv (k + 1)],
                    voteStamp := Function.update A'.voteStamp (cv (k + 1))
                      (ETime.of ((4 * (k + 1) : Nat) : Int)) }) h (by omega) hs
    (by rw [ts_nat, delta1]; push_cast; linarith) (joined_of_bot hj _)
    (Function.update_self _ _ _)
  obtain ⟨hsame, hlocks⟩ := optimisticConfirmation_of_some hsel
  refine ⟨hsame.restartTime.trans hj, hsame.votedSlot, hsame.pool, hsame.voteStamp,
    hsame.blockStamp, hsame.fgReported, ?_, ?_⟩
  · rw [hlocks]
    refine addLocks_le h (fun l hl => (hL l hl).imp fun m hm => ⟨by omega, hm.2⟩) le_rfl _ _ ?_
    rintro p hp
    rw [Set.mem_singleton_iff] at hp
    exact ⟨blk (k + 1), h.mem (le_trans h.fj (jexp_le _)) le_rfl, by rw [hp]⟩
  · rw [hlocks, hs]
    exact h.mem_liveLocks (Or.inr ⟨_, rfl, rfl⟩) (le_trans h.fj (jexp_le _)) le_rfl rfl
      (by rw [hs]; dsimp only; omega)

/-- `ac_on_block` of the own block of slot `k + 1`: the vote of slot `k + 1` and its fast lock. -/
theorem acOnBlock_tick {A : SAState sp1.n} {Φ : N1.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jexp (k + 1)) (k + 1)) (hj : A.restartTime = ⊥)
    (hvs : A.votedSlot = (k : Int)) (hpool : A.pool (k + 1) = []) (hcv : cv k ∈ A.pool k)
    (hL : LocksLe A.locks k) (htip : 1 ≤ k → (⟨(blk k).root, k, true, k + 2⟩ : Lock) ∈ A.locks) :
    ∃ A₃ e, acOnBlock sp1 v0 A Φ ((4 * (k + 1) : Nat) : Int) (blk (k + 1)) = (A₃, [e]) ∧
      e.msg = cv (k + 1) ∧ e.readPoint.pool = A.pool ∧ e.readPoint.restartTime = ⊥ ∧
      A₃.restartTime = ⊥ ∧ A₃.votedSlot = ((k + 1 : Nat) : Int) ∧
      A₃.pool = Function.update A.pool (k + 1) [cv (k + 1)] ∧
      A₃.voteStamp =
        Function.update A.voteStamp (cv (k + 1)) (ETime.of ((4 * (k + 1) : Nat) : Int)) ∧
      A₃.blockStamp = Function.update A.blockStamp (blk (k + 1)).root
        (ETime.of ((4 * (k + 1) : Nat) : Int)) ∧
      A₃.fgReported = A.fgReported ∧ LocksLe A₃.locks (k + 1) ∧
      (⟨(blk (k + 1)).root, k + 1, true, k + 1 + 2⟩ : Lock) ∈ A₃.locks := by
  have hs : sp1.slot (((4 * (k + 1) : Nat) : Int)) = k + 1 := by rw [slot_nat]; omega
  unfold acOnBlock
  rw [blockReceipt_blk hcv]
  rw [optimisticConfirmation_of_none (optimisticSelect_of_pool_nil (by rw [hs]; exact hpool))]
  obtain ⟨L₁, d, he, hL₁, htip₁⟩ := tryVote_blk
    (A := { A with blockStamp := Function.update A.blockStamp (blk (k + 1)).root
                    (ETime.of ((4 * (k + 1) : Nat) : Int)) }) h hj hvs hpool hL htip
  rw [he]
  exact ⟨_, _, rfl, rfl, rfl, hj, vote_admitted h hj hpool hL₁⟩

/-- `ac_to_fg` after the own block of slot `k + 1`: the source is the new tip. -/
theorem acToFG_tick {A : SAState sp1.n} {Φ : N1.Frm} {f k : Nat}
    (h : ChainFrame Φ f (jexp (k + 1)) (k + 1)) (hj : A.restartTime = ⊥)
    (htip : (⟨(blk (k + 1)).root, k + 1, true, k + 1 + 2⟩ : Lock) ∈ A.locks)
    (hrep : A.fgReported = (blk k).root) :
    (SA.acToFG sp1 A Φ ((4 * (k + 1) : Nat) : Int)).1 =
        { A with fgReported := (blk (k + 1)).root } ∧
      (SA.acToFG sp1 A Φ ((4 * (k + 1) : Nat) : Int)).2 = some (blk (k + 1)) := by
  have hs : sp1.slot (((4 * (k + 1) : Nat) : Int)) = k + 1 := by rw [slot_nat]; omega
  have hf : f ≤ k + 1 := le_trans h.fj (jexp_le _)
  have htip' := h.mem (le_trans h.fj (jexp_le _)) (le_refl (k + 1))
  have hd : deepest Φ (toFGCandidates sp1 A Φ ((4 * (k + 1) : Nat) : Int)) =
      some (blk (k + 1)) := by
    apply h.deepest_eq (fun B hB => hB.1.1)
    · exact ⟨h.mem_viableTree htip' (jexp_le _) le_rfl htip', _,
        h.mem_liveLocks htip hf le_rfl rfl (by rw [hs]; dsimp only; omega), rfl, rfl,
        by rw [hs]; dsimp only; omega⟩
    · intro B hB
      obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hB.1.1
      exact ⟨m, hm, rfl⟩
  have hn : ¬ AncR Φ (blk (k + 1)) A.fgReported := by
    rintro ⟨R, hR, hr, ha⟩
    rw [hrep] at hr
    obtain ⟨rfl, -, -⟩ := h.eq_of_root hR hr
    have := h.le_of_anc ha; omega
  unfold SA.acToFG
  rw [ite_neg (not_not.2 (joined_of_bot hj _))]
  dsimp only
  rw [hd]
  dsimp only
  rw [ite_neg hn]
  exact ⟨rfl, rfl⟩

/-- `ac_to_fg` returns nothing once the tip is reported. -/
theorem acToFG_none {A : SAState sp1.n} {Φ : N1.Frm} {f j τ : Nat} (h : ChainFrame Φ f j τ)
    (hrep : A.fgReported = (blk τ).root) (t : Time) :
    (SA.acToFG sp1 A Φ t).1 = A ∧ (SA.acToFG sp1 A Φ t).2 = none := by
  unfold SA.acToFG
  split_ifs
  all_goals try exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · rename_i C hC
      have hCt := (deepest_mem hC).1.1.1
      obtain ⟨m, -, hm, rfl⟩ := h.eq_of_mem hCt
      rw [ite_pos ⟨blk τ, h.mem (le_trans h.fj h.jτ) le_rfl, hrep.symm,
        h.anc (le_trans (h.mem_iff.1 hCt).1 le_rfl) hm le_rfl⟩]
      exact ⟨rfl, rfl⟩

/-! ## The ticks -/

/-- The latest slot whose block is accepted before the tick of time `t`. -/
def tip (t : Nat) : Nat := (t + 3) / 4 - 1

/-- The AC state before the tick of time `t`. -/
structure ACGood (A : SAState sp1.n) (t : Nat) : Prop where
  restart : A.restartTime = ⊥
  voted : A.votedSlot = if t ≤ 1 then -1 else ((tip t : Nat) : Int)
  pool : ∀ σ, A.pool σ = if 2 ≤ t ∧ σ ≤ tip t then [cv σ] else []
  vstamp : ∀ σ, 2 ≤ t → σ ≤ tip t → A.voteStamp (cv σ) < ⊤
  bstamp : ∀ m ≤ tip t, A.blockStamp (blk m).root < ⊤
  locks : LocksLe A.locks (tip t)
  tipLock : 1 ≤ tip t → (⟨(blk (tip t)).root, tip t, true, tip t + 2⟩ : Lock) ∈ A.locks
  reported : A.fgReported = (blk (tip t)).root

/-- The node state before the tick of time `t`. -/
structure Good (st : NodeState N1) (t : Nat) : Prop where
  fg : FGGood st.fg (tip t)
  atts : st.fg.atts = attList (tip t)
  record : RecGood st.record (tip t)
  ac : ACGood st.ac t

theorem good_init : Good (Node.init N1) 0 :=
  ⟨fgGood_init, rfl, recGood_empty,
    ⟨rfl, rfl, fun _ => by simp [Node.init, SAState.initial], fun _ h => by omega,
      fun m hm => by
        obtain rfl : m = 0 := by simp [tip] at hm; omega
        change (if (0 : Nat) = 0 then (⊥ : ETime) else ⊤) < ⊤
        simp,
      fun l hl => absurd hl (Set.notMem_empty _), fun h => by simp [tip] at h, rfl⟩⟩

theorem good_frame {st : NodeState N1} {t : Nat} (h : Good st t) :
    ∃ f, ChainFrame (Node.frame st) f (jexp (tip t)) (tip t) := fgGood_frame h.fg

theorem onTick_eq' (st : NodeState N1) (t : Time) (x : Nat) :
    Node.onTick (fun _ => v0) dg1 v0 st t x =
      ((tickStep (fun _ => v0) dg1 v0 (tickStep (fun _ => v0) dg1 v0
        (tickStep (fun _ => v0) dg1 v0 st t x .acTick).1 t x .proposal).1 t x
        .fgUpdate).1,
       (tickStep (fun _ => v0) dg1 v0 st t x .acTick).2 ++
        (tickStep (fun _ => v0) dg1 v0
          (tickStep (fun _ => v0) dg1 v0 st t x .acTick).1 t x .proposal).2 ++
        (tickStep (fun _ => v0) dg1 v0 (tickStep (fun _ => v0) dg1 v0
          (tickStep (fun _ => v0) dg1 v0 st t x .acTick).1 t x .proposal).1 t x
          .fgUpdate).2) := by
  simp [Node.onTick, runSteps, tickSteps]

theorem proposes_iff (n : Nat) :
    Node.Proposes (fun _ => v0) (v0 : Fin sp1.n) (n : Int) ↔ n % 4 = 0 ∧ 4 ≤ n := by
  unfold Node.Proposes
  rw [show sp1.toParams.slotOf (n : Int) = n / 4 from slotOf_nat n]
  change 0 < n / 4 ∧ (n : Int) = 4 * ((n / 4 : Nat) : Int) ∧ _ ↔ _
  constructor
  · rintro ⟨h1, h2, -⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega, Subsingleton.elim _ _⟩

theorem tickStep_proposal_no {st : NodeState N1} {n : Nat} (h : ¬ (n % 4 = 0 ∧ 4 ≤ n)) (x : Nat) :
    tickStep (fun _ => v0) dg1 v0 st (n : Int) x .proposal = (st, []) := by
  simp only [tickStep]
  rw [ite_neg (fun hp => h ((proposes_iff n).1 hp))]

theorem tickStep_fgUpdate_none {st : NodeState N1} {t : Nat} (hg : Good st t) (n : Nat) (x : Nat) :
    tickStep (fun _ => v0) dg1 v0 st (n : Int) x .fgUpdate =
      (st, [.ac ⟨.toFG, Node.frame st, []⟩]) := by
  obtain ⟨f, hf⟩ := good_frame hg
  obtain ⟨h1, h2⟩ := acToFG_none hf hg.ac.reported (n : Int)
  simp only [tickStep, Node.acToFG]
  split
  · rename_i heq
    change ({ st with ac := (SA.acToFG sp1 st.ac (Node.frame st) n).1 }, _) = _
    rw [h1]
  · rename_i C heq
    exact absurd (heq.symm.trans h2) (by simp)

/-- A tick with no AC call that changes anything but the locks. -/
theorem good_of_same {st st' : NodeState N1} {t : Nat} (h : Good st t) (hfg : st'.fg = st.fg)
    (hr : st'.record = st.record) (hs : Same st.ac st'.ac) (hL : LocksLe st'.ac.locks (tip t))
    (htip : 1 ≤ tip t → (⟨(blk (tip t)).root, tip t, true, tip t + 2⟩ : Lock) ∈ st'.ac.locks)
    (h1 : tip (t + 1) = tip t) (h2 : t ≤ 1 ↔ t + 1 ≤ 1) (h3 : 2 ≤ t ↔ 2 ≤ t + 1) :
    Good st' (t + 1) := by
  obtain ⟨hfg', hatts, hrec, hac⟩ := h
  refine ⟨hfg ▸ h1 ▸ hfg', by rw [hfg, hatts, h1], by rw [hr, h1]; exact hrec, ?_⟩
  refine ⟨hs.restartTime.trans hac.restart, ?_, fun σ => ?_, fun σ h2' hσ => ?_,
    fun m hm => ?_, h1 ▸ hL, h1 ▸ htip, ?_⟩
  · rw [hs.votedSlot, hac.voted, h1]; simp only [h2]
  · rw [hs.pool, hac.pool, h1]; simp only [h3]
  · rw [hs.voteStamp]; exact hac.vstamp σ (h3.2 h2') (h1 ▸ hσ)
  · rw [hs.blockStamp]; exact hac.bstamp m (h1 ▸ hm)
  · rw [hs.fgReported, hac.reported, h1]

theorem tickStep_fgUpdate_none' {st : NodeState N1} {f j τ : Nat}
    (hf : ChainFrame (Node.frame st) f j τ) (hrep : st.ac.fgReported = (blk τ).root) (n x : Nat) :
    tickStep (fun _ => v0) dg1 v0 st (n : Int) x .fgUpdate =
      (st, [.ac ⟨.toFG, Node.frame st, []⟩]) := by
  obtain ⟨h1, h2⟩ := acToFG_none hf hrep (n : Int)
  simp only [tickStep, Node.acToFG]
  split
  · change ({ st with ac := (SA.acToFG sp1 st.ac (Node.frame st) n).1 }, _) = _
    rw [h1]
  · rename_i C heq
    exact absurd (heq.symm.trans h2) (by simp)

theorem tickStep_acTick (st : NodeState N1) (t : Time) (x : Nat) :
    tickStep (fun _ => v0) dg1 v0 st t x .acTick =
      ({ st with ac := (acOnTick sp1 v0 st.ac (Node.frame st) t).1 },
      [.ac ⟨.tick, Node.frame st, (acOnTick sp1 v0 st.ac (Node.frame st) t).2⟩]) := rfl

theorem tip_of_mod1 {n : Nat} (h : n % 4 = 1) : tip n = n / 4 := by unfold tip; omega

/-- A tick with nothing to do. -/
theorem tick_noop {st : NodeState N1} {n : Nat} (hg : Good st n) (h1 : n ≠ 1)
    (hA : ¬ (n % 4 = 0 ∧ 4 ≤ n)) (hC : ¬ (n % 4 = 2 ∧ 4 ≤ n)) :
    Node.onTick (fun _ => v0) dg1 v0 st (n : Int) 0 =
      (st, [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩]) ∧ Good st (n + 1) := by
  obtain ⟨f, hf⟩ := good_frame hg
  have hstep : acOnTick sp1 v0 st.ac (Node.frame st) n = (st.ac, []) := by
    rw [acOnTick_eq _ _ _ hg.ac.restart, ite_neg hC]
    split_ifs with h4
    · refine tryVote_voted ?_
      rw [hg.ac.voted, ite_neg (by omega), slot_nat, tip_of_mod1 h4]
    · rfl
  rw [onTick_eq', tickStep_acTick, hstep]
  dsimp only
  rw [show ({ fg := st.fg, ac := st.ac, record := st.record } : NodeState N1) = st from rfl,
    tickStep_proposal_no hA, tickStep_fgUpdate_none' hf hg.ac.reported]
  refine ⟨rfl, good_of_same hg rfl rfl (Same.refl _) hg.ac.locks hg.ac.tipLock ?_ ?_ ?_⟩ <;>
    (try simp only [tip]) <;> omega

/-- The tick of `t_s + 2Δ`: the confirmation update of slot `s − 1`. -/
theorem tick_C {st : NodeState N1} {n : Nat} (hg : Good st n) (hC : n % 4 = 2 ∧ 4 ≤ n) :
    ∃ A', Node.onTick (fun _ => v0) dg1 v0 st (n : Int) 0 =
      ({ st with ac := A' }, [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.toFG, Node.frame st, []⟩]) ∧
      Good { st with ac := A' } (n + 1) := by
  obtain ⟨f, hf⟩ := good_frame hg
  have hA : ¬ (n % 4 = 0 ∧ 4 ≤ n) := by omega
  set A' := updateConfirmation sp1 st.ac (Node.frame st) n (n / 4 - 1)
  have hstep : acOnTick sp1 v0 st.ac (Node.frame st) n = (A', []) := by
    rw [acOnTick_eq _ _ _ hg.ac.restart, ite_pos hC]
  obtain ⟨hsame, hlocks⟩ := updateConfirmation_cases st.ac (Node.frame st) n (n / 4 - 1)
  have hL : LocksLe A'.locks (tip n) := by
    rcases hlocks with h | ⟨N, hN, h⟩
    · rw [h]; exact hg.ac.locks
    · rw [h]; exact addLocks_le hf hg.ac.locks le_rfl _ _ hN
  have htip : 1 ≤ tip n → (⟨(blk (tip n)).root, tip n, true, tip n + 2⟩ : Lock) ∈ A'.locks := by
    intro h1
    rcases hlocks with h | ⟨N, hN, h⟩
    · rw [h]; exact hg.ac.tipLock h1
    · rw [h]
      exact hf.mem_liveLocks (Or.inl (hg.ac.tipLock h1))
        (le_trans hf.fj (jexp_le _)) le_rfl rfl
        (by rw [slot_nat]; dsimp only; simp only [tip]; omega)
  rw [onTick_eq', tickStep_acTick, hstep]
  dsimp only
  rw [tickStep_proposal_no hA, tickStep_fgUpdate_none' (st := { st with ac := A' }) hf
    (hsame.fgReported.trans hg.ac.reported)]
  refine ⟨A', rfl, good_of_same hg rfl rfl hsame hL htip ?_ ?_ ?_⟩ <;>
    (try simp only [tip]) <;> omega

/-- The tick of time `1`: the vote of slot `0`. -/
theorem tick_B0 {st : NodeState N1} (hg : Good st 1) :
    ∃ A' e, Node.onTick (fun _ => v0) dg1 v0 st ((1 : Nat) : Int) 0 =
      ({ st with ac := A' }, [.ac ⟨.tick, Node.frame st, [e]⟩, .ac ⟨.toFG, Node.frame st, []⟩]) ∧
      e.msg = cv 0 ∧ e.readPoint.pool = st.ac.pool ∧ Good { st with ac := A' } 2 := by
  obtain ⟨f, hf⟩ := good_frame hg
  have htip : tip 1 = 0 := rfl
  rw [htip] at hf
  have hf0 : f = 0 := by have := hf.fj; simp [jexp] at this; omega
  subst hf0
  have hpool : st.ac.pool 0 = [] := by rw [hg.ac.pool]; simp
  obtain ⟨d, hv⟩ := tryVote_zero hf hg.ac.restart (by rw [hg.ac.voted]; rfl)
    (by have := hg.ac.locks; rwa [htip] at this)
  set A' := admitVote sp1 { st.ac with votedSlot := 0 } ((1 : Nat) : Int) (cv 0)
  have hstep : acOnTick sp1 v0 st.ac (Node.frame st) ((1 : Nat) : Int) =
      (A', [⟨cv 0, { st.ac with votedSlot := 0 }, some d⟩]) := by
    rw [acOnTick_eq _ _ _ hg.ac.restart, ite_neg (by omega), ite_pos rfl]; exact hv
  have hA' : A' =
      { st.ac with votedSlot := 0,
                   pool := Function.update st.ac.pool 0 [cv 0],
                   voteStamp :=
                     Function.update st.ac.voteStamp (cv 0) (ETime.of ((1 : Nat) : Int)) } :=
    admitVote_cv (slot_nat 1) hpool
  rw [onTick_eq', tickStep_acTick, hstep]
  dsimp only
  rw [tickStep_proposal_no (by omega), tickStep_fgUpdate_none' (st := { st with ac := A' })
    (f := 0) (j := jexp 0) (τ := 0) hf (by rw [hA']; exact hg.ac.reported)]
  refine ⟨A', _, rfl, rfl, rfl, ?_⟩
  obtain ⟨hfg, hatts, hrec, hac⟩ := hg
  have htip2 : tip 2 = 0 := rfl
  refine ⟨htip2 ▸ hfg, by rw [htip2]; exact hatts, by rw [htip2]; exact hrec, ?_⟩
  rw [hA']
  refine ⟨hac.restart, by rw [htip2]; rfl, fun σ => ?_, fun σ _ hσ => ?_, fun m hm => ?_,
    hac.locks, hac.tipLock, hac.reported⟩
  · rw [htip2]
    by_cases h0 : σ = 0
    · subst h0; simp
    · dsimp only
      rw [Function.update_of_ne h0, hac.pool, htip]; simp [h0]
  · rw [htip2] at hσ
    obtain rfl : σ = 0 := by omega
    dsimp only
    rw [Function.update_self]
    exact etime_of_lt_top _
  · exact hac.bstamp m hm

theorem mkBlock_tick {fg : Store sp1.toParams N1.Payload} {k : Nat} (h : FGGood fg k)
    (ha : fg.atts = attList k) :
    Node.mkBlock dg1 v0 fg ((4 * (k + 1) : Nat) : Int) 0 (blk k) ([cv k], [cv k]) =
      blk (k + 1) := by
  have hs : sp1.toParams.slotOf (((4 * (k + 1) : Nat) : Int)) = k + 1 := by
    rw [slotOf_nat]; omega
  unfold Node.mkBlock
  rw [proposalAttestations_blk h ha, hs, blk_fgPayload]
  rfl

theorem tip_A (k : Nat) : tip (4 * (k + 1)) = k := by unfold tip; omega

theorem tip_A1 (k : Nat) : tip (4 * (k + 1) + 1) = k + 1 := by unfold tip; omega

/-- **The tick of `t_{k+1}`**: the proposal of slot `k + 1` on the tip `k`, its acceptance, the
vote of slot `k + 1` with its fast lock, and the attestation of slot `k + 1`. -/
theorem tick_A {st : NodeState N1} {k : Nat} (hg : Good st (4 * (k + 1))) :
    ∃ fg' e st', st.fg.onBlock (blk (k + 1)) = some fg' ∧ FGGood fg' (k + 1) ∧
      Node.onTick (fun _ => v0) dg1 v0 st ((4 * (k + 1) : Nat) : Int) 0 =
        (st', [.ac ⟨.tick, Node.frame st, []⟩, .ac ⟨.proposal, Node.frame st, []⟩,
          .fg (.block (blk (k + 1)) true), .ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩,
          .ac ⟨.toFG, fg'.toFrame, []⟩, .fg (.attest (blk (k + 1)) (some (att (k + 1)))),
          .fg (.attestation (att (k + 1)))]) ∧
      e.msg = cv (k + 1) ∧ e.readPoint.pool = st.ac.pool ∧ Good st' (4 * (k + 1) + 1) := by
  obtain ⟨hfg, hatts, hrec, hac⟩ := hg
  rw [tip_A] at hfg hatts hrec
  set t : Nat := 4 * (k + 1) with ht
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  have hpoolk : st.ac.pool k = [cv k] := by rw [hac.pool, tip_A, ite_pos ⟨by omega, le_rfl⟩]
  have hpool1 : st.ac.pool (k + 1) = [] := by rw [hac.pool, tip_A, ite_neg (by omega)]
  -- `ac_on_tick` does nothing
  have hstep : acOnTick sp1 v0 st.ac (Node.frame st) (t : Int) = (st.ac, []) := by
    rw [acOnTick_eq _ _ _ hac.restart, ite_neg (by omega), ite_neg (by omega)]
  -- `ac_proposal`
  obtain ⟨L₁, d, hprop, hd, hL₁, htip₁⟩ := acProposal_tick hf hac.restart hpoolk
    (hac.vstamp k (by omega) (by rw [tip_A])) (hac.bstamp k (by rw [tip_A]))
    (by have := hac.locks; rwa [tip_A] at this)
    (fun h1 => by have := hac.tipLock (by rw [tip_A]; exact h1); rwa [tip_A] at this)
  -- the block
  obtain ⟨fg', hob, hfg', hatts'⟩ := fgGood_onBlock hfg
    (fun a ha => hatts ▸ payload_mem_attList k a ha)
  obtain ⟨f', hf'⟩ := fgGood_frame hfg'
  obtain ⟨A₃, e, hblk, he, hrp, -, h3r, h3v, h3p, h3vs, h3bs, h3rep, h3L, h3tip⟩ :=
    acOnBlock_tick (A := { st.ac with locks := L₁ }) hf' hac.restart
      (by rw [hac.voted, ite_neg (by omega), tip_A]) hpool1
      (by rw [hpoolk]; exact List.mem_singleton_self _)
      hL₁ htip₁
  -- `ac_to_fg`
  obtain ⟨hto1, hto2⟩ := acToFG_tick hf' h3r h3tip
    (h3rep.trans (by rw [hac.reported, tip_A]))
  -- the attestation
  obtain ⟨Λ', hatt, hrec'⟩ := attest_blk (s := k + 1) (by omega) hfg'
    (by rw [Nat.add_sub_cancel]; exact hrec)
  have honA := onAttestation_att (fg := fg') (s := k + 1) (by omega)
    (by rw [hatts', hatts, Nat.add_sub_cancel])
  have hmk := mkBlock_tick hfg hatts
  have hslot : ¬ sp1.toParams.slotOf ((t : Nat) : Int) < (blk (k + 1)).slot := by
    rw [slotOf_nat, blk_slot]; omega
  have hP : Node.Proposes (fun _ => v0) (v0 : Fin sp1.n) ((t : Nat) : Int) :=
    (proposes_iff t).2 ⟨by omega, by omega⟩
  have s2 : tickStep (fun _ => v0) dg1 v0 st (t : Int) 0 .proposal = (⟨fg', A₃, st.record⟩,
      [.ac ⟨.proposal, Node.frame st, []⟩, .fg (.block (blk (k + 1)) true),
        .ac ⟨.block (blk (k + 1)), fg'.toFrame, [e]⟩]) := by
    simp only [tickStep, ite_pos hP, Node.acProposal, Node.frame]
    rw [hprop]
    dsimp only
    rw [hd]
    simp only [Node.proposeBlock]
    rw [hmk]
    simp only [Node.onBlock, ite_neg hslot]
    rw [hob]
    dsimp only
    simp only [Node.acCall, Node.frame]
    dsimp only at hblk
    dsimp only [ACInterface.step]
    rw [hblk]
  have s3 : tickStep (fun _ => v0) dg1 v0 ⟨fg', A₃, st.record⟩ (t : Int) 0 .fgUpdate =
      (⟨fg'.onAttestation (att (k + 1)), { A₃ with fgReported := (blk (k + 1)).root }, Λ'⟩,
        [.ac ⟨.toFG, fg'.toFrame, []⟩, .fg (.attest (blk (k + 1)) (some (att (k + 1)))),
          .fg (.attestation (att (k + 1)))]) := by
    simp only [tickStep, Node.acToFG, Node.frame]
    rw [hto2]
    dsimp only
    simp only [Node.attest]
    rw [hto1]
    dsimp only
    rw [hatt]
    rfl
  refine ⟨fg', e,
    ⟨fg'.onAttestation (att (k + 1)), { A₃ with fgReported := (blk (k + 1)).root }, Λ'⟩,
    hob, hfg', ?_, he, hrp, ?_⟩
  · rw [onTick_eq', tickStep_acTick, hstep]
    dsimp only
    rw [show ({ fg := st.fg, ac := st.ac, record := st.record } : NodeState N1) = st from rfl,
      s2, s3]
    rfl
  · have ht1 : tip (t + 1) = k + 1 := tip_A1 k
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [honA, ht1]; exact ⟨hfg'.blocks, hfg'.sigma, hfg'.J, hfg'.hj, hfg'.hmax, hfg'.F⟩
    · rw [honA, ht1]
    · rw [ht1]; exact hrec'
    · refine ⟨h3r, ?_, fun σ => ?_, fun σ _ hσ => ?_, fun m hm => ?_, ?_, fun _ => ?_, ?_⟩
      · rw [h3v, ht1, ite_neg (by omega)]
      · rw [ht1]
        change A₃.pool σ = _
        rw [h3p]
        by_cases hσ : σ = k + 1
        · subst hσ; rw [Function.update_self, ite_pos ⟨by omega, le_rfl⟩]
        · rw [Function.update_of_ne hσ]
          change st.ac.pool σ = _
          rw [hac.pool, tip_A]
          by_cases hσk : σ ≤ k
          · rw [ite_pos ⟨by omega, hσk⟩, ite_pos ⟨by omega, by omega⟩]
          · rw [ite_neg (by omega), ite_neg (by omega)]
      · change A₃.voteStamp (cv σ) < ⊤
        rw [h3vs, ht1] at *
        by_cases hσ' : σ = k + 1
        · subst hσ'; rw [Function.update_self]; exact etime_of_lt_top _
        · rw [Function.update_of_ne (fun he => hσ' (congrArg Vote.slot he))]
          exact hac.vstamp σ (by omega) (by rw [tip_A]; omega)
      · change A₃.blockStamp (blk m).root < ⊤
        rw [h3bs]
        rw [ht1] at hm
        by_cases hm' : m = k + 1
        · subst hm'; rw [Function.update_self]; exact etime_of_lt_top _
        · rw [Function.update_of_ne (fun he => hm' (blk_root_inj he))]
          exact hac.bstamp m (by rw [tip_A]; omega)
      · rw [ht1]; exact h3L
      · rw [ht1]; exact h3tip
      · rw [ht1]

end Consensus.Goldilocks.Witness.One

end

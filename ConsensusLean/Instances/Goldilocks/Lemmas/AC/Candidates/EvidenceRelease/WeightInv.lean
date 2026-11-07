module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Interface

public section

/-! # Evidence-release: stored weights stay antitone along the chain

The run invariant behind the idempotence of a release stage followed by another backward stage
(`Candidates/LateCertificate`): at every reachable state of the evidence-release SA, every stored
weight is antitone along the chains of the frame of the last call, and of every later frame.

A weight is fixed at its write: `weightBelow Φ₀ o f`, a count `f` of the frame `Φ₀` of the write,
read on the chain of the written block. The counts are antitone along the chains of `Φ₀`
(`confirmationScore_antitone`, `optimisticVoters_antitone`, and for a slow lock a maximum of saved
counts, each a count of an earlier frame). The call law (`ACInterface.CallOK`) moves the frame only
by a frame step, which keeps the finalized tip moving forward inside the coherent set `U` of the
run's blocks. So the invariant (`WeightInv`) records, for each stored weight and each saved count,
a frame of `U` whose finalized tip is at or below the current one:

* `weightBelow_antitone`: such a weight is antitone along the chains of the current frame (a block
  between the current tip and a block of the write frame is a block of the write frame,
  `mem_tree_of_between`; ancestry in `U` between blocks of a frame is ancestry in the frame);
* every handler keeps the invariant at its call's frame (`weightInv_tryVoteW`, …,
  `weightInv_acRestartW`), and moving to a later frame keeps it (`WeightInv.later`);
* `weightInv_of_reachable`: it holds at every reachable state; `weightAntitone_of_reachable`: so
  every stored weight is antitone in the frame of the last call and in every later frame. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-! ### Frames inside a coherent set -/

private theorem lookup_self {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {B : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) : lookup Φ B.root = some B := by
  cases h : lookup Φ B.root with
  | none => exact absurd ⟨B, hB, rfl⟩ (lookup_eq_none h)
  | some B' =>
    obtain ⟨hB', hr⟩ := lookup_eq_some h
    exact congrArg some (hΦ.coherent.1 hB' hB hr)

private theorem lookup_of_not_mem {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦU : Φ.tree ⊆ U) {D : Blk sp.n FGP} (hDU : D ∈ U) (hD : D ∉ Φ.tree) :
    lookup Φ D.root = none := by
  cases h : lookup Φ D.root with
  | none => rfl
  | some D₀ =>
    obtain ⟨hD₀, hr⟩ := lookup_eq_some h
    exact absurd (hU.1 (hΦU hD₀) hDU hr ▸ hD₀) hD

/-- A block of `U` between a frame's finalized tip and a block of the frame is in the frame. -/
theorem mem_tree_of_between {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {Y D : Blk sp.n FGP} (hD : D ∈ Φ.tree)
    (hFY : Anc U Φ.F Y) (hYD : Anc U Y D) : Y ∈ Φ.tree := by
  have key : ∀ D, Anc Φ.tree Φ.F D → ∀ Y, Anc U Φ.F Y → Anc U Y D → Y ∈ Φ.tree := by
    intro D h
    induction h with
    | refl =>
      intro Y hFY hYF
      rw [Anc.antisymm hU hYF hFY]
      exact hΦ.rooted.1
    | @tail c d _ e ih =>
      intro Y hFY hYd
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hYd with h | ⟨p, hYp, ep⟩
      · exact h ▸ e.2.1
      · have hpc : p = c :=
          hU.1 ep.1 (hΦU e.1) (Option.some.inj (ep.2.2.symm.trans e.2.2))
        subst hpc
        exact ih Y hFY hYp
  exact key D (hΦ.rooted.2 D hD) Y hFY hYD

variable (sp) in
/-- `f` is antitone along the chains of the frame's tree. -/
def TreeAntitone (Φ : Frm sp.n FGP) (f : Blk sp.n FGP → Nat) : Prop :=
  ∀ Y ∈ Φ.tree, ∀ D ∈ Φ.tree, Φ.Anc Y D → f D ≤ f Y

theorem treeAntitone_iff (Φ : Frm sp.n FGP) (f : Blk sp.n FGP → Nat) :
    TreeAntitone sp Φ f ↔ ∀ Y ∈ Φ.tree, ∀ D ∈ Φ.tree, Φ.Anc Y D → f D ≤ f Y :=
  Iff.rfl

/-- **A weight written in an earlier frame is antitone in the current one.** -/
theorem weightBelow_antitone {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ₀ Φ : Frm sp.n FGP}
    (hΦ₀ : FrameOK Φ₀) (hΦ₀U : Φ₀.tree ⊆ U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (hF : Anc U Φ₀.F Φ.F) {o : Nat} {f : Blk sp.n FGP → Nat} (hf : TreeAntitone sp Φ₀ f) :
    TreeAntitone sp Φ fun Y => weightBelow sp Φ₀ o f Y.root := by
  intro Y hY D hD hYD
  change weightBelow sp Φ₀ o f D.root ≤ weightBelow sp Φ₀ o f Y.root
  by_cases hDo : D ∈ Φ₀.tree ∧ AncR Φ₀ D o
  · obtain ⟨hD₀, R, hR, hRr, hDR⟩ := hDo
    have hY₀ := mem_tree_of_between hU hΦ₀ hΦ₀U hD₀ (hF.trans ((hΦ.rooted.2 Y hY).mono hΦU))
      (hYD.mono hΦU)
    have hYD₀ := anc_tree_of_anc_U hU hΦ₀ hΦ₀U hY₀ (hYD.mono hΦU) hD₀
    rw [weightBelow_of_anc hΦ₀ f hD₀ ⟨R, hR, hRr, hDR⟩,
      weightBelow_of_anc hΦ₀ f hY₀ ⟨R, hR, hRr, hYD₀.trans hDR⟩]
    exact hf Y hY₀ D hD₀ hYD₀
  · have h0 : weightBelow sp Φ₀ o f D.root = 0 := by
      by_cases hD₀ : D ∈ Φ₀.tree
      · exact weightBelow_of_not_anc hΦ₀ f hD₀ fun h => hDo ⟨hD₀, h⟩
      · simp only [weightBelow, lookup_of_not_mem hU hΦ₀U (hΦU hD) hD₀]
    rw [h0]
    exact Nat.zero_le _

/-- A saved count of an earlier frame is antitone in the current one. -/
theorem updateCount_antitone {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φᵢ Φ : Frm sp.n FGP}
    (hΦᵢ : FrameOK Φᵢ) (hΦᵢU : Φᵢ.tree ⊆ U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (hF : Anc U Φᵢ.F Φ.F) (A : SAState sp.n) (s : Nat) :
    TreeAntitone sp Φ fun Y => updateCount sp A Φᵢ s Y.root := by
  intro Y hY D hD hYD
  by_cases hD₀ : D ∈ Φᵢ.tree
  · have hY₀ := mem_tree_of_between hU hΦᵢ hΦᵢU hD₀ (hF.trans ((hΦ.rooted.2 Y hY).mono hΦU))
      (hYD.mono hΦU)
    have hYD₀ := anc_tree_of_anc_U hU hΦᵢ hΦᵢU hY₀ (hYD.mono hΦU) hD₀
    simp only [updateCount, lookup_self hΦᵢ hD₀, lookup_self hΦᵢ hY₀, Option.map_some,
      Option.getD_some]
    exact confirmationScore_antitone A s hYD₀
  · simp only [updateCount, lookup_of_not_mem hU hΦᵢU (hΦU hD) hD₀, Option.map_none,
      Option.getD_none]
    exact Nat.zero_le _

/-! ### The invariant -/

variable (sp) in
/-- A weight written in a frame of `U` whose finalized tip is at or below `Φ.F`, from a count
antitone along that frame's chains. -/
def WrittenBefore (U : Set (Blk sp.n FGP)) (Φ : Frm sp.n FGP) (g : Nat → Nat) : Prop :=
  ∃ Φ₀ : Frm sp.n FGP, FrameOK Φ₀ ∧ Φ₀.tree ⊆ U ∧ Anc U Φ₀.F Φ.F ∧
    ∃ o f, TreeAntitone sp Φ₀ f ∧ g = weightBelow sp Φ₀ o f

variable (sp) in
/-- A saved count: none, or the count of an update in a frame of `U` whose finalized tip is at or
below `Φ.F`. -/
def SavedBefore (U : Set (Blk sp.n FGP)) (Φ : Frm sp.n FGP) (g : Nat → Nat) : Prop :=
  g = (fun _ => 0) ∨ ∃ Φᵢ : Frm sp.n FGP, FrameOK Φᵢ ∧ Φᵢ.tree ⊆ U ∧ Anc U Φᵢ.F Φ.F ∧
    ∃ (A : SAState sp.n) (s : Nat), g = updateCount sp A Φᵢ s

variable (sp) in
/-- **The weight invariant** at `Φ`: every stored weight and every saved count is of a frame no
later than `Φ`. -/
def WeightInv (U : Set (Blk sp.n FGP)) (Φ : Frm sp.n FGP) (X : WState sp.n) : Prop :=
  (∀ w ∈ X.wlocks, WrittenBefore sp U Φ w.weight) ∧ ∀ i, SavedBefore sp U Φ (X.counts i)

theorem WrittenBefore.later {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {g : Nat → Nat}
    (h : WrittenBefore sp U Φ g) (hF : Anc U Φ.F Φ'.F) : WrittenBefore sp U Φ' g := by
  obtain ⟨Φ₀, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨Φ₀, h₁, h₂, h₃.trans hF, h₄⟩

theorem SavedBefore.later {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {g : Nat → Nat}
    (h : SavedBefore sp U Φ g) (hF : Anc U Φ.F Φ'.F) : SavedBefore sp U Φ' g := by
  rcases h with h | ⟨Φᵢ, h₁, h₂, h₃, h₄⟩
  · exact Or.inl h
  · exact Or.inr ⟨Φᵢ, h₁, h₂, h₃.trans hF, h₄⟩

/-- Moving to a later frame keeps the invariant. -/
theorem WeightInv.later {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {X : WState sp.n}
    (h : WeightInv sp U Φ X) (hF : Anc U Φ.F Φ'.F) : WeightInv sp U Φ' X :=
  ⟨fun w hw => (h.1 w hw).later hF, fun i => (h.2 i).later hF⟩

/-- A saved count is antitone along the chains of a frame no earlier than its own. -/
theorem SavedBefore.antitone {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {g : Nat → Nat} (h : SavedBefore sp U Φ g) :
    TreeAntitone sp Φ fun Y => g Y.root := by
  rcases h with rfl | ⟨Φᵢ, h₁, h₂, h₃, A, s, rfl⟩
  · exact fun _ _ _ _ _ => le_rfl
  · exact updateCount_antitone hU h₁ h₂ hΦ hΦU h₃ A s

/-- A written weight is antitone along the chains of a frame no earlier than its write. -/
theorem WrittenBefore.antitone {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {w : WLock} (h : WrittenBefore sp U Φ w.weight) :
    TreeAntitone sp Φ fun Y => w.weight Y.root := by
  obtain ⟨Φ₀, h₁, h₂, h₃, o, f, hf, hw⟩ := h
  have := weightBelow_antitone hU h₁ h₂ hΦ hΦU h₃ (o := o) hf
  intro Y hY D hD hYD
  change w.weight D.root ≤ w.weight Y.root
  rw [hw]
  exact this Y hY D hD hYD

/-! ### The writes and the moves -/

theorem writtenBefore_now {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {o : Nat} {f : Blk sp.n FGP → Nat} (hf : TreeAntitone sp Φ f) :
    WrittenBefore sp U Φ (weightBelow sp Φ o f) :=
  ⟨Φ, hΦ, hΦU, .refl, o, f, hf, rfl⟩

theorem writtenBefore_fastWeight {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (s o : Nat) :
    WrittenBefore sp U Φ (fastWeight sp A Φ s o) :=
  writtenBefore_now hΦ hΦU fun _ _ _ _ hYD => confirmationScore_antitone A s hYD

theorem writtenBefore_optimisticWeight {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (s o : Nat) :
    WrittenBefore sp U Φ (optimisticWeight sp A Φ s o) :=
  writtenBefore_now hΦ hΦU fun _ _ _ _ hYD =>
    Set.ncard_le_ncard (optimisticVoters_antitone A s hYD) (Set.toFinite _)

theorem writtenBefore_slowWeight {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {C : Int → Nat → Nat}
    (hC : ∀ i, SavedBefore sp U Φ (C i)) (s o : Nat) :
    WrittenBefore sp U Φ (slowWeight sp Φ C s o) :=
  writtenBefore_now hΦ hΦU fun Y hY D hD hYD =>
    Finset.sup_mono_fun fun _ _ => (hC _).antitone hU hΦ hΦU Y hY D hD hYD

theorem savedBefore_saveCount {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {C : Int → Nat → Nat} (hC : ∀ i, SavedBefore sp U Φ (C i))
    (A : SAState sp.n) (s : Nat) : ∀ i, SavedBefore sp U Φ (saveCount sp C A Φ s i) := by
  intro i
  by_cases hi : i = (s : Int)
  · subst hi
    rw [saveCount, Function.update_self]
    exact Or.inr ⟨Φ, hΦ, hΦU, .refl, A, s, rfl⟩
  · rw [saveCount, Function.update_of_ne hi]
    exact hC i

theorem written_liveLocks {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP} {W : Set WLock}
    (hW : ∀ w ∈ W, WrittenBefore sp U Φ w.weight) (Φ' : Frm sp.n FGP) (t : Time) :
    ∀ w ∈ wlockStore.liveLocks sp W Φ' t, WrittenBefore sp U Φ w.weight := by
  rintro _ ⟨w, hw, -, -, -, -, rfl⟩
  exact hW w hw

theorem written_addLocksWith {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP} {W N : Set WLock}
    (hW : ∀ w ∈ W, WrittenBefore sp U Φ w.weight) (hN : ∀ w ∈ N, WrittenBefore sp U Φ w.weight)
    (Φ' : Frm sp.n FGP) (t : Time) :
    ∀ w ∈ wlockStore.addLocksWith sp W N Φ' t, WrittenBefore sp U Φ w.weight := by
  rw [LockStore.addLocksWith_eq]
  exact written_liveLocks (fun w hw => hw.elim (hW w) (hN w)) Φ' t

theorem written_unlockW {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP} {W : Set WLock}
    (hW : ∀ w ∈ W, WrittenBefore sp U Φ w.weight) {Φ' : Frm sp.n FGP} (hΦ' : FrameOK Φ')
    (t : Time) (s : Int) (V : View sp.n) :
    ∀ w ∈ unlockW sp W Φ' t s V, WrittenBefore sp U Φ w.weight := by
  intro w' hw'
  rw [unlockW_eq_unlockWith] at hw'
  obtain ⟨w, hw, ⟨r, rfl⟩, -⟩ :=
    LockStore.unlockWith_backward wlockStore_lawful (evidenceStage_lawful sp) () hΦ' W t s V w' hw'
  exact hW w hw

/-! ### The handlers -/

variable {U : Set (Blk sp.n FGP)}

theorem weightInv_ac {Φ : Frm sp.n FGP} {X : WState sp.n} (h : WeightInv sp U Φ X)
    (A : SAState sp.n) : WeightInv sp U Φ { X with ac := A } :=
  h

theorem weightInv_withLocks {Φ : Frm sp.n FGP} {X : WState sp.n} (h : WeightInv sp U Φ X)
    (A : SAState sp.n) {W : Set WLock} (hW : ∀ w ∈ W, WrittenBefore sp U Φ w.weight) :
    WeightInv sp U Φ (withLocks sp X A W) :=
  ⟨hW, h.2⟩

theorem weightInv_unlockState {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {X : WState sp.n}
    (h : WeightInv sp U Φ X) (t : Time) (s : Int) (V : View sp.n) :
    WeightInv sp U Φ (unlockState sp X Φ t s V) :=
  weightInv_withLocks h _ (written_unlockW h.1 hΦ t s V)

theorem weightInv_optimisticConfirmationW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (h : WeightInv sp U Φ X) (t : Time) :
    WeightInv sp U Φ (optimisticConfirmationW sp X Φ t) := by
  refine weightInv_withLocks h _ ?_
  unfold optimisticLocksW
  split
  · exact h.1
  · refine written_addLocksWith h.1 ?_ Φ t
    rintro w rfl
    rw [optimisticWrite_weight]
    exact writtenBefore_optimisticWeight hΦ hΦU _ _ _

theorem weightInv_updateConfirmationW (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (h : WeightInv sp U Φ X) (t : Time) (s : Nat) :
    WeightInv sp U Φ (updateConfirmationW sp X Φ t s) := by
  refine ⟨?_, savedBefore_saveCount hΦ hΦU h.2 X.ac s⟩
  change ∀ w ∈ updateLocksW sp X.wlocks X.ac X.counts Φ t s, WrittenBefore sp U Φ w.weight
  unfold updateLocksW
  split
  · exact h.1
  · refine written_addLocksWith h.1 ?_ Φ t
    rintro w ⟨p, -, rfl⟩
    dsimp only
    split
    · exact writtenBefore_fastWeight hΦ hΦU _ _ _
    · exact writtenBefore_slowWeight hU hΦ hΦU (savedBefore_saveCount hΦ hΦU h.2 X.ac s) _ _

theorem weightInv_tryVoteW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {X : WState sp.n} (h : WeightInv sp U Φ X) (self : Fin sp.n) (t : Time) :
    WeightInv sp U Φ (tryVoteW sp self X Φ t).1 := by
  unfold tryVoteW
  dsimp only
  split_ifs
  · exact h
  · exact h
  · refine weightInv_optimisticConfirmationW hΦ hΦU ?_ t
    exact weightInv_ac (weightInv_ac (weightInv_unlockState hΦ h t _ _) _) _
  · refine weightInv_optimisticConfirmationW hΦ hΦU ?_ t
    exact weightInv_ac (weightInv_ac h _) _

theorem weightInv_acOnMessageW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {X : WState sp.n} (h : WeightInv sp U Φ X) (self : Fin sp.n) (t : Time) (v : Vote sp.n) :
    WeightInv sp U Φ (acOnMessageW sp self X Φ t v).1 :=
  weightInv_tryVoteW hΦ hΦU (weightInv_optimisticConfirmationW hΦ hΦU (weightInv_ac h _) t) self t

theorem weightInv_acOnBlockW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {X : WState sp.n} (h : WeightInv sp U Φ X) (self : Fin sp.n) (t : Time) (B : Blk sp.n FGP) :
    WeightInv sp U Φ (acOnBlockW sp self X Φ t B).1 :=
  weightInv_tryVoteW hΦ hΦU (weightInv_optimisticConfirmationW hΦ hΦU (weightInv_ac h _) t) self t

theorem weightInv_acOnTickW (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (h : WeightInv sp U Φ X) (self : Fin sp.n) (t : Time) :
    WeightInv sp U Φ (acOnTickW sp self X Φ t).1 := by
  have hv := weightInv_tryVoteW hΦ hΦU h self t
  unfold acOnTickW
  dsimp only
  split_ifs
  · exact weightInv_updateConfirmationW hU hΦ hΦU hv t _
  · exact weightInv_updateConfirmationW hU hΦ hΦU h t _
  · exact hv
  · exact h
  · exact h

theorem weightInv_acProposalW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {X : WState sp.n}
    (h : WeightInv sp U Φ X) (t : Time) : WeightInv sp U Φ (acProposalW sp X Φ t).1 := by
  unfold acProposalW
  dsimp only
  split_ifs
  · exact weightInv_unlockState hΦ h t _ _
  · exact h

theorem weightInv_acToFGW {Φ : Frm sp.n FGP} {X : WState sp.n} (h : WeightInv sp U Φ X)
    (t : Time) : WeightInv sp U Φ (acToFGW sp X Φ t).1 :=
  h

theorem weightInv_acRestartW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {X : WState sp.n} (h : WeightInv sp U Φ X) (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (t : Time) : WeightInv sp U Φ (acRestartW sp ro self X Φ t).1 := by
  unfold acRestartW
  dsimp only
  have key : ∀ (l : List (Blk sp.n FGP)) (acc : WState sp.n × List (EmW sp FGP)),
      WeightInv sp U Φ acc.1 →
      WeightInv sp U Φ (l.foldl (fun acc B => let r := acOnBlockW sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons B l ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      exact ih _ (weightInv_acOnBlockW hΦ hΦU hacc self t B)
  exact key _ _ ⟨h.1, fun _ => Or.inl rfl⟩

/-! ### Reachable states -/

/-- The finalized tip of a call's frame is at or above the previous call's, inside `U`. -/
theorem callOK_F_anc {ro : ReplayOrder sp FGP} {Φ Φ' : Frm sp.n FGP} {t : Time}
    {c : (evidenceReleaseSA sp FGP ro).Call} (hΦU : Φ.tree ⊆ U)
    (h : (evidenceReleaseSA sp FGP ro).CallOK U Φ t c Φ') : Anc U Φ.F Φ'.F := by
  obtain ⟨⟨-, hΦ'U⟩, hc⟩ := h
  cases c with
  | block B =>
    obtain ⟨hs, -, -⟩ := hc
    have hB : B ∈ Φ'.tree := by
      rw [hs.tree_eq]
      exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩
    exact hs.F_anc_F'.mono (Set.insert_subset (hΦ'U hB) hΦU)
  | message m => rw [hc.1]; exact .refl
  | tick => rw [hc]; exact .refl
  | proposal => rw [hc]; exact .refl
  | toFG => rw [hc]; exact .refl
  | restart => rw [hc]; exact .refl

/-- **The weight invariant holds at every reachable state**, at the frame of its last call. -/
theorem weightInv_of_reachable (hU : Coherent U) {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {X : (evidenceReleaseSA sp FGP ro).State} {Φ : (evidenceReleaseSA sp FGP ro).Frm} {t : Time}
    (h : (evidenceReleaseSA sp FGP ro).ReachableAt self U X Φ t) :
    (FrameOK Φ ∧ Φ.tree ⊆ U) ∧ WeightInv sp U Φ X := by
  induction h with
  | init Φ _ hΦ => exact ⟨hΦ, fun w hw => absurd hw (Set.notMem_empty w), fun _ => Or.inl rfl⟩
  | @step X Φ Φ' t t' c _ _ hc ih =>
    obtain ⟨⟨hΦ, hΦU⟩, hinv⟩ := ih
    have hF := callOK_F_anc hΦU hc
    obtain ⟨⟨hΦ', hΦ'U⟩, -⟩ := hc
    have h' := hinv.later hF
    refine ⟨⟨hΦ', hΦ'U⟩, ?_⟩
    cases c with
    | tick => exact weightInv_acOnTickW hU hΦ' hΦ'U h' self t'
    | proposal => exact weightInv_acProposalW hΦ' h' t'
    | toFG => exact weightInv_acToFGW h' t'
    | message m => exact weightInv_acOnMessageW hΦ' hΦ'U h' self t' m
    | block B => exact weightInv_acOnBlockW hΦ' hΦ'U h' self t' B
    | restart => exact weightInv_acRestartW hΦ' hΦ'U h' ro self t'

/-- **Stored weights stay antitone along the chain**: at every reachable state of the
evidence-release SA inside a coherent `U`, every stored weight is antitone along the chains of
the frame of the last call, and of every later frame of `U` (finalized tip at or above). -/
theorem weightAntitone_of_reachable (hU : Coherent U) {ro : ReplayOrder sp FGP}
    {self : Fin sp.n} {X : (evidenceReleaseSA sp FGP ro).State}
    {Φ : (evidenceReleaseSA sp FGP ro).Frm} {t : Time}
    (h : (evidenceReleaseSA sp FGP ro).ReachableAt self U X Φ t) {Φ' : Frm sp.n FGP}
    (hΦ' : FrameOK Φ') (hΦ'U : Φ'.tree ⊆ U) (hF : Anc U Φ.F Φ'.F) :
    ∀ w ∈ X.wlocks, TreeAntitone sp Φ' fun Y => w.weight Y.root := fun w hw =>
  (((weightInv_of_reachable hU h).2.1 w hw).later hF).antitone hU hΦ' hΦ'U

end Consensus.Goldilocks.EvidenceRelease

end

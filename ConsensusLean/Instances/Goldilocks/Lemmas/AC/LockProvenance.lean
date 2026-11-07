module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Goldilocks SA: the lock-provenance toolkit

`FromP U L L' New`: every lock of `L'` sits below (inside `U`) a lock of `L` with its slot and
fast bit, or below a block `B` with `New l'.slot l'.fast B`. The SA functions that only move
locks back keep `FromP` (`FromP.of_movesBack`, `FromP.of_proposal`, `toFG_locks`), and it
composes (`FromP.trans`). Shared by the fast-lock provenance (`AC/Steps/Provenance`) and the slow
and stored slow-lock provenance (`Healing/AC/SlowLock`, `Healing/DrainProvenance`), which add
their own `New` for the writing functions. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- The block of `l'` is an ancestor (inside `U`) of the block of `l`, or `l' = l`. -/
def SitsBelow (U : Set (Blk sp.n FGP)) (l' l : Lock) : Prop :=
  l' = l ∨ ∃ L₁ ∈ U, L₁.root = l'.block ∧ ∃ L₂ ∈ U, L₂.root = l.block ∧ Anc U L₁ L₂

/-- The block of `l` is in `U` and an ancestor of `B` there. -/
def Below (U : Set (Blk sp.n FGP)) (l : Lock) (B : Blk sp.n FGP) : Prop :=
  ∃ L ∈ U, L.root = l.block ∧ Anc U L B

/-- Every lock of `L'` sits below a lock of `L` with its slot and fast bit, or below a block `B`
with `New l'.slot l'.fast B`. -/
def FromP (U : Set (Blk sp.n FGP)) (L L' : Set Lock)
    (New : Nat → Bool → Blk sp.n FGP → Prop) : Prop :=
  ∀ l' ∈ L', (∃ l ∈ L, l.fast = l'.fast ∧ l'.slot = l.slot ∧ SitsBelow U l' l) ∨
    ∃ B, New l'.slot l'.fast B ∧ Below U l' B

theorem sitsBelow_iff {U : Set (Blk sp.n FGP)} {l' l : Lock} :
    SitsBelow U l' l ↔
      l' = l ∨ ∃ L₁ ∈ U, L₁.root = l'.block ∧ ∃ L₂ ∈ U, L₂.root = l.block ∧ Anc U L₁ L₂ :=
  Iff.rfl

theorem below_iff {U : Set (Blk sp.n FGP)} {l : Lock} {B : Blk sp.n FGP} :
    Below U l B ↔ ∃ L ∈ U, L.root = l.block ∧ Anc U L B := Iff.rfl

theorem fromP_iff {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} :
    FromP U L L' New ↔ ∀ l' ∈ L', (∃ l ∈ L, l.fast = l'.fast ∧ l'.slot = l.slot ∧
      SitsBelow U l' l) ∨ ∃ B, New l'.slot l'.fast B ∧ Below U l' B := Iff.rfl

theorem FromP.of_eq {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h : L' = L) : FromP U L L' New := by
  subst h
  exact fun l hl => Or.inl ⟨l, hl, rfl, rfl, Or.inl rfl⟩

theorem FromP.mono {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New New' : Nat → Bool → Blk sp.n FGP → Prop} (h : FromP U L L' New)
    (hN : ∀ s f B, New s f B → New' s f B) : FromP U L L' New' := fun l hl =>
  (h l hl).imp_right fun ⟨B, h1, h2⟩ => ⟨B, hN _ _ _ h1, h2⟩

theorem FromP.trans {U : Set (Blk sp.n FGP)} (hU : Coherent U) {L₁ L₂ L₃ : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h₁ : FromP U L₁ L₂ New) (h₂ : FromP U L₂ L₃ New) :
    FromP U L₁ L₃ New := by
  intro l₃ hl₃
  rcases h₂ l₃ hl₃ with ⟨l₂, hl₂, hf₂, hs₂, hb₂⟩ | ⟨B, hN, hB⟩
  · rcases h₁ l₂ hl₂ with ⟨l₁, hl₁, hf₁, hs₁, hb₁⟩ | ⟨B, hN, L, hL, hLr, hLB⟩
    · refine Or.inl ⟨l₁, hl₁, hf₁.trans hf₂, hs₂.trans hs₁, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact hb₁
      rcases hb₁ with rfl | ⟨C₁, hC₁, hC₁r, C₂, hC₂, hC₂r, hC⟩
      · exact Or.inr ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      have : A₂ = C₁ := hU.1 hA₂ hC₁ (hA₂r.trans hC₁r.symm)
      subst this
      exact Or.inr ⟨A₁, hA₁, hA₁r, C₂, hC₂, hC₂r, hA.trans hC⟩
    · refine Or.inr ⟨B, hs₂ ▸ hf₂ ▸ hN, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact ⟨L, hL, hLr, hLB⟩
      have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
      subst this
      exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩
  · exact Or.inr ⟨B, hN, hB⟩

/-- Locks that move back in a frame inside `U` sit below the locks they come from. -/
theorem FromP.of_movesBack {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}
    (hΦ : Φ.tree ⊆ U) {L L' : Set Lock} {New : Nat → Bool → Blk sp.n FGP → Prop}
    (h : MovesBack sp Φ L L') : FromP U L L' New := by
  intro l' hl'
  obtain ⟨l, hl, hs, hfa, -, B, hB, hBr, B', hB', hB'r, hA⟩ := h l' hl'
  exact Or.inl ⟨l, hl, hfa.symm, hs, Or.inr ⟨B', hΦ hB', hB'r, B, hΦ hB, hBr,
    hA.mono hΦ⟩⟩

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

/-- `FromP.of_proposal` with the unlock given. -/
theorem FromP.of_proposalWith
    {L : Set Lock} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n)
    (t : Time) {New : Nat → Bool → Blk sp.n FGP → Prop}
    (hL : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1)
      (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)) L) :
    FromP U A.locks (acProposalWith sp L A Φ t).1.locks New := by
  unfold acProposalWith
  dsimp only
  split_ifs
  · exact FromP.of_movesBack hΦU (hL.movesBack hΦ)
  · exact FromP.of_eq rfl

theorem FromP.of_proposal (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n)
    (t : Time) {New : Nat → Bool → Blk sp.n FGP → Prop} :
    FromP U A.locks (acProposal sp A Φ t).1.locks New :=
  FromP.of_proposalWith hΦ hΦU A t (unlockRel_unlock hΦ _ _ _ _)

theorem toFG_locks (A : SAState sp.n) (t : Time) :
    (acToFG sp A Φ t).1.locks = A.locks := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

theorem Below.of_sitsBelow (hU : Coherent U) {l' l : Lock} {B : Blk sp.n FGP}
    (h : SitsBelow U l' l) (hB : Below U l B) : Below U l' B := by
  rcases h with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
  · exact hB
  obtain ⟨L, hL, hLr, hLB⟩ := hB
  have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
  subst this
  exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩

end Consensus.Goldilocks.SA

end

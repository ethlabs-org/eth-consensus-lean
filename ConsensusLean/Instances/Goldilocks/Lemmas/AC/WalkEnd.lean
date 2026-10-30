module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks SA: where a walk stops

`WalkEnd T sc el a E`: the walk of `T` (scores `sc`, eligibility `el`) from `a` stops at `E`,
some number of steps in, with no best eligible child at `E`. The end of a walk does not
depend on the fuel once it stops (`WalkEnd.unique`); a walk that passes `X` ends where the walk
from `X` ends (`WalkEnd.of_anc`); a walk with at least one step per block of `T` stops
(`walkEnd_ghost`); and if two walks have the same eligible children and scores at every block
other than the first walk's end `E`, the second walk from the start ends where the second walk
from `E` ends (`WalkEnd.congr`). Built on `Steps/Walk`'s `ghost_stopped`, `ghost_visits`,
`ghost_add` and `ghost_succ_of_best`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- The eligible children of `X` in `T`: the set `ghost` takes the best of (an `abbrev`, so that
it matches that set after `rw [ghost]`). -/
abbrev eligibleChildren (T : Set (Blk sp.n FGP)) (el : Blk sp.n FGP → Prop) (X : Blk sp.n FGP) :
    Set (Blk sp.n FGP) :=
  {B | B ∈ T ∧ B.parent = some X.root ∧ el B}

/-- The walk of `T` from `a` stops at `E`. -/
def WalkEnd (T : Set (Blk sp.n FGP)) (sc : Blk sp.n FGP → Nat) (el : Blk sp.n FGP → Prop)
    (a E : Blk sp.n FGP) : Prop :=
  ∃ f, ghost sp T sc el f a = E ∧ ¬ ∃ C, IsBest sp sc (eligibleChildren T el E) C

variable {T T₂ S : Set (Blk sp.n FGP)} {sc sc₂ : Blk sp.n FGP → Nat}
  {el el₂ : Blk sp.n FGP → Prop} {a E X : Blk sp.n FGP}

theorem walkEnd_iff : WalkEnd (sp := sp) T sc el a E ↔
    ∃ f, ghost sp T sc el f a = E ∧ ¬ ∃ C, IsBest sp sc (eligibleChildren T el E) C := Iff.rfl

/-- Being best is preserved by equal sets and scores that agree on them. -/
theorem IsBest.congr {S' : Set (Blk sp.n FGP)} (hS : S = S') (hsc : ∀ B ∈ S, sc B = sc₂ B)
    {C : Blk sp.n FGP} : IsBest sp sc S C ↔ IsBest sp sc₂ S' C := by
  subst hS
  constructor
  · rintro ⟨hC, h⟩
    exact ⟨hC, fun D hD hne => by rw [← hsc D hD, ← hsc C hC]; exact h D hD hne⟩
  · rintro ⟨hC, h⟩
    exact ⟨hC, fun D hD hne => by rw [hsc D hD, hsc C hC]; exact h D hD hne⟩

/-- A stopped walk ends at its start. -/
theorem walkEnd_self (h : ¬ ∃ C, IsBest sp sc (eligibleChildren T el a) C) :
    WalkEnd (sp := sp) T sc el a a :=
  ⟨0, rfl, h⟩

/-- One step: the walk from `a` ends where the walk from its best eligible child ends. -/
theorem WalkEnd.step {C : Blk sp.n FGP} (hC : IsBest sp sc (eligibleChildren T el a) C)
    (h : WalkEnd (sp := sp) T sc el C E) : WalkEnd (sp := sp) T sc el a E := by
  obtain ⟨f, hf, hs⟩ := h
  refine ⟨1 + f, ?_, hs⟩
  rw [ghost_add, ghost_succ_of_best (el := el) 0 a hC, hf]

/-- The end of a walk is unique. -/
theorem WalkEnd.unique {E' : Blk sp.n FGP} (h : WalkEnd (sp := sp) T sc el a E)
    (h' : WalkEnd (sp := sp) T sc el a E') : E = E' := by
  obtain ⟨f, rfl, hs⟩ := h
  obtain ⟨f', rfl, hs'⟩ := h'
  rcases le_total f f' with hle | hle
  · exact (ghost_fuel_stable hle hs).symm
  · exact ghost_fuel_stable hle hs'

/-- The end of a walk extends its start. -/
theorem WalkEnd.anc (hT : T ⊆ S) (ha : a ∈ S) (h : WalkEnd (sp := sp) T sc el a E) :
    Anc S a E := by
  obtain ⟨f, rfl, -⟩ := h
  exact anc_ghost hT f ha

/-- **A walk passes the blocks between its start and its end**: from such a block the walk ends
at the same block. -/
theorem WalkEnd.of_anc (hS : Coherent S) (hT : T ⊆ S) (h : WalkEnd (sp := sp) T sc el a E)
    (haX : Anc S a X) (hXE : Anc S X E) : WalkEnd (sp := sp) T sc el X E := by
  obtain ⟨f, rfl, hs⟩ := h
  obtain ⟨k, hk, rfl⟩ := ghost_visits hS hT f haX hXE
  exact ⟨f - k, by rw [← ghost_add, Nat.add_sub_cancel' hk], hs⟩

/-- **Enough fuel stops the walk**: with at least one step per block of `T`, the walk stops. -/
theorem walkEnd_ghost (hS : Coherent S) (hT : T ⊆ S) (hfin : T.Finite) {f : Nat}
    (hf : T.ncard ≤ f) (a : Blk sp.n FGP) :
    WalkEnd (sp := sp) T sc el a (ghost sp T sc el f a) :=
  ⟨f, rfl, ghost_stopped hS hT hfin hf a⟩

/-- **Two walks that agree away from the first walk's end**: if at every block other than `E`
(by root) the eligible children and their scores agree, the walk of the second tree from `a`
ends where its walk from `E` ends. -/
theorem WalkEnd.congr {E' : Blk sp.n FGP} (hS : Coherent S) (hT : T ⊆ S) (ha : a ∈ S)
    (hE : E ∈ S)
    (hag : ∀ X, X.root ≠ E.root → eligibleChildren T el X = eligibleChildren T₂ el₂ X ∧
      ∀ B ∈ eligibleChildren T el X, sc B = sc₂ B)
    (h : WalkEnd (sp := sp) T sc el a E) (h₂ : WalkEnd (sp := sp) T₂ sc₂ el₂ E E') :
    WalkEnd (sp := sp) T₂ sc₂ el₂ a E' := by
  obtain ⟨f, hf, hs⟩ := h
  induction f generalizing a with
  | zero =>
    obtain rfl : a = E := hf
    exact h₂
  | succ f ih =>
    by_cases hr : a.root = E.root
    · obtain rfl : a = E := hS.1 ha hE hr
      exact h₂
    rw [ghost] at hf
    split at hf
    · rename_i hb
      have hC := hb.choose_spec
      obtain ⟨heq, hsc⟩ := hag a hr
      exact (ih (hT hC.1.1) hf).step ((IsBest.congr heq hsc).1 hC)
    · subst hf
      exact absurd rfl hr

end Consensus.Goldilocks.SA

end

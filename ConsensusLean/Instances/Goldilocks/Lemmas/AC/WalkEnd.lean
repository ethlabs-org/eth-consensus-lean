module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks SA: where a walk stops

`WalkEnd T sc el a E`: the walk of `T` (scores `sc`, eligibility `el`) from `a` stops at `E`,
some number of steps in, with no best eligible child at `E`. The end of a walk does not
depend on the fuel once it stops (`WalkEnd.unique`); a walk that passes `X` ends where the walk
from `X` ends (`WalkEnd.of_anc`); a walk with at least one step per block of `T` stops
(`walkEnd_ghost`). Built on `Steps/Walk`'s `ghost_stopped`, `ghost_visits`,
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

end Consensus.Goldilocks.SA

end

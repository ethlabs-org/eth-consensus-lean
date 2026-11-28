module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks: the confirmation of a slot is a block with a strict majority of its slot

`getConfirmation_eq_of_majority`: in a well-formed frame, a slot-`s` block `P` above `Σ.F` whose
confirmation score is a strict majority of the slot's voters is the result of the update of slot
`s`. Every block with a strict majority is on one chain with it (A0.3), and no block strictly
above it has a supporter among the slot-`s` votes resolved by the cutoff. It reads one AC state
and one frame; the majority is its users' (`Service/Adopt` for constant faults and its
growing-fault form). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams)

variable {sp : ACParams} {FGP : Type}

/-- A block strictly above a slot-`s` block has no supporter among the slot-`s` votes resolved by a
cutoff: a vote cannot resolve to a head of a later slot. -/
private theorem confirmationScore_eq_zero {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ) {s : Nat}
    {P B : AC.Blk sp.n FGP} (hPs : P.slot = s) (hPB : Φ.Anc P B) (hne : P ≠ B) :
    AC.confirmationScore sp A Φ s B = 0 := by
  have hlt := ((Anc.slot_le hΦ.coherent hPB).2 hne)
  rw [AC.confirmationScore, Set.ncard_eq_zero]
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, x, ⟨-, hx⟩, -, hxs, R, hR, hRr, hBR⟩
  have hin : AC.InTree Φ x.head := ⟨R, hR, hRr⟩
  obtain ⟨R', hl⟩ : ∃ R', AC.lookup Φ x.head = some R' := by
    unfold AC.lookup; rw [dite_eq_left_of_eq_true (eq_true hin)]; exact ⟨_, rfl⟩
  obtain ⟨hR', hR'r⟩ := AC.lookup_eq_some hl
  obtain rfl : R' = R := hΦ.coherent.1 hR' hR (hR'r.trans hRr.symm)
  have hsR := (Anc.slot_le hΦ.coherent hBR).1
  have hxs' : x.slot = s := by exact_mod_cast hxs
  have : AC.resolutionTime A Φ x = ⊤ := by
    unfold AC.resolutionTime
    rw [hl]
    exact ite_eq_left (by omega)
  rw [this] at hx
  exact not_top_lt hx

/-- A supporting set outnumbering the remaining voters supplies a strict majority. -/
theorem confirmation_majority_of_cover {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {s : Nat} {B : AC.Blk sp.n FGP} {support opp : Set (Fin sp.n)}
    (hcover : AC.voters {v | v ∈ A.pool s} ⊆ support ∪ opp) (hcount : opp.ncard < support.ncard)
    (hsupp : support ⊆ AC.supporters Φ ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
      AC.resolutionTime A Φ v < AC.ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s B) :
    (AC.voters {v | v ∈ A.pool s}).ncard < 2 * AC.confirmationScore sp A Φ s B := by
  have h := (Set.ncard_le_ncard hcover).trans (Set.ncard_union_le _ _)
  have hs : support.ncard ≤ AC.confirmationScore sp A Φ s B := Set.ncard_le_ncard hsupp
  omega

/-- The confirmation extends any block above the finalized root with a strict majority. -/
theorem getConfirmation_extends_of_majority {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    (hΦ : FrameOK Φ) {P : AC.Blk sp.n FGP} {s : Nat} (hPt : P ∈ Φ.tree)
    (hFP : Φ.Anc Φ.F P)
    (hmaj : (AC.voters {v | v ∈ A.pool s}).ncard < 2 * AC.confirmationScore sp A Φ s P) :
    ∃ D, AC.getConfirmation sp A Φ s = some D ∧ Φ.Anc P D := by
  set S := {B | B ∈ Φ.tree ∧ Φ.Anc Φ.F B ∧
    (AC.voters {v | v ∈ A.pool s}).ncard < 2 * AC.confirmationScore sp A Φ s B}
  have hS : S ⊆ Φ.tree := fun X hX => hX.1
  set V : AC.View sp.n := ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
    AC.resolutionTime A Φ v < AC.ETime.of (sp.ts s + 2 * sp.Δ)}⟩
  have hcs : ∀ B, AC.confirmationScore sp A Φ s B = (AC.supporters Φ V s B).ncard :=
    fun _ => rfl
  have hsub : V.support ⊆ V.votes := fun _ hv => hv.1
  have hch : ∀ B ∈ S, ∀ C ∈ S, Compatible Φ.tree B C := fun B hB C hC =>
    AC.majority_chain sp _ Φ V s B C hΦ hsub hB.1 hC.1 (hcs B ▸ hB.2.2) (hcs C ▸ hC.2.2)
  obtain ⟨D, hD⟩ := AC.exists_deepest hΦ hS ⟨P, hPt, hFP, hmaj⟩
  exact ⟨D, hD, AC.anc_deepest hΦ hS hch hD P ⟨hPt, hFP, hmaj⟩⟩

/-- **The confirmation of slot `s` is a slot-`s` block with a strict majority**: in a well-formed
frame `Φ`, a block `P` of slot `s` in the tree, above `Σ.F`, whose confirmation score in `A` is a
strict majority of the slot's voters, is `getConfirmation`'s result. -/
theorem getConfirmation_eq_of_majority {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    (hΦ : FrameOK Φ) {P : AC.Blk sp.n FGP} {s : Nat} (hPs : P.slot = s) (hPt : P ∈ Φ.tree)
    (hFP : Φ.Anc Φ.F P)
    (hmaj : (AC.voters {v | v ∈ A.pool s}).ncard < 2 * AC.confirmationScore sp A Φ s P) :
    AC.getConfirmation sp A Φ s = some P := by
  obtain ⟨D, hD, hPD⟩ := getConfirmation_extends_of_majority hΦ hPt hFP hmaj
  rw [hD]
  by_contra hne
  have h0 := confirmationScore_eq_zero (A := A) hΦ hPs hPD fun h => hne (congrArg some h.symm)
  have := (AC.deepest_mem hD).1.2.2
  omega

end Consensus.Goldilocks.Compose

end

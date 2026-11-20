module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.TimeShiftedQuorum
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count

public section

/-! # The live fallback passes a forced prefix before voting

The old-slot evidence and the post-unlock state determine the fallback even if it is never
emitted. The geometry premises are about its domain and surviving locks, not its result. -/

namespace Consensus.Goldilocks.SA.TSQ

variable {sp : SAParams} {FGP : Type} {Φ : Frm sp.n FGP}

/-- Strict dominance at the protected block suffices for the whole path from the actual anchor of
the supplied state. In particular no vote or equality with a previously emitted head is needed. -/
theorem fallback_extends (ok : FrameOK Φ) (A : SAState sp.n) (s : Nat) (t : Time)
    {C : Blk sp.n FGP}
    (closed : ∀ B ∈ voterBlockTree sp A Φ (s + 1), ∀ X, Φ.Anc X B →
      X ∈ voterBlockTree sp A Φ (s + 1))
    (viable : C ∈ Φ.viableTree (voteDomain sp A Φ (s + 1)) ∨ Φ.Anc C Φ.fcRoot)
    (locks : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Compatible Φ.tree L C)
    (dominates : (voters (voteView A Φ s ⊤).votes).ncard -
      (supporters Φ (voteView A Φ s ⊤) s C).ncard <
      (scoreSeats Φ (voteView A Φ s (ETime.of (freeze sp (s + 1)))) s C).ncard) :
    Φ.Anc C (getHead sp A Φ t (Φ.viableTree (voteDomain sp A Φ (s + 1))) (voteView A Φ s ⊤) s) := by
  apply anc_getHead ok.coherent ok Set.Subset.rfl _ _ _ _ voteDomain_subset_tree
    (voteDomain_anc_closed closed) viable locks
  intro X D hD dp dc
  let V := voteView A Φ s ⊤
  let O := supporters Φ V s C
  let E := equivocators V.votes
  have sub : O ∪ E ⊆ voters V.votes := by
    rintro i (⟨_, v, hv, eq, _⟩ | ⟨v, hv, _, _, _, eq, _⟩)
    · exact ⟨v, (List.mem_filter.1 hv).1, eq⟩
    · exact ⟨v, hv, eq⟩
  have disj : Disjoint O E := Set.disjoint_left.2 fun _ hi => hi.1
  apply isBest_of_cover ok (fun _ hv => (List.mem_filter.1 hv).1)
    (fun _ hb => voteDomain_subset_tree hb.1) (SX := O ∪ E) Set.Subset.rfl _ hD dp dc
  rw [Set.union_assoc, Set.union_self, Set.union_sdiff_cancel_right disj.le_bot,
    Set.ncard_sdiff sub]
  have lower := Set.ncard_le_ncard (freeze_to_cast (a := A) (φ := Φ) (c := C) (slot := s)
    (f := ETime.of (freeze sp (s + 1))))
  rw [scoreSeats_eq (A := voteView A Φ s ⊤)] at lower
  change _ ≤ (O ∪ E).ncard at lower
  change (voters V.votes).ncard - O.ncard < _ at dominates
  have := Set.ncard_le_ncard sub
  omega

end Consensus.Goldilocks.SA.TSQ

end

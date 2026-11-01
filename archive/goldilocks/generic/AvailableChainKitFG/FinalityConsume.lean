module
public import AvailableChainKitFG.Certificates

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- A quorum covered by stored finality bits or matching rows finalizes the
old pending pair. A later justification in this transition keeps that pair. -/
theorem transition_finality_of_cover (E : Electorate V) (cfg : FGConfig)
    (σ : ChainState V) (B : FGBlock V) (rs : List (Row V)) (S : Finset V)
    (hlt : σ.h_F < σ.h_j) (hquorum : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ σ.finalize ∨
      ∃ a ∈ rs, a.signer = i ∧ a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) :
    (transition E cfg σ B rs).F = σ.J ∧
      (transition E cfg σ B rs).h_F = σ.h_j := by
  have mem_fold (rows : List (Row V)) (σ : ChainState V)
      (hlt : σ.h_F < σ.h_j) {i : V}
      (hi : i ∈ σ.finalize ∨
        ∃ a ∈ rows, a.signer = i ∧ a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) :
      i ∈ (rows.foldl process_row σ).finalize := by
    induction rows generalizing σ with
    | nil => simpa using hi
    | cons a rows ih =>
        obtain ⟨-, -, -, -, hJ, hhj, -, hhF⟩ := process_row_fields σ a
        apply ih (process_row σ a) (by rwa [hhF, hhj])
        rcases hi with hi | ⟨b, hb, hbi, hbf⟩
        · left
          rw [process_row_finalize]
          split_ifs <;> simp_all
        · rcases List.mem_cons.mp hb with rfl | hb
          · left
            rw [process_row_finalize]
            simp [hlt, hbf, hbi]
          · right
            exact ⟨b, hb, hbi, by simpa only [hhj, hJ] using hbf⟩
  have hsub : S ⊆ (foldRows σ B rs).finalize := by
    intro i hi
    exact mem_fold rs { σ with s := B.slot } hlt (hcover i hi)
  have hq := isQuorum_of_subset E hquorum hsub
  obtain ⟨-, -, -, hJ, hhj, -, hhF⟩ := foldRows_fields σ B rs
  have hready : finalityReady E (foldRows σ B rs) = true := by
    simp only [finalityReady, Bool.and_eq_true]
    exact ⟨by simpa only [hhF, hhj] using (decide_eq_true hlt), decide_eq_true hq⟩
  change (process_height_events E cfg (foldRows σ B rs)).F = σ.J ∧
    (process_height_events E cfg (foldRows σ B rs)).h_F = σ.h_j
  obtain ⟨hF, hhF'⟩ := process_height_events_F E cfg (foldRows σ B rs)
  rw [hF, hhF', afterFin_F, afterFin_h_F, hready]
  exact ⟨hJ, hhj⟩

/-- A non-genesis block consumes finality coverage for its parent's pending pair. -/
theorem derive_finality_of_cover (E : Electorate V) (cfg : FGConfig)
    (B : FGBlock V) (hB : B ≠ .genesis) (S : Finset V)
    (hlt : (derive E cfg B.parent).h_F < (derive E cfg B.parent).h_j)
    (hquorum : E.IsQuorum S)
    (hcover : ∀ i ∈ S, i ∈ (derive E cfg B.parent).finalize ∨
      ∃ a ∈ B.rows, a.signer = i ∧
        a.finality_pair = some ⟨(derive E cfg B.parent).h_j,
          (derive E cfg B.parent).J.root⟩) :
    (derive E cfg B).F = (derive E cfg B.parent).J ∧
      (derive E cfg B).h_F = (derive E cfg B.parent).h_j := by
  cases B with
  | genesis => exact (hB rfl).elim
  | node p s r_s x rs =>
      exact transition_finality_of_cover E cfg (derive E cfg p) (.node p s r_s x rs)
        rs S hlt hquorum hcover

end AvailableChain.KitFG
end

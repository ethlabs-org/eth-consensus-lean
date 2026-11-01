module
public import AvailableChainSAPC.Proofs.Projection

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem fold_field {α β γ : Type} (f : α → γ) (step : α → β → α)
    (h : ∀ st x, f (step st x) = f st) (xs : List β) (st : α) :
    f (xs.foldl step st) = f st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (h st x)

/-- Assembly preserves each field that certificate installation preserves. -/
theorem collectPCs_field (p : Params) {n : Nat} {α : Type} (f : State n → α)
    (hf : ∀ st c, f (installPC st c) = f st) (st : State n) :
    f (collectPCs p st) = f st := by
  unfold collectPCs
  apply fold_field f
  intro acc pair
  rcases pair with ⟨s, b⟩
  dsimp only
  split
  · rfl
  · exact hf _ _

theorem collectPCs_base (p : Params) {n : Nat} (st : State n) :
    (collectPCs p st).base = st.base :=
  collectPCs_field p State.base (by intros; rfl) st

theorem collectPCs_archive (p : Params) {n : Nat} (st : State n) :
    (collectPCs p st).receivedHeads = st.receivedHeads :=
  collectPCs_field p State.receivedHeads (by intros; rfl) st

theorem receiveHead_archive_mono (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    st.receivedHeads ⊆ (receiveHead p st o).receivedHeads := by
  unfold receiveHead
  split
  · dsimp only
    split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _
  · exact List.Subset.refl _

theorem receiveHead_archive_origin (p : Params) {n : Nat} (st : State n)
    (o h : HeadWire n) (hh : h ∈ (receiveHead p st o).receivedHeads) :
    h ∈ st.receivedHeads ∨ h = o := by
  unfold receiveHead at hh
  split at hh
  · dsimp only at hh
    split at hh
    · exact Or.inl hh
    · split at hh
      · exact Or.inl hh
      · simpa only [List.mem_append, List.mem_singleton] using hh
  · exact Or.inl hh

private theorem fold_receive_mono (p : Params) {n : Nat} (xs : List (HeadWire n))
    (st : State n) : st.receivedHeads ⊆ (xs.foldl (receiveHead p) st).receivedHeads := by
  induction xs generalizing st with
  | nil => exact List.Subset.refl _
  | cons x xs ih => exact List.Subset.trans (receiveHead_archive_mono p st x) (ih _)

theorem receiveHeads_archive_origin (p : Params) {n : Nat} (xs : List (HeadWire n))
    (st : State n) (h : HeadWire n)
    (hh : h ∈ (xs.foldl (receiveHead p) st).receivedHeads) :
    h ∈ st.receivedHeads ∨ h ∈ xs := by
  induction xs generalizing st with
  | nil => exact Or.inl hh
  | cons x xs ih =>
      rcases ih _ hh with hold | hrest
      · rcases receiveHead_archive_origin p st x h hold with hold | rfl
        · exact Or.inl hold
        · exact Or.inr (by simp)
      · exact Or.inr (List.mem_cons_of_mem x hrest)

theorem process_archive_mono (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.receivedHeads ⊆ (process p st o).receivedHeads := by
  unfold process
  split
  · simpa only [admitHead, collectPCs_archive] using receiveHead_archive_mono p st _
  · unfold admitProposal
    split
    · rw [collectPCs_archive]
      exact fold_receive_mono p _ { st with
        base := proposalBase p st o _ _ _
        proposals := st.proposals ++ [o] }
    · exact List.Subset.refl _
  · split
    · rw [collectPCs_archive]
      exact fold_receive_mono p _ _
    · exact List.Subset.refl _
  · exact List.Subset.refl _

/-- New archived signatures come from actual direct or carried input. -/
theorem process_archive_origin (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (h : HeadWire n) (hh : h ∈ (process p st o).receivedHeads) :
    h ∈ st.receivedHeads ∨ o = fromHead h ∨ carries o (fromHead h) := by
  unfold process at hh
  split at hh
  · rename_i r i data ha hp
    rw [admitHead, collectPCs_archive] at hh
    rcases receiveHead_archive_origin p st _ h hh with hold | rfl
    · exact Or.inl hold
    · exact Or.inr (Or.inl (by cases o; simp_all [fromHead]))
  · rename_i s b raw support c ha hp
    unfold admitProposal at hh
    split at hh
    · rw [collectPCs_archive] at hh
      rcases receiveHeads_archive_origin p _ _ h hh with hold | hnew
      · exact Or.inl hold
      · right; right
        simp only [carries, hp]
        apply List.mem_map.mpr
        refine ⟨h, ?_, rfl⟩
        rcases List.mem_append.mp hnew with hraw | hpc
        · exact List.mem_append_left _ (List.mem_append_left _ hraw)
        · exact List.mem_append_right _ hpc
    · exact Or.inl hh
  · rename_i c ha hp
    split at hh
    · rw [collectPCs_archive] at hh
      rcases receiveHeads_archive_origin p _ _ h hh with hold | hnew
      · exact Or.inl hold
      · exact Or.inr (Or.inr (by simpa only [carries, hp] using
          (List.mem_map.mpr ⟨h, hnew, rfl⟩)))
    · exact Or.inl hh
  · exact Or.inl hh

theorem clock_archive (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).receivedHeads = st.receivedHeads := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, saveTimely]
  all_goals split_ifs <;> rfl

end AvailableChain.SAPC
end

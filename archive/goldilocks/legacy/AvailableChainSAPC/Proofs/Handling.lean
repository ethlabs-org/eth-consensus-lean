module
public import AvailableChainSAPC.Proofs.ReceiptState
public import AvailableChainGridCO.Proofs.Handling

@[expose] public section
namespace AvailableChain.SAPC

/-- Erasing the ack gives exactly the shared base handler, even when
the archive rejects a future label or already contains the signature. -/
theorem receiveHead_base (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    (receiveHead p st o).base = GridCO.admitVote p.engine st.base (baseWire o) := by
  cases o with
  | mk auth data =>
      cases auth with
      | seat r i =>
          simp only [receiveHead]
          split
          · rename_i ht
            simp [GridCO.admitVote, baseWire, baseHead, GridCO.fromHead, SA.Params.engine, ht]
          · split <;> rfl
      | proposer s => rfl
      | none => rfl

theorem receiveHeads_base (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) :
    (xs.foldl (receiveHead p) st).base =
      xs.foldl (fun acc o => GridCO.admitVote p.engine acc (baseWire o)) st.base := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, receiveHead_base]; rfl

theorem proposalBase_now (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) :
    (proposalBase p st o b raw support).now = st.base.now := by
  unfold proposalBase GridCO.admitProposal
  dsimp only
  split_ifs <;> rfl

/-- Lift a shared receipt invariant through all direct and carried
SA-PC calls. PC assembly and installation do not change the base. -/
theorem process_base_invariant (p : Params) {n : Nat} (Q : GridCO.State n → Prop)
    (hhead : ∀ st o, Q st → Q (GridCO.admitVote p.engine st o))
    (hproposal : ∀ st o b, Q st → Q (GridCO.admitProposal p.engine st o b []))
    (st : State n) (o : Wire n) (h : Q st.base) : Q (process p st o).base := by
  have hfold (xs : List (HeadWire n)) (st : State n) (h : Q st.base) :
      Q (xs.foldl (receiveHead p) st).base := by
    induction xs generalizing st with
    | nil => exact h
    | cons x xs ih =>
        apply ih
        rw [receiveHead_base]
        exact hhead _ _ h
  unfold process
  split
  · simpa only [admitHead, collectPCs_base, receiveHead_base] using hhead _ _ h
  · unfold admitProposal
    split
    · rw [collectPCs_base]
      exact hfold _ _ (hproposal _ _ _ h)
    · exact h
  · split
    · simpa only [collectPCs_base, installPC] using hfold _ st h
    · exact h
  · exact h

/-- A raw handler call supplies the same base key or the same two-copy
equivocation evidence as SA. No equality of complete signed caches is used. -/
theorem receiveHead_base_mem_or_equivocates (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (data : HeadData)
    (hlo : (st.base.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.base.now / (4 * p.Δ)).toNat) :
    baseWire ⟨.seat r i, data⟩ ∈ (receiveHead p st ⟨.seat r i, data⟩).base.votes ∨
      GridCO.equivocates (GridCO.votesAt (receiveHead p st ⟨.seat r i, data⟩).base r) i = true := by
  rw [receiveHead_base]
  exact GridCO.admitVote_head_mem_or_equivocates p.engine st.base r i data.target hlo hhi

theorem receiveHeads_base_mem_or_equivocates (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) (r : Slot) (i : Fin n) (data : HeadData)
    (hlo : (st.base.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.base.now / (4 * p.Δ)).toNat)
    (hm : (⟨.seat r i, data⟩ : HeadWire n) ∈ xs) :
    baseWire ⟨.seat r i, data⟩ ∈ (xs.foldl (receiveHead p) st).base.votes ∨
      GridCO.equivocates (GridCO.votesAt (xs.foldl (receiveHead p) st).base r) i = true := by
  have h := GridCO.fold_heads_mem_or_equivocates p.engine (xs.map baseHead) st.base r i
    data.target hlo hhi (List.mem_map.mpr ⟨baseHead ⟨.seat r i, data⟩,
      List.mem_map.mpr ⟨⟨.seat r i, data⟩, hm, rfl⟩, rfl⟩)
  simpa only [receiveHeads_base, List.foldl_map, baseWire] using! h

/-- Actual direct, proposal-carried, and envelope-carried calls retain
all non-future complete signatures in the archive. -/
theorem handled_head_archived (p : Params) {n : Nat} (st : State n)
    (parent : Wire n) (r : Slot) (i : Fin n) (data : HeadData)
    (hhi : r ≤ (st.base.now / (4 * p.Δ)).toNat)
    (hh : handles p st parent (fromHead ⟨.seat r i, data⟩)) :
    (⟨.seat r i, data⟩ : HeadWire n) ∈ (process p st parent).receivedHeads := by
  rcases hh with rfl | hh
  · simpa only [process, fromHead, admitHead, collectPCs_archive] using
      receiveHead_mem p st ⟨.seat r i, data⟩ r rfl hhi
  · cases ha : parent.auth <;> cases hp : parent.payload <;>
      simp only [ha, hp] at hh <;> try contradiction
    · obtain ⟨henter, hmem⟩ := hh
      obtain ⟨o, ho, he⟩ := List.mem_map.mp hmem
      have heq : o = ⟨.seat r i, data⟩ := by
        cases o; cases he; rfl
      subst o
      simp only [process, ha, hp, admitProposal, henter, ↓reduceIte, collectPCs_archive]
      apply receiveHeads_mem p _ _ _ ho r rfl
      simpa only [proposalBase_now] using hhi
    · obtain ⟨hready, hmem⟩ := hh
      obtain ⟨o, ho, he⟩ := List.mem_map.mp hmem
      have heq : o = ⟨.seat r i, data⟩ := by
        cases o; cases he; rfl
      subst o
      simp only [process, ha, hp, hready, ↓reduceIte, collectPCs_archive, installPC]
      exact receiveHeads_mem p st _ _ ho r rfl hhi

/-- The archive-based `processed` hook retains the base acceptance
alternative required by shared view and relay arguments. -/
theorem handled_head_base_mem_or_equivocates (p : Params) {n : Nat} (st : State n)
    (parent : Wire n) (r : Slot) (i : Fin n) (data : HeadData)
    (hlo : (st.base.now / (4 * p.Δ)).toNat - 1 ≤ r)
    (hhi : r ≤ (st.base.now / (4 * p.Δ)).toNat)
    (hh : handles p st parent (fromHead ⟨.seat r i, data⟩)) :
    baseWire ⟨.seat r i, data⟩ ∈ (process p st parent).base.votes ∨
      GridCO.equivocates (GridCO.votesAt (process p st parent).base r) i = true := by
  rcases hh with rfl | hh
  · simpa only [process, fromHead, admitHead, collectPCs_base] using
      receiveHead_base_mem_or_equivocates p st r i data hlo hhi
  · cases ha : parent.auth <;> cases hp : parent.payload <;>
      simp only [ha, hp] at hh <;> try contradiction
    · obtain ⟨henter, hmem⟩ := hh
      obtain ⟨o, ho, he⟩ := List.mem_map.mp hmem
      have heq : o = ⟨.seat r i, data⟩ := by
        cases o; cases he; rfl
      subst o
      simp only [process, ha, hp, admitProposal, henter, ↓reduceIte, collectPCs_base]
      apply receiveHeads_base_mem_or_equivocates p _ _ r i data _ _ ho
      · simpa only [proposalBase_now] using hlo
      · simpa only [proposalBase_now] using hhi
    · obtain ⟨hready, hmem⟩ := hh
      obtain ⟨o, ho, he⟩ := List.mem_map.mp hmem
      have heq : o = ⟨.seat r i, data⟩ := by
        cases o; cases he; rfl
      subst o
      simp only [process, ha, hp, hready, ↓reduceIte, collectPCs_base, installPC]
      exact receiveHeads_base_mem_or_equivocates p st _ r i data hlo hhi ho

end AvailableChain.SAPC
end

module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Proofs.RowSelection

public section

namespace AvailableChain.FGSA

/-- Stores differ only by a permutation of the row pool. -/
def StoreSetEq {n : Nat} (st st' : State n) : Prop :=
  st' = { st with rowPool := st'.rowPool } ∧ st.rowPool.Perm st'.rowPool

/-- Admission uses only decoding and full-wire membership. -/
theorem admitRow_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (a : RowWire p.n) :
    StoreSetEq (admitRow p st a) (admitRow p st' a) := by
  obtain ⟨he, hp⟩ := h
  rw [he] at hp ⊢
  unfold admitRow
  cases hd : a.decode? with
  | none => exact ⟨rfl, hp⟩
  | some val =>
      simp only [hp.mem_iff]
      split
      · exact ⟨rfl, hp⟩
      · exact ⟨rfl, hp.append_right _⟩

/-- R7 selection preserves permutations of held content. -/
theorem proposalRows_perm_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (H : Block) :
    (proposalRows p st H).Perm (proposalRows p st' H) := by
  obtain ⟨he, hp⟩ := h
  rw [he] at hp ⊢
  change (proposalRowsFor p st (st.slot p) H).Perm
    (proposalRowsFor p { st with rowPool := st'.rowPool } (st.slot p) H)
  exact proposalRowsFor_perm p (st := st) (st' := { st with rowPool := st'.rowPool })
    rfl hp (List.Perm.refl _) _ _

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Row order preserves proposal failure or success.
Successful proposals have the same named parent, slot, votes and support, with permuted rows.
The packed bodies and roots can differ. This statement applies to arbitrary stores. -/
theorem propose_setEq (p : Params) {st st' : State p.n}
    (h : StoreSetEq st st') (s : Slot) :
    (propose p st s = none ∧ propose p st' s = none) ∨
      ∃ H raw sup rows rows', rows.Perm rows' ∧
        propose p st s = some (.proposal (namedProposal p H s 0 raw sup rows)) ∧
        propose p st' s = some (.proposal (namedProposal p H s 0 raw sup rows')) := by
  have hr := proposalRows_perm_setEq p h
  obtain ⟨he, _⟩ := h
  rw [he] at hr ⊢
  have hv : proposerVotes { st with rowPool := st'.rowPool } s = proposerVotes st s := rfl
  have hu : proposerSupport { st with rowPool := st'.rowPool } s = proposerSupport st s := rfl
  have hg (raw sup) : getHead p { st with rowPool := st'.rowPool } raw sup =
      getHead p st raw sup := rfl
  have hn (H) : namedByErase? { st with rowPool := st'.rowPool } H =
      namedByErase? st H := rfl
  by_cases hs : s = 0
  · exact Or.inl (by simp only [propose, hs, ↓reduceIte, and_self])
  · cases hN : namedByErase? st
        (getHead p st (proposerVotes st s) (proposerSupport st s)) with
    | none =>
        exact Or.inl (by
          simp only [propose, hs, ↓reduceIte, hv, hu, hg, hn, hN, Option.map_none, and_self])
    | some N =>
        refine Or.inr ⟨N, (proposerVotes st s).filterMap liftHead?,
          (proposerSupport st s).filterMap liftHead?, _, _,
          hr (getHead p st (proposerVotes st s) (proposerSupport st s)), ?_, ?_⟩ <;>
          simp only [propose, hs, ↓reduceIte, hv, hu, hg, hn, hN, Option.map_some]

end AvailableChain.FGSA
end

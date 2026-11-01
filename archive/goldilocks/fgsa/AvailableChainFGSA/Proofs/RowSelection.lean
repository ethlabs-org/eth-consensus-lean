module
public import AvailableChainFGSA.Model.RowSelection
public import AvailableChainFGSA.Proofs.RowValidity
public import AvailableChainGeneric.Proofs.AC.Votes

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The active selector is the R7 interface at the store's current slot. -/
theorem proposalRows_eq_proposalRowsFor (p : Params) (st : State p.n) (H : Block) :
    proposalRows p st H = proposalRowsFor p st (st.slot p) H := rfl

/-- [ROOT-DIGEST-2 W1; DC named rows]
Every block-row candidate has a stored proposal as its source. -/
theorem mem_allBlockRows_iff {n : Nat} (st : State n) (a : RowWire n) :
    a ∈ allBlockRows st ↔ ∃ o ∈ st.proposals, ∃ s N,
      o.decode = some (.block s N) ∧ a ∈ N.rows := by
  constructor
  · intro ha
    obtain ⟨rows, hr, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨o, ho, hd⟩ := List.mem_filterMap.mp hr
    cases he : o.decode with
    | none => rw [he] at hd; cases hd
    | some input =>
      cases input with
      | vote | row => rw [he] at hd; cases hd
      | block s N =>
        rw [he] at hd
        exact ⟨o, ho, s, N, he, (Option.some.inj hd) ▸ ha⟩
  · rintro ⟨o, ho, s, N, hd, ha⟩
    exact List.mem_flatten.mpr ⟨N.rows, List.mem_filterMap.mpr ⟨o, ho, by rw [hd]⟩, ha⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Selection has no result when the stored parent cannot be resolved. -/
theorem proposalRowsFor_missing (p : Params) (st : State p.n) (s : Slot) (H : Block)
    (h : fgBlockOf st H = none) : proposalRowsFor p st s H = [] := by
  delta proposalRowsFor proposalRowsCore
  rw [h]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
[R7] Membership is exactly held content, R6 validity, and exact chain absence. -/
theorem mem_proposalRowsFor_iff (p : Params) (st : State p.n) (s : Slot)
    (H : Block) (a : RowWire p.n) :
    a ∈ proposalRowsFor p st s H ↔ ∃ P, fgBlockOf st H = some P ∧
      (a ∈ st.rowPool ∨ a ∈ allBlockRows st) ∧
      Window.rowValidW (parentFoldState p s P) a = true ∧ a ∉ chainWireRows st H := by
  delta proposalRowsFor proposalRowsCore
  cases h : fgBlockOf st H <;> dsimp only <;> simp [List.mem_eraseDups]

private theorem eraseDups_sublist {α : Type} [DecidableEq α] (xs : List α) :
    xs.eraseDups.Sublist xs := by
  induction hlen : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => exact List.Sublist.refl _
    | cons a xs =>
      rw [List.eraseDups_cons]
      exact List.Sublist.cons_cons a
        ((ih _ (hlen ▸ Nat.lt_succ_of_le (List.length_filter_le _ _)) _ rfl).trans
          List.filter_sublist)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The selector returns each full signed row at most once. -/
theorem proposalRowsFor_nodup (p : Params) (st : State p.n) (s : Slot) (H : Block) :
    (proposalRowsFor p st s H).Nodup := by
  delta proposalRowsFor proposalRowsCore
  cases fgBlockOf st H with
  | none => exact List.nodup_nil
  | some P => exact (Gen.AC.vote_pool_eraseDups_nodup _).filter _

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Selected rows retain the order of their first held occurrences. -/
theorem proposalRowsFor_sublist (p : Params) (st : State p.n) (s : Slot) (H : Block) :
    (proposalRowsFor p st s H).Sublist (st.rowPool ++ allBlockRows st) := by
  delta proposalRowsFor proposalRowsCore
  cases fgBlockOf st H with
  | none => exact List.nil_sublist _
  | some P => exact List.filter_sublist.trans (eraseDups_sublist _)

/-- [ROOT-DIGEST-2 W1; DC named rows]
Every selected row comes from the pool or one admitted proposal. -/
theorem proposalRowsFor_origin (p : Params) (st : State p.n) (s : Slot)
    (H : Block) (a : RowWire p.n) (ha : a ∈ proposalRowsFor p st s H) :
    a ∈ st.rowPool ∨ ∃ o ∈ st.proposals, ∃ t N,
      o.decode = some (.block t N) ∧ a ∈ N.rows := by
  obtain ⟨_, _, ha, _⟩ := (mem_proposalRowsFor_iff p st s H a).mp ha
  exact ha.imp_right ((mem_allBlockRows_iff st a).mp)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Selection supplies the common-parent validity premise. -/
theorem proposalRowsFor_valid (p : Params) (st : State p.n) (s : Slot)
    (H : Block) (P : FGBlock (Fin p.n)) (hP : fgBlockOf st H = some P) :
    rowsValidForParent p P s (proposalRowsFor p st s H) = true := by
  rw [rowsValidForParent_iff]
  intro a ha
  obtain ⟨Q, hQ, _, hv, _⟩ := (mem_proposalRowsFor_iff p st s H a).mp ha
  have : Q = P := Option.some.inj (hQ.symm.trans hP)
  simpa [this] using hv

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An exact row on the parent chain is never selected. -/
theorem proposalRowsFor_excludes_chain (p : Params) (st : State p.n) (s : Slot)
    (H : Block) (a : RowWire p.n) (ha : a ∈ chainWireRows st H) :
    a ∉ proposalRowsFor p st s H := by
  intro hm
  obtain ⟨_, _, _, _, hn⟩ := (mem_proposalRowsFor_iff p st s H a).mp hm
  exact hn ha

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Reordering held rows keeps selector membership. The resulting list can
change order, and therefore its packed block root can change. -/
theorem proposalRowsFor_perm (p : Params) {st st' : State p.n}
    (hfg : st.fg = st'.fg) (hpool : st.rowPool.Perm st'.rowPool)
    (hprops : st.proposals.Perm st'.proposals) (s : Slot) (H : Block) :
    (proposalRowsFor p st s H).Perm (proposalRowsFor p st' s H) := by
  have hb : (allBlockRows st).Perm (allBlockRows st') :=
    (hprops.filterMap _).flatten
  have hc : (chainWireRows st H).Perm (chainWireRows st' H) :=
    (hprops.filterMap _).flatten
  apply (List.perm_ext_iff_of_nodup (proposalRowsFor_nodup p st s H)
    (proposalRowsFor_nodup p st' s H)).mpr
  intro a
  have hP : fgBlockOf st H = fgBlockOf st' H := by
    delta fgBlockOf
    rw [hfg]
  simp only [mem_proposalRowsFor_iff, hP, hpool.mem_iff, hb.mem_iff, hc.mem_iff]

end AvailableChain.FGSA
end

module
public import AvailableChainFGSA.Proofs.Metadata

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

private theorem admission_r6wW (p : Params) (st : State p.n) (h : CStoreInv p st)
    (valid : ∀ P s r_s x rs, FGBlock.node P s r_s x rs ∈ st.fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true)
    (s : Slot) (N : NamedProposal p.n) :
    ∀ P t r_t x rs, FGBlock.node P t r_t x rs ∈ (admitBlock p st s N).fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  by_cases hNamed : namedParentHeld st N = true
  swap
  · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
    exact valid
  cases hP : parentFG st N.erase with
  | none =>
      rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
      exact valid
  | some P =>
      cases accepted : blockAccepted p st s N P with
      | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, accepted⟩))]
          exact valid
      | true =>
          obtain ⟨pool, eq, _⟩ := admitBlock_accepted_eq p st s N P hNamed hP
            accepted
          intro Q t r_t x rs stored a ha
          rw [eq] at stored
          dsimp only at stored
          rw [(accepted_st2 p st h s N P hP accepted).2.1,
            Finset.mem_insert] at stored
          rcases stored with new | old
          · change FGBlock.node Q t r_t x rs = .node P N.erase.slot N.erase.root (packInner (appOf
            N.erase.body) N.rows)
              (N.rows.filterMap RowWire.toRow?) at new
            cases new
            obtain ⟨wire, hw, hd⟩ := List.mem_filterMap.mp ha
            have hv := (rowsValidForParent_iff p P N.erase.slot N.rows).mp
              (blockAccepted_rowsValid accepted) wire hw
            rw [Window.rowValidW_def, hd] at hv
            exact hv
          · exact valid Q t r_t x rs old a ha

private theorem process_r6wW (p : Params) (st : State p.n) (h : CStoreInv p st)
    (valid : ∀ P s r_s x rs, FGBlock.node P s r_s x rs ∈ st.fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true) (o : Wire p.n) :
    ∀ P s r_s x rs, FGBlock.node P s r_s x rs ∈ (process p st o).fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  change ∀ P s r_s x rs, FGBlock.node P s r_s x rs ∈ (match o.decode with
    | some (.vote t i b) => admitHead p st t i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block t N) => admitBlock p st t N
    | none => st).fg.TF → ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true
  cases decoded : o.decode with
  | none => exact valid
  | some input =>
      cases input with
      | vote t i b => exact valid
      | row i body =>
          change ∀ P s r_s x rs,
            FGBlock.node P s r_s x rs ∈ (admitRow p st ⟨o.auth, body⟩).fg.TF →
              ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true
          rcases admitRow_eq p st ⟨o.auth, body⟩ with eq | eq <;> rw [eq] <;> exact valid
      | block t N => exact admission_r6wW p st h valid t N

/-- [ROOT-DIGEST-2 W1; DC named rows]
[S4.2b r2 ruling] Every stored non-genesis block has R6W-valid decoded
rows at its immutable parent. Unchecked Reachable deliveries suffice for R6W.
This is a separate invariant; no field is added to either store invariant. -/
theorem stored_r6wW (p : Params) {st : State p.n} (reachable : Reachable p st) :
    ∀ P s r_s x rs, FGBlock.node P s r_s x rs ∈ st.fg.TF →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  induction reachable with
  | init =>
      intro P s r_s x rs stored
      change FGBlock.node P s r_s x rs ∈ ({.genesis} : Finset (FGBlock (Fin p.n))) at stored
      simp only [Finset.mem_singleton] at stored
      cases stored
  | restart w _ ih => exact ih
  | tick t _ ih =>
      simpa only [clock_fg] using ih
  | deliver o reachable ih =>
      exact process_r6wW p _ (storeInvariant p _ reachable) ih o

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Tree closure extends the new admission invariant to every ancestor row
of a stored block, at the active window parent view. -/
theorem stored_chain_r6wW (p : Params) {st : State p.n} (reachable : Reachable p st)
    (B : FGBlock (Fin p.n)) (stored : B ∈ st.fg.TF) :
    ∀ P s r_s x rs, FGBlock.Preceq (.node P s r_s x rs) B →
      ∀ a ∈ rs, Window.r6w (Window.derive p p.K_W P) a = true := by
  intro P s r_s x rs ancestor a ha
  have closed := KitFG.ancestor_closed_of_parent_closed st.fg.TF
    (storeInvariant p st reachable).fg.closed
  exact stored_r6wW p reachable P s r_s x rs (closed B stored _ ancestor) a ha

end AvailableChain.FGSA
end

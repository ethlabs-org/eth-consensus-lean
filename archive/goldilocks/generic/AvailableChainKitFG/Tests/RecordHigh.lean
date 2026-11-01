module
public import AvailableChainKitFG.RecordHigh -- shake: keep (axioms)

public section

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.RecordHigh

open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3: close the finite table before checking distinct roots. -/
theorem finite_view_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T := by
  rintro X Y ⟨W, hW, hX⟩ ⟨U, hU, hY⟩ hr
  exact hinj X (ancestor_closed_of_parent_closed T hcl W hW X hX)
    Y (ancestor_closed_of_parent_closed T hcl U hU Y hY) hr

-- The initial record supports every inclusive cut, including zero.
example (h0 : Height) (entry : Height → BlockId) : HighRecord h0 entry Record.initial := by
  intro h _
  exact ⟨Or.inl rfl, rfl, Or.inl rfl⟩

-- A source exactly at the cut writes a target and a same-row finality lock.
example :
    HighRecord 2 (fun _ => B1.root)
      (record_row Record.initial (clientRow Record.initial (0 : Fin 4)
        (some (2, B1.root)) ⟨2, B1.root, 0⟩)) := by
  apply (recordHigh 2 (fun _ => B1.root) Record.initial (0 : Fin 4)
    (some (2, B1.root)) ⟨2, B1.root, 0⟩
    (fun _ _ => ⟨Or.inl rfl, rfl, Or.inl rfl⟩) ?_ ?_).1
  · intro h T hf _
    cases hf
    rfl
  · intro fp hfp _
    exact congrArg FinalityPair.target (finality_pair_record_conditions hfp).1

example :
    (clientRow Record.initial (0 : Fin 4) (some (2, B1.root))
      ⟨2, B1.root, 0⟩).height_pair = .vote 2 B1.root false ∧
    (record_row Record.initial (clientRow Record.initial (0 : Fin 4)
      (some (2, B1.root)) ⟨2, B1.root, 0⟩)).lock 2 = some B1.root := by
  decide +kernel

-- A stored lock and a stored target repeat the canonical target at the cut.
example (Λ : Record) (hΛ : HighRecord 2 (fun _ => B1.root) Λ) :
    ∀ h T timeout,
      (clientRow Λ (0 : Fin 4) (some (2, B1.root)) clientHdNone).height_pair =
        .vote h T timeout → 2 ≤ h → T = B1.root ∧ timeout = false := by
  apply (recordHigh 2 (fun _ => B1.root) Λ (0 : Fin 4)
    (some (2, B1.root)) clientHdNone hΛ ?_ ?_).2
  · intro h T hf _
    cases hf
    rfl
  · intro fp hfp hh
    have heq := (finality_pair_record_conditions hfp).1
    have hheight := congrArg FinalityPair.height heq
    change fp.height = 0 at hheight
    simp only [Height] at *
    omega

example :
    (clientRow (Record.initial.with_lock 2 B1.root) (0 : Fin 4)
      (some (2, B1.root)) clientHdNone).height_pair = .vote 2 B1.root false ∧
    (clientRow (Record.initial.with_target 2 B1.root) (0 : Fin 4)
      (some (2, B1.root)) clientHdNone).height_pair = .vote 2 B1.root false := by
  decide +kernel

-- A timeout below the cut remains allowed; a timeout at the cut is excluded.
example : HighRecord 2 (fun _ => B1.root) (Record.initial.with_timeout 1) := by
  intro h hh
  refine ⟨Or.inl rfl, ?_, Or.inl rfl⟩
  change (if h = 1 then true else false) = false
  rw [ite_eq_right (by simp only [Height] at *; omega)]

example : ¬ HighRecord 2 (fun _ => B1.root) (Record.initial.with_timeout 2) := by
  intro h
  have ht := (h 2 (by simp only [Height] at *; omega)).2.1
  change true = false at ht
  cases ht

-- A real contest at H = h0 is allowed. Its conflicting rows are below the cut.
example : (fjControls E4 cfg1 .genesis {childA, Y}).H ≤ 3 := by
  apply noHighContest E4 cfg1 3 (fun _ => B1.root) ∅
    (chainRows childA ∪ chainRows Y) .genesis {childA, Y}
    (viewRootInj_mono (finite_view_roots {.genesis, B1, B1b, childA, Y}
      (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel) ?_ ?_ (by
          decide +kernel)
  · intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · have hsmall : ∀ a ∈ chainRows childA ∪ chainRows Y,
        a.height_pair = .vote 1 genesisRoot false ∨
        a.height_pair = .vote 2 B1.root false ∨
        a.height_pair = .vote 2 B1b.root false ∨
        a.height_pair = .vote 2 B1b.root true := by
      decide +kernel
    intro a ha _ h T timeout hp hh
    rcases hsmall a ha with heq | heq | heq | heq <;>
      rw [heq] at hp <;> cases hp <;> simp only [Height] at hh <;> omega

example : (fjControls E4 cfg1 .genesis {childA, Y}).contest = true ∧
    (fjControls E4 cfg1 .genesis {childA, Y}).H = 3 := by decide +kernel

-- At the protected height, a canonical target quorum excludes the contest.
example : (fjControls E4 cfg1 .genesis {childA}).contest = false := by
  cases hc : (fjControls E4 cfg1 .genesis {childA}).contest with
  | false => rfl
  | true =>
      have hbound := noHighContest E4 cfg1 2 (fun _ => B1.root) {3}
        (chainRows childA) .genesis {childA}
        (viewRootInj_mono (finite_view_roots {.genesis, B1, B1b, childA, Y}
      (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)
        (by intro W hW; rw [Finset.mem_singleton.mp hW])
        (by
          have hknown : ∀ a ∈ chainRows childA,
              a.height_pair = .vote 1 genesisRoot false ∨
              a.height_pair = .vote 2 B1.root false := by decide +kernel
          intro a ha _ h T timeout hp hh
          rcases hknown a ha with heq | heq
          · rw [heq] at hp
            cases hp
            simp only [Height] at hh
            omega
          · rw [heq] at hp
            cases hp
            exact ⟨rfl, rfl⟩) hc
      have hh : (fjControls E4 cfg1 .genesis {childA}).H = 3 := by decide +kernel
      simp only [Height] at *
      omega

-- An empty candidate set falls back to genesis, also at the zero cut.
example : (fjControls E4 cfg1 B1 {.genesis}).contest = false := by
  cases hc : (fjControls E4 cfg1 B1 {.genesis}).contest with
  | false => rfl
  | true =>
      have hbound := noHighContest E4 cfg1 0 (fun _ => genesisRoot) ∅ ∅ B1
        {.genesis} (finite_view_roots _ (by decide +kernel) (by decide +kernel))
        (by decide +kernel) (by decide +kernel)
        (by intro a ha; exact (Finset.notMem_empty a ha).elim) hc
      have hh : (fjControls E4 cfg1 B1 {.genesis}).H = 1 := by decide +kernel
      simp only [Height] at *
      omega

-- The two paper bounds use the same inclusive API.
example (μ y : Height) : μ < y ↔ μ + 1 ≤ y := by simp only [Height] at *; omega
example (μ H j : Height) (hc : H = j + 1) : H ≤ μ + 1 ↔ ¬ μ < j := by
  simp only [Height] at *
  omega
example (M H j : Height) (hc : H = j + 1) : H ≤ M + 1 ↔ ¬ M + 1 ≤ j := by
  simp only [Height] at *
  omega

end AvailableChain.KitFG.Tests.RecordHigh
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.KitFG.Tests.RecordHigh.finite_view_roots

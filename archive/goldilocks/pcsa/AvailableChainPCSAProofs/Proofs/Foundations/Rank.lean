module
public import AvailableChainPCSA.Model.Store
public import AvailableChainGeneric.Proofs.Pure.PCRank

public section

/-! The store's PC choice and the Generic rank order (pcsa34-r4.3 §2.3).
The adapter keeps the concrete PC as its target. Rank arithmetic stays in
Generic Pure/PCRank. -/

namespace AvailableChain.PCSA
variable {n : Nat}

private def rankView (c : PC n) : Gen.Pure.PC n (PC n) := ⟨c.slot, c, ∅⟩
private def rankKey (c : Gen.Pure.PC n (PC n)) : Nat ×ₗ BlockId :=
  toLex (c.target.target.depth, c.target.target.root)

/-- The concrete comparison is the Generic strict rank comparison. -/
private theorem pcBelow_rankLT (a b : PC n) :
    pcBelow a b = true ↔ Gen.Pure.RankLT rankKey (rankView a) (rankView b) := by
  rw [Gen.Pure.RankLT_def]
  dsimp only [pcBelow, rankView, rankKey]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Prod.Lex.toLex_lt_toLex]

/-- PC choice commutes with the Generic rank adapter. -/
private theorem preferPC_rankView (old : Option (PC n)) (c : PC n) :
    (preferPC old c).map rankView = Gen.Pure.preferPC rankKey (old.map rankView) (rankView c) := by
  cases old with
  | none => rfl
  | some a =>
    simp only [Option.map_some]
    rw [Gen.Pure.preferPC_some]
    unfold preferPC
    dsimp only
    by_cases h : pcBelow a c = true
    · rw [ite_eq_left h, Gen.Pure.pickPC_of_rankLT ((pcBelow_rankLT a c).mp h)]
      rfl
    · rw [ite_eq_right h, Gen.Pure.pickPC_of_not_rankLT
        (fun h' => h ((pcBelow_rankLT a c).mpr h'))]
      rfl

/-- One candidate makes the stored choice nonempty. -/
theorem pcsa_preferPC_isSome (old : Option (PC n)) (c : PC n) :
    (preferPC old c).isSome = true := by
  have h := Gen.Pure.preferPC_isSome (key := rankKey) (old.map rankView) (rankView c)
  rw [← preferPC_rankView] at h
  cases he : preferPC old c <;> simp_all

/-- A chosen PC was held or is the supplied candidate. -/
theorem pcsa_preferPC_eq_or (old : Option (PC n)) (c d : PC n)
    (h : preferPC old c = some d) : old = some d ∨ c = d := by
  have hh := congrArg (Option.map rankView) h
  rw [preferPC_rankView] at hh
  obtain hh | hh := Gen.Pure.preferPC_eq_or hh
  · cases old with
    | none => simp at hh
    | some a =>
      left
      exact congrArg some (congrArg Gen.Pure.PC.target (Option.some.inj hh))
  · exact Or.inr (congrArg Gen.Pure.PC.target hh)

/-- Offering the same PC again does not change the choice. -/
theorem pcsa_preferPC_idem (old : Option (PC n)) (c : PC n) :
    preferPC (preferPC old c) c = preferPC old c := by
  have h := Gen.Pure.preferPC_idem (key := rankKey) (old.map rankView) (rankView c)
  rw [← preferPC_rankView, ← preferPC_rankView] at h
  have he := congrArg (Option.map Gen.Pure.PC.target) h
  simp only [Option.map_map, Function.comp_def] at he
  dsimp only [rankView] at he
  simpa using he

/-- Every result of the PC fold is in its input or its initial choice. -/
theorem foldl_preferPC_mem (cs : List (PC n)) (old : Option (PC n)) (c : PC n)
    (h : cs.foldl preferPC old = some c) : c ∈ cs ∨ old = some c := by
  induction cs generalizing old with
  | nil => exact Or.inr h
  | cons a cs ih =>
    obtain hm | hm := ih (preferPC old a) h
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · obtain hm | hm := pcsa_preferPC_eq_or old a c hm
      · exact Or.inr hm
      · exact Or.inl (List.mem_cons.mpr (Or.inl hm.symm))

/-- The best PC is held in the input list. -/
theorem bestPC_mem (cs : List (PC n)) (c : PC n) (h : bestPC cs = some c) : c ∈ cs := by
  obtain h | h := foldl_preferPC_mem cs none c h
  · exact h
  · contradiction

/-- The empty input has no best PC. -/
theorem bestPC_nil : bestPC ([] : List (PC n)) = none := rfl

/-- A one-PC input selects that PC. -/
theorem bestPC_singleton (c : PC n) : bestPC [c] = some c := rfl

end AvailableChain.PCSA
end

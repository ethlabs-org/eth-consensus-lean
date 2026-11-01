module
public import AvailableChainGeneric.Proofs.Pure.ScheduleW -- shake: keep (concrete examples and axiom audit commands)

public section

namespace AvailableChain.Gen.Pure

example : FGoodE_W (fun s => 0 < s) 3 3 1 :=
  ⟨by decide, by decide, ⟨9, by decide, by decide, by decide⟩, by decide⟩

example : FGood4_W (fun s => 0 < s) 3 3 1 :=
  ⟨⟨by decide, by decide, ⟨9, by decide, by decide, by decide⟩, by decide⟩, by decide⟩

example : Tail_W (fun s => 0 < s) 3 3 1 :=
  ⟨by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩

/-- Each eligible window has a witness, including the first nonempty search. -/
example : RecFE_W (fun s => 0 < s) 3 3 12 1 12 0 61 1 := by
  refine ⟨by decide, ?_⟩
  intro q hq _ _
  refine ⟨q, ⟨le_rfl, by omega⟩, ?_⟩
  rw [FGoodE_W_def]
  exact ⟨by change (0 : Nat) < q * 3; omega,
    by change (0 : Nat) < (q + 1) * 3; omega,
    ⟨(q + 2) * 3, by omega, le_rfl, by change (0 : Nat) < (q + 2) * 3; omega⟩,
    by change (0 : Nat) < (q + 2) * 3 + 3; omega⟩

example : RecF4_W (fun s => 0 < s) 3 3 12 1 12 0 61 1 := by
  refine ⟨by decide, ?_⟩
  intro q hq _ _
  refine ⟨q, ⟨le_rfl, by omega⟩, ?_⟩
  rw [FGood4_W_def, FGoodE_W_def]
  exact ⟨⟨by change (0 : Nat) < q * 3; omega,
    by change (0 : Nat) < (q + 1) * 3; omega,
    ⟨(q + 2) * 3, by omega, le_rfl, by change (0 : Nat) < (q + 2) * 3; omega⟩,
    by change (0 : Nat) < (q + 2) * 3 + 3; omega⟩,
    by change (0 : Nat) < (q + 1) * 3 + 3; omega⟩

example : (1 : Nat) ≤ 1 ∧ (0 : Time) ≤ 1 * 12 ∧
    ((1 : Time) + 1 + 1) * 12 + 12 + 1 ≤ 61 := by decide

example : FGoodE_W (fun s => 0 < s) 2 2 1 :=
  ⟨by decide, by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩

/-- The fourth slot supplies the carrier even at the smallest allowed R. -/
example : FGood4_W (fun s => s = 2 ∨ s = 4 ∨ s = 6 ∨ s = 8) 2 2 1 := by
  apply (fgood4_W_two_iff _ _ _ (by decide)).2
  exact ⟨⟨by decide, by decide, by decide⟩, by decide⟩

example : FGoodE_W (fun s => 0 < s) 3 3 1 ↔ FGood4_W (fun s => 0 < s) 3 3 1 :=
  fgoodE_W_full_round_iff _ _ _

/-- At horizon 32 the first receipt is outside the search; at 33 it is included. -/
example : RecF4_W (fun _ => False) 2 2 8 1 8 0 32 1 := by
  refine ⟨by decide, ?_⟩
  intro q hq _ hw
  change ((q : Int) + 1 + 1) * 8 + 8 + 1 ≤ 32 at hw
  exfalso
  omega

example : ¬ RecF4_W (fun _ => False) 2 2 8 1 8 0 33 1 := by
  intro h
  obtain ⟨r, _, hr⟩ := h.2 1 (by decide) (by decide) (by decide)
  exact hr.1.1

/-- The old recurrence and FinForm use the same finite receipt guard. -/
example (H : Slot → Prop) :
    RecF4_W H 2 2 8 1 8 0 33 1 ↔ RecF4 H 2 8 1 0 33 1 :=
  recF4_W_two_iff H 2 8 1 0 33 1 (by decide)

example (H : Slot → Prop) :
    RecF4_W H 2 2 8 1 8 0 33 1 ↔ FinForm.recF4.holds H 2 8 1 0 33 1 :=
  recF4_W_two_iff_holds H 2 8 1 0 33 1 (by decide)

#print axioms fgood4_W_implies_fgoodE_W
#print axioms recF4_W_implies_recFE_W
#print axioms fgoodE_W_two
#print axioms fgood4_W_two
#print axioms tail_W_two
#print axioms recFE_W_eight_delta
#print axioms recFE_W_extract
#print axioms recFE_W_receipt_lt

end AvailableChain.Gen.Pure

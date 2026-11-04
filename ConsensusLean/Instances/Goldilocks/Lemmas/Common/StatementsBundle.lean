module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Claims
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Goldilocks: the Common statements, assembled

`CommonStatements` (`Lemmas/Common/Claims`): F.2 (a), (b) are `Anc.antisymm` and `Anc.total`;
F.2 (c), the deepest common ancestor, is the common ancestor of greatest slot (the common
ancestors of `B` lie on the chain of ancestors of `B`, with slots at most `B.slot`); F.3 is the
injectivity of the digest's content; and the slot of a time is the greatest slot that starts by
it (`slotTime s ≥ s`, from `slotTime 0 = 0` and strict monotonicity). -/

namespace Consensus.Goldilocks

/-- **F.2 (c).** -/
theorem deepest_common_ancestor : DeepestCommonAncestor := by
  classical
  rw [deepestCommonAncestor_iff]
  intro n FGP ACP S R B C hS hRB hRC
  let P : Nat → Prop := fun k => ∃ D, Anc S D B ∧ Anc S D C ∧ D.slot = k
  have hR : P R.slot := ⟨R, hRB, hRC, rfl⟩
  have hRle : R.slot ≤ B.slot := (hRB.slot_le hS).1
  obtain ⟨D, hDB, hDC, hDs⟩ := Nat.findGreatest_spec (P := P) hRle hR
  refine ⟨D, hDB, hDC, fun D' hD'B hD'C => ?_⟩
  rcases hD'B.total hS hDB with h | h
  · exact h
  · by_cases hne : D = D'
    · exact hne ▸ .refl
    · have hlt := (h.slot_le hS).2 hne
      have hle : D'.slot ≤ Nat.findGreatest P B.slot :=
        Nat.le_findGreatest (hD'B.slot_le hS).1 ⟨D', hD'B, hD'C, rfl⟩
      omega

/-- **F.3.** -/
theorem digest_determines_block : DigestDeterminesBlock := by
  rw [digestDeterminesBlock_iff]
  intro n FGP ACP dg B C hcoll hB hC hr hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcoll (hB.symm.trans (hr.trans hC))
  cases B
  cases C
  simp_all

/-- `slotTime s ≥ s`: start times are strictly increasing integers from `0`. -/
private theorem le_slotTime (P : Params) (s : Nat) : (s : Time) ≤ P.slotTime s := by
  induction s with
  | zero => rw [P.slotTime_zero]; rfl
  | succ s ih =>
    have h : P.slotTime s < P.slotTime (s + 1) := P.slotTime_strictMono (Nat.lt_succ_self s)
    have h' : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by push_cast; rfl
    change ((s + 1 : Nat) : Int) ≤ P.slotTime (s + 1)
    rw [h']
    exact Int.add_one_le_of_lt (lt_of_le_of_lt ih h)

/-- **The slot of a time.** -/
theorem slotOf_spec : SlotOfSpec := by
  rw [slotOfSpec_iff]
  intro P t ht
  have h0 : P.slotTime 0 ≤ t := by rw [P.slotTime_zero]; exact ht
  refine ⟨Nat.findGreatest_spec (P := fun s => P.slotTime s ≤ t) (Nat.zero_le _) h0, ?_⟩
  by_contra hle
  push Not at hle
  have hs : ((P.slotOf t + 1 : Nat) : Int) ≤ t := (le_slotTime P (P.slotOf t + 1)).trans hle
  have hle' : P.slotOf t + 1 ≤ t.toNat := by omega
  have := Nat.le_findGreatest (P := fun s => P.slotTime s ≤ t) hle' hle
  change P.slotOf t + 1 ≤ P.slotOf t at this
  omega

/-- **The Common statements.** -/
theorem common_statements : CommonStatements where
  ancAntisymm := ancAntisymm_iff.mpr fun _ _ _ _ _ _ hS h h' => Anc.antisymm hS h h'
  ancTotal := ancTotal_iff.mpr fun _ _ _ _ _ _ _ hS h h' => Anc.total hS h h'
  deepestCommonAncestor := deepest_common_ancestor
  digestDeterminesBlock := digest_determines_block
  slotOfSpec := slotOf_spec

end Consensus.Goldilocks

end

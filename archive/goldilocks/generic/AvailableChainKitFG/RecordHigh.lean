module
public import AvailableChainKitFG.RecordHighDef
public import AvailableChainKitFG.ClientSafety
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- One client write keeps the high record guards and emits no high timeout.
DC: ValidatorClient/W4FKChainFinalityRows.lean:115–129 (guard consumer).
INTENTIONAL: H1 and the record induction supply the guard; record
TS blueprint/22-finality.md:770–773. H.13 uses h0 = μ+1; FF2 uses h0 = M+1
(TS blueprint/21-healing.md:2563–2575; blueprint/22-finality.md:735–741). -/
theorem recordHigh : RecordHighStatement := by
  intro V h0 entry Λ signer fields hd hΛ hfields hfinal
  let a : Row V := ⟨signer, height_pair Λ fields (finality_pair Λ hd), finality_pair Λ hd⟩
  have hlock : ∀ h, h0 ≤ h →
      own_lock Λ h (finality_pair Λ hd) = none ∨
        own_lock Λ h (finality_pair Λ hd) = some (entry h) := by
    intro h hh
    cases hfp : finality_pair Λ hd with
    | none => exact (hΛ h hh).2.2
    | some fp =>
        by_cases heq : fp.height = h
        · have hentry := hfinal fp hfp (heq ▸ hh)
          right
          change (if fp.height = h then some fp.target else Λ.lock h) = some (entry h)
          rw [ite_eq_left heq, hentry, heq]
        · change (if fp.height = h then some fp.target else Λ.lock h) = none ∨
            (if fp.height = h then some fp.target else Λ.lock h) = some (entry h)
          rw [ite_eq_right heq]
          exact (hΛ h hh).2.2
  have hrow : ∀ h T timeout, a.height_pair = .vote h T timeout → h0 ≤ h →
      T = entry h ∧ timeout = false := by
    intro h T timeout hp hh
    have hf := height_pair_vote_fields hp
    have hT := hfields h T hf hh
    refine ⟨hT, ?_⟩
    rcases hlock h hh with hn | hs
    · change height_pair Λ fields (finality_pair Λ hd) = .vote h T timeout at hp
      rw [hf] at hp
      have heq : height_pair Λ (some (h, T)) (finality_pair Λ hd) =
          .vote h T false := by
        change (if Λ.timeout h then .vote h T true else
          match own_lock Λ h (finality_pair Λ hd) with
          | some locked => if locked = T then .vote h T false else .empty
          | none => match Λ.target h with
            | some recorded => if recorded = T then .vote h T false else .vote h T true
            | none => .vote h T false) = (NamedHeightPair.vote h T false)
        rw [(hΛ h hh).2.1, hn]
        rcases (hΛ h hh).1 with ht | ht <;> rw [ht] <;>
          simp only [hT, Bool.false_eq_true, ↓reduceIte]
      rw [heq] at hp
      exact (NamedHeightPair.vote.inj hp).2.2.symm
    · exact (height_pair_of_own_lock (hΛ h hh).2.1 hs hp).1
  refine ⟨?_, hrow⟩
  intro h hh
  refine ⟨record_row_target_compatible_of Λ a (hΛ h hh).1
    (fun T hp => (hrow h T false hp hh).1), ?_, ?_⟩
  · apply record_row_timeout_false_of_ne Λ a (hΛ h hh).2.1
    intro T hp
    exact Bool.noConfusion (hrow h T true hp hh).2
  · rw [record_row_lock]
    exact hlock h hh

/-- The justification and crossing quorums name the same high entry.
DC: none; INTENTIONAL addition: FJ contest replaces DC's NJ case; record
TS blueprint/21-healing.md:2579–2581. H.13 gives H ≤ μ+1, which excludes
j > μ in a contest; FF2 gives H ≤ M+1 (TS blueprint/22-finality.md:775–779). -/
theorem noHighContest : NoHighContestStatement := by
  intro V _ _ _ E cfg h0 entry faulty A F vw hinj hcap hrows hhigh hcontest
  change (decide (frontier E cfg vw = (lexMax E cfg F vw).1 + 1) &&
    decide (∃ W ∈ vw, hOf E cfg W = frontier E cfg vw ∧
      ¬ FGBlock.Preceq (lexMax E cfg F vw).2 W)) = true at hcontest
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcontest
  obtain ⟨hH, W, hW, hWh, hnot⟩ := hcontest
  change frontier E cfg vw ≤ h0
  by_contra hbound
  have hj : h0 ≤ (lexMax E cfg F vw).1 := by
    simp only [Height] at hH hbound ⊢
    omega
  by_cases hex : ∃ K ∈ vw, FGBlock.Preceq F (derive E cfg K).J
  · obtain ⟨K, hK, _, hlex, _⟩ := lexMax_spec E cfg F vw hinj hex
    rw [hlex] at hH hj hnot
    dsimp only at hH hj hnot
    by_cases hz : (derive E cfg K).h_j = 0
    · rw [justified_zero_is_genesis E cfg K hz] at hnot
      exact hnot (genesis_preceq W)
    · obtain ⟨Qj, hQj, hwj⟩ := justification_certificate E cfg K hz
      obtain ⟨i, hi, hif⟩ := honest_in_quorum E faulty hQj hcap
      obtain ⟨carrier, a, hac, ha, hai, hap⟩ := hwj i hi
      have hJ := (hhigh a (hrows K hK (mem_chainRows_of_carrier hac ha))
        (hai ▸ hif) _ _ false hap hj).1
      have hlt : (derive E cfg K).h_j < (derive E cfg W).h := by
        change (derive E cfg W).h = frontier E cfg vw at hWh
        simp only [Height] at hWh hH ⊢
        omega
      obtain ⟨X, hXW, _, Qx, hQx, hwx⟩ :=
        height_crossing E cfg W _ (Nat.one_le_iff_ne_zero.mpr hz) hlt
      obtain ⟨k, hk, hkf⟩ := honest_in_quorum E faulty hQx hcap
      obtain ⟨crossing, b, hbc, hb, hbk, hbp⟩ := hwx k hk
      have hbA := hrows W hW (mem_chainRows_of_carrier hbc hb)
      cases hp : b.height_pair with
      | empty =>
          rw [hp] at hbp
          change false = true at hbp
          cases hbp
      | vote g T timeout =>
          rw [hp] at hbp
          change decide (g = (derive E cfg K).h_j ∧ T = X.root) = true at hbp
          have hm := of_decide_eq_true hbp
          have hX := (hhigh b hbA (hbk ▸ hkf) g T timeout hp (hm.1 ▸ hj)).1
          have hroot : X.root = (derive E cfg K).J.root := by
            rw [← hm.2, hX, hm.1, hJ]
          exact hnot ((hinj X (derive E cfg K).J ⟨W, hW, hXW⟩
            ⟨K, hK, (derive_anchors_preceq E cfg K).2⟩ hroot) ▸ hXW)
  · have hlex := lexMax_of_none E cfg F vw (fun K hK hFK => hex ⟨K, hK, hFK⟩)
    rw [hlex] at hnot
    exact hnot (genesis_preceq W)

end AvailableChain.KitFG
end

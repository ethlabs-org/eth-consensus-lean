module
public import AvailableChainFGSAClaims.Statements.Fold
public import AvailableChainFGSARun.Proofs.ClientTrace

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

variable [Fintype V]

omit [Fintype V] in
/-- FINAL 22:948–958. Membership in the linked-seat filter.
DC: INTENTIONAL: FG-SA uses linked seats. -/
theorem kmid_honestSeats_mem (i : Fin p.n) :
    i ∈ honestSeats p c rho ↔ rho.seatOf (.base .fg) i ∈ rho.honest := by
  have hdef : honestSeats p c rho =
      @Finset.filter (Fin p.n) (fun i => rho.seatOf (.base .fg) i ∈ rho.honest)
        (fun i => Classical.propDecidable (rho.seatOf (.base .fg) i ∈ rho.honest))
        Finset.univ := honestSeats_def p c rho
  rw [hdef]
  simpa only [Finset.mem_univ, true_and] using
    (@Finset.mem_filter (Fin p.n) (fun k => rho.seatOf (.base .fg) k ∈ rho.honest)
      (fun k => Classical.propDecidable (rho.seatOf (.base .fg) k ∈ rho.honest))
      Finset.univ i)

/-- FINAL 22:593–598. Under the recovery fault bound the honest seats form a quorum.
DC: INTENTIONAL: FG-SA uses linked unit-weight seats. -/
theorem kmid_honest_quorum (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3) :
    p.E.IsQuorum (honestSeats p c rho) := by
  classical
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have himage : (honestSeats p c rho).image (rho.seatOf (.base .fg)) = rho.honest := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (kmid_honestSeats_mem p c rho i).mp hi
    · intro hx
      have hs : rho.seatOf (.base .fg) (e.symm x) = x := by
        have h := he (e.symm x)
        rw [Equiv.apply_symm_apply] at h
        exact h
      refine Finset.mem_image.mpr ⟨e.symm x, ?_, hs⟩
      apply (kmid_honestSeats_mem p c rho _).mpr
      rw [hs]
      exact hx
  have hinj : Function.Injective (rho.seatOf (.base .fg)) :=
    (hL.toCStar (.base .fg) trivial).1
  have hcard : (honestSeats p c rho).card = rho.honest.card := by
    have h := Finset.card_image_of_injective (honestSeats p c rho) hinj
    exact h.symm.trans (congrArg Finset.card himage)
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hb := Finset.card_le_univ rho.honest
    rw [hn] at hb
    omega
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
  change p.E.q ≤ p.E.weightOf (honestSeats p c rho)
  have hw : p.E.weightOf (honestSeats p c rho) = (honestSeats p c rho).card := by
    change (∑ _ ∈ honestSeats p c rho, (1 : Nat)) = _
    simp
  rw [hq, hw, hcard, Gen.Pure.qF_def]
  have := p.nPos
  omega

end AvailableChain.FGSA.Run
end

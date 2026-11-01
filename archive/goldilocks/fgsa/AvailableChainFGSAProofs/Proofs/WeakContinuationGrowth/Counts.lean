module
public import AvailableChainFGSAClaims.Statements.WeakContinuationGrowth

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure Gen.V2.Duty

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- DC weak participation: linked unit seats give a strict half cap. -/
theorem wcg_half_of_participation
    (hlinked : V2.D.Linked (fgsaFamilies p c).linked rho) {t : Time}
    (hpart : (faulty rho).card < (awakeHonest E rho t).card) :
    2 * (faulty rho).card < p.n := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hlinked.toCStar trivial).symm
  have hawake : (awakeHonest E rho t).card ≤ rho.honest.card := by
    rw [awakeHonest_def]
    exact Finset.card_filter_le _ _
  have hcard : (faulty rho).card + rho.honest.card = p.n := by
    rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hh := Finset.card_le_univ rho.honest
    omega
  omega

/-- The sleep denominator gives the half cap directly from joined members. -/
theorem wcg_half_of_joined_participation
    (hlinked : V2.D.Linked (fgsaFamilies p c).linked rho) {t : Time}
    (hpart : (faulty rho).card < (joinedHonest p E rho t).card) :
    2 * (faulty rho).card < p.n := by
  classical
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hlinked.toCStar trivial).symm
  have hjoined : (joinedHonest p E rho t).card ≤ rho.honest.card :=
    Finset.card_filter_le _ _
  have hcard : (faulty rho).card + rho.honest.card = p.n := by
    rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    have hh := Finset.card_le_univ rho.honest
    omega
  omega

/-- DC one-quorum origin: the half cap implies FaultQ, without FaultX. -/
theorem wcg_faultQ_of_half {a : Nat} (hhalf : 2 * a < p.n) :
    FaultQ p.n a := by
  constructor
  rw [qF_def]
  omega

/-- A nonempty strict suffix supplies a covered participation time.
No half cap is inferred for an empty suffix. -/
theorem wcg_suffix_faultQ {E' : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (h : CleanGrowthContinuationSleep₂ p c E source E' rho ΔF)
    (hne : source.horizon < rho.horizon) : FaultQ p.n (faulty rho).card :=
  wcg_faultQ_of_half (wcg_half_of_joined_participation h.base.linked
    (h.joinedParticipation rho.horizon hne le_rfl))

end AvailableChain.FGSA.Run
end

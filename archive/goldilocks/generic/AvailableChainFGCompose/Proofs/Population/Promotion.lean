module
public import AvailableChainFGCompose.Statements.Population.Promotion
public import AvailableChainFGCompose.Statements.Population.Seats
public import AvailableChainFGCompose.Proofs.Healing.Promotion

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (H : FGHeightView (Fin n)) (T : FGTiming) (pair : Wire → NamedHeightPair)
variable (Ef : Electorate (Fin n)) (laws : FGHeightLaws Ef H)

include laws in
/-- SAME: choose the opening's coverage witnesses once, before any terminal carrier. -/
theorem healing_promotion_fixed_rows_holder {A : Finset (Fin n)} {r height : Nat} {Q : Block}
    (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty)
    (hentry : OpeningEntry R E rho H T r height)
    (hcovered : OpeningCoveredFG R S E rho H T pair A r Q)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (H K).T_h.root = (H L).T_h.root → (H K).T_h = (H L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots) :
    ∃ U, EntryAt H U height ∧ FixedRowsFG R S E rho H T pair A r height Q U := by
  have honest (i) (hi : i ∈ A) : safetyHolder S rho i ∈ rho.honest := by
    simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hA hi
  obtain ⟨e, he⟩ := hentry
  obtain ⟨i₀, hi₀⟩ := hne
  let x₀ := safetyHolder S rho i₀
  have hx₀ := honest i₀ hi₀
  obtain ⟨K₀, _, _, _, _, _, hK₀, _⟩ := hcovered i₀ hi₀
  obtain ⟨hh₀, hr₀⟩ := he x₀ K₀ hx₀ hK₀
  let U := (H K₀).T_h
  refine ⟨U, ⟨(laws.entry_same_height K₀).trans hh₀, laws.entry_idem K₀⟩, ?_⟩
  intro i hi
  let x := safetyHolder S rho i
  have hx := honest i hi
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hr, ha, hn⟩ := hcovered i hi
  obtain ⟨hh, hroot⟩ := he x K hx hK
  have hU : (H K).T_h = U := entryAgreement x x₀ K K₀ hx hx₀ hK hK₀
    (hroot.trans hr₀.symm)
  refine ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hU ▸ laws.entry_preceq K,
    sourceSlot x K hx hK, hh, hU, hr, ha, ?_⟩
  rw [hh, hU] at hn
  change ∃ timeout, pair a = .vote height U.root timeout
  cases hp : pair a with
  | empty => rw [hp] at hn; cases hn
  | vote h root timeout =>
    rw [hp] at hn
    have heq : (h, root) = (height, U.root) := Option.some.inj hn
    cases heq
    exact ⟨timeout, rfl⟩

/-- SAME: add the slot bound to the same entry and the same selected batch. -/
theorem p0d3_bound_batch_holder {A : Finset (Fin n)} {r height : Nat} {Q : Block}
    (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty)
    (batch : ∃ U, EntryAt H U height ∧ FixedRowsFG R S E rho H T pair A r height Q U)
    (entrySlot : ∀ x K U, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → (H K).T_h = U →
      U.slot ≤ r * T.roundSlots) :
    ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧
      FixedRowsFG R S E rho H T pair A r height Q U := by
  obtain ⟨U, hU, hrows⟩ := batch
  obtain ⟨i, hi⟩ := hne
  have hx : safetyHolder S rho i ∈ rho.honest := by
    simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hA hi
  obtain ⟨K, _, _, _, _, _, hK, _, _, _, _, _, he, _⟩ := hrows i hi
  exact ⟨U, hU, entrySlot (safetyHolder S rho i) K U hx hK he, hrows⟩

include laws in
/-- SAME: construct the bounded batch from the opening and its original coverage. -/
theorem healing_promotion_bounded_rows_holder {A : Finset (Fin n)} {r height : Nat} {Q : Block}
    (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty)
    (hentry : OpeningEntry R E rho H T r height)
    (hcovered : OpeningCoveredFG R S E rho H T pair A r Q)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (H K).T_h.root = (H L).T_h.root → (H K).T_h = (H L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot) :
    ∃ U, EntryAt H U height ∧ U.slot ≤ r * T.roundSlots ∧
      FixedRowsFG R S E rho H T pair A r height Q U := by
  have batch := healing_promotion_fixed_rows_holder R S E rho H T pair Ef laws
    hA hne hentry hcovered entryAgreement sourceSlot
  exact p0d3_bound_batch_holder R S E rho H T pair hA hne batch
    (fun x K U hx hK hU => healing_promotion_entry_slot R E rho H T Ef laws
      hx hK hU sourceSlot ancestorSlot)

end AvailableChain.FGCompose
end

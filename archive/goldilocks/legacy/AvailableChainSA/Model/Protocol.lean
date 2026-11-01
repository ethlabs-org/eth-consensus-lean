module
public import AvailableChainGridCO.Model.Protocol

@[expose] public section

namespace AvailableChain.SA

open AvailableChain.Generic

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
SA parameters from slow-arming.md §3. Counts are integer seats. -/
structure Params where
  Δ : Time
  n : Nat
  k : Nat
  η : Time
  deltaPos : 0 < Δ
  nPos : 0 < n
  kLarge : 2 ≤ k
  etaNonneg : 0 ≤ η

private theorem member_le_max (xs : List Nat) (acc g : Nat) (h : g ∈ xs) :
    g ≤ xs.foldl max acc := by
  have hacc (ys : List Nat) (a : Nat) : a ≤ ys.foldl max a := by
    induction ys generalizing a with
    | nil => exact le_refl _
    | cons y ys ih => exact (le_max_left _ _).trans (ih _)
  induction xs generalizing acc with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst x; exact (le_max_right _ _).trans (hacc _ _)
    · exact ih _ ht

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Adapter for the shared Goldfish engine. The dense grid is unused by
SA admission. It provides the existing engine parameter type without
adding a parameter or premise to SA. -/
def Params.engine (p : Params) : GridCO.Params where
  Δ := p.Δ
  n := p.n
  m := p.k
  η := p.η
  grid := (Finset.range (p.n + 1)).erase 0
  θ_R := 1 / 2
  deltaPos := p.deltaPos
  mLarge := p.kLarge
  one_mem := by have := p.nPos; simp; omega
  levels_pos := by intro g hg; exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hg).1
  levels_le := by intro g hg; have := Finset.mem_range.mp (Finset.mem_erase.mp hg).2; omega
  etaNonneg := p.etaNonneg
  thetaLower := le_refl _
  thetaUpper := by norm_num
  gridMatchesTheta := by
    intro a h ha hh hmajority
    have hah : a < h := by
      have hq : (a : ℚ) < h := by push_cast at hmajority; linarith
      exact_mod_cast hq
    apply lt_of_lt_of_le hah
    apply member_le_max
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, ⟨by omega, by omega⟩, le_refl _⟩

abbrev State (n : Nat) := GridCO.State n .block
abbrev Msg (n : Nat) := GridCO.Msg n .block
abbrev Wire (n : Nat) := GridCO.Wire n .block
abbrev HeadWire (n : Nat) := GridCO.HeadWire n .block

abbrev lifetime (p : Params) := GridCO.lifetime p.engine
abbrev proposalTime (p : Params) := GridCO.proposalTime p.engine
abbrev voteTime (p : Params) := GridCO.voteTime p.engine
abbrev earlyTime (p : Params) := GridCO.earlyTime p.engine
abbrev freezeTime (p : Params) := GridCO.freezeTime p.engine
abbrev releaseTime (p : Params) := GridCO.releaseTime p.engine
abbrev gateTime (p : Params) := GridCO.gateTime p.engine
abbrev releaseThreshold (p : Params) := GridCO.releaseThreshold p.engine
abbrev confirmation (p : Params) {n : Nat} := @GridCO.confirmation p.engine n .block
abbrev confirmationFrom (p : Params) {n : Nat} := @GridCO.confirmationFrom p.engine n .block
abbrev prefixSupport (p : Params) {n : Nat} := @GridCO.prefixSupport p.engine n .block
abbrev savedGenuine {n : Nat} := @GridCO.savedGenuine n .block
abbrev slowEligible (p : Params) {n : Nat} := @GridCO.slowEligible p.engine n .block
abbrev gate (p : Params) {n : Nat} := @GridCO.gate GridCO.slowLeasePolicy p.engine n .block
abbrev clock (p : Params) {n : Nat} := @GridCO.clock GridCO.slowLeasePolicy p.engine n .block
abbrev gateFrom (p : Params) {n : Nat} := @GridCO.gateFrom GridCO.slowLeasePolicy p.engine n .block
abbrev clockFrom
    (p : Params) {n : Nat} := @GridCO.clockFrom GridCO.slowLeasePolicy p.engine n .block
abbrev release (p : Params) {n : Nat} := @GridCO.release p.engine n .block
abbrev process (p : Params) {n : Nat} := @GridCO.process p.engine n .block
abbrev act (p : Params) {n : Nat} := @GridCO.act p.engine n .block
abbrev propose (p : Params) {n : Nat} := @GridCO.propose p.engine n .block
abbrev initial (n : Nat) := GridCO.initial n .block
abbrev stable {n : Nat} := @GridCO.stable n .block
abbrev confirmed {n : Nat} := @GridCO.confirmed n .block
abbrev block {n : Nat} := @GridCO.block n .block
abbrev deadlineOf {n : Nat} := @GridCO.deadlineOf n .block
abbrev expire {n : Nat} := @GridCO.expire n .block

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Slow arming, one release level. All wire rules, views, and handlers
are the shared Grid CO engine. Only raw history and lease admission differ. -/
abbrev sa (p : Params) : ProtocolSpec p.n :=
  @GridCO.gridCO GridCO.slowLeasePolicy p.engine

namespace Root

/-- [ROOT-DIGEST-2 W1; DC GoldfishVote] Root-mode SA store. -/
abbrev State (n : Nat) := GridCO.State n .root

abbrev confirmation (p : Params) {n : Nat} := @GridCO.confirmation p.engine n .root
abbrev confirmationFrom (p : Params) {n : Nat} := @GridCO.confirmationFrom p.engine n .root
abbrev prefixSupport (p : Params) {n : Nat} := @GridCO.prefixSupport p.engine n .root
abbrev savedGenuine {n : Nat} := @GridCO.savedGenuine n .root
abbrev slowEligible (p : Params) {n : Nat} := @GridCO.slowEligible p.engine n .root
abbrev gate (p : Params) {n : Nat} := @GridCO.gate GridCO.slowLeasePolicy p.engine n .root
abbrev clock (p : Params) {n : Nat} := @GridCO.clock GridCO.slowLeasePolicy p.engine n .root
abbrev gateFrom (p : Params) {n : Nat} := @GridCO.gateFrom GridCO.slowLeasePolicy p.engine n .root
abbrev clockFrom (p : Params) {n : Nat} := @GridCO.clockFrom GridCO.slowLeasePolicy p.engine n .root
abbrev release (p : Params) {n : Nat} := @GridCO.release p.engine n .root
abbrev process (p : Params) {n : Nat} := @GridCO.process p.engine n .root
abbrev act (p : Params) {n : Nat} := @GridCO.act p.engine n .root
abbrev propose (p : Params) {n : Nat} := @GridCO.propose p.engine n .root
abbrev initial (n : Nat) := GridCO.initial n .root
abbrev stable {n : Nat} := @GridCO.stable n .root
abbrev confirmed {n : Nat} := @GridCO.confirmed n .root
abbrev block {n : Nat} := @GridCO.block n .root
abbrev deadlineOf {n : Nat} := @GridCO.deadlineOf n .root
abbrev expire {n : Nat} := @GridCO.expire n .root

end Root

end AvailableChain.SA
end

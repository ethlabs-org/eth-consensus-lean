module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Accountable

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # `fg.causalCap.core.v1`: the causal cap for a bound M (part (b))

A crossing of a height needs a quorum of matching rows, and a quorum has a
row of a signer outside a set of weight below q. Thus a chain whose rows from
such signers all have height at most M cannot cross M+1. Faulty rows can be
new; they cannot cross a height alone. Part (a) (an honest row of height h has
`h ≤` the signer's archival maximum) is a run fact: `provenance_entry` with
`comp.cut.v1`. -/

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- G17 R-CAP at a read. `B` is the held block and `R a` means that row `a`
was released before that read. The run supplies `hrows` from authentic row
origins and carrier closure; no row-pool membership is required.

`hcap` is the weighted FaultQ premise. For unit weights, F1.7 bounds the
faulty signer count by the faulty holder count, then uses `FaultQ.lt` and
`KitFG.unit_toWeights_q` from `WeightsBridge`.
A block of height at least `y + 2` needs an honest row at exactly `y + 1`. -/
theorem causalCap_row (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V)
    (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hh : y + 2 ≤ (derive E cfg B).h) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      ∃ T t, a.height_pair = .vote (y + 1) T t := by
  unfold Height at *
  obtain ⟨X, -, -, Q, hQ, hw⟩ :=
    height_crossing E cfg B (y + 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
  obtain ⟨carrier, a, hc, ha, hai, hm⟩ := hw i hiQ
  have haB : a ∈ chainRows B := mem_chainRows_of_carrier hc ha
  have haf : a.signer ∉ faulty := hai ▸ hif
  refine ⟨a, haB, haf, hrows a haB haf, ?_⟩
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote k T t =>
      have hk : k = y + 1 := by
        simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
        exact hm.1
      exact ⟨T, t, by rw [hk]⟩

/-- The justified-height form of G17 follows from `h_j < h`. -/
theorem causalCap_justified_row (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V)
    (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hj : y + 1 ≤ (derive E cfg B).h_j) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      ∃ T t, a.height_pair = .vote (y + 1) T t := by
  have := justified_below_height E cfg B
  unfold Height at *
  exact causalCap_row E cfg faulty hcap y B R hrows (by unfold Height at *; omega)

/-- A positive finalization has an honest finality row released before the
read. Its certificate height is exactly `h_F`, hence at least `y`.
F1.7 uses the head that supplied this finality pair for the one-action lag.
The premise `0 < y` excludes genesis, which has no certificate rows. -/
theorem finalityCap_row (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V)
    (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hy : 0 < y) (hF : y ≤ (derive E cfg B).h_F) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      a.finality_pair = some ⟨(derive E cfg B).h_F, (derive E cfg B).F.root⟩ := by
  unfold Height at *
  obtain ⟨F, -, rfl, Q, hQ, hw⟩ := finality_certificate E cfg B (by unfold Height at *; omega)
  obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
  obtain ⟨carrier, a, hc, ha, hai, hf⟩ := hw i hiQ
  have haB : a ∈ chainRows B := mem_chainRows_of_carrier hc ha
  have haf : a.signer ∉ faulty := hai ▸ hif
  exact ⟨a, haB, haf, hrows a haB haf, hf⟩

/-- A positive finalization also needs an honest height row at exactly `y`.
This is the height-row form of the cap, from `h_F ≤ h_j < h`.
The finality row and this height row need not be the same row. -/
theorem finalityCap_height_row (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V)
    (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hy : 0 < y) (hF : y ≤ (derive E cfg B).h_F) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      ∃ T t, a.height_pair = .vote y T t := by
  have := heights_ordered E cfg B
  unfold Height at *
  have hy' : y - 1 + 1 = y := by omega
  simpa only [hy'] using
    causalCap_justified_row E cfg faulty hcap (y - 1) B R hrows (by unfold Height at *; omega)

/-- [pin fg.causalCap.core.v1] (b) A chain whose rows from signers outside
`faulty` all have height ≤ M has state height ≤ M+1 and justified height ≤ M,
when the faulty weight is below q. -/
theorem causalCap (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (M : Height) (B : FGBlock V)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty →
      ∀ h T t, a.height_pair = .vote h T t → h ≤ M) :
    (derive E cfg B).h ≤ M + 1 ∧ (derive E cfg B).h_j ≤ M := by
  have hh : (derive E cfg B).h ≤ M + 1 := by
    by_contra hlt
    have hlt' : M + 1 < (derive E cfg B).h := by
      unfold Height at *
      omega
    obtain ⟨X, -, -, Q, hQ, hw⟩ := height_crossing E cfg B (M + 1) (Nat.le_add_left 1 M) hlt'
    obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
    obtain ⟨carrier, a, hc, ha, hai, hm⟩ := hw i hiQ
    have haB : a ∈ chainRows B := mem_chainRows_of_carrier hc ha
    cases hp : a.height_pair with
    | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
    | vote k T t =>
        have hk : k = M + 1 := by
          simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
          exact hm.1
        have := hrows a haB (hai ▸ hif) k T t hp
        unfold Height at *
        omega
  refine ⟨hh, ?_⟩
  have := justified_below_height E cfg B
  unfold Height at *
  omega

/-- [pin comp.cut.v1] (item 4, partial: the arithmetic j ≤ M < H−1 under hrows)
At a frontier `H ≥ M+2`, such a justification is not the active root
(`H ≠ h_j + 1`). -/
theorem causalCap_notRoot (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (M : Height) (B : FGBlock V)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty →
      ∀ h T t, a.height_pair = .vote h T t → h ≤ M)
    (H : Height) (hH : M + 2 ≤ H) : (derive E cfg B).h_j + 1 ≠ H := by
  have := (causalCap E cfg faulty hcap M B hrows).2
  unfold Height at *
  omega

end AvailableChain.KitFG
end

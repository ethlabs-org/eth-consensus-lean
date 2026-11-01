module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Accountable

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # `fj.crossingNoFinal.v1`: a conflicting crossing of j proves that J cannot finalize

r148 (`fj-redteam.md`, lines 234–258). Let J be justified at j, and let W
of height above j not extend J. The first crossing of j on W's chain has a
progress quorum for an entry `X ≠ J`. (1) A finality QC for J meets it in
E1 weight. (2) An honest member of J's target QC and of the crossing QC has a
timeout row for X. (3) `crossing_maturity` proves the general disjunction: a
block that raises its parent's height has a target quorum for the parent's
entry, or its slot is mature. The composition at the crossing block of j on W
(clause 2 excludes the target quorum, so the crossing is at the uniform
maturity slot) is a paper step. (4) "J cannot finalize in a continuation that
keeps the fault bound" is a paper step from (1): the E1 weight is
`≥ 2q − W > a`. -/

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [helper] The crossing of j on W's chain names an entry X with `X.root ≠ J.root`,
with a quorum of rows on W's chain that match `(j, X.root)` (a target or a
timeout). Clauses 1 and 2 use this crossing. -/
theorem exists_crossing_quorum_ne_justified (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
  (hroot : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W) :
    ∃ X : FGBlock V, X.root ≠ (derive E cfg B).J.root ∧ ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (derive E cfg B).h_j X.root = true := by
  obtain ⟨X, hXW, -, Q, hQ, hw⟩ :=
    height_crossing E cfg W _ (Nat.one_le_iff_ne_zero.mpr hJ) hW
  refine ⟨X, fun hr => hnot ?_, Q, hQ, fun i hi => ?_⟩
  · rw [← hroot _ _ (Or.inr hXW) (Or.inl ((derive_anchors_preceq E cfg B).2)) hr]
    exact hXW
  · obtain ⟨carrier, b, hc, hb, hbi, hm⟩ := hw i hi
    exact ⟨b, mem_chainRows_of_carrier hc hb, hbi, hm⟩

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `exists_crossing_quorum_ne_justified`.
Delete after F2 (GLY E-13). -/
theorem crossing_other_entry (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W) :
    ∃ X : FGBlock V, X.root ≠ (derive E cfg B).J.root ∧ ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (derive E cfg B).h_j X.root = true :=
  exists_crossing_quorum_ne_justified E cfg B W hroot hJ hW hnot

/-- [pin fj.crossingNoFinal.v1] (clause 1) Let J be justified at j on B, and let
W of height > j not extend J. Any finality QC for `(j, J)`, in any row pool A
(before or after the crossing; no chain needs to carry it), gives E1 weight
between A and W's rows. -/
theorem e1Weight_of_finalityQC_not_preceq (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
  (hroot : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (A : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q)
    (hfin : ∀ i ∈ Q, ∃ a ∈ A, a.signer = i ∧
      a.finality_pair = some ⟨(derive E cfg B).h_j, (derive E cfg B).J.root⟩) :
    HasE1WeightBetween E A (chainRows W) := by
  obtain ⟨X, hne, Qc, hQc, hwc⟩ := exists_crossing_quorum_ne_justified E cfg B W hroot hJ hW hnot
  refine ⟨Q ∩ Qc, quorum_intersection E hQ hQc, fun i hi => ?_⟩
  obtain ⟨hf, hc⟩ := Finset.mem_inter.mp hi
  obtain ⟨f, hfA, hfi, hfp⟩ := hfin i hf
  obtain ⟨b, hbW, hbi, hm⟩ := hwc i hc
  exact ⟨f, hfA, b, hbW, hfi, hbi,
    e1Slashable_of_matchesEntry f b _ X.root _ (hfi.trans hbi.symm) hfp hm hne⟩

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `e1Weight_of_finalityQC_not_preceq`.
Delete after F2 (GLY E-13). -/
theorem crossingNoFinal_QC (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (A : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q)
    (hfin : ∀ i ∈ Q, ∃ a ∈ A, a.signer = i ∧
      a.finality_pair = some ⟨(derive E cfg B).h_j, (derive E cfg B).J.root⟩) :
    HasE1WeightBetween E A (chainRows W) :=
  e1Weight_of_finalityQC_not_preceq E cfg B W hroot hJ hW hnot A Q hQ hfin

/-- [helper] Chain form of clause 1: if `J` is justified at `j` on chain
`B`, a block `W` of height > j does not extend `J`, and a chain `D` finalizes
`J` at `j`, then E1 weight exists between `W`'s and `D`'s rows. `B` only
identifies `J`. -/
theorem slashableWeight_of_finalized_crossing (E : Electorate V) (cfg : FGConfig)
    (B W D : FGBlock V) (hroot : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (hfin : (derive E cfg D).F = (derive E cfg B).J)
    (hfinH : (derive E cfg D).h_F = (derive E cfg B).h_j) :
    HasSlashableWeightBetween E (chainRows W) (chainRows D) := by
  have hnz : (derive E cfg D).h_F ≠ 0 := hfinH ▸ hJ
  obtain ⟨F, -, rfl, Q, hQ, hw⟩ := finality_certificate E cfg D hnz
  refine hasSlashableWeightBetween_of_hasE1WeightBetween_swap
    (e1Weight_of_finalityQC_not_preceq E cfg B W hroot hJ hW hnot (chainRows D) Q hQ fun i hi => ?_)
  obtain ⟨carrier, a, hc, ha, hai, hap⟩ := hw i hi
  rw [hfinH, hfin] at hap
  exact ⟨a, mem_chainRows_of_carrier hc ha, hai, hap⟩

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `slashableWeight_of_finalized_crossing`.
Delete after F2 (GLY E-13). -/
theorem crossingNoFinal (E : Electorate V) (cfg : FGConfig) (B W D : FGBlock V)
    (hroot : RootInjectiveOn W D ∧ RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (hfin : (derive E cfg D).F = (derive E cfg B).J)
    (hfinH : (derive E cfg D).h_F = (derive E cfg B).h_j) :
    HasSlashableWeightBetween E (chainRows W) (chainRows D) :=
  slashableWeight_of_finalized_crossing E cfg B W D hroot.2 hJ hW hnot hfin hfinH

/-- [pin fj.crossingNoFinal.v1] (clause 2) Let J be justified at j on B, and let
W of height > j not extend J. If the faulty weight is below `2q − W`, and no
signer outside `faulty` has an E1 or E2 pair between the two chains, then some
signer outside `faulty` has a target row for `(j, J)` on B's chain and a
TIMEOUT row at j, for an entry X ≠ J, on W's chain. -/
theorem exists_honest_timeout_of_crossing (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (derive E cfg B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair = .vote (derive E cfg B).h_j (derive E cfg B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧ b.height_pair = .vote (derive E cfg B).h_j X true) := by
  obtain ⟨Qj, hQj, hwj⟩ := justification_certificate_rows E cfg B hJ
  obtain ⟨X, hne, Qc, hQc, hwc⟩ := exists_crossing_quorum_ne_justified E cfg B W hroot hJ hW hnot
  obtain ⟨i, hi, hif⟩ := honest_in_intersection E faulty hQj hQc hcap
  obtain ⟨hij, hic⟩ := Finset.mem_inter.mp hi
  obtain ⟨a, haB, hai, hap⟩ := hwj i hij
  obtain ⟨b, hbW, hbi, hm⟩ := hwc i hic
  refine ⟨i, hif, X.root, hne, ⟨a, haB, hai, hap⟩, b, hbW, hbi, ?_⟩
  cases hbp : b.height_pair with
  | empty => simp [hbp, NamedHeightPair.matchesEntry] at hm
  | vote k T t =>
      simp only [hbp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      cases t with
      | true => rfl
      | false =>
          exfalso
          refine hhonest a haB b hbW (hai ▸ hif) ?_
          have h2 : e2Slashable a b = true := by
            simp [e2Slashable, sameSigner, e2Fields, hap, hbp, hai, hbi, Ne.symm hne]
          change slashable a b = true
          simp only [slashable, h2, Bool.or_true]

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `exists_honest_timeout_of_crossing`.
Delete after F2 (GLY E-13). -/
theorem crossingNeedsTimeout (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (derive E cfg B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair = .vote (derive E cfg B).h_j (derive E cfg B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧ b.height_pair = .vote (derive E cfg B).h_j X true) :=
  exists_honest_timeout_of_crossing E cfg faulty B W hroot hcap hJ hW hnot hhonest

/-- [pin fj.crossingNoFinal.v1] (clause 3) A block that raises its parent's
height does so with a target quorum for the parent's entry, or at a slot at
least the entry's slot plus δ_t (spec `process_height_events`, lines 921–943). -/
theorem crossing_maturity (E : Electorate V) (cfg : FGConfig) (p : FGBlock V) (s : Slot) (r_s :
  BlockId)
    (x : Nat) (rs : List (Row V))
    (hup : (derive E cfg p).h < (derive E cfg (.node p s r_s x rs)).h) :
    (∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ a ∈ chainRows (.node p s r_s x rs), a.signer = i ∧
        a.height_pair = .vote (derive E cfg p).h (derive E cfg p).T_h.root false) ∨
      (derive E cfg p).T_h.slot + cfg.timeoutDelay ≤ s := by
  set σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs with hσ
  obtain ⟨-, hh, hT, -⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
  have hs : σ.s = s := foldRows_s (derive E cfg p) (.node p s r_s x rs) rs
  have hw := folded_witnesses E cfg p s r_s x rs
  have htarget : E.IsQuorum (afterFin E σ).target_participation →
      ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ a ∈ chainRows (.node p s r_s x rs),
        a.signer = i ∧
        a.height_pair = .vote (derive E cfg p).h (derive E cfg p).T_h.root false := by
    intro hq
    rw [afterFin_target_participation] at hq
    refine ⟨_, hq, fun i hi => ?_⟩
    obtain ⟨a, ⟨carrier, hc, ha⟩, hai, hap⟩ := hw.target i hi
    rw [hh, hT] at hap
    exact ⟨a, mem_chainRows_of_carrier hc ha, hai, hap⟩
  rw [derive_node, process_height_events_eq] at hup
  split_ifs at hup with h1 h2
  · exact Or.inl (htarget (isQuorum_of_targetQuorum E h1))
  · rcases quorum_of_progReady E cfg h2 with hq | ⟨hm, -⟩
    · exact Or.inl (htarget hq)
    · refine Or.inr ?_
      rwa [afterFin_T_h, afterFin_s, hT, hs] at hm
  · exfalso
    rw [afterFin_h, hh] at hup
    exact lt_irrefl _ hup

end AvailableChain.KitFG
end

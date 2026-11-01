module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.WeightsBridge
public import AvailableChainGeneric.Proofs.Pure.Quorum
public import Mathlib.Tactic

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Weighted quorum intersection
(port: DC/DecoupledConsensusProofs/Protocol/ChainState/Evidence.lean:71-97) -/

omit [DecidableEq V] in
/-- [helper] A quorum has a member outside a set of weight below `q`. -/
theorem honest_in_quorum (E : Electorate V) (faulty : Finset V) {Q : Finset V}
    (hQ : E.IsQuorum Q) (hcap : E.weightOf faulty < E.q) : ∃ i ∈ Q, i ∉ faulty := by
  exact AvailableChain.Gen.Pure.quorum_honest E.toWeights faulty
    ((isQuorum_toWeights_iff E Q).mpr hQ)
    (by simpa only [toWeights_weightOf, toWeights_q] using hcap)

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Evidence.lean:83-92 (quorum_intersection)
/-- [helper] -/
theorem quorum_intersection (E : Electorate V) {Q Q' : Finset V}
    (hQ : E.IsQuorum Q) (hQ' : E.IsQuorum Q') :
    2 * E.q ≤ E.totalWeight + E.weightOf (Q ∩ Q') := by
  simpa only [toWeights_q, toWeights_totalWeight, toWeights_weightOf] using
    (AvailableChain.Gen.Pure.quorum_intersection E.toWeights
      ((isQuorum_toWeights_iff E Q).mpr hQ)
      ((isQuorum_toWeights_iff E Q').mpr hQ'))

/-- [helper] Two quorums meet outside a set of weight below `2q − W`. -/
theorem honest_in_intersection (E : Electorate V) (faulty : Finset V) {Q Q' : Finset V}
    (hQ : E.IsQuorum Q) (hQ' : E.IsQuorum Q')
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q) :
    ∃ i ∈ Q ∩ Q', i ∉ faulty := by
  exact AvailableChain.Gen.Pure.quorum_inter_honest E.toWeights (F := faulty)
    ((isQuorum_toWeights_iff E Q).mpr hQ)
    ((isQuorum_toWeights_iff E Q').mpr hQ')
    (by simpa only [toWeights_weightOf, toWeights_totalWeight, toWeights_q] using hcap)

/-! ## Ancestry
(port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean; the DC `Block` type
carries `depth` as a def in its own objects file.
`AvailableChainSimplexFG/Objects.lean` has no such helper, so this file has a
local `depth` measure, used only to prove `preceq_antisymm`.) -/

omit [DecidableEq V] [Fintype V] in
-- port: DC/DecoupledConsensusModel/Objects/Blocks.lean:229-232 (depth)
/-- [helper] A structural depth measure, needed only to prove
`preceq_antisymm`: the number of parent edges from genesis. -/
private def depth : FGBlock V → Nat
  | .genesis => 0
  | .node p _ _ _ _ => depth p + 1

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:36-38 (preceq_self)
/-- [helper] `B ⪯ B`. -/
theorem preceq_refl (B : FGBlock V) : FGBlock.Preceq B B := by
  cases B with
  | genesis => simp [FGBlock.Preceq, FGBlock.preceq]
  | node p s r_s r rs => simp [FGBlock.Preceq, FGBlock.preceq]

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:46-60 (preceq_trans)
/-- [helper] `⪯` is transitive. -/
theorem preceq_trans {A B C : FGBlock V} (h₁ : FGBlock.Preceq A B)
    (h₂ : FGBlock.Preceq B C) : FGBlock.Preceq A C := by
  induction C with
  | genesis =>
      simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq] at h₂
      subst h₂
      exact h₁
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h₂
      change FGBlock.preceq A (FGBlock.node p s r_s r rs) = true
      rcases h₂ with h | h
      · subst h
        exact h₁
      · have hAp : FGBlock.preceq A p = true := ih h
        simp only [FGBlock.preceq, hAp, Bool.or_true]

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:64-76 (preceq_depth_le)
private theorem preceq_depth_le {B C : FGBlock V} (h : FGBlock.Preceq B C) :
    depth B ≤ depth C := by
  induction C with
  | genesis =>
      simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq] at h
      subst h
      exact Nat.le_refl _
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · subst h
        exact Nat.le_refl _
      · have := ih h
        simp only [depth]
        omega

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:80-90 (preceq_eq_of_depth_le)
private theorem preceq_eq_of_depth_le {B C : FGBlock V} (h : FGBlock.Preceq B C)
    (hd : depth C ≤ depth B) : B = C := by
  induction C with
  | genesis =>
      simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq] at h
      exact h
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact h
      · exfalso
        have h1 := preceq_depth_le h
        simp only [depth] at hd
        omega

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:92-97 (preceq_antisymm)
/-- [helper] `⪯` is antisymmetric. Proved from `depth` alone: no
well-formedness hypothesis is needed. -/
theorem preceq_antisymm {B C : FGBlock V} (h₁ : FGBlock.Preceq B C)
    (h₂ : FGBlock.Preceq C B) : B = C :=
  preceq_eq_of_depth_le h₁ (preceq_depth_le h₂)

omit [Fintype V] in
-- port: DC/DecoupledConsensusModel/Objects/{Blocks,NamedBlocks}.lean
-- (the `.genesis` case of `preceq`)
/-- [helper] `A ⪯ genesis ↔ A = genesis`. -/
theorem preceq_genesis {A : FGBlock V} : FGBlock.Preceq A .genesis ↔ A = .genesis := by
  simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq]

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:56-63 (preceq_genesis)
/-- [helper] Genesis precedes every block. -/
theorem genesis_preceq (B : FGBlock V) : FGBlock.Preceq .genesis B := by
  induction B with
  | genesis => exact preceq_refl _
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at ih ⊢
      exact Or.inr ih

omit [Fintype V] in
-- port: DC/DecoupledConsensusModel/Objects/Blocks.lean (`compatible`'s `||`)
/-- [helper] `compatible` is commutative. -/
theorem compatible_comm (A B : FGBlock V) :
    FGBlock.compatible A B = FGBlock.compatible B A := by
  unfold FGBlock.compatible
  exact Bool.or_comm _ _

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:99-127 (preceq_linear)
/-- [helper] Two ancestors of one block are comparable. -/
theorem preceq_total_of_common {A B W : FGBlock V}
    (hA : FGBlock.Preceq A W) (hB : FGBlock.Preceq B W) :
    FGBlock.Preceq A B ∨ FGBlock.Preceq B A := by
  induction W with
  | genesis =>
      simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq] at hA hB
      subst hA
      subst hB
      exact Or.inl (preceq_refl _)
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hA hB
      rcases hA with hA | hA
      · rcases hB with hB | hB
        · subst hA; subst hB; exact Or.inl (preceq_refl _)
        · subst hA
          refine Or.inr ?_
          change FGBlock.preceq B (FGBlock.node p s r_s r rs) = true
          simp only [FGBlock.preceq, hB, Bool.or_true]
      · rcases hB with hB | hB
        · subst hB
          refine Or.inl ?_
          change FGBlock.preceq A (FGBlock.node p s r_s r rs) = true
          simp only [FGBlock.preceq, hA, Bool.or_true]
        · exact ih hA hB

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Objects/Ancestry.lean:129-135 (compatible_of_preceq_common)
/-- [helper] Two blocks on one chain are compatible. -/
theorem compatible_of_preceq_common {X Y Z : FGBlock V}
    (hX : FGBlock.Preceq X Z) (hY : FGBlock.Preceq Y Z) :
    FGBlock.compatible X Y = true := by
  unfold FGBlock.compatible
  simp only [Bool.or_eq_true]
  exact preceq_total_of_common hX hY

omit [Fintype V] in
/-- [helper] A strict descendant has a child of the ancestor on its path. -/
theorem child_toward {B W : FGBlock V} (h : FGBlock.Preceq B W) (hne : B ≠ W) :
    ∃ C, C.parent = B ∧ C ≠ .genesis ∧ FGBlock.Preceq C W := by
  induction W with
  | genesis =>
      simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq] at h
      exact absurd h hne
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact absurd h hne
      · by_cases hBp : B = p
        · subst hBp
          refine ⟨FGBlock.node B s r_s r rs, rfl, ?_, preceq_refl _⟩
          intro hcontra
          injection hcontra
        · obtain ⟨C, hC1, hC2, hC3⟩ := ih h hBp
          refine ⟨C, hC1, hC2, ?_⟩
          change FGBlock.preceq C (FGBlock.node p s r_s r rs) = true
          have hpW : FGBlock.preceq p (FGBlock.node p s r_s r rs) = true := by
            simp only [FGBlock.preceq, Bool.or_eq_true]
            exact Or.inr (preceq_refl p)
          exact preceq_trans hC3 hpW

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Chain.lean:78-90 (chain_attestations_mono)
/-- [helper] The carried rows only grow along the chain. -/
theorem chainRows_mono {A B : FGBlock V} (h : FGBlock.Preceq A B) :
    chainRows A ⊆ chainRows B := by
  induction B with
  | genesis =>
      simp only [FGBlock.Preceq, FGBlock.preceq, decide_eq_true_eq] at h
      subst h
      exact Finset.Subset.refl _
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · subst h
        exact Finset.Subset.refl _
      · refine (ih h).trans ?_
        simp only [chainRows]
        exact Finset.subset_union_right

omit [Fintype V] in
-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:15-29
-- (own_row_erase_mem, on_chain_erase_mem)
/-- [helper] A row carried by a block of the chain is in the chain's rows. -/
theorem mem_chainRows_of_carrier {carrier B : FGBlock V} {a : Row V}
    (hc : FGBlock.Preceq carrier B) (ha : a ∈ carrier.rows) : a ∈ chainRows B := by
  refine chainRows_mono hc ?_
  cases carrier with
  | genesis => simp [FGBlock.rows] at ha
  | node p s r_s r rs =>
      simp only [chainRows, Finset.mem_union, List.mem_toFinset]
      exact Or.inl ha

end AvailableChain.KitFG
end

module
public import AvailableChainKitFG.Certificates
public import AvailableChainKitFG.RootScopeDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Main.lean:39-48
-- (rootInjectiveOnAncestors_symm)
/-- [helper] `RootInjectiveOn` is symmetric in the two tips. -/
theorem RootInjectiveOn.symm [RowCodec V] {B₁ B₂ : FGBlock V} (h : RootInjectiveOn B₁ B₂) :
    RootInjectiveOn B₂ B₁ :=
  fun X Y hX hY hr => h X Y hX.symm hY.symm hr

/-! ## Root injectivity and evidence helpers -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:31-48
-- (matching_finality_e1)
/-- [helper] A finality row for `(h, T)` and a row of the same signer that
matches the entry `(h, X)` with `X ≠ T` are E1. A timeout at `h` matches every
entry at `h`, so it is also E1. -/
theorem e1Slashable_of_matchesEntry (f a : Row V) (h : Height) (X T : BlockId)
    (hs : f.signer = a.signer) (hf : f.finality_pair = some ⟨h, T⟩)
    (hm : a.height_pair.matchesEntry h X = true) (hne : X ≠ T) :
    e1Slashable f a = true := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height root timeout =>
      have heq : height = h ∧ root = X := by
        simpa only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hm
      rcases heq with ⟨rfl, rfl⟩
      cases timeout <;>
        simp [e1Slashable, e1Fields, sameSigner, conflictsWithFinality, hp, hf, hs, hne]

omit [DecidableEq V] in
/-- [helper] `e1Fields` tests each side's finality pair against the other's
height pair, so it is symmetric. -/
theorem e1Fields_comm (a b : Row V) : e1Fields a b = e1Fields b a := by
  unfold e1Fields
  exact Bool.or_comm _ _

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Evidence.lean:35-51
-- (slashableBetween_of_e1EvidenceForPair)
/-- [helper] One E1 pair is slashable between the two pools. -/
theorem slashableBetween_of_e1 {A₁ A₂ : Finset (Row V)} {i : V} {a b : Row V}
    (ha : a ∈ A₁) (hb : b ∈ A₂) (hai : a.signer = i) (hbi : b.signer = i)
    (h : e1Slashable a b = true) : SlashableBetween A₁ A₂ i := by
  refine ⟨a, ha, b, hb, hai, hbi, ?_⟩
  change slashable a b = true
  simp only [slashable, h, Bool.true_or]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Main.lean:52-70
-- (slashableBetween_of_e1EvidenceForPair_swap)
/-- [helper] One E1 pair, read in the other pool order. -/
theorem slashableBetween_of_e1_swap {A₁ A₂ : Finset (Row V)} {i : V} {a b : Row V}
    (ha : a ∈ A₂) (hb : b ∈ A₁) (hai : a.signer = i) (hbi : b.signer = i)
    (h : e1Slashable a b = true) : SlashableBetween A₁ A₂ i := by
  refine slashableBetween_of_e1 hb ha hbi hai ?_
  simp only [e1Slashable, sameSigner, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1.symm, (e1Fields_comm b a).trans h.2⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean:207-220
-- (slashableBetween_of_e2EvidenceAtHeight)
/-- [helper] E2 evidence at a fixed height against two different entries is
slashable between the two pools. -/
theorem slashableBetween_of_e2EvidenceAtHeight {h : Height} {T₁ T₂ : BlockId}
    {A₁ A₂ : Finset (Row V)} {i : V} (hne : T₁ ≠ T₂)
    (hev : E2EvidenceAtHeight h T₁ T₂ A₁ A₂ i) : SlashableBetween A₁ A₂ i := by
  obtain ⟨a, ha, b, hb, hai, hbi, hpa, hpb⟩ := hev
  refine ⟨a, ha, b, hb, hai, hbi, ?_⟩
  have hv : a.signer = b.signer := by rw [hai, hbi]
  have h2 : e2Slashable a b = true := by
    simp [e2Slashable, sameSigner, e2Fields, hpa, hpb, hv, hne]
  change slashable a b = true
  simp only [slashable, h2, Bool.or_true]

variable [Fintype V]

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Evidence.lean:53-62
-- (hasE1WeightAt_toSlashableWeight)
/-- [helper] E1 weight is slashable weight. -/
theorem hasSlashableWeightBetween_of_hasE1WeightBetween {E : Electorate V}
    {A₁ A₂ : Finset (Row V)} (h : HasE1WeightBetween E A₁ A₂) :
    HasSlashableWeightBetween E A₁ A₂ := by
  obtain ⟨S, hw, hev⟩ := h
  refine ⟨S, hw, fun i hi => ?_⟩
  obtain ⟨a, ha, b, hb, hai, hbi, h1⟩ := hev i hi
  exact slashableBetween_of_e1 ha hb hai hbi h1

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/Main.lean:74-79
-- (hasSlashableWeightBetween_of_hasE1WeightAt_swap)
/-- [helper] E1 weight is slashable weight in the other pool order. -/
theorem hasSlashableWeightBetween_of_hasE1WeightBetween_swap {E : Electorate V}
    {A₁ A₂ : Finset (Row V)} (h : HasE1WeightBetween E A₂ A₁) :
    HasSlashableWeightBetween E A₁ A₂ := by
  obtain ⟨S, hw, hev⟩ := h
  refine ⟨S, hw, fun i hi => ?_⟩
  obtain ⟨a, ha, b, hb, hai, hbi, h1⟩ := hev i hi
  exact slashableBetween_of_e1_swap ha hb hai hbi h1

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean:222-227
-- (hasSlashableWeightBetween_of_hasE2WeightAt)
/-- [helper] E2 weight against two different entries is slashable weight. -/
theorem hasSlashableWeightBetween_of_hasE2WeightAt {E : Electorate V} {h : Height}
    {T₁ T₂ : BlockId} {A₁ A₂ : Finset (Row V)} (hne : T₁ ≠ T₂)
    (hev : HasE2WeightAt E h T₁ T₂ A₁ A₂) : HasSlashableWeightBetween E A₁ A₂ := by
  obtain ⟨S, hw, hE⟩ := hev
  exact ⟨S, hw, fun i hi => slashableBetween_of_e2EvidenceAtHeight hne (hE i hi)⟩

/-! ## `fg.uniqueJust.v1` -/

omit [DecidableEq V] in
-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean:229-255
-- (justification_unique_per_height)
/-- [pin fg.uniqueJust.v1] (Lemma U, certificate form) Two target quorums at one
height for different entries give `2q − W` of E2 weight at that height, against
those two entries. -/
theorem uniqueJust (E : Electorate V) {A₁ A₂ : Finset (Row V)} {Q₁ Q₂ : Finset V}
    {h : Height} {T₁ T₂ : BlockId}
    (hQ₁ : E.IsQuorum Q₁) (hQ₂ : E.IsQuorum Q₂)
    (hw₁ : ∀ i ∈ Q₁, ∃ a ∈ A₁, a.signer = i ∧ a.height_pair = .vote h T₁ false)
    (hw₂ : ∀ i ∈ Q₂, ∃ b ∈ A₂, b.signer = i ∧ b.height_pair = .vote h T₂ false) :
    HasE2WeightAt E h T₁ T₂ A₁ A₂ := by
  classical
  refine ⟨Q₁ ∩ Q₂, quorum_intersection E hQ₁ hQ₂, fun i hi => ?_⟩
  obtain ⟨hi₁, hi₂⟩ := Finset.mem_inter.mp hi
  obtain ⟨a, ha, hai, hpa⟩ := hw₁ i hi₁
  obtain ⟨b, hb, hbi, hpb⟩ := hw₂ i hi₂
  exact ⟨a, ha, b, hb, hai, hbi, hpa, hpb⟩

-- port: DC/DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean:257-270
-- (justification_unique_per_height_slashable)
/-- [helper] The slashable form of `uniqueJust` for different entries (port:
vcE:261). -/
theorem uniqueJust_slashable (E : Electorate V) {A₁ A₂ : Finset (Row V)} {Q₁ Q₂ : Finset V}
    {h : Height} {T₁ T₂ : BlockId} (hne : T₁ ≠ T₂)
    (hQ₁ : E.IsQuorum Q₁) (hQ₂ : E.IsQuorum Q₂)
    (hw₁ : ∀ i ∈ Q₁, ∃ a ∈ A₁, a.signer = i ∧ a.height_pair = .vote h T₁ false)
    (hw₂ : ∀ i ∈ Q₂, ∃ b ∈ A₂, b.signer = i ∧ b.height_pair = .vote h T₂ false) :
    HasSlashableWeightBetween E A₁ A₂ :=
  hasSlashableWeightBetween_of_hasE2WeightAt hne (uniqueJust E hQ₁ hQ₂ hw₁ hw₂)

variable [RowCodec V]

/-- [helper] The justification certificate of a chain, with its witnesses in
the chain's rows. -/
theorem justification_certificate_rows (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hnz : (derive E cfg D).h_j ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ a ∈ chainRows D, a.signer = i ∧
      a.height_pair = .vote (derive E cfg D).h_j (derive E cfg D).J.root false := by
  obtain ⟨Q, hQ, hw⟩ := justification_certificate E cfg D hnz
  refine ⟨Q, hQ, fun i hi => ?_⟩
  obtain ⟨carrier, a, hc, ha, hai, hpa⟩ := hw i hi
  exact ⟨a, mem_chainRows_of_carrier hc ha, hai, hpa⟩

/-- [pin fg.uniqueJust.v1] (chain form) Two chains justified at one height have
the same J, or E2 weight exists between their rows. -/
theorem slashableWeight_or_justified_eq (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂)
    (hh : (derive E cfg B₁).h_j = (derive E cfg B₂).h_j) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      (derive E cfg B₁).J = (derive E cfg B₂).J := by
  by_cases hz : (derive E cfg B₁).h_j = 0
  · refine Or.inr ?_
    rw [justified_zero_is_genesis E cfg B₁ hz,
      justified_zero_is_genesis E cfg B₂ (hh.symm.trans hz)]
  · by_cases hr : (derive E cfg B₁).J.root = (derive E cfg B₂).J.root
    · exact Or.inr (hroot _ _ (Or.inl ((derive_anchors_preceq E cfg B₁).2)) (Or.inr
      ((derive_anchors_preceq E cfg B₂).2)) hr)
    · obtain ⟨Q₁, hQ₁, hw₁⟩ := justification_certificate_rows E cfg B₁ hz
      obtain ⟨Q₂, hQ₂, hw₂⟩ := justification_certificate_rows E cfg B₂ (hh ▸ hz)
      rw [← hh] at hw₂
      exact Or.inl (uniqueJust_slashable E hr hQ₁ hQ₂ hw₁ hw₂)

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `slashableWeight_or_justified_eq`.
Delete after F2 (GLY E-13). -/
theorem uniqueJust_chains (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂)
    (hh : (derive E cfg B₁).h_j = (derive E cfg B₂).h_j) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      (derive E cfg B₁).J = (derive E cfg B₂).J :=
  slashableWeight_or_justified_eq E cfg B₁ B₂ hroot hh

/-! ## `fg.finalLock.v1` -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50-85
-- (finalized_preceq_of_height_lt)
/-- [helper] The E1 form of `finalLock`: `W` extends `F(B)`, or the finality
quorum of `B` and the crossing quorum of `W` at `h_F(B)` meet in `2q − W` weight
of E1 pairs, with the finality row from `B`'s chain first. -/
theorem e1Weight_or_finalized_preceq (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasE1WeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W := by
  by_cases hz : (derive E cfg B).h_F = 0
  · refine Or.inr ?_
    rw [finalized_zero_is_genesis E cfg B hz]
    exact genesis_preceq W
  · obtain ⟨F, -, rfl, Qf, hQf, hwf⟩ := finality_certificate E cfg B hz
    obtain ⟨X, hXW, -, Qc, hQc, hwc⟩ :=
      height_crossing E cfg W _ (Nat.one_le_iff_ne_zero.mpr hz) hh
    by_cases hr : X.root = (derive E cfg B).F.root
    · refine Or.inr ?_
      rw [← hroot _ _ (Or.inr hXW) (Or.inl ((derive_anchors_preceq E cfg B).1)) hr]
      exact hXW
    · refine Or.inl ⟨Qf ∩ Qc, quorum_intersection E hQf hQc, fun i hi => ?_⟩
      obtain ⟨hf, hc⟩ := Finset.mem_inter.mp hi
      obtain ⟨cB, b, hcB, hb, hbi, hbf⟩ := hwf i hf
      obtain ⟨cW, a, hcW, ha, hai, ham⟩ := hwc i hc
      exact ⟨b, mem_chainRows_of_carrier hcB hb, a, mem_chainRows_of_carrier hcW ha, hbi, hai,
        e1Slashable_of_matchesEntry b a _ X.root _ (hbi.trans hai.symm) hbf ham hr⟩

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `e1Weight_or_finalized_preceq`.
Delete after F2 (GLY E-13). -/
theorem finalLock_e1 (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasE1WeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  e1Weight_or_finalized_preceq E cfg B W hroot hh

/-- [pin fg.finalLock.v1] A block above a finalized height extends the
finalized checkpoint, or E1 weight exists. This is the pure form of the
finalized-crossing law (r148 fj-redteam.md:226); the registered slashable bound
removes the evidence branch. -/
theorem slashableWeight_or_finalized_preceq (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  (e1Weight_or_finalized_preceq E cfg B W hroot hh).imp
    hasSlashableWeightBetween_of_hasE1WeightBetween id

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `slashableWeight_or_finalized_preceq`.
Delete after F2 (GLY E-13). -/
theorem finalLock (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  slashableWeight_or_finalized_preceq E cfg B W hroot hh

/-! ## `fg.accountable.v1` -/

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/WholeRunFinalitySafety.lean:136-193
-- (namedAccountableSafety_oriented; its certificate argument is `finalLock_e1`)
/-- [helper] Accountable safety, oriented by the finalized heights: the lower
finalization and the crossing of its height on the other chain. -/
theorem e1Weight_or_finalized_compatible_of_le (E : Electorate V) (cfg : FGConfig)
    (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂)
    (hle : (derive E cfg B₁).h_F ≤ (derive E cfg B₂).h_F) :
    HasE1WeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true := by
  have hlt : (derive E cfg B₁).h_F < (derive E cfg B₂).h :=
    Nat.lt_of_le_of_lt hle (finalized_below_height E cfg B₂)
  rcases e1Weight_or_finalized_preceq E cfg B₁ B₂ hroot hlt with hev | hF
  · exact Or.inl hev
  · exact Or.inr (compatible_of_preceq_common hF (derive_anchors_preceq E cfg B₂).1)

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `e1Weight_or_finalized_compatible_of_le`.
Delete after F2 (GLY E-13). -/
theorem accountable_oriented (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂)
    (hle : (derive E cfg B₁).h_F ≤ (derive E cfg B₂).h_F) :
    HasE1WeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true :=
  e1Weight_or_finalized_compatible_of_le E cfg B₁ B₂ hroot hle

-- port: DC/DecoupledConsensusProofs/Protocol/ChainState/WholeRunFinalitySafety.lean:195-213
-- (namedChainAccountableSafety)
/-- [pin fg.accountable.v1] (conflicting finalizations) Two finalized
checkpoints are compatible, or the two chains' rows convict weight `2q − W`
(E1 or E2). -/
theorem slashableWeight_or_finalized_compatible (E : Electorate V) (cfg : FGConfig)
    (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true := by
  rcases Nat.le_total (derive E cfg B₁).h_F (derive E cfg B₂).h_F with hle | hle
  · exact (e1Weight_or_finalized_compatible_of_le E cfg B₁ B₂ hroot hle).imp
      hasSlashableWeightBetween_of_hasE1WeightBetween id
  · rcases e1Weight_or_finalized_compatible_of_le E cfg B₂ B₁ hroot.symm hle with hev | hc
    · exact Or.inl (hasSlashableWeightBetween_of_hasE1WeightBetween_swap hev)
    · exact Or.inr ((compatible_comm _ _).trans hc)

set_option linter.unusedVariables false in
/-- Compatibility wrapper for `slashableWeight_or_finalized_compatible`.
Delete after F2 (GLY E-13). -/
theorem accountable (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true :=
  slashableWeight_or_finalized_compatible E cfg B₁ B₂ hroot

end AvailableChain.KitFG
end

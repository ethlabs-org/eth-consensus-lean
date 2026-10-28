module
public import ConsensusShape.Problem
public import ConsensusShape.Transfer
public import ConsensusShape.Payload
public import ConsensusModelProofs.Laws
@[expose] public section
namespace Consensus.Shape
open Model
open Run
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family} {E : Env V}

omit [Nonempty V] in
/-- The compiled ledger trace is exactly the prefix-preserving image of the chain trace. -/
theorem ledgerTrace (rho : Model.Run (compiled F) E) :
    (Model.sysOf (compiled F) V).trace ⟨E, rho⟩ = (chainTrace rho).map ledgerOf := by
  unfold Model.sysOf Trace.map chainTrace Model.Run.readIdx readChainIdx
  change (Trace.mk _ _ _ _) = (Trace.mk _ _ _ _)
  congr 1
  funext g v i
  cases g <;> rfl

/-- Apply growth at the requested read time minus its latency. The resulting
honest proposal is after submission, so its encoded mempool contains the transaction. -/
theorem liveFrom_txLive (rho : Model.Run (compiled F) E) {C : Constants}
    {g : Out} {start : Time} {d : Nat}
    (hl : LiveFrom rho C (match g with
      | .confirmed => (protoOf F E).confirmed
      | .stable => (protoOf F E).stable
      | .finalized => (protoOf F E).finalized) start d) :
    ((chainTrace rho).map ledgerOf).TxLive ((C.catchUp : Time) * E.Δ) g start
      ((d : Time) * E.Δ) := by
  intro x t t' ht hs hdt hh v hv
  dsimp only [Time] at *
  obtain ⟨s, h, hp, _, hprop, hin, _⟩ := hl (t' - (d : Time) * E.Δ)
    (le_trans ht (le_sub_iff_add_le.mpr hdt))
    (by simpa only [sub_add_cancel] using (show t' ≤ rho.horizon from hh))
  have he : t' - (d : Time) * E.Δ + (d : Time) * E.Δ = t' := sub_add_cancel _ _
  rw [he] at hin
  have hin' := hin v hv
  have hmem : x ∈ decodeTxs h.input := by
    rw [honestProposal_payload rho hprop, decode_encodeTxs]
    exact submitted_mem_mempool rho hprop.1 hs (le_trans (le_sub_iff_add_le.mpr hdt) (le_of_lt hp))
  change x ∈ ledgerOf ((chainTrace rho).read g v ((chainTrace rho).endCut t'))
  apply (mem_ledgerOf _ _).mpr
  refine ⟨h, ?_, hmem⟩
  cases g <;> exact hin'

/-- Every shape claim refines its corresponding consensus-problem claim. -/
theorem refinement (C : Constants) : RefinementStatement F C V := by
  intro hc
  constructor
  · exact Model.sysOf_laws _ _
  · rintro ⟨E, rho⟩ hv
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.outputOrder V E rho hv).map ledgerOf_prefix
  · rintro ⟨E, rho⟩ hv
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.finalizedMonotone V E rho hv).map ledgerOf_prefix
  · rintro ⟨E, rho⟩ hv v hh hs
    apply hc.honestNeverSlashed V E rho hv v hh
    rcases hs with ⟨o, ho, o', ho', ha, ha', hconf⟩
    refine ⟨o, ?_, o', ?_, ha, ha', hconf⟩
    · rcases ho with ⟨w, hw, z, hz, he⟩
      cases he
      exact ⟨w, hw, hz⟩
    · rcases ho' with ⟨w, hw, z, hz, he⟩
      cases he
      exact ⟨w, hw, hz⟩
  · rintro ⟨E, rho⟩ hv _
    rcases hc.finalizedAccountable V E rho hv with ha | he
    · left
      intro u hu v hv i j hi hj
      rcases ha u hu v hv i j hi hj with hh | hh
      · left
        exact Compatible.map ledgerOf_prefix hh
      · right
        convert hh using 2
        congr 1
        apply Finset.ext
        intro x
        simp only [System.convicted, slashedBy, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨o, ho, o', ho', h₁, h₂, h₃⟩
          refine ⟨o, ?_, o', ?_, h₁, h₂, h₃⟩
          · rcases ho with h | h
            · obtain ⟨z, hz, he⟩ := h; cases he; exact Or.inl hz
            · obtain ⟨z, hz, he⟩ := h; cases he; exact Or.inr hz
          · rcases ho' with h | h
            · obtain ⟨z, hz, he⟩ := h; cases he; exact Or.inl hz
            · obtain ⟨z, hz, he⟩ := h; cases he; exact Or.inr hz
        · rintro ⟨o, ho, o', ho', h₁, h₂, h₃⟩
          refine ⟨o, ?_, o', ?_, h₁, h₂, h₃⟩
          · rcases ho with ho | ho
            · exact Or.inl ⟨o, ho, rfl⟩
            · exact Or.inr ⟨o, ho, rfl⟩
          · rcases ho' with ho | ho
            · exact Or.inl ⟨o', ho, rfl⟩
            · exact Or.inr ⟨o', ho, rfl⟩
    · exact Or.inr he
  · rintro ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.confirmedSafe V E rho ha).imp (fun h => h.map ledgerOf_prefix) id
  · rintro ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.stableSafe V E rho ha).imp (fun h => h.map ledgerOf_prefix) id
  · rintro k ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.confirmedLive V E rho k ha).imp (liveFrom_txLive rho) id
  · rintro k ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.stableLive V E rho k ha).imp (liveFrom_txLive rho) id
  · rintro T b₀ b₁ ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.stableResilient V E rho T b₀ b₁ ha).imp (fun h => h.map ledgerOf_prefix) id
  · rintro T b₀ b₁ ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.stableResilientFast V E rho T b₀ b₁ ha).imp (fun h => h.map ledgerOf_prefix) id
  · rintro k ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.recovered V E rho k ha).imp
      (fun h => ⟨h.confirmedSafe.map ledgerOf_prefix, h.stableSafe.map ledgerOf_prefix⟩) id
  · rintro k ⟨E, rho⟩ _ ha
    try dsimp only []
    simp only [ledgerTrace]
    exact (hc.finalizedLive V E rho k ha).imp (liveFrom_txLive rho) id
end Consensus.Shape
end

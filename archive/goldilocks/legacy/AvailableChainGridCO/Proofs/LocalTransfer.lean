module
public import AvailableChainGridCO.Proofs.MergedViews

@[expose] public section
namespace AvailableChain.GridCO
open AvailableChain.Generic AvailableChain.Statements.Generic
set_option linter.unusedSectionVars false
variable [LeasePolicy]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A reader's own early resolved HEAD is present and resolved at its
ordinary freeze. This uses local receipt history, with no relay premise. -/
theorem local_early_at_freeze {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (reader : V)
    (o : Wire p.n) (ho : o ∈ earlyVotes p (gateInput p rho r reader) r) :
    o ∈ votesAt (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r ∧
    resolvedBefore (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader)
      o (freezeTime p r) = true := by
  have hs := hx.toScheduleWellFormed
  obtain ⟨hraw, hres⟩ := List.mem_filter.mp ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hraw
  cases hb : o.payload with
  | proposal b raw support => simp [headLabel?, hb] at hl
  | head B =>
    have htarget : headTarget? o = some B := by simp [headTarget?, hb]
    simp only [resolvedBefore_block, htarget, Bool.and_eq_true,
      decide_eq_true_eq, blockKnown] at hres
    have hpub : PublicTime E (earlyTime p r) := by
      refine ⟨4 * r + 2, ?_⟩
      simp only [earlyTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hz : 0 ≤ earlyTime p r := by
      dsimp [earlyTime, proposalTime]
      nlinarith [p.deltaPos, Int.natCast_nonneg r]
    have hef : earlyTime p r ≤ freezeTime p r := by
      dsimp [earlyTime, freezeTime]; linarith [p.deltaPos]
    have hvote := hres.1.2
    change o ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) reader).votes at hm
    change stampVote (Run.stateBeforeTime (gridCO p) rho (gateTime p r) reader) o < _ at hvote
    rw [time_input_eq_event_prefix p E rho hs] at hm hvote
    obtain ⟨i, _, t, ha, ht⟩ := stored_head_accepted_before p E rho hs _ reader o _ hpub hz hm hvote
    obtain ⟨parent, hi, _⟩ := ha.1
    have hpost : o ∈ (Run.stateBefore (gridCO p) rho (i + 1) reader).votes := by
      simpa [gridCO, processed, hb] using ha.2.2
    obtain ⟨hmem, hstamp⟩ := stored_vote_stamp_before_cut p E rho hs hi hpost ht hef
    have hB : B ∈ (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader).blocks ∧
        stampBlock (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) B <
          freezeTime p r := by
      by_cases hg : B = .genesis
      · subst B
        obtain ⟨hm, he⟩ := genesis_stored_at_time p E rho hs (freezeTime p r) reader
        refine ⟨hm, ?_⟩
        rw [he]
        dsimp [freezeTime, proposalTime]
        nlinarith [p.deltaPos, Int.natCast_nonneg r]
      · have hstored := hres.1.1.1
        have hbstamp := hres.2
        change B ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) reader).blocks at hstored
        change stampBlock (Run.stateBeforeTime (gridCO p) rho (gateTime p r) reader) B <
          _ at hbstamp
        rw [time_input_eq_event_prefix p E rho hs] at hstored hbstamp
        obtain ⟨j, _, u, obj, raw, support, hp, ha, hu⟩ :=
          stored_block_accepted_before p E rho hs _ reader B _ hg hpub hz hstored hbstamp
        obtain ⟨parent, hj, _⟩ := ha.1
        exact stored_block_stamp_before_cut p E rho hs hj
          (by simpa [gridCO, processed, hp, blockKnown] using ha.2.2) (hu.trans_le hef) (le_refl _)
    exact ⟨List.mem_filter.mpr ⟨hmem, hl⟩, by
      refine (resolvedBefore_block _ o _).trans ?_
      simp only [htarget, Bool.and_eq_true, decide_eq_true_eq, blockKnown]
      exact ⟨⟨⟨hB.1, hres.1.1.2⟩, hstamp.trans_le hef⟩, hB.2⟩⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Local frozen and merged views satisfy the transfer receipt conditions
against that reader's own later gate. This holds during an outage. -/
theorem local_transferReceipts {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (B : Block) :
    TransferReceipts p (gateInput p rho r reader) r (nextHeadState p rho r reader).blocks
      (voterView p (nextHeadState p rho r reader) (r + 1))
      (voterSupportView p (nextHeadState p rho r reader) (r + 1)) B := by
  have hs := hx.toScheduleWellFormed
  refine ⟨?_, ?_, nextHeadState_support_subset_raw_of_execution p E rho hΔ r hx hh reader hr⟩
  · intro o ho _
    obtain ⟨hm, hres⟩ := local_early_at_freeze p E rho hΔ hx r reader o (List.mem_filter.mp ho).1
    have hold := (resolvedBefore_block _ o _).symm.trans hres
    cases ht : headTarget? o with
    | none => simp [ht] at hold
    | some target =>
      have htree : target ∈
          (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader).blocks := by
        have h := hold
        simp only [ht, Bool.and_eq_true, decide_eq_true_eq, blockKnown] at h
        exact h.1.1.1
      refine ⟨?_, target, rfl,
        (freezeInput_receiptPrefix_nextHead p E rho hs r reader).blocks.subset htree⟩
      simp only [voterSupportView, Nat.add_sub_cancel,
        nextHeadState_frozenAt_of_execution p E rho hΔ r hx hh reader hr]
      exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_filter.mpr ⟨hm, hres⟩))
  · intro o ho i hi
    have hsub : votesAt (releaseInput p rho r reader) r ⊆
        lateVotes p (gateInput p rho r reader) r := by
      intro q hq
      obtain ⟨hq, hlabel⟩ := List.mem_filter.mp hq
      have hprefix := time_input_receiptPrefix p E rho hs (releaseTime p r) (gateTime p r)
        (by dsimp [releaseTime, gateTime]; linarith [p.deltaPos]) reader
      have hstamp := (time_input_stamps_lt p E rho hs (gateTime p r)
        (by dsimp [gateTime, proposalTime]
            nlinarith [p.deltaPos, Int.natCast_nonneg r]) reader).1 q
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hprefix.votes.subset hq, hlabel⟩,
        decide_eq_true hstamp⟩
    rcases nextHeadState_raw_receipt_of_execution p E rho hΔ r hx hh reader hr o i hi ho
      with hm | he
    · exact Or.inl (hsub hm)
    · exact Or.inr (equivocates_mono _ _ i hsub he)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A local genuine prefix transfers to the preceding would-be HEAD when
its live root is compatible. The statement needs no synchronous relay. -/
theorem local_transfer_from_engine {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho r reader) r = some C) (hp : Block.Preceq B C)
    (hroot : Block.Compatible (liveRoot (nextHeadState p rho r reader)) B) :
    Block.Preceq B (nextHead p (nextHeadState p rho r reader) r) := by
  have hpositive : 0 < (prefixSupportSeats p (gateInput p rho r reader) r B).card := by
    have hm := confirmation_majority p (gateInput p rho r reader) r C hc
    have hle := prefixSupport_mono p (gateInput p rho r reader) r B C hp
    rw [prefixSupport_eq_card p _ r B] at hle
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpositive
  obtain ⟨o, ho, _, target, ht, htarget⟩ :=
    prefixSupportSeats_witness p (gateInput p rho r reader) r B i hi
  obtain ⟨_, hres⟩ := local_early_at_freeze p E rho hΔ hx r reader o (List.mem_filter.mp ho).1
  have htargetmem : target ∈
      (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader).blocks := by
    have hres := (resolvedBefore_block _ o _).symm.trans hres
    simp only [ht, Bool.and_eq_true, decide_eq_true_eq, blockKnown] at hres
    exact hres.1.1.1
  apply forkChoice_covers_of_transfer p (gateInput p rho r reader)
    (nextHeadState p rho r reader) r (r + 1) _ _ _ B C hc hp
    (local_transferReceipts p E rho hΔ hx r hh reader hr B) hroot
  intro A hn hA
  have hstored := run_time_stored_prefix_closed p rho (freezeTime p r) reader target
    htargetmem A hn (prefix_trans A B target hA htarget)
  apply List.mem_filter.mpr
  have hprefix := freezeInput_receiptPrefix_nextHead p E rho hx.toScheduleWellFormed r reader
  refine ⟨hprefix.blocks.subset hstored, Bool.or_eq_true_iff.mpr (Or.inl ?_)⟩
  simp only [Nat.add_sub_cancel,
    nextHeadState_frozenAt_of_execution p E rho hΔ r hx hh reader hr]
  rw [(freezeView_at_input p E rho hx.toScheduleWellFormed r reader).2]
  exact decide_eq_true hstored

end AvailableChain.GridCO
end

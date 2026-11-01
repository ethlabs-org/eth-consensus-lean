module
public import AvailableChainGridCO.Proofs.Frozen
public import AvailableChainGridCO.Proofs.Transfer

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem early_public {V : Type} (p : Params) (E : Env V)
    (hΔ : E.Δ = p.Δ) (r : Slot) : PublicTime E (earlyTime p r) := by
  refine ⟨4 * r + 2, ?_⟩
  simp only [earlyTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem early_nonneg (p : Params) (r : Slot) : 0 ≤ earlyTime p r := by
  dsimp [earlyTime, proposalTime]
  nlinarith [p.deltaPos, Int.natCast_nonneg r]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A surviving early HEAD is present before the ordinary freeze with a stamp before the
ordinary freeze. This includes faulty support and sleeping readers. -/
theorem synchronous_early_head_at_freeze {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ cleanSupport p (gateInput p rho r source) r) :
    o ∈ votesAt (Run.stateBeforeTime (gridCO p) rho
      (freezeTime p r) reader) r ∧
      stampVote (Run.stateBeforeTime (gridCO p) rho
        (freezeTime p r) reader) o < freezeTime p r := by
  have hearly := (List.mem_filter.mp ho).1
  obtain ⟨hraw, hres⟩ := List.mem_filter.mp hearly
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hraw
  have hhead : ∃ B, o.payload = .head B := by
    cases ho : o.payload <;> simp_all [headLabel?]
  obtain ⟨B, hb⟩ := hhead
  have ht : stampVote (gateInput p rho r source) o < earlyTime p r := by
    simp only [resolvedBefore_block, headTarget?, hb, Bool.and_eq_true, decide_eq_true_eq] at hres
    exact hres.1.2
  change o ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source).votes at hm
  change stampVote (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source) o < _ at ht
  rw [time_input_eq_event_prefix p E rho hsync.1.toScheduleWellFormed] at hm ht
  obtain ⟨index, _, t, ha, ht⟩ := stored_head_accepted_before p E rho
    hsync.1.toScheduleWellFormed _ source o (earlyTime p r)
      (early_public p E hΔ r) (early_nonneg p r) hm ht
  have hsettle := synchronous_accepted_head_before p E rho hΔ r hsync source reader hs hr
    index o B t (freezeTime p r) (freezeTime p r) hb (by simpa using hl) ha
    (by rw [hΔ]; dsimp [earlyTime, freezeTime] at *; linarith)
    (by rw [hΔ]; dsimp [freezeTime]; linarith [p.deltaPos])
    (by dsimp [freezeTime, gateTime]; linarith [p.deltaPos])
    (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos])
  obtain ⟨i, hi⟩ : ∃ i, headSeat? o = some i := by
    cases o with
    | mk auth payload => cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?]
  have hne := synchronous_survivor_not_equivocating p E rho hΔ r hsync
    source reader hs hr o i ho hi
  have hsub : stampedVotes (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader)
      r (freezeTime p r) ⊆ votesAt (releaseInput p rho r reader) r := by
    intro q hq
    obtain ⟨hq, _⟩ := List.mem_filter.mp hq
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hq
    apply List.mem_filter.mpr
    refine ⟨?_, hl⟩
    exact (time_input_receiptPrefix p E rho hsync.1.toScheduleWellFormed
      (freezeTime p r) (releaseTime p r)
      (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos]) reader).votes.subset hm
  have hm := (hsettle i hi).resolve_right (fun he => by
    have he' := equivocates_mono _ _ i hsub he
    rw [hne] at he'
    contradiction)
  obtain ⟨hm, hstamp⟩ := List.mem_filter.mp hm
  exact ⟨hm, of_decide_eq_true hstamp⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The target of an early resolved HEAD is stored before the ordinary freeze with
an early block stamp. Its accepted proposal relays independently of the HEAD. -/
theorem synchronous_early_target_at_freeze {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (B : Block) (hb : headTarget? o = some B)
    (ho : o ∈ earlyVotes p (gateInput p rho r source) r) :
    B ∈ (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader).blocks ∧
      stampBlock (Run.stateBeforeTime (gridCO p) rho
        (freezeTime p r) reader) B < freezeTime p r := by
  have hsched := hsync.1.toScheduleWellFormed
  by_cases hn : B = .genesis
  · subst B
    obtain ⟨hm, ht⟩ := genesis_stored_at_time p E rho hsched (freezeTime p r) reader
    refine ⟨hm, ?_⟩
    rw [ht]
    dsimp [freezeTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hres := (List.mem_filter.mp ho).2
  simp only [resolvedBefore_block, hb, Bool.and_eq_true, decide_eq_true_eq, blockKnown] at hres
  have hm := hres.1.1.1
  have ht := hres.2
  change B ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source).blocks at hm
  change stampBlock (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source) B < _ at ht
  rw [time_input_eq_event_prefix p E rho hsched] at hm ht
  obtain ⟨index, _, t, obj, raw, support, hp, ha, ht⟩ := stored_block_accepted_before p E rho
    hsched _ source B (earlyTime p r) hn (early_public p E hΔ r) (early_nonneg p r) hm ht
  obtain ⟨j, e, hj, he, hstored⟩ := synchronous_accepted_block_before p E rho hΔ r hsync
    source reader hs hr index obj t (freezeTime p r) hp ha
    (by rw [hΔ]; dsimp [earlyTime, freezeTime] at *; linarith)
    (by rw [hΔ]; dsimp [freezeTime]; linarith [p.deltaPos])
    (by dsimp [freezeTime, gateTime]; linarith [p.deltaPos])
  exact stored_block_stamp_before_cut p E rho hsched hj
    (by simpa [processed, hp, blockKnown] using hstored) he
    (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos])

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Receipt lists before the ordinary freeze remain available after release. -/
theorem freezeInput_receiptPrefix_nextHead {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (r : Slot) (reader : V) :
    ReceiptPrefix (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader)
      (nextHeadState p rho r reader) := by
  apply (time_input_receiptPrefix p E rho hs (freezeTime p r) (releaseTime p r)
    (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos]) reader).trans
  have hd := clock_receiptData p (releaseInput p rho r reader) (releaseTime p r)
  have ⟨h1, h2, h3, h4⟩ :
      (nextHeadState p rho r reader).blocks = (releaseInput p rho r reader).blocks ∧
      (nextHeadState p rho r reader).blockStamp = (releaseInput p rho r reader).blockStamp ∧
      (nextHeadState p rho r reader).votes = (releaseInput p rho r reader).votes ∧
      (nextHeadState p rho r reader).voteStamp = (releaseInput p rho r reader).voteStamp := by
    simpa [receiptData, nextHeadState] using hd
  constructor <;> simp_all [releaseInput]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Forward relay places every surviving early HEAD in the actual next
ordinary support view, even if a proposal omits it from declared support. -/
theorem synchronous_early_head_in_voterSupport {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ cleanSupport p (gateInput p rho r source) r) :
    o ∈ voterSupportView p (nextHeadState p rho r reader) (r + 1) ∧
      ∃ B, headTarget? o = some B ∧ B ∈ (nextHeadState p rho r reader).blocks := by
  obtain ⟨hm, ht⟩ := synchronous_early_head_at_freeze p E rho hΔ r hsync source reader hs hr o ho
  have hearly := (List.mem_filter.mp ho).1
  have hres := (List.mem_filter.mp hearly).2
  cases hb : headTarget? o with
  | none => simp [resolvedBefore_block, hb] at hres
  | some B =>
      obtain ⟨hB, hstamp⟩ := synchronous_early_target_at_freeze p E rho hΔ r hsync
        source reader hs hr o B hb hearly
      have hresolved : resolvedBefore
          (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader)
          o (freezeTime p r) = true := by
        refine (resolvedBefore_block
          (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader)
          o (freezeTime p r)).trans ?_
        rw [hb]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        simp only [resolvedBefore_block, hb, Bool.and_eq_true, decide_eq_true_eq] at hres
        exact ⟨⟨⟨by simpa [blockKnown] using hB, hres.1.1.2⟩, ht⟩, hstamp⟩
      refine ⟨?_, B, rfl, (freezeInput_receiptPrefix_nextHead p E rho
        hsync.1.toScheduleWellFormed r reader).blocks.subset hB⟩
      simp only [voterSupportView, Nat.add_sub_cancel,
        nextHeadState_frozenAt p E rho hΔ r hsync reader hr]
      apply List.mem_eraseDups.mpr
      exact List.mem_append_left _ (List.mem_filter.mpr ⟨hm, hresolved⟩)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every non-genesis ancestor of an early HEAD target lies in the actual
next voter tree. The saved block domain supplies the full path at once. -/
theorem synchronous_early_path_in_voterTree {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ earlyVotes p (gateInput p rho r source) r)
    (target B : Block) (ht : headTarget? o = some target)
    (hn : B ≠ .genesis) (hp : Block.Preceq B target) :
    B ∈ voterTree p (nextHeadState p rho r reader) (r + 1) := by
  have htarget := (synchronous_early_target_at_freeze p E rho hΔ r hsync
    source reader hs hr o target ht ho).1
  have hB := run_time_stored_prefix_closed p rho (freezeTime p r) reader target htarget B hn hp
  apply List.mem_filter.mpr
  refine ⟨(freezeInput_receiptPrefix_nextHead p E rho
    hsync.1.toScheduleWellFormed r reader).blocks.subset hB, ?_⟩
  apply Bool.or_eq_true_iff.mpr
  apply Or.inl
  simp only [Nat.add_sub_cancel, nextHeadState_frozenAt p E rho hΔ r hsync reader hr]
  rw [(freezeView_at_input p E rho hsync.1.toScheduleWellFormed r reader).2]
  exact decide_eq_true hB

end AvailableChain.GridCO
end

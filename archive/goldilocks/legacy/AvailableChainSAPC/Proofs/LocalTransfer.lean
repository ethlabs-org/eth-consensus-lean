module
public import AvailableChainSAPC.Proofs.GenuineTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A reader retains its own early resolved HEAD and target at the
freeze. No forward relay is needed across the outage boundary. -/
theorem local_early_at_freeze {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (i : Fin p.n) (b : Block)
    (early : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈ GridCO.earlyVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    let st := (Run.stateBeforeTime (sapc p) rho (freezeTime p r) v).base
    b ∈ st.blocks ∧
      (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈ (GridCO.freezeView p.engine st r).2.1 := by
  obtain ⟨key, block⟩ := early_head_at_early p E rho hs hΔ r v _ b rfl early
  have time : earlyTime p r ≤ freezeTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have receipts := time_input_base_receiptPrefix p E rho hs _ _ time v
  have stored := receipts.blocks.subset block
  refine ⟨stored, ?_⟩
  apply List.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply List.mem_filter.mpr
    exact ⟨receipts.votes.subset key, by simp [GridCO.headLabel?]⟩
  · have resolved := (List.mem_filter.mp early).2
    simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
      Option.getD_some, Bool.and_eq_true_iff, decide_eq_true_eq] at resolved
    have positive : 0 < freezeTime p r := by
      change 0 < 4 * p.Δ * (r : Time) + 3 * p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg r]
    have stamps := time_input_stamps_lt p E rho hs _ positive v
    simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
      Option.getD_some, Bool.and_eq_true_iff, decide_eq_true_eq, GridCO.blockKnown]
    exact ⟨⟨⟨stored, resolved.1.1.2⟩, stamps.1 _⟩, stamps.2 _⟩

/-- The reader's local frozen receipts and local reverse receipts supply
the same SA transfer object as healthy cross-reader relay. -/
theorem local_genuine_transfer_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (hv : v ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon) (B : Block) :
    GridCO.TransferReceipts p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r
      (headState p rho (r + 1) v).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) v).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) v).base (r + 1)) B := by
  have back := local_back_receipts p E rho hx.toScheduleWellFormed r v
  apply genuine_transfer_receipts_of_support p E rho hx r v v B _ back
  apply cleanSupport_in_voterSupport_of_frozen_receipts p E rho hx.toScheduleWellFormed
    hΔ r v v hv hh _ back
  intro i b early
  have localReceipt := local_early_at_freeze p E rho hx.toScheduleWellFormed hΔ r v i b early
  exact ⟨localReceipt.1, Or.inl localReceipt.2⟩

/-- Positive local genuine support supplies the complete path in the next
ordinary HEAD domain, including when the reader is asleep. -/
theorem local_genuine_path_in_voterTree {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (hv : v ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C) (nonzero : B ≠ .genesis) :
    B ∈ GridCO.voterTree p.engine (headState p rho (r + 1) v).base (r + 1) := by
  have majority := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r C raw
  have mono := GridCO.prefixSupport_mono p.engine
    (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B C below
  have positive : 0 < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B := by omega
  rw [GridCO.prefixSupport_eq_card] at positive
  obtain ⟨i, hi⟩ := Finset.card_pos.mp positive
  obtain ⟨o, ho, seat, target, targetEq, belowTarget⟩ :=
    GridCO.prefixSupportSeats_witness p.engine _ r B i hi
  have early := (List.mem_filter.mp ho).1
  have label : GridCO.headLabel? o = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp early).1).2
  obtain ⟨b, rfl⟩ := GridCO.head_wire_shape o r i label seat
  have eq : b = target := Option.some.inj targetEq
  subst target
  exact path_in_voterTree_of_frozen_target p E rho hs hΔ r v hv hh b B
    (local_early_at_freeze p E rho hs hΔ r v i b early).1 nonzero belowTarget

/-- The pending local raw result transfers before its gate without a
lease for B or any relay premise. Only the finite root and, in active
mode, the selected PC must be compatible with B. -/
theorem local_genuine_activePC_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (hv : v ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C)
    (root : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) v).base) B)
    (cert : capBroken p (headState p rho (r + 1) v) = false →
      ∀ pc, selectedPC p (headState p rho (r + 1) v) (r + 1) = some pc →
        Block.Compatible pc.target B) :
    Block.Preceq B (headData p rho (r + 1) v).target := by
  have receipts := local_genuine_transfer_receipts p E rho hx hΔ r v hv hh B
  have path (a : Block) (hn : a ≠ .genesis) (ha : Block.Preceq a B) :=
    local_genuine_path_in_voterTree p E rho hx.toScheduleWellFormed hΔ r v hv hh a C raw
      (GridCO.prefix_trans a B C ha below) hn
  cases active : capBroken p (headState p rho (r + 1) v) with
  | true =>
    have covers := @GridCO.forkChoice_covers_of_transfer GridCO.slowLeasePolicy p.n
      p.engine _ _ r (r + 1) _ _ _ B C raw below receipts root path
    simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, decide_false, Bool.false_eq_true, ↓reduceIte, active, choice] using! covers
  | false =>
    have covers := choice_covers_of_genuine_transfer p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base
      (headState p rho (r + 1) v) r (r + 1)
      (activeVoterTree p (headState p rho (r + 1) v) (r + 1)
        (selectedPC p (headState p rho (r + 1) v) (r + 1))) _ _ B C
      (selectedPC p (headState p rho (r + 1) v) (r + 1)) raw below receipts
      (fun a hn ha => activeVoterTree_contains_plain p _ _ _ (path a hn ha)) root (cert active)
    simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, decide_false, Bool.false_eq_true, ↓reduceIte, active] using! covers

end AvailableChain.SAPC
end

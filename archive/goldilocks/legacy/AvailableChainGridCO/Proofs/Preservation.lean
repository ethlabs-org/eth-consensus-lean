module
public import AvailableChainGridCO.Proofs.HeadTargets
public import AvailableChainGridCO.Proofs.Support

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An awake honest reader emits its ordinary next HEAD after the release
clock. The signature is the run's seat for that label. -/
theorem next_head_emitted {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (reader : V)
    (hr : reader ∈ rho.honest) (ha : E.awake reader (voteTime p (r + 1)) = true)
    (hh : voteTime p (r + 1) ≤ rho.horizon) :
    Run.emits (gridCO p) E rho reader
      ⟨.seat (r + 1) ((rho.seatOf (r + 1)).symm reader),
        .head (nextHead p (nextHeadState p rho r reader) r)⟩ (voteTime p (r + 1)) := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (voteTime p (r + 1)) := by
    refine ⟨4 * (r + 1) + 1, ?_⟩
    simp only [voteTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    ring
  have ht : 0 ≤ voteTime p (r + 1) := by
    unfold voteTime proposalTime
    exact add_nonneg (mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg _))
      (le_of_lt p.deltaPos)
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp (hx.tick_total reader hr _ hpub ht hh)
  refine ⟨index, hi, ?_⟩
  simp only [Run.emittedAt, ha, ↓reduceIte, List.mem_append]
  apply Or.inl
  apply Or.inl
  apply List.mem_filterMap.mpr
  refine ⟨r + 1, (duties_spec p _ _).mpr rfl, ?_⟩
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hi]
  change ((act p (clock p (Run.stateBeforeTime (gridCO p) rho (voteTime p (r + 1)) reader)
    (voteTime p (r + 1))) (r + 1)).map _) = _
  rw [← release_eq_next_vote]
  simp [act, targetOfBlock, nextHead, nextHeadState, releaseInput]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Synchronous delivery provides the complete resolved early batch for
the next label, including target paths and honest-seat authentication. -/
theorem synchronous_next_head_batch {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho (r + 1)) (B : Block)
    (hcover : ∀ reader ∈ rho.honest,
      Block.Preceq B (nextHead p (nextHeadState p rho r reader) r))
    (reader : V) (hr : reader ∈ rho.honest) :
    ∀ u ∈ awakeAt E rho.honest (voteTime p (r + 1)), ∃ o,
      o ∈ earlyVotes p (gateInput p rho (r + 1) reader) (r + 1) ∧
      headSeat? o = some ((rho.seatOf (r + 1)).symm u) ∧
      ∃ target, headTarget? o = some target ∧ Block.Preceq B target := by
  intro u hu
  obtain ⟨hh, ha⟩ := Finset.mem_filter.mp hu
  have hvote : voteTime p (r + 1) ≤ rho.horizon := by
    apply le_trans _ hsync.horizon
    dsimp [voteTime, earlyTime]
    linarith [p.deltaPos]
  have hem := next_head_emitted p E rho hsync.execution hΔ r u hh ha hvote
  let target := nextHead p (nextHeadState p rho r u) r
  let seat := (rho.seatOf (r + 1)).symm u
  have he : Run.emits (gridCO p) E rho (rho.seatOf (r + 1) seat)
      ⟨.seat (r + 1) seat, .head target⟩ (voteTime p (r + 1)) := by
    simpa [seat] using hem
  refine ⟨⟨.seat (r + 1) seat, .head target⟩, ?_, rfl, target, rfl, hcover u hh⟩
  exact synchronous_honest_head_earlyVotes p E rho hΔ (r + 1) hsync seat target
    (by simpa [seat] using hh) he reader hr

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A complete early honest batch preserves its common prefix in the raw
genuine gate result. Later delivery can be arbitrary. -/
theorem preserve_of_early_delivery
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, EarlyDelivery p E rho (r + 1) →
      AwakeMajority E rho (voteTime p (r + 1)) → ∀ B,
      (∀ reader ∈ rho.honest,
        Block.preceq B (nextHead p (nextHeadState p rho r reader) r) = true) →
      ∀ reader ∈ rho.honest, ∃ C,
        confirmation p (gateInput p rho (r + 1) reader) (r + 1) = some C ∧
        Block.preceq B C = true ∧ B ∈ (gateInput p rho (r + 1) reader).blocks := by
  intro r hsync hm B hcover reader hr
  have hbatch := synchronous_next_head_batch p E rho hΔ r hsync B hcover reader hr
  obtain ⟨C, hc, hp⟩ := confirmation_covers_early_honest_batch p E rho hsync.execution
    (gateTime p (r + 1)) reader (r + 1) B hm hbatch
  refine ⟨C, hc, hp, ?_⟩
  by_cases hg : B = .genesis
  · subst B
    exact (genesis_stored_at_time p E rho hsync.execution.toScheduleWellFormed
      (gateTime p (r + 1)) reader).1
  · have hs := prefixSupport_ge_early_honest_batch p E rho hsync.execution
      (gateTime p (r + 1)) reader (r + 1) B hbatch
    have hpos : 0 < prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B :=
      lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hm) hs
    obtain ⟨target, ht, _, hb⟩ := prefixSupport_target p _ (r + 1) B hpos
    exact run_time_stored_prefix_closed p rho _ reader target ht B hg hb

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Prefix preservation follows from the engine, the label's delivery
premises, and h>a. -/
theorem preserve_from_engine
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, SynchronousLabel p E rho (r + 1) →
      AwakeMajority E rho (voteTime p (r + 1)) → ∀ B,
      (∀ reader ∈ rho.honest,
        Block.preceq B (nextHead p (nextHeadState p rho r reader) r) = true) →
      ∀ reader ∈ rho.honest, ∃ C,
        confirmation p (gateInput p rho (r + 1) reader) (r + 1) = some C ∧
        Block.preceq B C = true ∧ B ∈ (gateInput p rho (r + 1) reader).blocks := by
  intro r hsync
  exact preserve_of_early_delivery p E rho hΔ r (.of_synchronous hsync)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A fresh block covered by every ordinary HEAD repairs the public record
at its 6Δ gate if the local guard permits the write. Early delivery supplies
all receipt and path premises of the repair. -/
theorem read_gate_repairs_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hd : EarlyDelivery p E rho (r + 1))
    (hm : AwakeMajority E rho (voteTime p (r + 1)))
    (hh : gateTime p (r + 1) ≤ rho.horizon) (B : Block) (hslot : B.slot = r + 1)
    (hcover : ∀ reader ∈ rho.honest,
      Block.Preceq B (nextHead p (nextHeadState p rho r reader) r))
    (reader : V) (hr : reader ∈ rho.honest)
    (hg : (gateInput p rho (r + 1) reader).obligations.any
      (fun (target, _, _) => !Block.compatible target B) = false) :
    stable (Run.readAt (gridCO p) rho (proposalTime p (r + 1) + 6 * p.Δ) reader) = B := by
  exact read_gate_repairs_early_honest_batch p E rho hd.execution hΔ (r + 1)
    (Nat.succ_pos r) hh reader hr B hslot hm
    (synchronous_next_head_batch p E rho hΔ r hd B hcover reader hr) hg

end AvailableChain.GridCO
end

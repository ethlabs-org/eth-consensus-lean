module
public import AvailableChainSAPC.Proofs.HeadTargets
public import AvailableChainSAPC.Proofs.Proposals

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

def headState {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (v : V) : State p.n :=
  clock p (Run.stateBeforeTime (sapc p) rho (voteTime p r) v) (voteTime p r)

def headData {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (v : V) : HeadData :=
  let st := headState p rho r v
  let target := headTarget p st r
  ⟨target, ackFor st r target⟩

/-- The duty clock creates no blocks. All selected target paths were
already admitted strictly before the HEAD. -/
theorem headData_target_stored {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (v : V) :
    (headData p rho r v).target ∈
      (Run.stateBeforeTime (sapc p) rho (voteTime p r) v).base.blocks := by
  set_option backward.isDefEq.respectTransparency false in
  have h := headTarget_mem_at_fold p
    ((rho.events.filter (fun e => decide (e.time < voteTime p r))) ++ [.tick v (voteTime p r)])
    v r
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    World.step, Function.update_self] at h
  change headTarget p (headState p rho r v) r ∈ (headState p rho r v).base.blocks at h
  simpa only [headData, headState, clock_blocks] using! h

theorem headData_target_slot {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (v : V) : (headData p rho r v).target.slot ≤ r :=
  stored_before_head_slot_le p E rho hs r v _ (headData_target_stored p rho r v)

/-- Every awake honest seat emits the complete target-and-ack payload
computed at its actual tick. No signature is synthesized from a base key. -/
theorem honest_head_emitted {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (i : Fin p.n)
    (hh : rho.seatOf r i ∈ rho.honest)
    (ha : E.awake (rho.seatOf r i) (voteTime p r) = true)
    (horizon : voteTime p r ≤ rho.horizon) :
    Run.emits (sapc p) E rho (rho.seatOf r i)
      (fromHead ⟨.seat r i, headData p rho r (rho.seatOf r i)⟩) (voteTime p r) := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (voteTime p r) := by
    refine ⟨4 * r + 1, ?_⟩
    change 4 * p.Δ * (r : Time) + p.Δ = (4 * r + 1 : Nat) * E.Δ
    rw [hΔ]
    push_cast
    ring
  have hn : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total _ hh _ hpub hn horizon)
  refine ⟨index, hi, ?_⟩
  simp only [Run.emittedAt, ha, ↓reduceIte, List.mem_append]
  apply Or.inl
  apply Or.inl
  apply List.mem_filterMap.mpr
  refine ⟨r, ((sapc p).duties_spec r _).mpr rfl, ?_⟩
  rw [stateBefore_tick_eq_stateBeforeTime hs hi]
  simp [sapc, act, headData, headState, fromHead]

/-- Transfer an admitted block from a strict input, using the same
accepted-source relay as installed certificates. -/
theorem strict_block_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source deadline : Time)
    (ht : source ≤ deadline) (hrelay : RelayBy p rho source deadline)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b : Block)
    (hb : b ∈ (Run.stateBeforeTime (sapc p) rho source v).base.blocks) :
    b ∈ (Run.stateBeforeTime (sapc p) rho deadline w).base.blocks := by
  have he : Run.stateBeforeTime (sapc p) rho source = Run.readAt (sapc p) rho (source - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [he] at hb
  apply read_block_relay p E rho hs (source - 1) deadline (by linarith) _ v w hv hw b hb
  intro u hu i o t htime ha reader hr hn
  exact hrelay u hu i o t (le_of_lt (Int.le_sub_one_iff.mp htime)) ha reader hr hn

/-- An honest HEAD's whole admitted target path relays by its early
deadline. The sender need not emit a separate path-carrying message. -/
theorem headData_target_at_early {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) :
    (headData p rho r v).target ∈
      (Run.stateBeforeTime (sapc p) rho (earlyTime p r) w).base.blocks := by
  have he : max (voteTime p r) E.t_GST + E.Δ = earlyTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 2 * p.Δ
    ring
  apply strict_block_relay p E rho hs (voteTime p r) (earlyTime p r)
    (by change 4 * p.Δ * (r : Time) + p.Δ ≤ _; change _ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
        linarith [p.deltaPos]) _ v w hv hw _ (headData_target_stored p rho r v)
  rw [← he]
  exact synchronous_relayBy p E rho (voteTime p r) hrelay (by rwa [he])

end AvailableChain.SAPC
end

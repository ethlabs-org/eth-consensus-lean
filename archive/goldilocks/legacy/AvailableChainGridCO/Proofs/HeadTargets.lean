module
public import AvailableChainGridCO.Proofs.Paths

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every obligation target remains in the local block store. -/
def TargetsStored {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.obligations, row.1 ∈ st.blocks

private theorem write_targetsStored {n : Nat} (st : State n) (B : Block)
    (g : Nat) (deadline : Time) (h : TargetsStored st) (hb : B ∈ st.blocks) :
    TargetsStored (writeObligation st B g deadline) := by
  intro row hr
  rcases List.mem_append.mp hr with hold | hnew
  · exact h row (List.mem_filter.mp hold).1
  · have he := List.mem_singleton.mp hnew
    simpa [he] using! hb

private theorem writeKeys_targetsStored {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (deadline : Time)
    (h : TargetsStored st) (hk : ∀ key ∈ keys, key.1 ∈ st.blocks) :
    TargetsStored (writeKeys st keys deadline) := by
  induction keys generalizing st with
  | nil => exact h
  | cons key keys ih =>
      apply ih (writeObligation st key.1 key.2 deadline)
        (write_targetsStored st key.1 key.2 deadline h (hk key (by simp)))
      intro x hx
      exact hk x (List.mem_cons_of_mem key hx)

private theorem gate_targetsStored (p : Params) {n : Nat} (st : State n)
    (r : Slot) (h : TargetsStored st) : TargetsStored (gate p st r) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! h
  | some B =>
      by_cases hg : st.obligations.any (fun (target, _, _) => !Block.compatible target B) = true
      · simpa [gate, hc, hg] using! h
      · have hg' := Bool.eq_false_iff.mpr hg
        rw [gate_eq_writeKeys p st r B hc hg']
        refine writeKeys_targetsStored _ _ _ ?_ ?_
        · exact h
        · intro key hk
          obtain ⟨C, hC, hmap⟩ := List.mem_flatMap.mp hk
          obtain ⟨g, _, he⟩ := List.mem_map.mp hmap
          rw [← he]
          exact (List.mem_filter.mp hC).1

theorem clock_targetsStored (p : Params) {n : Nat} (st : State n)
    (t : Time) (h : TargetsStored st) : TargetsStored (clock p st t) := by
  have hpre : TargetsStored (clockPreGate p st t) := by
    intro row hr
    have hb := h row (clockPreGate_obligations_subset p st t row hr)
    have he := congrArg Prod.fst (clockPreGate_receiptData p st t)
    change (clockPreGate p st t).blocks = st.blocks at he
    rw [he]
    exact hb
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · exact gate_targetsStored p _ _ hpre
  · exact hpre

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
All reachable obligations refer to stored blocks, without synchrony. -/
theorem run_targetsStored {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (i : Nat) (reader : V) :
    TargetsStored (Run.stateBefore (gridCO p) rho i reader) := by
  set_option backward.isDefEq.respectTransparency false in
  induction i with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial, TargetsStored]
  | succ i ih =>
      cases hi : rho.events[i]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick v t =>
              by_cases hv : reader = v
              · subst v
                simpa [World.step] using! clock_targetsStored p _ t ih
              · simpa [World.step, hv] using ih
          | deliver v o t =>
              by_cases hv : reader = v
              · subst v
                simp only [World.step, Function.update_self]
                intro row hr
                have hold : row ∈ (Run.stateBefore (gridCO p) rho i reader).obligations := by
                  simpa only [gridCO, process_obligations] using! hr
                exact (process_receiptPrefix p _ o).blocks.subset (ih row hold)
              · simpa [World.step, hv] using ih

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A live root is stored if genesis and all obligation targets are stored. -/
theorem liveRoot_mem_blocks {n : Nat} (st : State n) (h : TargetsStored st)
    (hg : Block.genesis ∈ st.blocks) : liveRoot st ∈ st.blocks := by
  rcases (liveRoot_is_deepest st).1 with he | hm
  · simpa [he] using hg
  · obtain ⟨row, hr, he⟩ := List.mem_filterMap.mp hm
    rcases row with ⟨B, g, d⟩
    change (if st.now < d then some B else none) = some (liveRoot st) at he
    split at he
    · have hrow : B = liveRoot st := Option.some.inj he
      rw [← hrow]
      exact h (B, g, d) hr
    · contradiction

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The ordinary HEAD walk ends at a stored block, including when the
live root is absent from the frozen voter tree. -/
theorem head_walk_mem_blocks (p : Params) {n : Nat} (st : State n) (r : Slot)
    (h : TargetsStored st) (hg : Block.genesis ∈ st.blocks) :
    forkChoice st (voterTree p st r) (voterView p st r)
      (voterSupportView p st r) r ∈ st.blocks := by
  unfold forkChoice ghost
  rcases ghostWalk_mem (voterTree p st r).eraseDups _ _
      (voterTree p st r).eraseDups.length (liveRoot st) with he | hm
  · rw [he]
    exact liveRoot_mem_blocks st h hg
  · exact (List.mem_filter.mp (List.mem_eraseDups.mp hm)).1

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The target of an honest HEAD was already stored before its emission
clock tick. Its path can therefore use accepted-object relay. -/
theorem emitted_head_target_stored {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (source : V) (r : Slot) (i : Fin p.n) (B : Block)
    (he : Run.emits (gridCO p) E rho source ⟨.seat r i, .head B⟩ (voteTime p r)) :
    B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) source).blocks ∧ B.slot ≤ r := by
  obtain ⟨index, hi, hem⟩ := he
  have ha := (emitted_head_action p E rho index source _ _ r B hem rfl rfl).2
  have hstate : Run.stateBefore (gridCO p) rho (index + 1) source =
      clock p (Run.stateBefore (gridCO p) rho index source) (voteTime p r) := by
    rw [stateBefore_succ_event hi]
    simp [World.step, gridCO]
  have htargets := run_targetsStored p rho (index + 1) source
  have hg := (stateBefore_receiptPrefix p rho (Nat.zero_le (index + 1)) source).blocks.subset
    (show Block.genesis ∈ (Run.stateBefore (gridCO p) rho 0 source).blocks by
      simp [Run.stateBefore, World.init, gridCO, initial])
  rw [hstate] at htargets hg
  have hb : B ∈ (clock p (Run.stateBefore (gridCO p) rho index source) (voteTime p r)).blocks := by
    by_cases hz : r = 0
    · subst r
      have heq : B = .genesis := by simpa [act, targetOfBlock] using ha.symm
      simpa [heq] using hg
    · have heq : forkChoice
          (clock p (Run.stateBefore (gridCO p) rho index source) (voteTime p r))
          (voterTree p (clock p (Run.stateBefore (gridCO p) rho index source) (voteTime p r)) r)
          (voterView p (clock p (Run.stateBefore (gridCO p) rho index source) (voteTime p r)) r)
          (voterSupportView p
            (clock p (Run.stateBefore (gridCO p) rho index source) (voteTime p r)) r) r = B := by
        simpa [act, targetOfBlock, hz] using ha
      rw [← heq]
      exact head_walk_mem_blocks p _ r htargets hg
  have hblocks := congrArg Prod.fst
    (clock_receiptData p (Run.stateBefore (gridCO p) rho index source) (voteTime p r))
  change (clock p _ _).blocks = _ at hblocks
  rw [hblocks, stateBefore_tick_eq_stateBeforeTime hs hi] at hb
  exact ⟨hb, stored_before_head_slot_le p E rho hs r source B hb⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A synchronous honest HEAD and its target are fully resolved at the
reader's gate, with no added receipt, stamp, path, or slot premise. -/
theorem synchronous_honest_head_earlyVotes {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (i : Fin p.n) (B : Block) (hh : rho.seatOf r i ∈ rho.honest)
    (he : Run.emits (gridCO p) E rho (rho.seatOf r i)
      ⟨.seat r i, .head B⟩ (voteTime p r))
    (reader : V) (hr : reader ∈ rho.honest) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈ earlyVotes p (gateInput p rho r reader) r := by
  obtain ⟨hm, hslot⟩ := emitted_head_target_stored p E rho hsync.execution.toScheduleWellFormed
    (rho.seatOf r i) r i B he
  exact synchronous_honest_head_resolved p E rho hΔ r hsync i B hh he hm hslot reader hr

end AvailableChain.GridCO
end

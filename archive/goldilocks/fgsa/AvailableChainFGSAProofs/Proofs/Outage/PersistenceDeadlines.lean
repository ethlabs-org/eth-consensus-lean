module
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingGate
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming
public import AvailableChainFGSARun.Proofs.AncestorDeadlinesStore

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

private theorem deadline_process_rows (st : State p.n) (o : Wire p.n) :
    (process p st o).base.obligations ⊆ st.base.obligations := by
  unfold process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some input =>
    cases input with
    | vote s seat b => rw [admitHead_obligations]
    | row seat body => rw [Internal.admitRow_base]
    | block s N =>
      change (admitBlock p st s N).base.obligations ⊆ st.base.obligations
      unfold admitBlock
      split
      · exact List.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          dsimp only
          split
          · rw [Internal.foldl_admitRow_base]
            split
            · intro row hm
              rwa [admitProposal_obligations_slow] at hm
            · intro row hm
              rw [reconcile_obligations] at hm
              have hold := (List.mem_filter.mp hm).1
              rwa [admitProposal_obligations_slow] at hold
          · exact List.Subset.refl _

/-- A gate row is unchanged or has the exact deadline of this gate.
The new target is a prefix of its raw result. Suppressed gates add no row. -/
theorem outage_gate_row_deadline (st : State p.n) (s : Slot)
    (row : Block × Nat × Time) (hr : row ∈ (gateStep p st s).base.obligations) :
    row ∈ st.base.obligations ∨
      joinedNow p st = true ∧ ∃ C,
        SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s = some C ∧
        Block.Preceq row.1 C ∧ row.2.2 = SA.gateTime p.toParams s + L p := by
  unfold gateStep at hr
  rw [normalizeS_fields] at hr
  split at hr
  · exact Or.inl hr
  · split at hr
    · exact Or.inl hr
    · rename_i hJ
      have hj : joinedNow p st = true := by
        cases he : joinedNow p st <;> simp_all
      change row ∈ (SA.Root.gateFrom p.toParams (eraseFG st.fg.F)
        (actView st) s).obligations at hr
      cases hraw : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s with
      | none =>
        unfold SA.Root.gateFrom GridCO.gateFrom at hr
        rw [show GridCO.confirmationFrom p.toParams.engine (eraseFG st.fg.F)
          (actView st) s = none from hraw] at hr
        exact Or.inl hr
      | some C =>
        cases hg : (actView st).obligations.any (fun row => !Block.compatible row.1 C) with
        | true =>
          unfold SA.Root.gateFrom GridCO.gateFrom at hr
          rw [show GridCO.confirmationFrom p.toParams.engine (eraseFG st.fg.F)
            (actView st) s = some C from hraw] at hr
          dsimp only at hr
          rw [hg] at hr
          exact Or.inl hr
        | false =>
          rw [gateFrom_eq_writeKeys_fgsa p.toParams _ _ s C hraw hg] at hr
          rcases writeKeys_deadline_cases _ _ _ row hr with hold | ⟨hk, hd⟩
          · exact Or.inl hold
          · right
            refine ⟨hj, C, rfl, ?_, hd⟩
            rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy] at hk
            obtain ⟨X, hX, hk⟩ := List.mem_flatMap.mp hk
            obtain ⟨g, _, he⟩ := List.mem_map.mp hk
            have hrow : row.1 = X := (congrArg Prod.fst he).symm
            rw [hrow]
            exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp hX).2).2

/-- Every retained row has an actual gate origin and its exact write deadline.
Delivery and restart add no rows. No global restart premise is used. -/
theorem outage_row_deadline_origin (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (row : Block × Nat × Time)
    (hm : row ∈ (storeAt p c E rho i x).base.obligations) :
    ∃ j < i, ∃ s C, enabledGateAt p c E rho j x s ∧
      gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
      row.2.2 = SA.gateTime p.toParams s + L p := by
  induction i with
  | zero => cases hm
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      have hst : storeAt p c E rho (i + 1) x = storeAt p c E rho i x := by
        simp [storeAt, V2.D.Run.stateBefore, List.take_add_one, he]
      rw [hst] at hm
      obtain ⟨j, hj, rest⟩ := ih hm
      exact ⟨j, hj.trans (Nat.lt_succ_self i), rest⟩
    | some e =>
      have hold (h : row ∈ (storeAt p c E rho i x).base.obligations) :
          ∃ j < i + 1, ∃ s C, enabledGateAt p c E rho j x s ∧
            gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
            row.2.2 = SA.gateTime p.toParams s + L p := by
        obtain ⟨j, hj, rest⟩ := ih h
        exact ⟨j, hj.trans (Nat.lt_succ_self i), rest⟩
      have hstep := V2.D.Run.stateBefore_succ E rho he
      cases e with
      | restart y t =>
        change row ∈ (V2.D.Run.stateBefore E rho (i + 1) x).st.base.obligations at hm
        rw [hstep] at hm
        by_cases hyx : y = x
        · subst y
          simp only [V2.D.World.step, Function.update_self] at hm
          change row ∈ (acRestart p (storeAt p c E rho i x) t).base.obligations at hm
          rw [acRestart_obligations] at hm
          exact hold hm
        · simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hyx)] at hm
          exact hold hm
      | deliver y o t =>
        change row ∈ (V2.D.Run.stateBefore E rho (i + 1) x).st.base.obligations at hm
        rw [hstep] at hm
        by_cases hyx : y = x
        · subst y
          simp only [V2.D.World.step, Function.update_self] at hm
          exact hold (deadline_process_rows _ _ hm)
        · simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hyx)] at hm
          exact hold hm
      | tick y t =>
        by_cases hyx : y = x
        · subst y
          have hst : storeAt p c E rho (i + 1) x = clock p (storeAt p c E rho i x) t := by
            exact (congrArg Node.st (V2.D.Run.step_tick_eq E rho he).1).trans
              (tick_st (c := c) E rho _ x t)
          rw [hst] at hm
          by_cases hg : ∃ s, SA.gateTime p.toParams s = t
          · obtain ⟨s, rfl⟩ := hg
            rw [arming_clock_gate] at hm
            rcases outage_gate_row_deadline _ s row hm with hm | ⟨hj, C, hraw, hRC, hd⟩
            · exact hold ((clockPre_obligations_sublist p _ _).subset hm)
            · have hG : enabledGateAt p c E rho i x s := by
                refine ⟨he, ?_⟩
                rw [clockPre_joined] at hj
                have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
                  (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
                    (fgsa_gate_slot (c := c) (rho.stateBefore E i x) s)
                cases hr : (storeAt p c E rho i x).restartTime with
                | none => trivial
                | some w =>
                  rw [hr] at hj
                  change decide (w ≤ 4 * p.Δ *
                    ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) = true at hj
                  change w ≤ 4 * p.Δ * (s : Int)
                  simpa only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
                    decide_eq_true_eq] using hj
              have hres := inclusion_gate_raw_at_tick E rho hs hG
              rw [hraw] at hres
              exact ⟨i, Nat.lt_succ_self i, s, C, hG, hres, hRC, hd⟩
          · rw [inclusion_clock_offGate p _ t (fun s h => hg ⟨s, h⟩)] at hm
            exact hold ((clockPre_obligations_sublist p _ _).subset hm)
        · change row ∈ (V2.D.Run.stateBefore E rho (i + 1) x).st.base.obligations at hm
          rw [hstep] at hm
          simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hyx)] at hm
          exact hold hm

/-- Late compatible results bound every remaining conflicting row by handover.
The origin may be in an earlier receiver epoch, including a row kept at restart. -/
theorem outage_conflicting_row_deadline (hs : V2.D.ScheduleWellFormed E rho)
    (r : Slot) (B : Block) (i : Nat) (x : V)
    (hResults : ∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
      gateResultAt p c E rho j = some (some C) → Block.Compatible C B)
    (row : Block × Nat × Time) (hm : row ∈ (storeAt p c E rho i x).base.obligations)
    (hConflict : ¬ Block.Compatible row.1 B) : row.2.2 ≤ OutageEnd p r := by
  obtain ⟨j, hji, s, C, hG, hC, hRC, hd⟩ := outage_row_deadline_origin hs i x row hm
  have hsr : s ≤ r := by
    by_contra hn
    exact hConflict (block_compatible_of_preceq_compatible hRC
      (hResults j s C hji (Nat.lt_of_not_ge hn) hG hC))
  rw [hd, (outage_handover_time p r).2]
  linarith [(arming_gate_le_iff p s r).mpr hsr]

/-- Every row in the pre-gate clock has survived this tick's strict expiry filter. -/
theorem outage_clockPre_expired_rows (st : State p.n) (t : Time) :
    (clockPre p st t).base.obligations ⊆
      (GridCO.expire { st.base with now := t } t).obligations := by
  unfold clockPre
  dsimp only
  split_ifs <;>
    first
    | exact List.Subset.refl _
    | exact fun row hr => (List.mem_filter.mp hr).1

/-- At handover the actual clock has no conflicting rows.
The result uses exact write origins and removes rows at deadline equality. -/
theorem outage_handover_rows_compatible (hs : V2.D.ScheduleWellFormed E rho)
    (r : Slot) (B : Block) (i : Nat) (x : V)
    (hResults : ∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
      gateResultAt p c E rho j = some (some C) → Block.Compatible C B) :
    ∀ row ∈ (clock p (storeAt p c E rho i x) (OutageEnd p r)).base.obligations,
      Block.Compatible row.1 B := by
  have hoff : ∀ s, SA.gateTime p.toParams s ≠ OutageEnd p r := by
    intro s
    rw [(outage_handover_time p r).1]
    intro he
    rw [arming_gate_eq, arming_vote_eq] at he
    have hz : (4 * (s : Int) + 5 - 4 * ((r + p.k + 1 : Nat) : Int)) * p.Δ = 0 := by
      linear_combination he
    rcases mul_eq_zero.mp hz with h | h
    · omega
    · exact (ne_of_gt p.deltaPos h).elim
  rw [inclusion_clock_offGate p _ _ hoff]
  intro row hr
  by_contra hConflict
  have hm := (clockPre_obligations_sublist p _ _).subset hr
  have hdeadline := outage_conflicting_row_deadline hs r B i x hResults row hm hConflict
  have hLive : OutageEnd p r < row.2.2 :=
    of_decide_eq_true (List.mem_filter.mp (outage_clockPre_expired_rows _ _ hr)).2
  exact (not_lt_of_ge hdeadline) hLive

/-- An actual handover HEAD tick clears the old conflicting rows before its duty.
This conclusion applies even when that HEAD duty is suppressed after a wake. -/
theorem outage_handover_tick_rows (hs : V2.D.ScheduleWellFormed E rho)
    (r : Slot) (B : Block) {i : Nat} {x : V}
    (hi : rho.events[i]? = some (.tick x (OutageEnd p r)))
    (hResults : ∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
      gateResultAt p c E rho j = some (some C) → Block.Compatible C B) :
    ∀ row ∈ (storeAt p c E rho (i + 1) x).base.obligations, Block.Compatible row.1 B := by
  have hst : storeAt p c E rho (i + 1) x = clock p (storeAt p c E rho i x) (OutageEnd p r) :=
    (congrArg Node.st (V2.D.Run.step_tick_eq E rho hi).1).trans
      (tick_st (c := c) E rho _ x _)
  rw [hst]
  exact outage_handover_rows_compatible hs r B i x hResults

end AvailableChain.FGSA.Run
end

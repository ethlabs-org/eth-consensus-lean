module
public import AvailableChainGridCO.Proofs.Snapshot

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The ordinary saved view at one local freeze. -/
def freezeView (p : Params) {n : Nat} (st : State n) (r : Slot) :=
  ((votesAt st r).filter (fun o => stampVote st o < freezeTime p r),
   (votesAt st r).filter (fun o => resolvedBefore st o (freezeTime p r)),
   st.blocks.filter (fun B => stampBlock st B < freezeTime p r))

private theorem fold_frozen {n : Nat} {α : Type} (xs : List α)
    (f : State n → α → State n) (st : State n)
    (h : ∀ st x, (f st x).frozen = st.frozen) :
    (xs.foldl f st).frozen = st.frozen := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, h]

/-- Gates do not change the ordinary frozen views. -/
theorem gate_frozen (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).frozen = st.frozen := by
  unfold gate
  split
  · rfl
  · dsimp only
    split
    · rfl
    · apply fold_frozen
      intro st B
      exact fold_frozen _ _ st (by intros; rfl)

private theorem admitVote_frozen (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (admitVote p st o).frozen = st.frozen := by
  unfold admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

/-- Deliveries do not change the saved views. Proposal merge is separate. -/
theorem process_frozen (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).frozen = st.frozen := by
  unfold process
  split
  · exact admitVote_frozen p st o
  · unfold admitProposal
    dsimp only
    split <;> split
    all_goals first | rfl | exact fold_frozen _ _ _ (by intros; apply admitVote_frozen)
  · rfl

/-- Receipt stamps make the freeze independent of the local clock field. -/
theorem freezeView_eq_of_receiptData (p : Params) {n : Nat} (a b : State n)
    (he : receiptData a = receiptData b) (hb : ReceiptStamped b) (r : Slot) :
    freezeView p a r = freezeView p b r := by
  have ⟨hblocks, hbs, hvotes, hvs⟩ : a.blocks = b.blocks ∧ a.blockStamp = b.blockStamp ∧
      a.votes = b.votes ∧ a.voteStamp = b.voteStamp := by simpa [receiptData] using he
  have hprefix : ReceiptPrefix b a := by constructor <;> simp_all
  have hraw : votesAt a r = votesAt b r := by simp only [votesAt, hvotes]
  unfold freezeView
  apply Prod.ext
  · rw [hraw]
    apply List.filter_congr
    intro o ho
    rw [hprefix.stampVote hb o (List.mem_filter.mp ho).1]
  · apply Prod.ext
    · rw [hraw]
      apply List.filter_congr
      intro o ho
      exact resolvedBefore_eq_of_receiptData a b he hb o (List.mem_filter.mp ho).1 _
    · rw [hblocks]
      apply List.filter_congr
      intro B hB
      rw [hprefix.stampBlock hb B hB]

/-- The clock appends exactly one ordinary view at its freeze time. -/
theorem clock_frozen (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : ReceiptStamped st) :
    (clock p st t).frozen =
      if 0 ≤ t - 3 * p.Δ && t == freezeTime p ((t - 3 * p.Δ) / (4 * p.Δ)).toNat then
        st.frozen ++ [(((t - 3 * p.Δ) / (4 * p.Δ)).toNat,
          freezeView p st ((t - 3 * p.Δ) / (4 * p.Δ)).toNat)]
      else st.frozen := by
  have hf := freezeView_eq_of_receiptData p (expire { st with now := t } t) st rfl hs
  unfold clock
  dsimp only
  split
  all_goals try rw [gate_frozen]
  all_goals split <;> split <;> split
  all_goals simp_all only [freeze, expire, release, freezeView]

/-- Every saved row comes from a local freeze tick and its strict input. -/
theorem stored_freeze_origin {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) (r : Slot)
    (view : List (Wire p.n) × List (Wire p.n) × List Block)
    (hm : (r, view) ∈ (Run.stateBefore (gridCO p) rho index reader).frozen) :
    ∃ j < index,
      rho.events[j]? = some (.tick reader (freezeTime p r)) ∧
      view = freezeView p (Run.stateBefore (gridCO p) rho j reader) r := by
  set_option backward.isDefEq.respectTransparency false in
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial] at hm
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none =>
          obtain ⟨j, hj, hrest⟩ := ih (by simpa [Run.stateBefore, List.take_add_one, hi] using hm)
          exact ⟨j, by omega, hrest⟩
      | some e =>
          rw [stateBefore_succ_event hi] at hm
          cases e with
          | tick v t =>
              by_cases hv : reader = v
              · subst v
                simp only [World.step, Function.update_self] at hm
                change (r, view) ∈ (clock p _ t).frozen at hm
                rw [clock_frozen p _ t (run_receiptStamped p rho index reader)] at hm
                split at hm
                · rename_i hf
                  rcases List.mem_append.mp hm with hold | hnew
                  · obtain ⟨j, hj, hrest⟩ := ih hold
                    exact ⟨j, by omega, hrest⟩
                  · have he : r = ((t - 3 * p.Δ) / (4 * p.Δ)).toNat ∧
                        view = freezeView p (Run.stateBefore (gridCO p) rho index reader)
                          ((t - 3 * p.Δ) / (4 * p.Δ)).toNat := by simpa using hnew
                    have ht : t = freezeTime p r := by
                      rw [he.1]
                      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hf).2
                    exact ⟨index, by omega, by simpa [ht] using hi, by simpa [he.1] using he.2⟩
                · obtain ⟨j, hj, hrest⟩ := ih hm
                  exact ⟨j, by omega, hrest⟩
              · obtain ⟨j, hj, hrest⟩ := ih (by simpa [World.step, hv] using hm)
                exact ⟨j, by omega, hrest⟩
          | deliver v o t =>
              have hold : (r, view) ∈ (Run.stateBefore (gridCO p) rho index reader).frozen := by
                by_cases hv : reader = v
                · subst v; simpa [World.step, gridCO, process_frozen] using! hm
                · simpa [World.step, hv] using hm
              obtain ⟨j, hj, hrest⟩ := ih hold
              exact ⟨j, by omega, hrest⟩

/-- Saved views grow by append through the event list. -/
theorem stateBefore_frozen_prefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) {i j : Nat} (hij : i ≤ j) (reader : V) :
    (Run.stateBefore (gridCO p) rho i reader).frozen <+:
      (Run.stateBefore (gridCO p) rho j reader).frozen := by
  set_option backward.isDefEq.respectTransparency false in
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with he | hlt
      · subst i; rfl
      · apply (ih (by omega)).trans
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick v t =>
                by_cases hv : reader = v
                · subst v
                  simp only [World.step, Function.update_self]
                  change _ <+: (clock p _ t).frozen
                  rw [clock_frozen p _ t (run_receiptStamped p rho j reader)]
                  split <;> simp
                · simp [World.step, hv]
            | deliver v o t =>
                by_cases hv : reader = v
                · subst v; simp [World.step, gridCO, process_frozen]
                · simp [World.step, hv]

/-- The ordinary view saved by an honest reader is the view of its unique
freeze tick. This theorem includes sleeping readers. -/
theorem frozenAt_after_freeze {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (reader : V) (hr : reader ∈ rho.honest)
    (cut : Time) (hcut : freezeTime p r < cut) (hh : freezeTime p r ≤ rho.horizon) :
    frozenAt (Run.stateBeforeTime (gridCO p) rho cut reader) r =
      some (freezeView p (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r) := by
  have hpub : PublicTime E (freezeTime p r) := by
    refine ⟨4 * r + 3, ?_⟩
    simp only [freezeTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hzero : 0 ≤ freezeTime p r := by
    dsimp [freezeTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total reader hr _ hpub hzero hh)
  have hstate := stateBefore_tick_eq_stateBeforeTime hs hi
  have hpost : (r, freezeView p (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r) ∈
      (Run.stateBefore (gridCO p) rho (i + 1) reader).frozen := by
    rw [stateBefore_succ_event hi]
    simp only [World.step, Function.update_self]
    change _ ∈ (clock p _ (freezeTime p r)).frozen
    rw [clock_frozen p _ _ (run_receiptStamped p rho i reader), hstate]
    have ht : freezeTime p r - 3 * p.Δ = 4 * p.Δ * (r : Time) := by
      simp [freezeTime, proposalTime]
    have hd : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
    simp [ht, hd, mul_nonneg (show 0 ≤ 4 * p.Δ by linarith [p.deltaPos])
      (Int.natCast_nonneg r)]
  have hil : i < (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length :=
    (index_lt_read_length_iff hs (cut - 1) hi).mpr (Int.le_sub_one_iff.mpr hcut)
  rw [time_input_eq_event_prefix p E rho hs]
  have hm := (stateBefore_frozen_prefix p rho (Nat.succ_le_of_lt hil) reader).subset hpost
  unfold frozenAt
  cases hf : (Run.stateBefore (gridCO p) rho
      (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length reader).frozen.find?
      (fun row => row.1 == r) with
  | none => have h := List.find?_eq_none.mp hf _ hm; simp at h
  | some row =>
      have he : row.1 = r := by simpa using List.find?_some hf
      obtain ⟨j, _, hj, hv⟩ := stored_freeze_origin p rho _ reader row.1 row.2
        (List.mem_of_find?_eq_some hf)
      rw [he] at hj hv
      rw [stateBefore_tick_eq_stateBeforeTime hs hj] at hv
      simp only [Option.map_some]
      exact congrArg some hv

/-- A strict input at positive time has an earlier local clock. -/
theorem time_input_now_lt {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (hc : 0 < cut) (reader : V) :
    (Run.stateBeforeTime (gridCO p) rho cut reader).now < cut := by
  rw [time_input_eq_event_prefix p E rho hs]
  rcases stateBefore_now_source p rho
    (rho.events.filter (fun e : Event V (gridCO p).Object =>
      decide (e.time ≤ cut - 1))).length reader with hz | ⟨j, hj, he⟩
  · simpa [hz] using hc
  · exact Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (cut - 1) he).mp hj)

/-- All receipt stamps in a positive strict input precede its time. -/
theorem time_input_stamps_lt {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (hc : 0 < cut) (reader : V) :
    (∀ o, stampVote (Run.stateBeforeTime (gridCO p) rho cut reader) o < cut) ∧
    (∀ B, stampBlock (Run.stateBeforeTime (gridCO p) rho cut reader) B < cut) := by
  have ht := time_input_now_lt p E rho hs cut hc reader
  rw [time_input_eq_event_prefix p E rho hs] at ht ⊢
  have hb := run_stampsBounded p E rho hs
    (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length reader
  exact ⟨fun o => (hb.stampVote_le o).trans_lt ht,
    fun B => (hb.stampBlock_le B).trans_lt ht⟩

/-- No receipt in the strict freeze input is excluded by its timestamp. -/
theorem freezeView_at_input {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) :
    let st := Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader
    (freezeView p st r).1 = votesAt st r ∧
      (freezeView p st r).2.2 = st.blocks := by
  have hp : 0 < freezeTime p r := by
    dsimp [freezeTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have ht := time_input_stamps_lt p E rho hs _ hp reader
  dsimp only [freezeView]
  constructor <;> apply List.filter_eq_self.mpr
  · intro o _; exact decide_eq_true (ht.1 o)
  · intro B _; exact decide_eq_true (ht.2 B)

/-- Receipt lists in strict inputs preserve their order. -/
theorem time_input_receiptPrefix {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (a b : Time) (hab : a ≤ b) (reader : V) :
    ReceiptPrefix (Run.stateBeforeTime (gridCO p) rho a reader)
      (Run.stateBeforeTime (gridCO p) rho b reader) := by
  rw [time_input_eq_event_prefix p E rho hs, time_input_eq_event_prefix p E rho hs]
  exact stateBefore_receiptPrefix p rho
    (read_length_mono (rho := rho) (a - 1) (b - 1) (sub_le_sub_right hab 1)) reader

/-- A later clock cannot replace the first saved view for a label. -/
theorem clock_frozenAt_of_some (p : Params) {n : Nat} (st : State n)
    (hs : ReceiptStamped st) (r : Slot)
    (view : List (Wire n) × List (Wire n) × List Block)
    (hv : frozenAt st r = some view) (t : Time) :
    frozenAt (clock p st t) r = some view := by
  unfold frozenAt at hv ⊢
  rw [clock_frozen p st t hs]
  split
  · rw [List.find?_append]
    cases hf : st.frozen.find? (fun row => row.1 == r) with
    | none => simp only [hf, Option.map_none, reduceCtorEq] at hv
    | some row => simpa only [hf, Option.or_some] using! hv
  · exact hv

/-- The next ordinary HEAD uses the exact previous-label freeze. -/
theorem nextHeadState_frozenAt_of_execution {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hx : ExecutionValid (gridCO p) E rho) (hh : gateTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    frozenAt (nextHeadState p rho r reader) r =
      some (freezeView p (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r) := by
  apply clock_frozenAt_of_some p _ (run_time_receiptStamped p rho _ reader)
  exact frozenAt_after_freeze p E rho hx.toScheduleWellFormed hΔ r reader hr
    (releaseTime p r) (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos])
    (le_trans (by dsimp [freezeTime, gateTime]; linarith [p.deltaPos]) hh)

theorem nextHeadState_frozenAt {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (reader : V) (hr : reader ∈ rho.honest) :
    frozenAt (nextHeadState p rho r reader) r =
      some (freezeView p (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r) :=
  nextHeadState_frozenAt_of_execution p E rho hΔ r hsync.1 hsync.2.2.1 reader hr

end AvailableChain.GridCO
end

module
public import AvailableChainGridCO.Proofs.Coverage

@[expose] public section
namespace AvailableChain.GridCO
open AvailableChain.Generic AvailableChain.Statements.Generic
set_option linter.unusedSectionVars false
variable [LeasePolicy]

private theorem fold_field {n : Nat} {α β : Type} (f : State n → α)
    (step : State n → β → State n) (h : ∀ st x, f (step st x) = f st)
    (xs : List β) (st : State n) : f (xs.foldl step st) = f st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (h st x)

theorem process_genuine (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).genuine = st.genuine := by
  have hv (st : State n) (o : Wire n) : (admitVote p st o).genuine = st.genuine := by
    unfold admitVote
    split
    · dsimp only; split <;> rfl
    · rfl
  unfold process
  split
  · exact hv _ _
  · unfold admitProposal
    dsimp only
    split <;> split
    all_goals first
      | rfl
      | exact fold_field State.genuine _ (fun st o => hv st (fromHead o)) _ _
  · rfl

theorem gate_genuine (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).genuine = recordGenuine st r (confirmation p st r) := by
  cases hc : confirmation p st r with
  | none => simp [gate, hc]
  | some C =>
    simp only [gate, hc]
    split
    · rfl
    · apply fold_field State.genuine
      intro acc b
      exact fold_field State.genuine _ (by intros; rfl) _ _

theorem clockPreGate_genuine (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clockPreGate p st t).genuine = st.genuine := by
  unfold clockPreGate
  dsimp only
  split <;> split <;> split <;> rfl

theorem recordGenuine_origin {n : Nat} (st : State n) (r s : Slot)
    (result C : Option Block) (hm : (s, C) ∈ recordGenuine st r result) :
    (s, C) ∈ st.genuine ∨ s = r ∧ C = result := by
  unfold recordGenuine at hm
  split at hm
  · simpa only [List.mem_append, List.mem_singleton, Prod.mk.injEq] using hm
  · exact Or.inl hm

theorem clock_genuine_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : ReceiptStamped st) (r : Slot) (C : Option Block)
    (hm : (r, C) ∈ (clock p st t).genuine) :
    (r, C) ∈ st.genuine ∨ t = gateTime p r ∧ C = confirmation p st r := by
  rw [clock_eq_gate_prestate] at hm
  dsimp only at hm
  split at hm
  · rename_i hgate
    rw [gate_genuine] at hm
    rcases recordGenuine_origin _ _ r _ C hm with hold | ⟨he, hc⟩
    · exact Or.inl (by simpa only [clockPreGate_genuine] using hold)
    · subst r
      exact Or.inr ⟨by simpa using (Bool.and_eq_true_iff.mp hgate).2,
        hc.trans (confirmation_eq_of_receiptData p _ st (clockPreGate_receiptData p st t) hs _)⟩
  · exact Or.inl (by simpa only [clockPreGate_genuine] using hm)

/-- Each saved result, including an empty or vetoed one, comes from that
reader's actual clock gate. Deliveries cannot create or replace a result. -/
theorem run_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (reader : V) (r : Slot) (C : Option Block)
    (hm : (r, C) ∈ (Run.stateBefore (gridCO p) rho index reader).genuine) :
    ∃ j < index, rho.events[j]? = some (.tick reader (gateTime p r)) ∧
      C = confirmation p (gateInput p rho r reader) r := by
  set_option backward.isDefEq.respectTransparency false in
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial] at hm
  | succ index ih =>
    cases hi : rho.events[index]? with
    | none =>
      obtain ⟨j, hj, rest⟩ := ih (by simpa [Run.stateBefore, List.take_add_one, hi] using hm)
      exact ⟨j, by omega, rest⟩
    | some e =>
      rw [stateBefore_succ_event hi] at hm
      cases e with
      | tick v t =>
        by_cases hv : reader = v
        · subst v
          have hm' : (r, C) ∈
              (clock p (Run.stateBefore (gridCO p) rho index reader) t).genuine := by
            simpa [World.step] using! hm
          rcases clock_genuine_origin p _ t (run_receiptStamped p rho index reader) r C hm'
            with hold | ⟨ht, hc⟩
          · obtain ⟨j, hj, rest⟩ := ih hold
            exact ⟨j, by omega, rest⟩
          · subst t
            rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hc
            exact ⟨index, by omega, hi, hc⟩
        · obtain ⟨j, hj, rest⟩ := ih (by simpa [World.step, hv] using hm)
          exact ⟨j, by omega, rest⟩
      | deliver v o t =>
        have hold : (r, C) ∈ (Run.stateBefore (gridCO p) rho index reader).genuine := by
          by_cases hv : reader = v
          · subst v; simpa [World.step, gridCO, process_genuine] using! hm
          · simpa [World.step, hv] using hm
        obtain ⟨j, hj, rest⟩ := ih hold
        exact ⟨j, by omega, rest⟩

theorem time_input_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) (r : Slot) (C : Option Block)
    (hm : (r, C) ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).genuine) :
    gateTime p r < cut ∧ C = confirmation p (gateInput p rho r reader) r := by
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨j, hj, hi, hc⟩ := run_genuine_origin p E rho hs _ reader r C hm
  exact ⟨Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (cut - 1) hi).mp hj), hc⟩

/-- Reading a saved label reveals its exact raw result, not an accepted
stable record and not a later re-evaluation. -/
theorem savedGenuine_input_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) (r : Slot) (C : Option Block)
    (hm : savedGenuine (Run.stateBeforeTime (gridCO p) rho cut reader) r = some C) :
    gateTime p r < cut ∧ C = confirmation p (gateInput p rho r reader) r := by
  unfold savedGenuine at hm
  obtain ⟨row, hrow, he⟩ := Option.map_eq_some_iff.mp hm
  have hr : row.1 = r := by simpa using List.find?_some hrow
  have hpair : row = (r, C) := Prod.ext hr he
  exact time_input_genuine_origin p E rho hs cut reader r C
    (hpair ▸ List.mem_of_find?_eq_some hrow)

theorem recordGenuine_subset {n : Nat} (st : State n) (r : Slot) (C : Option Block) :
    st.genuine ⊆ recordGenuine st r C := by
  unfold recordGenuine
  split
  · exact List.subset_append_left _ _
  · exact List.Subset.refl _

theorem clock_genuine_subset (p : Params) {n : Nat} (st : State n) (t : Time) :
    st.genuine ⊆ (clock p st t).genuine := by
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rw [gate_genuine]
    simpa only [clockPreGate_genuine] using recordGenuine_subset (clockPreGate p st t) _ _
  · rw [clockPreGate_genuine]

theorem run_genuine_mono {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (start finish : Nat) (hle : start ≤ finish) (reader : V) :
    (Run.stateBefore (gridCO p) rho start reader).genuine ⊆
      (Run.stateBefore (gridCO p) rho finish reader).genuine := by
  set_option backward.isDefEq.respectTransparency false in
  induction finish with
  | zero =>
    simpa only [Nat.le_zero.mp hle] using
      (List.Subset.refl (Run.stateBefore (gridCO p) rho 0 reader).genuine)
  | succ finish ih =>
    by_cases he : start = finish + 1
    · subst start; exact List.Subset.refl _
    apply List.Subset.trans (ih (by omega))
    cases hi : rho.events[finish]? with
    | none => simp [Run.stateBefore, List.take_add_one, hi]
    | some e =>
      rw [stateBefore_succ_event hi]
      cases e with
      | tick v t =>
        by_cases hv : reader = v
        · subst v; simpa [World.step] using! clock_genuine_subset p _ t
        · simp [World.step, hv]
      | deliver v o t =>
        by_cases hv : reader = v
        · subst v; simp [World.step, gridCO, process_genuine]
        · simp [World.step, hv]

/-- Every earlier gate is present at a later strict input of an honest
reader. Sleeping readers execute the same public clock. -/
theorem time_input_genuine_mem {V : Type} [DecidableEq V] (p : Params)
    (hsa : LeasePolicy.slowArming = true)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (cut : Time) (reader : V) (hr : reader ∈ rho.honest)
    (r : Slot) (hlt : gateTime p r < cut) (hh : gateTime p r ≤ rho.horizon) :
    (r, confirmation p (gateInput p rho r reader) r) ∈
      (Run.stateBeforeTime (gridCO p) rho cut reader).genuine := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    simp only [gateTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ gateTime p r := by
    dsimp [gateTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total reader hr _ hpub hz hh)
  have hempty : savedGenuine (gateInput p rho r reader) r = none := by
    cases hc : savedGenuine (gateInput p rho r reader) r with
    | none => rfl
    | some C =>
      have hbad := (savedGenuine_input_origin p E rho hs _ reader r C hc).1
      exact (lt_irrefl _ hbad).elim
  have hpost : (r, confirmation p (gateInput p rho r reader) r) ∈
      (Run.stateBefore (gridCO p) rho (i + 1) reader).genuine := by
    rw [stateBefore_succ_event hi]
    simp only [World.step, Function.update_self]
    change _ ∈ (clock p _ _).genuine
    rw [stateBefore_tick_eq_stateBeforeTime hs hi, clock_at_gate, gate_genuine]
    have hdata := confirmation_eq_of_receiptData p _ (gateInput p rho r reader)
      (clockPreGate_receiptData p _ (gateTime p r)) (run_time_receiptStamped p rho _ reader) r
    change _ ∈ recordGenuine
      (clockPreGate p (gateInput p rho r reader) (gateTime p r)) r
      (confirmation p (clockPreGate p (gateInput p rho r reader) (gateTime p r)) r)
    have hsaved : savedGenuine
        (clockPreGate p (gateInput p rho r reader) (gateTime p r)) r = none := by
      simpa only [savedGenuine, clockPreGate_genuine] using hempty
    rw [hdata]
    simp [recordGenuine, hsa, hsaved]
  rw [time_input_eq_event_prefix p E rho hs]
  exact run_genuine_mono p rho (i + 1) _
    (Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
      (Int.le_sub_one_iff.mpr hlt))) reader hpost

theorem time_input_savedGenuine {V : Type} [DecidableEq V] (p : Params)
    (hsa : LeasePolicy.slowArming = true)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (cut : Time) (reader : V) (hr : reader ∈ rho.honest)
    (r : Slot) (hlt : gateTime p r < cut) (hh : gateTime p r ≤ rho.horizon) :
    savedGenuine (Run.stateBeforeTime (gridCO p) rho cut reader) r =
      some (confirmation p (gateInput p rho r reader) r) := by
  cases hc : savedGenuine (Run.stateBeforeTime (gridCO p) rho cut reader) r with
  | some C =>
    exact congrArg some (savedGenuine_input_origin p E rho hs cut reader r C hc).2
  | none =>
    have hm := time_input_genuine_mem p hsa E rho hs hΔ cut reader hr r hlt hh
    have hf : ((Run.stateBeforeTime (gridCO p) rho cut reader).genuine.find?
        (fun row => row.1 == r)) = none := by
      simpa only [savedGenuine, Option.map_eq_none_iff] using hc
    have hbad := List.find?_eq_none.mp hf _ hm
    simp at hbad

theorem admissionLevels_preGate (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : ReceiptStamped st) (r : Slot) (B : Block) :
    admissionLevels p (clockPreGate p st t) r B = admissionLevels p st r B := by
  have hcount := prefixSupport_eq_of_receiptData p _ st
    (clockPreGate_receiptData p st t) hs r B
  simp only [admissionLevels, hcount, slowEligible, savedGenuine, clockPreGate_genuine]
  rfl


end AvailableChain.GridCO
end

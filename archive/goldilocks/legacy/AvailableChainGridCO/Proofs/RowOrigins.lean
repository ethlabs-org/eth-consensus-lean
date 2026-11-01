module
public import AvailableChainGridCO.Proofs.RawHistory

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A write either preserves an exact old row, including its deadline,
or supplies the exact written key and new deadline. Taking a maximum
cannot invent a deadline or transfer it between strengths. -/
theorem writeObligation_row_origin {n : Nat} (st : State n) (B K : Block)
    (g k : Nat) (d limit : Time)
    (hm : (K, k, d) ∈ (writeObligation st B g limit).obligations) :
    (K, k, d) ∈ st.obligations ∨ K = B ∧ k = g ∧ d = limit := by
  rcases List.mem_append.mp hm with hold | hnew
  · exact Or.inl (List.mem_filter.mp hold).1
  · have he := List.mem_singleton.mp hnew
    have hK : K = B := congrArg Prod.fst he
    have hk : k = g := congrArg (fun row : Block × Nat × Time => row.2.1) he
    subst K; subst k
    have hd : d = max ((deadlineOf st B g).getD limit) limit := congrArg (fun row => row.2.2) he
    unfold deadlineOf at hd
    cases hf : st.obligations.find? (fun (target, level, _) => target == B && level == g) with
    | none => exact Or.inr ⟨rfl, rfl, by simpa [hf] using hd⟩
    | some row =>
        have hrow := List.mem_of_find?_eq_some hf
        have hkey := List.find?_some hf
        have hB : row.1 = B := by simpa using (Bool.and_eq_true_iff.mp hkey).1
        have hg : row.2.1 = g := by simpa using (Bool.and_eq_true_iff.mp hkey).2
        simp only [hf, Option.map_some, Option.getD_some] at hd
        rcases le_total row.2.2 limit with hle | hle
        · exact Or.inr ⟨rfl, rfl, hd.trans (max_eq_right hle)⟩
        · left
          have hd' : d = row.2.2 := hd.trans (max_eq_left hle)
          have heq : row = (B, g, d) := Prod.ext hB (Prod.ext hg hd'.symm)
          simpa only [heq] using hrow

/-- A complete list of writes preserves the same exact-row alternative. -/
theorem writeKeys_row_origin {n : Nat} (st : State n) (keys : List (Block × Nat))
    (B : Block) (g : Nat) (d limit : Time)
    (hm : (B, g, d) ∈ (writeKeys st keys limit).obligations) :
    (B, g, d) ∈ st.obligations ∨ (B, g) ∈ keys ∧ d = limit := by
  induction keys generalizing st with
  | nil => exact Or.inl hm
  | cons key keys ih =>
      rcases ih _ hm with hold | ⟨hkey, hd⟩
      · rcases writeObligation_row_origin st key.1 B key.2 g d limit hold with hold | ⟨hB, hg, hd⟩
        · exact Or.inl hold
        · exact Or.inr ⟨List.mem_cons.mpr (Or.inl (by simp [hB, hg])), hd⟩
      · exact Or.inr ⟨List.mem_cons_of_mem key hkey, hd⟩

section Shared
variable [LeasePolicy]

/-- A new gate row records its own admission test and exact public deadline.
A renewal at another level cannot be its source. -/
theorem gate_row_admitted_origin (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (g : Nat) (d : Time) (hm : (B, g, d) ∈ (gate p st r).obligations) :
    (B, g, d) ∈ st.obligations ∨ ∃ C,
      confirmation p st r = some C ∧ Block.Preceq B C ∧
      g ∈ admissionLevels p st r B ∧ d = gateTime p r + lifetime p := by
  cases hc : confirmation p st r with
  | none => exact Or.inl (by simpa [gate, hc] using hm)
  | some C =>
      by_cases hg : st.obligations.any (fun (target, _, _) => !Block.compatible target C) = true
      · exact Or.inl (by simpa [gate, hc, hg] using hm)
      · rw [gate_eq_writeKeys p st r C hc (Bool.eq_false_iff.mpr hg)] at hm
        rcases writeKeys_row_origin _ _ B g d _ hm with hold | ⟨hkey, hd⟩
        · exact Or.inl hold
        · obtain ⟨A, hA, hmap⟩ := List.mem_flatMap.mp hkey
          obtain ⟨k, hk, he⟩ := List.mem_map.mp hmap
          have hAB : A = B := congrArg Prod.fst he
          have hkg : k = g := congrArg Prod.snd he
          subst A; subst k
          have hprefix := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hA).2).2
          exact Or.inr ⟨C, rfl, hprefix, hk, hd⟩


/-- Clock phases can remove rows but cannot create a new source except at
the actual gate. The source support is measured on the strict clock input. -/
theorem clock_row_admitted_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : ReceiptStamped st) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (clock p st t).obligations) :
    (B, g, d) ∈ st.obligations ∨ ∃ r C,
      t = gateTime p r ∧ confirmation p st r = some C ∧ Block.Preceq B C ∧
      g ∈ admissionLevels p st r B ∧ d = gateTime p r + lifetime p := by
  rw [clock_eq_gate_prestate] at hm
  dsimp only at hm
  split at hm
  · rename_i hgate
    rcases gate_row_admitted_origin p _ _ B g d hm with hold | ⟨C, hc, hp, hadmit, hd⟩
    · exact Or.inl (clockPreGate_obligations_subset p st t _ hold)
    · refine Or.inr ⟨_, C, by simpa using (Bool.and_eq_true_iff.mp hgate).2, ?_, hp, ?_, hd⟩
      · rwa [confirmation_eq_of_receiptData p _ st (clockPreGate_receiptData p st t) hs] at hc
      · rwa [admissionLevels_preGate p st t hs] at hadmit
  · exact Or.inl (clockPreGate_obligations_subset p st t _ hm)

/-- Every reachable row has a real gate source for that exact level and
deadline. The source passes the selected policy's admission test. -/
theorem run_row_genuine_admitted_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho index reader).obligations) :
    ∃ j < index, ∃ r C, rho.events[j]? = some (.tick reader (gateTime p r)) ∧
      confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C ∧
      g ∈ admissionLevels p (gateInput p rho r reader) r B ∧
      d = gateTime p r + lifetime p := by
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
                have hrow : (B, g, d) ∈
                    (clock p (Run.stateBefore (gridCO p) rho index reader) t).obligations := by
                  simpa [World.step] using! hm
                rcases clock_row_admitted_origin p _ t (run_receiptStamped p rho index reader)
                    B g d hrow with hold | ⟨r, C, ht, hc, hp, hadmit, hd⟩
                · obtain ⟨j, hj, rest⟩ := ih hold
                  exact ⟨j, by omega, rest⟩
                · subst t
                  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hc hadmit
                  exact ⟨index, by omega, r, C, hi, hc, hp, hadmit, hd⟩
              · obtain ⟨j, hj, rest⟩ := ih (by simpa [World.step, hv] using hm)
                exact ⟨j, by omega, rest⟩
          | deliver v o t =>
              have hold : (B, g, d) ∈
                  (Run.stateBefore (gridCO p) rho index reader).obligations := by
                by_cases hv : reader = v
                · subst v; simpa [World.step, gridCO, process_obligations] using! hm
                · simpa [World.step, hv] using hm
              obtain ⟨j, hj, rest⟩ := ih hold
              exact ⟨j, by omega, rest⟩

/-- The exact-row source also applies to strict time inputs. -/
theorem time_input_row_genuine_admitted_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).obligations) :
    ∃ r C, gateTime p r < cut ∧
      confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C ∧
      g ∈ admissionLevels p (gateInput p rho r reader) r B ∧
      d = gateTime p r + lifetime p := by
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨j, hj, r, C, hi, rest⟩ := run_row_genuine_admitted_origin p E rho hs _ reader B g d hm
  exact ⟨r, C, Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (cut - 1) hi).mp hj), rest⟩

end Shared


private theorem grid_admission {n : Nat} (p : Params) (st : State n) (r : Slot) (B : Block)
    (g : Nat) (hg : g ∈ admissionLevels p st r B) :
    g ∈ p.grid ∧ g ≤ prefixSupport p st r B := by
  simpa using (List.mem_filter.mp hg).2

theorem gate_row_origin (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (g : Nat) (d : Time) (hm : (B, g, d) ∈ (gate p st r).obligations) :
    (B, g, d) ∈ st.obligations ∨ ∃ C,
      confirmation p st r = some C ∧ Block.Preceq B C ∧
      g ∈ p.grid ∧ g ≤ prefixSupport p st r B ∧ d = gateTime p r + lifetime p := by
  rcases gate_row_admitted_origin p st r B g d hm with hold | ⟨C, hc, hp, ha, hd⟩
  · exact Or.inl hold
  · exact Or.inr ⟨C, hc, hp, (grid_admission p st r B g ha).1,
      (grid_admission p st r B g ha).2, hd⟩

theorem clock_row_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : ReceiptStamped st) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (clock p st t).obligations) :
    (B, g, d) ∈ st.obligations ∨ ∃ r C,
      t = gateTime p r ∧ confirmation p st r = some C ∧ Block.Preceq B C ∧
      g ∈ p.grid ∧ g ≤ prefixSupport p st r B ∧ d = gateTime p r + lifetime p := by
  rcases clock_row_admitted_origin p st t hs B g d hm with hold | ⟨r, C, ht, hc, hp, ha, hd⟩
  · exact Or.inl hold
  · exact Or.inr ⟨r, C, ht, hc, hp, (grid_admission p st r B g ha).1,
      (grid_admission p st r B g ha).2, hd⟩

theorem run_row_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho index reader).obligations) :
    ∃ j < index, ∃ r C, rho.events[j]? = some (.tick reader (gateTime p r)) ∧
      confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C ∧
      g ∈ p.grid ∧ g ≤ prefixSupport p (gateInput p rho r reader) r B ∧
      d = gateTime p r + lifetime p := by
  obtain ⟨j, hj, r, C, hi, hc, hp, ha, hd⟩ :=
    run_row_genuine_admitted_origin p E rho hs index reader B g d hm
  exact ⟨j, hj, r, C, hi, hc, hp, (grid_admission p _ r B g ha).1,
    (grid_admission p _ r B g ha).2, hd⟩

theorem time_input_row_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).obligations) :
    ∃ r C, gateTime p r < cut ∧
      confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C ∧
      g ∈ p.grid ∧ g ≤ prefixSupport p (gateInput p rho r reader) r B ∧
      d = gateTime p r + lifetime p := by
  obtain ⟨r, C, ht, hc, hp, ha, hd⟩ :=
    time_input_row_genuine_admitted_origin p E rho hs cut reader B g d hm
  exact ⟨r, C, ht, hc, hp, (grid_admission p _ r B g ha).1,
    (grid_admission p _ r B g ha).2, hd⟩

/-- At the end of one stage, every surviving row was written from a HEAD
at or after the stage's start. The old pending gate is included: even its
deadline has expired. The source uses the same key and strength. -/
theorem nextHeadState_row_source_after_stage {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (boundary r : Slot) (hstage : boundary + p.m ≤ r + 1)
    (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (nextHeadState p rho r reader).obligations) :
    ∃ s C, boundary ≤ s ∧ s < r ∧
      confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C ∧
      g ∈ p.grid ∧ g ≤ prefixSupport p (gateInput p rho s reader) s B ∧
      d = gateTime p s + lifetime p := by
  have hrow := nextHeadState_row_survives_release p rho r reader B g d hm
  obtain ⟨s, C, ht, hc, hp, hg, hcount, hd⟩ := time_input_row_genuine_origin p E rho hs
    (releaseTime p r) reader B g d (List.mem_filter.mp hrow.1).1
  refine ⟨s, C, ?_, ?_, hc, hp, hg, hcount, hd⟩
  · by_contra hn
    have hdeadline := old_head_deadline_by_next_stage p s boundary (Nat.lt_of_not_ge hn)
    have htime : voteTime p boundary + (lifetime p + p.Δ) ≤ releaseTime p r := by
      have he : voteTime p (boundary + p.m) =
          voteTime p boundary + (lifetime p + p.Δ) := by
        simpa using healing_stage_time p boundary 1
      rw [release_eq_next_vote, ← he]
      dsimp [voteTime, proposalTime]
      have hi : (boundary : Time) + p.m ≤ (r : Time) + 1 := by exact_mod_cast hstage
      nlinarith [p.deltaPos]
    rw [← hd] at hdeadline
    exact (not_lt.mpr (hdeadline.trans htime)) hrow.2
  · by_contra hn
    have hgate := (gateTime_le_iff p r s).mpr (Nat.le_of_not_gt hn)
    dsimp [gateTime, releaseTime] at ht hgate
    linarith [p.deltaPos]

end AvailableChain.GridCO
end

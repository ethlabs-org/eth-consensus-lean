module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainGridCO.Proofs.MergedViews
public import AvailableChainGridCO.Proofs.Preservation
public import AvailableChainGridCO.Proofs.HistoryInduction

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A gate can add only prefixes of its genuine result to the map. -/
theorem gate_target_origin (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (gate p st r).obligations) :
    (∃ k deadline, (B, k, deadline) ∈ st.obligations) ∨
      ∃ C, confirmation p st r = some C ∧ Block.Preceq B C :=
  gateFrom_target_origin p .genesis st r B g d hm

/-- Expiry and release add no target. A new clock target comes from its
actual gate and the genuine result of the strict input. -/
theorem clock_target_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (hs : ReceiptStamped st) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (clock p st t).obligations) :
    (∃ k deadline, (B, k, deadline) ∈ st.obligations) ∨
      ∃ r C, t = gateTime p r ∧ confirmation p st r = some C ∧ Block.Preceq B C := by
  rw [clock_eq_gate_prestate] at hm
  dsimp only at hm
  split at hm
  · rename_i hgate
    rcases gate_target_origin p _ _ B g d hm with ⟨k, deadline, hold⟩ | ⟨C, hc, hp⟩
    · exact Or.inl ⟨k, deadline, clockPreGate_obligations_subset p st t _ hold⟩
    · refine Or.inr ⟨_, C, by simpa using (Bool.and_eq_true_iff.mp hgate).2, ?_, hp⟩
      rw [confirmation_eq_of_receiptData p _ st (clockPreGate_receiptData p st t) hs] at hc
      exact hc
  · exact Or.inl ⟨g, d, clockPreGate_obligations_subset p st t _ hm⟩

/-- Each reachable obligation target has an earlier genuine gate source.
Deletion, renewal, and pending gates cannot create an unsupported target. -/
theorem run_target_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho index reader).obligations) :
    ∃ j < index, ∃ r C,
      rho.events[j]? = some (.tick reader (gateTime p r)) ∧
      confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C := by
  set_option backward.isDefEq.respectTransparency false in
  induction index generalizing g d with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial] at hm
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none =>
          obtain ⟨j, hj, hrest⟩ := ih g d (by
            simpa [Run.stateBefore, List.take_add_one, hi] using hm)
          exact ⟨j, by omega, hrest⟩
      | some e =>
          rw [stateBefore_succ_event hi] at hm
          cases e with
          | tick v t =>
              by_cases hv : reader = v
              · subst v
                have hrow : (B, g, d) ∈
                    (clock p (Run.stateBefore (gridCO p) rho index reader) t).obligations := by
                  simpa [World.step] using! hm
                rcases clock_target_origin p _ t (run_receiptStamped p rho index reader)
                    B g d hrow with ⟨k, deadline, hold⟩ | ⟨r, C, ht, hc, hp⟩
                · obtain ⟨j, hj, hrest⟩ := ih k deadline hold
                  exact ⟨j, by omega, hrest⟩
                · subst t
                  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hc
                  exact ⟨index, by omega, r, C, hi, hc, hp⟩
              · obtain ⟨j, hj, hrest⟩ := ih g d (by simpa [World.step, hv] using hm)
                exact ⟨j, by omega, hrest⟩
          | deliver v o t =>
              have hold : (B, g, d) ∈
                  (Run.stateBefore (gridCO p) rho index reader).obligations := by
                by_cases hv : reader = v
                · subst v; simpa [World.step, gridCO, process_obligations] using! hm
                · simpa [World.step, hv] using hm
              obtain ⟨j, hj, hrest⟩ := ih g d hold
              exact ⟨j, by omega, hrest⟩

/-- A target in a strict input comes from a strictly earlier gate. -/
theorem time_input_target_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).obligations) :
    ∃ r C, gateTime p r < cut ∧
      confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C := by
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨j, hj, r, C, hi, hc, hp⟩ := run_target_genuine_origin p E rho hs _ reader B g d hm
  exact ⟨r, C, Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (cut - 1) hi).mp hj), hc, hp⟩

/-- Rows present at release r came from labels strictly smaller than r.
The label-r gate is still pending at this instant. -/
theorem nextHeadState_target_genuine_origin {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (nextHeadState p rho r reader).obligations) :
    ∃ s C, s < r ∧ confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
  have hrow := (nextHeadState_row_survives_release p rho r reader B g d hm).1
  have hold := (List.mem_filter.mp hrow).1
  obtain ⟨s, C, ht, hc, hp⟩ := time_input_target_genuine_origin p E rho hs
    (releaseTime p r) reader B g d hold
  refine ⟨s, C, ?_, hc, hp⟩
  by_contra hn
  have hle := (gateTime_le_iff p r s).mpr (le_of_not_gt hn)
  dsimp [gateTime, releaseTime] at ht hle
  linarith [p.deltaPos]

/-- The clean history induction has two parts. Every older genuine result
is retained by every current result. Every current result transfers to
the next ordinary HEAD. -/
theorem clean_genuine_history {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r) :
    (∀ s, s < r → ∀ source ∈ rho.honest, ∀ B,
      confirmation p (gateInput p rho s source) s = some B →
      ∀ reader ∈ rho.honest, ∃ C,
        confirmation p (gateInput p rho r reader) r = some C ∧ Block.Preceq B C) ∧
    (∀ source ∈ rho.honest, ∀ B,
      confirmation p (gateInput p rho r source) r = some B →
      ∀ reader ∈ rho.honest,
        Block.Preceq B (nextHead p (nextHeadState p rho r reader) r)) := by
  apply genuine_history_induction (fun v => v ∈ rho.honest)
    (fun s v => confirmation p (gateInput p rho s v) s)
    (fun s v => nextHead p (nextHeadState p rho s v) s) r
  · intro s hs continuation source hsource B hc reader hreader
    have hsync := hclean (s + 1) (Nat.succ_le_of_lt hs)
    obtain ⟨C, hC, hBC, _⟩ := preserve_from_engine p E rho hΔ s hsync
      hsync.2.1 B (continuation source hsource B hc) reader hreader
    exact ⟨C, hC, hBC⟩
  · intro s hs history source hsource B hc
    have hsync := hclean s hs
    apply transfer_from_engine p E rho hΔ s hsync
      source hsource B B hc (block_preceq_self B)
    intro reader hreader K hK
    obtain ⟨⟨target, g, d⟩, hm, ht⟩ := List.mem_filterMap.mp hK
    dsimp only at ht
    split at ht
    · have he : target = K := Option.some.inj ht
      subst target
      obtain ⟨a, D, has, hD, hKD⟩ := nextHeadState_target_genuine_origin p E rho
        hsync.1.toScheduleWellFormed s reader K g d hm
      obtain ⟨C, hC, hDC⟩ := history a has reader hreader D hD source hsource
      have he : C = B := Option.some.inj (hC.symm.trans hc)
      subst C
      exact Bool.or_eq_true_iff.mpr (Or.inl (prefix_trans K D B hKD hDC))
    · simp at ht

/-- Strictly later clean genuine results extend every earlier one. -/
theorem clean_genuine_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r s : Slot) (hrs : r < s) (hclean : CleanThroughLabel p E rho s)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C : Block) (hB : confirmation p (gateInput p rho r source) r = some B)
    (hC : confirmation p (gateInput p rho s reader) s = some C) : Block.Preceq B C := by
  obtain ⟨D, hD, hp⟩ := (clean_genuine_history p E rho hΔ s hclean).1 r hrs source hs B hB reader hr
  have he : D = C := Option.some.inj (hD.symm.trans hC)
  simpa [he] using hp

end AvailableChain.GridCO
end

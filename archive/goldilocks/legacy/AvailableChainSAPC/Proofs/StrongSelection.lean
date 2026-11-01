module
public import AvailableChainSAPC.Proofs.StrongSteps

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Every completed freeze retains its exact live PC, including `none`.
This is a local scheduled-clock fact; it uses no network premise. -/
theorem frozenPCAt_after_freeze {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (hv : v ∈ rho.honest)
    (cut : Time) (before : freezeTime p r < cut) (horizon : freezeTime p r ≤ rho.horizon) :
    frozenPCAt (Run.stateBeforeTime (sapc p) rho cut v) r =
      (Run.stateBeforeTime (sapc p) rho (freezeTime p r) v).bestPC := by
  set_option backward.isDefEq.respectTransparency false in
  have pub : PublicTime E (freezeTime p r) := by
    refine ⟨4 * r + 3, ?_⟩
    change 4 * p.Δ * (r : Time) + 3 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ freezeTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hs.tick_total v hv _ pub nonneg horizon)
  have post : ∃ c, (r, c) ∈ (Run.stateBefore (sapc p) rho (i + 1) v).frozenPC := by
    rw [stateBefore_succ_event tick]
    simp only [World.step, Function.update_self]
    change ∃ c, (r, c) ∈ (clock p _ (freezeTime p r)).frozenPC
    rw [clock_frozenPC]
    have time : freezeTime p r - 3 * p.Δ = 4 * p.Δ * (r : Time) := by
      change 4 * p.Δ * (r : Time) + 3 * p.Δ - 3 * p.Δ = _
      ring
    have mul : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
    simp only [time, Int.mul_ediv_cancel_left _ mul, Int.toNat_natCast]
    have pos : 0 ≤ 4 * p.Δ * (r : Time) := by
      have := p.deltaPos
      positivity
    simp only [pos, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    split
    · rename_i existsRow
      obtain ⟨row, member, label⟩ := List.any_eq_true.mp existsRow
      rcases row with ⟨label', cert⟩
      have eq : label' = r := by simpa using label
      subst label'
      exact ⟨cert, member⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  have bound := (index_lt_read_length_iff hs (cut - 1) tick).mpr
    (Int.le_sub_one_iff.mpr before)
  rw [time_input_eq_event_prefix p E rho hs]
  obtain ⟨c, member⟩ := post
  have retained := (stateBefore_frozenPC_prefix p rho (Nat.succ_le_of_lt bound) v).subset member
  unfold frozenPCAt
  cases found : (Run.stateBefore (sapc p) rho
      (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length v).frozenPC.find?
      (fun row => row.1 == r) with
  | none => have bad := List.find?_eq_none.mp found _ retained; simp at bad
  | some row =>
    have label : row.1 = r := by simpa using List.find?_some found
    obtain ⟨j, _, source, eq⟩ := frozenPC_origin_before p rho _ v row.1 row.2
      (List.mem_of_find?_eq_some found)
    rw [label] at source
    rw [stateBefore_tick_eq_stateBeforeTime hs source] at eq
    simpa only [Option.map_some, Option.getD_some] using eq

/-- Later clocks retain a nonempty frozen selection. -/
theorem clock_frozenPCAt_retained (p : Params) {n : Nat} (st : State n)
    (t : Time) (r : Slot) (c : PC n) (frozen : frozenPCAt st r = some c) :
    frozenPCAt (clock p st t) r = some c := by
  unfold frozenPCAt at frozen ⊢
  cases found : st.frozenPC.find? (fun row => row.1 == r) with
  | none => simp [found] at frozen
  | some row =>
    rcases clock_frozenPC_cases p st t with unchanged | ⟨_, added⟩
    · simpa only [unchanged] using frozen
    · simpa only [added, List.find?_append, found, Option.or_some] using! frozen

/-- Carried selection retains at least the frozen rank, for arbitrary
proposal authors and arrival order. Equal ranks retain the old encoding. -/
theorem selectedPC_rank (p : Params) {n : Nat} (st : State n) (r : Slot) :
    PCRankLE (frozenPCAt st (r - 1)) (selectedPC p st r) := by
  have fold (xs : List (Wire n)) (best : Option (PC n)) :
      PCRankLE best (xs.foldl (fun best o => match o.payload with
        | .proposal b _ _ (some c) =>
            if b.slot == r && pcValid p st c then preferPC best c else best
        | _ => best) best) := by
    induction xs generalizing best with
    | nil => exact .refl _
    | cons o xs ih =>
      apply PCRankLE.trans _ (ih _)
      dsimp only
      split
      · split
        · exact preferPC_rank _ _
        · exact .refl _
      · exact .refl _
  exact fold st.proposals (frozenPCAt st (r - 1))

/-- Common installation retains a rank floor at every later strict
input. Target preservation is supplied separately by preparation coverage. -/
theorem strongArmed_rank_beforeTime {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (t : Time) (after : b₀ ≤ t) (v : V) (hv : v ∈ rho.honest) :
    ∃ d, (Run.stateBeforeTime (sapc p) rho t v).bestPC = some d ∧ c.slot ≤ d.slot := by
  obtain ⟨d, installed, rank, _⟩ := strongArmed_common_pc p E rho hΔ T b₀ h u hu c selected v hv
  have input (t : Time) : Run.stateBeforeTime (sapc p) rho t =
      Run.readAt (sapc p) rho (t - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at installed ⊢
  obtain ⟨e, later, next⟩ := strong_certificate_retained p E rho h.execution.toScheduleWellFormed
    v (b₀ - 1) (t - 1) (by linarith) d installed
  exact ⟨e, later, rank.trans next⟩

/-- A freeze after common installation seeds the selected HEAD rank.
No later live receipt or proposal delivery is required. -/
theorem strongArmed_selected_rank {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (after : b₀ ≤ freezeTime p r)
    (horizon : voteTime p (r + 1) ≤ rho.horizon) (v : V) (hv : v ∈ rho.honest) :
    ∃ d, selectedPC p (headState p rho (r + 1) v) (r + 1) = some d ∧ c.slot ≤ d.slot := by
  have before : freezeTime p r < voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ <
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast; linarith [p.deltaPos]
  obtain ⟨d, live, rank⟩ := strongArmed_rank_beforeTime p E rho hΔ T b₀ h u hu c selected
    (freezeTime p r) after v hv
  have frozen := (frozenPCAt_after_freeze p E rho h.execution.toScheduleWellFormed hΔ r v hv
    _ before (before.le.trans horizon)).trans live
  have headFrozen := clock_frozenPCAt_retained p _ (voteTime p (r + 1)) r d frozen
  obtain ⟨e, choice, next⟩ := selectedPC_rank p (headState p rho (r + 1) v) (r + 1) d
    (by simpa only [Nat.add_sub_cancel] using! headFrozen)
  refine ⟨e, choice, rank.trans ?_⟩
  rcases next with rfl | next
  · exact le_refl _
  · exact next.le

end AvailableChain.SAPC
end

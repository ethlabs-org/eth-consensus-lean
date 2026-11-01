module
public import AvailableChainGridCO.Proofs.GenuineHistory
public import AvailableChainGridCO.Proofs.Regimes

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A public gate record is genesis or a genuine result of this or an
older gate. This source fact does not require synchrony. -/
theorem gate_record_genuine_origin {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon) (reader : V) (hr : reader ∈ rho.honest) :
    stable (Run.readAt (gridCO p) rho (gateTime p r) reader) = .genesis ∨
      ∃ s, s ≤ r ∧ confirmation p (gateInput p rho s reader) s =
        some (stable (Run.readAt (gridCO p) rho (gateTime p r) reader)) := by
  induction r with
  | zero =>
      rcases read_gate_record_cases p E rho hs hΔ 0 hh reader hr with he | hc
      · exact Or.inl (he.trans (by simp [gate_input_record p E rho hs]))
      · exact Or.inr ⟨0, le_refl _, hc⟩
  | succ r ih =>
      rcases read_gate_record_cases p E rho hs hΔ (r + 1) hh reader hr with he | hc
      · have he' : stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader) =
            stable (Run.readAt (gridCO p) rho (gateTime p r) reader) := by
          simpa [gate_input_record p E rho hs] using he
        rw [he']
        rcases ih ((gateTime_le_iff p r (r + 1)).mpr (Nat.le_succ r) |>.trans hh) with
          hg | ⟨s, hs, hc⟩
        · exact Or.inl hg
        · exact Or.inr ⟨s, hs.trans (Nat.le_succ r), hc⟩
      · exact Or.inr ⟨r + 1, le_refl _, hc⟩

/-- A gate's old record has a genuine source at a strictly older label. -/
theorem gate_input_genuine_origin {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon) (reader : V) (hr : reader ∈ rho.honest) :
    stable (gateInput p rho r reader) = .genesis ∨
      ∃ s, s < r ∧ confirmation p (gateInput p rho s reader) s =
        some (stable (gateInput p rho r reader)) := by
  cases r with
  | zero => exact Or.inl (by simp [gate_input_record p E rho hs])
  | succ r =>
      simp only [gate_input_record p E rho hs]
      rcases gate_record_genuine_origin p E rho hs hΔ r
        (((gateTime_le_iff p r (r + 1)).mpr (Nat.le_succ r)).trans hh) reader hr with
        hg | ⟨s, hs, hc⟩
      · exact Or.inl hg
      · exact Or.inr ⟨s, Nat.lt_succ_of_le hs, hc⟩

/-- Every clean gate retains its preceding record. This follows from
ordered genuine results. -/
theorem clean_gate_record_monotone {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (reader : V) (hr : reader ∈ rho.honest) :
    Block.Preceq (stable (gateInput p rho r reader))
      (stable (Run.readAt (gridCO p) rho (gateTime p r) reader)) := by
  have hsync := hclean r (le_refl _)
  rcases read_gate_record_cases p E rho hsync.1.toScheduleWellFormed hΔ r
      hsync.2.2.1 reader hr with he | hc
  · rw [he]; exact block_preceq_self _
  · rcases gate_input_genuine_origin p E rho hsync.1.toScheduleWellFormed hΔ r
        hsync.2.2.1 reader hr with hg | ⟨s, hs, hsource⟩
    · rw [hg]; exact genesis_prefix _
    · exact clean_genuine_prefix p E rho hΔ s r hs hclean reader reader hr hr _ _ hsource hc

/-- Any two clean public gate records are compatible, including a reader
that kept an older record. No later gate beyond either read is required. -/
theorem clean_gate_reads_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r s : Slot) (hclean : CleanThroughLabel p E rho (max r s))
    (u v : V) (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Compatible (stable (Run.readAt (gridCO p) rho (gateTime p r) u))
      (stable (Run.readAt (gridCO p) rho (gateTime p s) v)) := by
  have hr := hclean r (le_max_left _ _)
  have hs := hclean s (le_max_right _ _)
  rcases gate_record_genuine_origin p E rho hr.1.toScheduleWellFormed hΔ r hr.2.2.1 u hu
    with hg | ⟨a, har, ha⟩
  · rw [hg]; exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_prefix _))
  rcases gate_record_genuine_origin p E rho hs.1.toScheduleWellFormed hΔ s hs.2.2.1 v hv
    with hg | ⟨b, hbs, hb⟩
  · rw [hg]; exact Bool.or_eq_true_iff.mpr (Or.inr (genesis_prefix _))
  rcases lt_trichotomy a b with hab | he | hba
  · exact Bool.or_eq_true_iff.mpr (Or.inl (clean_genuine_prefix p E rho hΔ a b hab
      (fun k hk => hclean k (hk.trans (hbs.trans (le_max_right _ _)))) u v hu hv _ _ ha hb))
  · subst b
    exact sameLabel_from_engine p E rho hΔ a
      (hclean a (har.trans (le_max_left _ _))) u hu v hv _ _ ha hb
  · exact Bool.or_eq_true_iff.mpr (Or.inr (clean_genuine_prefix p E rho hΔ b a hba
      (fun k hk => hclean k (hk.trans (har.trans (le_max_left _ _)))) v u hv hu _ _ hb ha))

/-- One reader's clean gate records only extend. -/
theorem clean_gate_record_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r s : Slot) (hrs : r ≤ s) (hclean : CleanThroughLabel p E rho s)
    (reader : V) (hr : reader ∈ rho.honest) :
    Block.Preceq (stable (Run.readAt (gridCO p) rho (gateTime p r) reader))
      (stable (Run.readAt (gridCO p) rho (gateTime p s) reader)) := by
  induction s with
  | zero => have he : r = 0 := Nat.le_zero.mp hrs; subst r; exact block_preceq_self _
  | succ s ih =>
      rcases Nat.eq_or_lt_of_le hrs with he | hlt
      · subst r; exact block_preceq_self _
      · have hsync := hclean (s + 1) (le_refl _)
        have hp := clean_gate_record_monotone p E rho hΔ (s + 1) hclean reader hr
        have hinput : stable (gateInput p rho (s + 1) reader) =
            stable (Run.readAt (gridCO p) rho (gateTime p s) reader) := by
          simp [gate_input_record p E rho hsync.1.toScheduleWellFormed]
        rw [hinput] at hp
        exact prefix_trans _ _ _ (ih (Nat.le_of_lt_succ hlt)
          (fun k hk => hclean k (hk.trans (Nat.le_succ s)))) hp

/-- Clean monotonicity for all honest reads follows from the engine.
The proof includes the last incomplete label in a finite run. -/
theorem stable_monotone_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (t₀ : Time)
    (hsleep : SleepyRegime (gridCO p) E (gridInterface p) rho t₀) :
    MonotoneFrom (gridCO p) rho (gridInterface p).stable t₀ := by
  intro reader hr t t' _ htt' hh
  change Block.Preceq (stable (Run.readAt (gridCO p) rho t reader))
    (stable (Run.readAt (gridCO p) rho t' reader))
  by_cases ht : t < gateTime p 0
  · rw [read_stable_before_first_gate p rho t ht reader]
    exact genesis_prefix _
  obtain ⟨r, hrlo, hrhi⟩ := exists_latest_gate p t (le_of_not_gt ht)
  obtain ⟨s, hslo, hshi⟩ := exists_latest_gate p t' (le_trans (le_of_not_gt ht) htt')
  rw [read_stable_eq_latest_gate p E rho hsleep.execution.toScheduleWellFormed
      r t hrlo hrhi reader,
    read_stable_eq_latest_gate p E rho hsleep.execution.toScheduleWellFormed
      s t' hslo hshi reader]
  have hrs : r ≤ s := by
    by_contra hc
    have := (gateTime_le_iff p (s + 1) r).mpr (Nat.succ_le_of_lt (Nat.lt_of_not_ge hc))
    linarith
  exact clean_gate_record_prefix p E rho hΔ r s hrs
    (cleanThroughLabel_of_sleepy t₀ hsleep s (hslo.trans hh)) reader hr

/-- Clean safety of the public stable output, from the frozen contract
premises and the engine. -/
theorem stable_safe_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (t₀ : Time)
    (hsleep : SleepyRegime (gridCO p) E (gridInterface p) rho t₀) :
    SafeFrom (gridCO p) rho (gridInterface p).stable t₀ := by
  refine ⟨?_, stable_monotone_from_engine p E rho hΔ t₀ hsleep⟩
  intro u hu v hv t t' _ hh _ hh'
  change Block.Compatible (stable (Run.readAt (gridCO p) rho t u))
    (stable (Run.readAt (gridCO p) rho t' v))
  by_cases ht : t < gateTime p 0
  · rw [read_stable_before_first_gate p rho t ht u]
    exact Bool.or_eq_true_iff.mpr (Or.inl (genesis_prefix _))
  by_cases ht' : t' < gateTime p 0
  · rw [read_stable_before_first_gate p rho t' ht' v]
    exact Bool.or_eq_true_iff.mpr (Or.inr (genesis_prefix _))
  obtain ⟨r, hrlo, hrhi⟩ := exists_latest_gate p t (le_of_not_gt ht)
  obtain ⟨s, hslo, hshi⟩ := exists_latest_gate p t' (le_of_not_gt ht')
  rw [read_stable_eq_latest_gate p E rho hsleep.execution.toScheduleWellFormed
      r t hrlo hrhi u,
    read_stable_eq_latest_gate p E rho hsleep.execution.toScheduleWellFormed
      s t' hslo hshi v]
  apply clean_gate_reads_compatible p E rho hΔ r s _ u v hu hv
  apply cleanThroughLabel_of_sleepy t₀ hsleep
  rcases le_total r s with h | h
  · simpa [max_eq_right h] using hslo.trans hh'
  · simpa [max_eq_left h] using hrlo.trans hh

/-- Both exposed outputs satisfy clean safety under Sleepy. -/
theorem clean_safety_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (t₀ : Time)
    (hsleep : SleepyRegime (gridCO p) E (gridInterface p) rho t₀) :
    SafeFrom (gridCO p) rho (gridInterface p).stable t₀ ∧
      SafeFrom (gridCO p) rho (gridInterface p).confirmed t₀ :=
  ⟨stable_safe_from_engine p E rho hΔ t₀ hsleep,
    stable_safe_from_engine p E rho hΔ t₀ hsleep⟩

/-- Both contract outputs are monotone in the clean Sleepy regime. -/
theorem monotone_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (t₀ : Time)
    (hsleep : SleepyRegime (gridCO p) E (gridInterface p) rho t₀) :
    MonotoneFrom (gridCO p) rho (gridInterface p).confirmed t₀ ∧
      MonotoneFrom (gridCO p) rho (gridInterface p).stable t₀ :=
  ⟨stable_monotone_from_engine p E rho hΔ t₀ hsleep,
    stable_monotone_from_engine p E rho hΔ t₀ hsleep⟩

end AvailableChain.GridCO
end

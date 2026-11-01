module
public import AvailableChainGridCO.Proofs.RecoveryRepair
public import AvailableChainGridCO.Proofs.RepairedHistory

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false
variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- After all levels are supported, every later genuine result extends
every earlier genuine result in the suffix. -/
theorem stage_genuine_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (boundary : Slot) (hpos : 0 < boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary ∅)
    (r s : Slot) (hbr : boundary ≤ r) (hrs : r < s) (hh : gateTime p s ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C : Block) (hB : confirmation p (gateInput p rho r source) r = some B)
    (hC : confirmation p (gateInput p rho s reader) s = some C) : Block.Preceq B C := by
  have hperm := permanent_support_at_level p E rho hΔ boundary hpos ∅ 0
    (by simp) hseq hrows r hbr
    (((gateTime_le_iff p r s).mpr hrs.le).trans hh) source hs B B hB
    (block_preceq_self _) (Nat.zero_le _)
  have hhead := (hperm (s - 1) (Nat.le_sub_one_of_lt hrs)
    (((gateTime_le_iff p (s - 1) s).mpr (Nat.sub_le s 1)).trans hh)).2
  have he : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.zero_le r |>.trans_lt hrs)
  have hpres := preserve_from_engine p E rho hΔ (s - 1)
  rw [he] at hpres
  have hsync := hseq s (hbr.trans hrs.le) hh
  obtain ⟨C', hC', hp, _⟩ := hpres hsync hsync.2.1 B hhead reader hr
  have heq : C' = C := Option.some.inj (hC'.symm.trans hC)
  simpa only [heq] using! hp

/-- Once a gate repairs a record to a genuine result, all later records
have a genuine source at or after that repair. Old pre-recovery records
cannot reappear through expiry, release, or a rejected gate. -/
theorem gate_record_origin_after_repair {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (hs : ScheduleWellFormed E rho)
    (repair : Slot) (B : Block)
    (hrepair : ∀ reader ∈ rho.honest,
      stable (Run.readAt (gridCO p) rho (gateTime p repair) reader) = B)
    (hconf : ∀ reader ∈ rho.honest, confirmation p (gateInput p rho repair reader) repair = some B)
    (t : Slot) (hrt : repair ≤ t) (hh : gateTime p t ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    ∃ s, repair ≤ s ∧ s ≤ t ∧ confirmation p (gateInput p rho s reader) s =
      some (stable (Run.readAt (gridCO p) rho (gateTime p t) reader)) := by
  apply repaired_record_source
    (fun s => confirmation p (gateInput p rho s reader) s)
    (fun s => stable (Run.readAt (gridCO p) rho (gateTime p s) reader))
    (fun s => gateTime p s ≤ rho.horizon)
    (fun s t le hh => ((gateTime_le_iff p s t).mpr le).trans hh) repair
    (by rw [hrepair reader hr]; exact hconf reader hr) _ t hrt hh
  intro s after bound
  rcases read_gate_record_cases p E rho hs hΔ s bound reader hr with old | raw
  · left
    rw [old, gate_input_record p E rho hs]
    simp only [show s ≠ 0 from Nat.ne_zero_of_lt after, ↓reduceIte]
  · exact Or.inr raw

/-- Repaired gate records are monotone throughout the supported suffix. -/
theorem repaired_gate_record_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho) (boundary : Slot) (hpos : 0 < boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary ∅)
    (repair : Slot) (hbr : boundary ≤ repair) (B : Block)
    (hrepair : ∀ reader ∈ rho.honest,
      stable (Run.readAt (gridCO p) rho (gateTime p repair) reader) = B)
    (hconf : ∀ reader ∈ rho.honest, confirmation p (gateInput p rho repair reader) repair = some B)
    (r t : Slot) (hrr : repair ≤ r) (hrt : r ≤ t) (hh : gateTime p t ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    Block.Preceq (stable (Run.readAt (gridCO p) rho (gateTime p r) reader))
      (stable (Run.readAt (gridCO p) rho (gateTime p t) reader)) := by
  apply repaired_record_prefix
    (fun s => confirmation p (gateInput p rho s reader) s)
    (fun s => stable (Run.readAt (gridCO p) rho (gateTime p s) reader))
    (fun s => gateTime p s ≤ rho.horizon)
    (fun s t le hh => ((gateTime_le_iff p s t).mpr le).trans hh) repair
    (by rw [hrepair reader hr]; exact hconf reader hr) _ _ r t hrr hrt hh
  · intro s after bound
    rcases read_gate_record_cases p E rho hexec.toScheduleWellFormed hΔ s bound reader hr
      with old | raw
    · left
      rw [old, gate_input_record p E rho hexec.toScheduleWellFormed]
      simp only [show s ≠ 0 from Nat.ne_zero_of_lt after, ↓reduceIte]
    · exact Or.inr raw
  · intro a b lo lt bound C D rawC rawD
    exact stage_genuine_prefix p E rho hΔ boundary hpos hseq hrows a b (hbr.trans lo)
      lt bound reader reader hr hr C D rawC rawD

/-- Any two repaired gate records are compatible, including retained
records at the final incomplete label of a finite run. -/
theorem repaired_gate_records_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho) (boundary : Slot) (hpos : 0 < boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary ∅)
    (repair : Slot) (hbr : boundary ≤ repair) (B : Block)
    (hrepair : ∀ reader ∈ rho.honest,
      stable (Run.readAt (gridCO p) rho (gateTime p repair) reader) = B)
    (hconf : ∀ reader ∈ rho.honest, confirmation p (gateInput p rho repair reader) repair = some B)
    (r s : Slot) (hrr : repair ≤ r) (hrs : repair ≤ s)
    (hhr : gateTime p r ≤ rho.horizon) (hhs : gateTime p s ≤ rho.horizon)
    (u v : V) (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Compatible (stable (Run.readAt (gridCO p) rho (gateTime p r) u))
      (stable (Run.readAt (gridCO p) rho (gateTime p s) v)) := by
  obtain ⟨a, hra, har, ha⟩ := gate_record_origin_after_repair p E rho hΔ
    hexec.toScheduleWellFormed repair B hrepair hconf r hrr hhr u hu
  obtain ⟨b, hrb, hbs, hb⟩ := gate_record_origin_after_repair p E rho hΔ
    hexec.toScheduleWellFormed repair B hrepair hconf s hrs hhs v hv
  have hha := ((gateTime_le_iff p a r).mpr har).trans hhr
  have hhb := ((gateTime_le_iff p b s).mpr hbs).trans hhs
  rcases lt_trichotomy a b with hab | he | hba
  · exact Bool.or_eq_true_iff.mpr (Or.inl (stage_genuine_prefix p E rho hΔ boundary hpos
      hseq hrows a b (hbr.trans hra) hab hhb u v hu hv _ _ ha hb))
  · subst b
    exact sameLabel_from_engine p E rho hΔ a (hseq a (hbr.trans hra) hha)
      u hu v hv _ _ ha hb
  · exact Bool.or_eq_true_iff.mpr (Or.inr (stage_genuine_prefix p E rho hΔ boundary hpos
      hseq hrows b a (hbr.trans hrb) hba hha v u hv hu _ _ hb ha))

/-- Repair starts a safe suffix for all honest read times. -/
theorem safe_from_repaired_gate {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho) (boundary : Slot) (hpos : 0 < boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary ∅)
    (repair : Slot) (hbr : boundary ≤ repair) (B : Block)
    (hrepair : ∀ reader ∈ rho.honest,
      stable (Run.readAt (gridCO p) rho (gateTime p repair) reader) = B)
    (hconf : ∀ reader ∈ rho.honest,
      confirmation p (gateInput p rho repair reader) repair = some B) :
    SafeFrom (gridCO p) rho (gridInterface p).stable (gateTime p repair) := by
  have hs := hexec.toScheduleWellFormed
  have latest (t : Time) (ht : gateTime p repair ≤ t) :
      ∃ r, repair ≤ r ∧ gateTime p r ≤ t ∧ t < gateTime p (r + 1) := by
    obtain ⟨r, hlo, hhi⟩ := exists_latest_gate p t
      (((gateTime_le_iff p 0 repair).mpr (Nat.zero_le _)).trans ht)
    refine ⟨r, ?_, hlo, hhi⟩
    by_contra hn
    have hle := (gateTime_le_iff p (r + 1) repair).mpr (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
    exact (not_lt.mpr (hle.trans ht)) hhi
  constructor
  · intro u hu v hv t t' ht hh ht' hh'
    obtain ⟨r, hrr, hrlo, hrhi⟩ := latest t ht
    obtain ⟨s, hrs, hslo, hshi⟩ := latest t' ht'
    change Block.Compatible (stable (Run.readAt (gridCO p) rho t u))
      (stable (Run.readAt (gridCO p) rho t' v))
    rw [read_stable_eq_latest_gate p E rho hs r t hrlo hrhi u,
      read_stable_eq_latest_gate p E rho hs s t' hslo hshi v]
    exact repaired_gate_records_compatible p E rho hΔ hexec boundary hpos hseq hrows repair hbr
      B hrepair hconf r s hrr hrs (hrlo.trans hh) (hslo.trans hh') u v hu hv
  · intro v hv t t' ht htt' hh'
    obtain ⟨r, hrr, hrlo, hrhi⟩ := latest t ht
    obtain ⟨s, _, hslo, hshi⟩ := latest t' (ht.trans htt')
    change Block.Preceq (stable (Run.readAt (gridCO p) rho t v))
      (stable (Run.readAt (gridCO p) rho t' v))
    rw [read_stable_eq_latest_gate p E rho hs r t hrlo hrhi v,
      read_stable_eq_latest_gate p E rho hs s t' hslo hshi v]
    have hrs : r ≤ s := by
      by_contra hn
      have hle := (gateTime_le_iff p (s + 1) r).mpr (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
      exact (not_lt.mpr (hle.trans (hrlo.trans htt'))) hshi
    exact repaired_gate_record_prefix p E rho hΔ hexec boundary hpos hseq hrows repair hbr
      B hrepair hconf r s hrr hrs (hslo.trans hh') v hv

end AvailableChain.GridCO
end

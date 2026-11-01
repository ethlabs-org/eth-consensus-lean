module
public import AvailableChainSA.Proofs.Clean
public import AvailableChainGridCO.Proofs.RawHistory
public import AvailableChainGridCO.Proofs.RecoveryPersistence

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic
local instance saSlowWindowLeasePolicy : GridCO.LeasePolicy := GridCO.slowLeasePolicy

/-- Every SA lease has the one fixed release level. Admission can use a
single high count or the consecutive local history; it does not add counts. -/
theorem admissionLevels_iff (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) (g : Nat) :
    g ∈ GridCO.admissionLevels p.engine st r B ↔
      g = releaseThreshold p ∧
        (releaseThreshold p ≤ prefixSupport p st r B ∨ slowEligible p st r B = true) := by
  have hpolicy : GridCO.LeasePolicy.slowArming = true := rfl
  simp only [GridCO.admissionLevels, hpolicy, ↓reduceIte]
  split <;> simp_all

/-- A saved slow window gives real raw results at every earlier label in
that window. The source is the same reader, including when it slept. -/
theorem slowEligible_input_covers {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sa p))
    (hs : ScheduleWellFormed E rho) (reader : V) (r s : Slot) (B : Block)
    (hslow : slowEligible p (GridCO.gateInput p.engine rho r reader) r B = true)
    (hsr : s < r) (hwindow : r + 1 ≤ s + p.k) :
    ∃ C, confirmation p (GridCO.gateInput p.engine rho s reader) s = some C ∧
      Block.Preceq B C := by
  obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp hslow
  have hlen : p.k ≤ r + 1 := of_decide_eq_true hlen
  have hm : r - s - 1 ∈ List.range (p.k - 1) := by simp; simp only [Slot] at *; omega
  have hp := List.all_eq_true.mp hall (r - s - 1) hm
  have he : r - (r - s - 1 + 1) = s := by simp only [Slot] at *; omega
  rw [he] at hp
  cases hc : GridCO.savedGenuine (GridCO.gateInput p.engine rho r reader) s with
  | none => simp [hc] at hp
  | some result =>
    cases result with
    | none => simp [hc] at hp
    | some C =>
      refine ⟨C, ?_, by simpa [hc] using! hp⟩
      exact (GridCO.savedGenuine_input_origin p.engine E rho hs _ reader s (some C) hc).2.symm

/-- Complete earlier local results fill the executable slow test. Empty
or absent labels cannot be replaced by a result at another label. -/
theorem slowEligible_of_input_covers {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sa p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (reader : V) (hr : reader ∈ rho.honest) (r : Slot) (B : Block)
    (hlen : p.k ≤ r + 1) (hh : gateTime p r ≤ rho.horizon)
    (hresults : ∀ s, s < r → r + 1 ≤ s + p.k → ∃ C,
      confirmation p (GridCO.gateInput p.engine rho s reader) s = some C ∧ Block.Preceq B C) :
    slowEligible p (GridCO.gateInput p.engine rho r reader) r B = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hlen, List.all_eq_true.mpr ?_⟩
  intro j hj
  have hj : j < p.k - 1 := List.mem_range.mp hj
  have hsr : r - (j + 1) < r := by have := p.kLarge; simp only [Slot] at *; omega
  have hwindow : r + 1 ≤ r - (j + 1) + p.k := by simp only [Slot] at *; omega
  obtain ⟨C, hc, hBC⟩ := hresults _ hsr hwindow
  have htime : gateTime p (r - (j + 1)) < gateTime p r := by
    apply lt_of_not_ge
    intro h
    exact (not_le.mpr hsr) ((GridCO.gateTime_le_iff p.engine _ _).mp h)
  have hsaved := GridCO.time_input_savedGenuine p.engine rfl E rho hs hΔ (gateTime p r)
    reader hr (r - (j + 1)) htime (htime.le.trans hh)
  change GridCO.savedGenuine (GridCO.gateInput p.engine rho r reader) _ = _ at hsaved
  change GridCO.confirmation p.engine _ _ = some C at hc
  rw [hsaved, hc]
  exact hBC

/-- Fully synchronous slow history excludes every conflicting live row
at its final release. An older row expires at or before that HEAD. -/
theorem slow_window_rows_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sa p) E rho) (r : Slot) (source : V) (hsource : source ∈ rho.honest)
    (B : Block)
    (hslow : slowEligible p (GridCO.gateInput p.engine rho r source) r B = true)
    (hseq : ∀ s, s < r → r + 1 ≤ s + p.k → GridCO.SynchronousLabel p.engine E rho s) :
    GridCO.ReleasedRowsCompatible p.engine rho r B := by
  intro reader hr K g d hm
  have hsurvive := GridCO.nextHeadState_row_survives_release p.engine rho r reader K g d hm
  have hold := (List.mem_filter.mp hsurvive.1).1
  obtain ⟨s, C, ht, hc, hKC, _, hd⟩ := GridCO.time_input_row_genuine_admitted_origin
    p.engine E rho hx.toScheduleWellFormed (releaseTime p r) reader K g d hold
  have hsr : s < r := by
    by_contra hn
    have hle := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
    dsimp [GridCO.gateTime, releaseTime, GridCO.releaseTime] at ht hle
    linarith [p.engine.deltaPos]
  by_cases hw : r + 1 ≤ s + p.k
  · obtain ⟨D, hD, hBD⟩ := slowEligible_input_covers p E rho hx.toScheduleWellFormed
      source r s B hslow hsr hw
    have hcomp := GridCO.sameLabel_from_engine p.engine E rho hΔ s (hseq s hsr hw)
      reader hr source hsource C D hc hD
    exact GridCO.compatible_prefixes K C B D hKC hBD hcomp
  · have hsold : (s : Time) + p.k ≤ r := by
      exact_mod_cast (by simp only [Slot] at *; omega : s + p.k ≤ r)
    have hlive := hsurvive.2
    rw [hd] at hlive
    dsimp [GridCO.gateTime, GridCO.lifetime, GridCO.releaseTime, GridCO.proposalTime,
      Params.engine] at hlive
    nlinarith [p.deltaPos]

/-- A qualifying slow source transfers its prefix and retains that support
through every later synchronous label, even after its own lease is removed. -/
theorem slow_source_permanent_support {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (GridCO.gateInput p.engine rho r source) r = some C)
    (hp : Block.Preceq B C)
    (hslow : slowEligible p (GridCO.gateInput p.engine rho r source) r B = true)
    (hwindow : ∀ s, s < r → r + 1 ≤ s + p.k → GridCO.SynchronousLabel p.engine E rho s)
    (hsync : GridCO.SynchronousLabel p.engine E rho r)
    (hseq : ∀ t, r ≤ t → gateTime p t ≤ rho.horizon → GridCO.SynchronousLabel p.engine E rho t) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      GridCO.ReleasedRowsCompatible p.engine rho t B ∧ GridCO.HeadCovers p.engine rho t B := by
  have hrows := slow_window_rows_compatible p E rho hΔ hsync.1 r source hs B hslow hwindow
  have hheads : GridCO.HeadCovers p.engine rho r B := by
    apply GridCO.transfer_of_stronger_rows_from_engine p.engine E rho hΔ r hsync
      source hs B C hc hp
    intro reader hr K g d hm _
    exact hrows reader hr K g d hm
  intro t hrt hh
  have hperm := GridCO.permanent_support_of_release p.engine E rho hΔ r hsync hseq
    source hs B C hc hp hrows hheads t hrt hh
  exact ⟨hperm.1, hperm.2.1⟩

end AvailableChain.SA
end

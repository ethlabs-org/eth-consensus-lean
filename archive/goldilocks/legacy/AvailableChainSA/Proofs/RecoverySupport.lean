module
public import AvailableChainSA.Proofs.SlowWindow
public import AvailableChainGridCO.Proofs.RecoveryRepair

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic
local instance saRecoverySupportLeasePolicy : GridCO.LeasePolicy := GridCO.slowLeasePolicy

/-- A fast source releases every conflicting row at equality and then
retains support from its source through the synchronous suffix. -/
theorem fast_source_permanent_support {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (GridCO.gateInput p.engine rho r source) r = some C)
    (hp : Block.Preceq B C)
    (hcount : releaseThreshold p ≤ prefixSupport p (GridCO.gateInput p.engine rho r source) r B)
    (hsync : GridCO.SynchronousLabel p.engine E rho r)
    (hseq : ∀ t, r ≤ t → gateTime p t ≤ rho.horizon → GridCO.SynchronousLabel p.engine E rho t) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      GridCO.ReleasedRowsCompatible p.engine rho t B ∧ GridCO.HeadCovers p.engine rho t B := by
  have hrows : GridCO.ReleasedRowsCompatible p.engine rho r B := by
    intro reader hr K g d hm
    have hold := (List.mem_filter.mp
      (GridCO.nextHeadState_row_survives_release p.engine rho r reader K g d hm).1).1
    obtain ⟨s, D, _, _, _, ha, _⟩ := GridCO.time_input_row_genuine_admitted_origin
      p.engine E rho hsync.1.toScheduleWellFormed (releaseTime p r) reader K g d hold
    have hg : g = releaseThreshold p := (admissionLevels_iff p _ s K g).mp ha |>.1
    cases hcomp : Block.compatible K B with
    | true => exact hcomp
    | false =>
      have hlt := GridCO.nextHeadState_conflict_stronger p.engine E rho hΔ r hsync
        source reader hs hr B C K g d hc hp hcomp hm
      rw [hg] at hlt
      exact (not_lt.mpr hcount hlt).elim
  have hheads : GridCO.HeadCovers p.engine rho r B := by
    apply GridCO.transfer_of_stronger_rows_from_engine p.engine E rho hΔ r hsync
      source hs B C hc hp
    intro reader hr K g d hm _
    exact hrows reader hr K g d hm
  intro t hrt hh
  have hperm := GridCO.permanent_support_of_release p.engine E rho hΔ r hsync hseq
    source hs B C hc hp hrows hheads t hrt hh
  exact ⟨hperm.1, hperm.2.1⟩

/-- By this HEAD every source with a non-synchronous slow label has expired. -/
def recoveryBoundary (p : Params) (b : Slot) : Slot := b + (2 * p.k - 1)

theorem recoveryBoundary_time (p : Params) (b : Slot) :
    proposalTime p (recoveryBoundary p b) = proposalTime p b + 2 * lifetime p - 2 * p.Δ := by
  have hk : 1 ≤ 2 * p.k := by have := p.kLarge; omega
  simp only [proposalTime, recoveryBoundary, GridCO.proposalTime, lifetime,
    GridCO.lifetime, Params.engine, Nat.cast_add, Nat.cast_sub hk, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  ring

theorem live_source_after_window (p : Params) (b s : Slot)
    (hd : voteTime p (recoveryBoundary p b) < gateTime p s + lifetime p) :
    b + p.k - 1 ≤ s := by
  have hk : 2 ≤ p.k := p.kLarge
  by_contra hn
  have hsk : (s : Time) + 2 ≤ (b : Time) + p.k := by
    have h : s + 2 ≤ b + p.k := by simp only [Slot] at *; omega
    exact_mod_cast h
  have he : proposalTime p (recoveryBoundary p b) =
      proposalTime p b + 2 * lifetime p - 2 * p.Δ := recoveryBoundary_time p b
  change proposalTime p (recoveryBoundary p b) + p.Δ < gateTime p s + lifetime p at hd
  rw [he] at hd
  dsimp [proposalTime, gateTime, lifetime, GridCO.proposalTime, GridCO.gateTime,
    GridCO.lifetime, Params.engine] at hd
  nlinarith [p.deltaPos]

/-- All sources that can outlive the two-lease boundary have permanent
support. A full synchronous slow window, not an accumulated count, proves this. -/
theorem admitted_sources_after_two_leases {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (b : Slot)
    (hseq : ∀ t, b ≤ t → gateTime p t ≤ rho.horizon → GridCO.SynchronousLabel p.engine E rho t) :
    GridCO.AdmittedSourcesSupported p.engine rho (recoveryBoundary p b) := by
  intro s hh source hs B C g hd hc hp ha
  have hwindow := live_source_after_window p b s hd
  have hbs : b ≤ s := by have := p.kLarge; simp only [Slot] at *; omega
  have hsync := hseq s hbs hh
  have hseq' : ∀ t, s ≤ t → gateTime p t ≤ rho.horizon →
      GridCO.SynchronousLabel p.engine E rho t := fun t hst hhor => hseq t (hbs.trans hst) hhor
  rcases (admissionLevels_iff p _ s B g).mp ha |>.2 with hfast | hslow
  · exact fast_source_permanent_support p E rho hΔ s source hs B C hc hp hfast hsync hseq'
  · apply slow_source_permanent_support p E rho hΔ s source hs B C hc hp hslow _ hsync hseq'
    intro t hts htwindow
    have hbt : b ≤ t := by simp only [Slot] at *; omega
    exact hseq t hbt (((GridCO.gateTime_le_iff p.engine t s).mpr hts.le).trans hh)

/-- Every live row beyond the boundary has support in the preceding
honest batch, as required by the shared repaired-suffix proof. -/
theorem rows_supported_of_sources {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sa p))
    (hx : ExecutionValid (sa p) E rho) (boundary : Slot)
    (hsources : GridCO.AdmittedSourcesSupported p.engine rho boundary) :
    GridCO.RowsSupportedOutside p.engine rho boundary ∅ := by
  intro r hbr hh reader hr B g d hm _
  have hsurvive := GridCO.nextHeadState_row_survives_release p.engine rho r reader B g d hm
  have hold := (List.mem_filter.mp hsurvive.1).1
  obtain ⟨s, C, ht, hc, hp, ha, hd⟩ := GridCO.time_input_row_genuine_admitted_origin
    p.engine E rho hx.toScheduleWellFormed (releaseTime p r) reader B g d hold
  have hsr : s < r := by
    by_contra hn
    have hle := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
    dsimp [GridCO.gateTime, releaseTime, GridCO.releaseTime] at ht hle
    linarith [p.engine.deltaPos]
  have hbound : voteTime p boundary < gateTime p s + lifetime p := by
    have hle := (GridCO.gateTime_le_iff p.engine boundary r).mpr hbr
    have hlive := hsurvive.2
    rw [hd] at hlive
    dsimp [voteTime, gateTime, lifetime, GridCO.voteTime,
      GridCO.gateTime, GridCO.releaseTime] at *
    linarith [p.engine.deltaPos]
  exact (hsources s (((GridCO.gateTime_le_iff p.engine s r).mpr hsr.le).trans hh)
    reader hr B C g hbound hc hp ha (r - 1) (Nat.le_sub_one_of_lt hsr)
    (((GridCO.gateTime_le_iff p.engine (r - 1) r).mpr (Nat.sub_le r 1)).trans hh)).2

end AvailableChain.SA
end

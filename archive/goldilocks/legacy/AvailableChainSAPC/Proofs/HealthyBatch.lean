module
public import AvailableChainSAPC.Proofs.Preservation
public import AvailableChainSA.Proofs.SlowWindow

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The last healthy HEAD batch is present in the pending raw gate.
Only its early cutoff must precede the outage boundary. -/
theorem healthy_head_in_earlyVotes {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (cut : Time)
    (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (u v : V) (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    (awake : E.awake u (voteTime p r) = true) :
    (⟨.seat r ((rho.seatOf r).symm u), .head (headData p rho r u).target⟩ : GridCO.Wire p.n) ∈
      GridCO.earlyVotes p.engine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r := by
  have deadline : voteTime p r + E.Δ = earlyTime p r := by
    rw [hΔ]
    change 4 * p.Δ * (r : Time) + p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 2 * p.Δ
    ring
  have voteLe : voteTime p r ≤ earlyTime p r := by
    rw [← deadline, hΔ]
    linarith [p.deltaPos]
  have emitted := honest_head_emitted p E rho hx.toScheduleWellFormed hΔ r
    ((rho.seatOf r).symm u) (by simpa using hu) (by simpa using awake) (voteLe.trans hh)
  simp only [Equiv.apply_symm_apply] at emitted
  apply head_in_earlyVotes_of_delivery p E rho hx hΔ r u v hu hv
  · rw [← deadline]
    exact healthy_relayBy p E rho cut _ relay (by rwa [deadline])
  · obtain ⟨t, hlo, hhi, j, handle⟩ := net.broadcast u hu _ _ emitted v hv
      (by rwa [deadline]) rfl
    exact ⟨t, hlo, by rwa [deadline] at hhi, j, handle⟩

/-- The complete healthy batch gives a support bound even when the gate's
late receipts and PC authority change during the outage. -/
theorem healthy_prefixSupport_ge_awake {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (cut : Time)
    (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (B : Block) (cover : ∀ u ∈ rho.honest, Block.Preceq B (headData p rho r u).target)
    (v : V) (hv : v ∈ rho.honest) :
    (awakeAt E rho.honest (voteTime p r)).card ≤ GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B :=
  prefixSupport_ge_honest_batch p E rho hx r B cover v
    (fun u hu ha => healthy_head_in_earlyVotes p E rho hx hΔ cut net relay r hearly hh
      u v hu hv ha)

/-- A healthy covering batch gives the pending raw result, without any
relay, count, or cap condition at its later gate time. -/
theorem healthy_preserve_from_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (cut : Time)
    (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (majority : AwakeMajority E rho (voteTime p r)) (B : Block)
    (cover : ∀ u ∈ rho.honest, Block.Preceq B (headData p rho r u).target)
    (v : V) (hv : v ∈ rho.honest) : ∃ C,
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C ∧
      Block.Preceq B C :=
  preserve_of_early_heads p E rho hx r majority B cover v
    (fun u hu ha => healthy_head_in_earlyVotes p E rho hx hΔ cut net relay r hearly hh
      u v hu hv ha)

/-- The fast-outage count gives actual SA admission at the pending gate.
It does not require the PC to permit the whole raw descendant. -/
theorem healthy_fast_admission {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (cut : Time)
    (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (high : SA.releaseThreshold p ≤ (awakeAt E rho.honest (voteTime p r)).card)
    (B : Block) (cover : ∀ u ∈ rho.honest, Block.Preceq B (headData p rho r u).target)
    (v : V) (hv : v ∈ rho.honest) :
    SA.releaseThreshold p ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B := by
  apply (SA.admissionLevels_iff p _ r B (SA.releaseThreshold p)).mpr
  exact ⟨rfl, Or.inl (high.trans
    (healthy_prefixSupport_ge_awake p E rho hx hΔ cut net relay r hearly hh B cover v hv))⟩

end AvailableChain.SAPC
end

module
public import AvailableChainSAPC.Proofs.GenuineTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem freeze_le_gate (p : Params) (r : Slot) : freezeTime p r ≤ gateTime p r := by
  change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
  linarith [p.deltaPos]

/-- Contract synchrony supplies both directions of the genuine-support
comparison. Its GST boundary is the early cutoff, not proposal time. -/
theorem synchronous_transfer_relays {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : gateTime p r ≤ rho.horizon) :
    RelayBy p rho (earlyTime p r) (freezeTime p r) ∧
      RelayBy p rho (voteTime p (r + 1)) (gateTime p r) := by
  have he : max (earlyTime p r) E.t_GST + E.Δ = freezeTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 2 * p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 3 * p.Δ
    ring
  have hv : E.t_GST ≤ voteTime p (r + 1) := by
    apply hsync.trans
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hg : max (voteTime p (r + 1)) E.t_GST + E.Δ = gateTime p r := by
    rw [max_eq_left hv, hΔ]
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ + p.Δ =
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    ring
  exact ⟨he ▸ synchronous_relayBy p E rho _ hrelay
      (he.symm ▸ (freeze_le_gate p r).trans hh),
    hg ▸ synchronous_relayBy p E rho _ hrelay (hg.symm ▸ hh)⟩

/-- A healthy prefix through the gate supplies the same two relay
interfaces. No delivery after the prefix is used. -/
theorem healthy_transfer_relays {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (cut : Time) (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hcut : gateTime p r ≤ cut) :
    RelayBy p rho (earlyTime p r) (freezeTime p r) ∧
      RelayBy p rho (voteTime p (r + 1)) (gateTime p r) := by
  have he : earlyTime p r + E.Δ = freezeTime p r := by
    rw [hΔ]
    change 4 * p.Δ * (r : Time) + 2 * p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 3 * p.Δ
    ring
  have hg : voteTime p (r + 1) + E.Δ = gateTime p r := by
    rw [hΔ]
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ + p.Δ =
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    ring
  exact ⟨he ▸ healthy_relayBy p E rho cut _ hrelay
      (he.symm ▸ (freeze_le_gate p r).trans hcut),
    hg ▸ healthy_relayBy p E rho cut _ hrelay (hg.symm ▸ hcut)⟩

theorem synchronous_sameLabel {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b c : Block)
    (hb : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) w).base r = some c) :
    Block.Compatible b c := by
  obtain ⟨hf, hbck⟩ := synchronous_transfer_relays p E rho hΔ hrelay r hsync hh
  exact sameLabel_from_engine p E rho hx hΔ r v w hv hw
    ((freeze_le_gate p r).trans hh) hf hbck b c hb hc

theorem synchronous_genuine_compatiblePC_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    (hcert : ∀ pc, selectedPC p (headState p rho (r + 1) w) (r + 1) = some pc →
      Block.Compatible pc.target b)
    : Block.Preceq b (headData p rho (r + 1) w).target := by
  obtain ⟨hf, hbck⟩ := synchronous_transfer_relays p E rho hΔ hrelay r hsync hh
  exact genuine_compatiblePC_head_covers p E rho hx hΔ r v w hv hw
    ((freeze_le_gate p r).trans hh) hf hbck b c hc hp hr hcert

/-- A reader's own raw result transfers with only the forward deadline
inside the run. The raw result is evaluated on the actual strict input;
no future gate tick or run extension is assumed. -/
theorem synchronous_local_genuine_activePC_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : freezeTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (b c : Block)
    (hc : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r = some c)
    (hp : Block.Preceq b c)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) reader).base) b)
    (hcert : capBroken p (headState p rho (r + 1) reader) = false →
      ∀ pc, selectedPC p (headState p rho (r + 1) reader) (r + 1) = some pc →
      Block.Compatible pc.target b) :
    Block.Preceq b (headData p rho (r + 1) reader).target := by
  have he : max (earlyTime p r) E.t_GST + E.Δ = freezeTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 2 * p.Δ + p.Δ =
      4 * p.Δ * (r : Time) + 3 * p.Δ
    ring
  exact genuine_activePC_head_covers_of_back_receipts p E rho hx hΔ r reader reader
    hr hr hh (he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hh))
    (local_back_receipts p E rho hx.toScheduleWellFormed r reader) b c hc hp hroot hcert

/-- A reader's own raw result transfers with only the forward deadline
inside the run. The raw result is evaluated on the actual strict input;
no future gate tick or run extension is assumed. -/
theorem synchronous_local_genuine_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : freezeTime p r ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (b c : Block)
    (hc : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r = some c)
    (hp : Block.Preceq b c)
    (hroot : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) reader).base) b)
    (hcert : ∀ pc, selectedPC p (headState p rho (r + 1) reader) (r + 1) = some pc →
      Block.Compatible pc.target b) :
    Block.Preceq b (headData p rho (r + 1) reader).target :=
  synchronous_local_genuine_activePC_head_covers p E rho hx hΔ hrelay r hsync hh reader hr
    b c hc hp hroot (fun _ => hcert)

theorem synchronous_genuine_highSupport_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ earlyTime p r) (hh : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hsupport : pcFaultCap p < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r b)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    : Block.Preceq b (headData p rho (r + 1) w).target := by
  obtain ⟨hf, hbck⟩ := synchronous_transfer_relays p E rho hΔ hrelay r hsync hh
  exact genuine_highSupport_head_covers p E rho hx hΔ r v w hv hw
    ((freeze_le_gate p r).trans hh) hf hbck b c hc hp hsupport hr

theorem healthy_sameLabel {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ)
    (cut : Time) (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hcut : gateTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b c : Block)
    (hb : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) w).base r = some c) :
    Block.Compatible b c := by
  obtain ⟨hf, hbck⟩ := healthy_transfer_relays p E rho hΔ cut hrelay r hcut
  exact sameLabel_from_engine p E rho hx hΔ r v w hv hw
    ((freeze_le_gate p r).trans hh) hf hbck b c hb hc

theorem healthy_genuine_compatiblePC_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ)
    (cut : Time) (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hcut : gateTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    (hcert : ∀ pc, selectedPC p (headState p rho (r + 1) w) (r + 1) = some pc →
      Block.Compatible pc.target b)
    : Block.Preceq b (headData p rho (r + 1) w).target := by
  obtain ⟨hf, hbck⟩ := healthy_transfer_relays p E rho hΔ cut hrelay r hcut
  exact genuine_compatiblePC_head_covers p E rho hx hΔ r v w hv hw
    ((freeze_le_gate p r).trans hh) hf hbck b c hc hp hr hcert

theorem healthy_genuine_highSupport_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ)
    (cut : Time) (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hcut : gateTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hsupport : pcFaultCap p < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r b)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    : Block.Preceq b (headData p rho (r + 1) w).target := by
  obtain ⟨hf, hbck⟩ := healthy_transfer_relays p E rho hΔ cut hrelay r hcut
  exact genuine_highSupport_head_covers p E rho hx hΔ r v w hv hw
    ((freeze_le_gate p r).trans hh) hf hbck b c hc hp hsupport hr

end AvailableChain.SAPC
end

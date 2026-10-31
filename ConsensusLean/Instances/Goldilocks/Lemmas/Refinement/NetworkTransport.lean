module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding

public section

/-! # Open network transport suppliers

These are goals for the concrete publisher/simulation adapter, not extra premises of Accepted.
The trace parameters remain independent here. `Setup.params` now gives protocol delay
Δp = Δe + 1; this endpoint slack does not instantiate any supplier below. For FG row service,
ΔF := sp.Δ is the protocol bound, not the engine delay.
All three suppliers include message, block, acceptance-relay and attestation service. Receipt
alone proves none of the acceptance-relay fields. No supplier is claimed implemented here.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (family S)) E)
  {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (ΔF : Time)

/-- OPEN supplier: PSync supplies GST at the node level. Paper route: actual same-time
publication gives network service by max(send, GST, latest wake)+Δe; authenticated provenance
gives the lower bound, recursive processing gives a call, and +1 gives the strict endpoint.
Acceptance relay additionally requires the parent-first induction, NoColl and chain-state
agreement. Vote/attestation admissions need their own source/time provenance. The adapter
must identify H, node keys, flattened cuts, horizon and awake intervals with the engine run. -/
def PSyncTransport : Prop :=
  ∀ g, rho.log.PSync rho.point g → tr.GSTRun H ΔF g

/-- OPEN supplier: SyncUntil supplies only recipient-deadline-cut SyncBefore, not SyncRun
with a send-time cutoff. Paper route: a node deadline ≤ b puts its engine service endpoint
strictly below b under +1. Wakes are included in that deadline. All four service fields need
the same publication/processing joins as PSyncTransport. No post-outage service is inferred. -/
def SyncUntilTransport : Prop :=
  ∀ b, rho.log.SyncUntil rho.point b → tr.SyncBefore H ΔF b

/-- OPEN supplier: global synchrony gives SyncRun on nonnegative send windows. In particular
this does not derive a send-window SyncRun from SyncUntil: a late wake can put its deadline
after the latter's cutoff. The concrete adapter must discharge the same four service leaves. -/
def SyncRunTransport : Prop :=
  rho.log.PSync rho.point 0 → ∀ a b, 0 ≤ a → tr.SyncRun H ΔF a b

/-- OPEN concrete supplier: actual signed/admitted FG rows receive the protocol delay,
not an independent setup coefficient. This services an existing attestation; it never
produces a row. Source emission/admission must supply an actual released canonical object;
engine service supplies holdings by Δe, provenance and recursive processing supply the call
after its source time, and the installed Δp = Δe + 1 gives the strict endpoint. The adapter
must still identify keys, cuts, awake intervals and horizon. This is not an extra Healthy
premise; source availability and usable-row obligations remain separate. -/
def PSyncFGRowTransport : Prop :=
  ∀ g, rho.log.PSync rho.point g →
    ∀ x ∈ H, ∀ i a, tr.SendOrAdmitAttAt x i a →
      ∀ y ∈ H, ∀ j, tr.IsCall y j →
        tr.deadline y j (max (tr.time i) g) sp.Δ ≤ tr.time j →
        tr.AttDeliveredBy y j (tr.time i) (max (tr.time i) g) sp.Δ a

/-- Pure endpoint arithmetic, independent of the unimplemented adapter. Service at the engine
endpoint is strictly before the protocol endpoint, including equality at the engine bound.
This buys no forwarding delay and is paid once, not once per ancestor. -/
theorem delivery_endpoint_slack (base received Δe Δp : Time)
    (hdelay : Δp = Δe + 1) (hreceived : received ≤ base + Δe) :
    received < base + Δp := by
  simp only [Time] at *
  omega

/-- A qualifying protocol deadline places the engine endpoint strictly before the outage
cutoff. The cutoff itself is allowed for the protocol deadline. -/
theorem delivery_endpoint_before_cutoff (base cutoff Δe Δp : Time)
    (hdelay : Δp = Δe + 1) (hcut : base + Δp ≤ cutoff) :
    base + Δe < cutoff := by
  simp only [Time] at *
  omega

end Consensus.Goldilocks.Refinement

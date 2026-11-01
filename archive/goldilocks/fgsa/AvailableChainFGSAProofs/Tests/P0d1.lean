module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d1
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def d1G0Core (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private def d1G0Reads (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (d1G0Core p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem d1G0ObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (d1G0Core p c) (d1G0Reads p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def d1G0Timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def d1G0Kind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private theorem d1G0WitnessProjection {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (d1G0Core p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem d1G0ReceiptProjection {i m : Nat} {deadline : Time}
    (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (d1G0Core p c) E rho (d1G0Reads p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, d1G0WitnessProjection p c E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, d1G0WitnessProjection p c E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff,
      d1G0WitnessProjection p c E rho hrC, d1G0WitnessProjection p c E rho hrW⟩

private theorem d1G0FrameCorrespondence (nd : Node p) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) :
    SettledPhaseFrame p nd.st m J contested ↔
      FGCompose.SettledPhaseFrame (d1G0Core p c) (d1G0Reads p c) nd m J contested := by
  cases J <;> rfl

private theorem d1G0FiveClauses : RPhase p c E rho ↔
    FGCompose.RPhase (d1G0Core p c) E rho (d1G0Reads p c) (d1G0Timing p)
      (recoveryStart p E) (fun nd s => FGSA.voterBlocks p nd.st s) := by
  constructor
  · rintro ⟨ha, hb, hc, hd, he⟩
    refine ⟨ha, hb, ?_, ?_, he⟩
    · intro i ev v m kind
      cases kind with
      | gap => exact hc i ev v m .gap
      | topJ => exact hc i ev v m .topJ
      | contest => exact hc i ev v m .contest
    · intro u v m J contested
      cases J with
      | none => exact hd u v m none contested
      | some B => exact hd u v m (some B) contested
  · rintro ⟨ha, hb, hc, hd, he⟩
    refine ⟨ha, hb, ?_, ?_, he⟩
    · intro i ev v m kind
      cases kind with
      | gap => exact hc i ev v m .gap
      | topJ => exact hc i ev v m .topJ
      | contest => exact hc i ev v m .contest
    · intro u v m J contested
      cases J with
      | none => exact hd u v m none contested
      | some B => exact hd u v m (some B) contested


private theorem d1G0ActualReceipts [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (i : Nat) (ev : V2.Event V (Obj p)) (m : Nat)
    (hi : rho.events[i]? = some ev) (hr : recoveryStart p E ≤ ev.time) (hm : 1 ≤ m)
    (hf : frontierAtIdx p c E rho (i + 1) = m) (hh : ev.time + p.Δ ≤ rho.horizon) :
    FGCompose.PhaseWitnessReceiptScope (d1G0Core p c) E rho (d1G0Reads p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) (i + 1) m
      (ev.time + p.Δ) :=
  d1G0ReceiptProjection p c E rho
    (healing_phase_witness_receipts_recovery E rho hrec i ev m hi hr hm hf hh)

private theorem d1G0ClosedAssembly [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) :
    FGCompose.RPhase (d1G0Core p c) E rho (d1G0Reads p c) (d1G0Timing p)
      (recoveryStart p E) (fun nd s => FGSA.voterBlocks p nd.st s) :=
  (d1G0FiveClauses p c E rho).mp (healing_rPhase_recovery E rho hrec mono crossing)

-- The closed recovery assembly supplies HEAD inclusion for the native frozen read.
private theorem d1G0NativeHeadProjection (nd : Node p) (s : Slot) :
    (fun nd s => FGSA.voterBlocks p nd.st s) nd s = FGSA.voterBlocks p nd.st s := rfl

#print axioms d1G0NativeHeadProjection
#print axioms AvailableChain.FGCompose.healing_phase_head_inclusion
#print axioms AvailableChain.FGSA.Run.healing_evidence_spread_recovery

#print axioms d1G0ObsLaws
#print axioms d1G0WitnessProjection
#print axioms d1G0ReceiptProjection
#print axioms d1G0FrameCorrespondence
#print axioms d1G0FiveClauses
#print axioms d1G0ActualReceipts
#print axioms d1G0ClosedAssembly
#print axioms AvailableChain.FGSA.Run.healing_rPhase_recovery

end AvailableChain.FGSA.Run.Tests.P0d1
end

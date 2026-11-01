module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTail

public section

/-! Blueprint 21 HG.4:1698--1720; frontier plan §3.3.
The row tail uses HG.1 across same-frontier events. A rise supplies an
earlier row through RCap. This module does not assert the terminal rise tail.
INLINE writes: fgsa_leaseOrigins_lastWrite (Foundations/Leases).
INLINE rowCoverage: rowPermission_covered (Foundations/RowPermission). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cTailCore (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem p0d5cTailCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d5cTailCore p c) := by
  have h : p0d5cTailCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm
  rw [h]
  exact fgsaCoreLaws p c

private def p0d5cTailTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cTailTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cTailTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5cTailObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5cTailCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5cTailObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5cTailCore p c) (p0d5cTailObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5cTailSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d5cTailKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private abbrev p0d5cTailPair (a : RowWire p.n) : NamedHeightPair := a.payload.height_pair

private theorem p0d5cTailPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5cTailCore p c) E rho (p0d5cTailObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

omit [DecidableEq V] in
private theorem p0d5cTailSeed_iff (E : Generic.Env V) {u : Time} {q : Slot} :
    FGCompose.FrontierSeedQualification (p0d5cTailTiming p) p.k E.t_GST u q ↔
      FrontierSeedQualification p E u q :=
  (frontierSeedQualification_iff p E u q).symm

private theorem p0d5cTailStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (h : FrontierSearchStart p c E rho i ev m kind) :
    FGCompose.FrontierSearchStart (p0d5cTailCore p c) E rho (p0d5cTailObs p c) (p0d5cTailTiming p)
      (recoveryStart p E) i ev m (p0d5cTailKind kind) := by
  have h' := (frontierSearchStart_iff p c E rho i ev m kind).mp h
  cases kind <;> exact h'


-- Continuing local service of the frozen exact-service seed (TFrontier).
private theorem p0d5cTailLocal (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (frontier : TFrontier p c E rho) {u : Time} {m q : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (he : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hseed : FrontierSeedQualification p E u q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hp : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested) :
    ∀ v, SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cTailCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cTailCore p c) (p0d5cTailSafety p c) E rho (p0d5cTailObs
        p c)
        (p0d5cTailTiming p) (fgsaInterface p c) p0d5cTailPair q Q Qfg m v := by
  intro v hg hv hcap
  obtain ⟨htransfer, hrepair, hopen⟩ := frontier u v m J contested q Q Qfg hready hQ he hh
    hexact ((frontierSeedQualification_iff p E u q).mp hseed) hu hp hg hv hcap
  refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
  · intro s B hqs hgate hprop
    exact (hrepair s B hqs hgate hprop).1
  · intro r hqr hrt
    obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
    refine ⟨?_, hent, hheight, htime⟩
    intro x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ', hr, ha, hn⟩ := hcov x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ', hr, ha, hn⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.4 and IF.3(a); frontier plan §3.3/§4.
DC: SAME first honest height-m row within P-4Δ of the saved seed.
The closed horizon includes equality. No phase through this endpoint is assumed. -/
theorem healing_frontierTail_row [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {m : Nat} {t : Time} (hserved : StrongServed p c E rho m t)
    (hhor : t + (P p - 4 * p.Δ) ≤ rho.horizon) :
    FirstHeightRowBy p c E rho m (t + (P p - 4 * p.Δ)) := by
  obtain ⟨u, J, contested, q, Q, Qfg, hgst, hQ, hErase, hHeight, hService,
    hseed, hu, hphase, hqt, _, _⟩ := (strongServed_iff p c E rho m t).mp hserved
  have frontier := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage
  have h := FGCompose.healing_frontierTail_row (p0d5cTailCore p c) (p0d5cTailSafety p c) E rho
      (p0d5cTailObs p c)
    (p0d5cTailTiming p) (fgsaInterface p c) p0d5cTailPair (fun nd B => chainWireRows nd.st B) p.E
    (fgCertificateLaws p) (fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (p0d5cTailTimingLaws p) hrec.base.valid.toScheduleWellFormed ⟨mono⟩ cap
    ((p0d5cTailPhase_iff E rho).mpr hphase) hQ hqt
    (p0d5cTailLocal E rho frontier hgst hQ hErase hHeight hService hseed hu hphase) hhor
  exact (firstHeightRowBy_iff p c E rho m _).mpr h

end AvailableChain.FGSA.Run
end

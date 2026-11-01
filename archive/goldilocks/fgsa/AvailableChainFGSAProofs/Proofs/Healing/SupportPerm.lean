module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow

public section

/-! H-SUPPORT S4 assembly (plan §6–§7; ruling B31). Both PhaseBody arms give the three
Transfers clauses. The S3 output clause carries the B31 guard d_s + 4Δ ≤ v, so the
result is scoped to a late source in one phase. The universal wrapper keeps an explicit
phase-service producer input. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Exact service inputs for the two active body arms, restricted to their phase. -/
structure SupportPermanenceServices (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (u v : Time) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) : Prop where
  fast : ∀ s x nd B, HealingWindow p E 1 s →
    u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
    x ∈ rho.honest → postClock E rho x (SA.gateTime p.toParams s) = some nd →
    B ∈ (fastWriteAt nd.st s).getD [] → FastSupportScope E rho s v x
  slow : ∀ s x st C B j, HealingWindow p E 1 s →
    u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
    x ∈ rho.honest → E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) →
    gateIn p c E rho x s = some st →
    gateResult p c E rho x s = some (some C) →
    Block.Preceq B C →
    GridCO.slowEligible p.toParams.engine (actView st) s B = true →
    IsGateTick p c rho j x s → SlowSupportScope E rho s v x
  proposals : ∀ s B, HealingWindow p E 1 s →
    u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
    PhaseBody p c E rho s B →
    ∀ r, s + 1 ≤ r → SA.proposalTime p.toParams (r + 1) ≤ v →
    ∀ ip x, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))) →
    joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)) →
    ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:620–715 (H.4, H.4-S, H.2 S1–S3); plan H-SUPPORT §6, ruling B31.
DC: INTENTIONAL Transfers for one late source in one phase, with the S3 output
clause under the B31 guard d_s + 4Δ ≤ v. -/
theorem healing_phase_transfers [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) (hbody : PhaseBody p c E rho s B) :
    Transfers p c E rho s B v := by
  have hCut : HealingWindow p E 1 s :=
    healing_window_of_cut E (healing_ready_vote_cutoff E (hready.trans hhead))
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hProposal := hServices.proposals s B hCut hhead hgate hbody
  obtain ⟨x, hx, hfast | ⟨hgw, st, C, jx, hst, hres, _, hBC, hel, hjx, _⟩⟩ := hbody
  · obtain ⟨nd, hnd, hB⟩ := hfast
    have hFast := hServices.fast s x nd B hCut hhead hgate hx hnd hB
    refine ⟨fun z i H hz hi hv hH => ?_, ?_, fun i z hz hguard => ?_⟩
    · exact healing_fast_heads E rho hrec mono crossing writes hgst hphase hhead hgate hx hnd
        hB hFast hCut i hi hv z hz H hH
    · exact healing_fast_proposals E rho hrec mono crossing writes hgst hphase hhead hgate hx
        hnd hB hFast hCut hProposal
    · exact healing_fast_output E rho hrec mono crossing writes hgst hphase hhead hgate hguard
        hx hnd hB hFast hCut i z hz
  · have hSlow := hServices.slow s x st C B jx hCut hhead hgate hx hgw hst hres hBC hel hjx
    refine ⟨fun z i H hz hi hv hH => ?_, ?_, fun i z hz hguard => ?_⟩
    · exact healing_slow_heads E rho hrec mono crossing writes hgst hphase hhead hgate hx hgw
        hst hres hBC hel hjx hSlow hCut i hi hv z hz H hH
    · exact healing_slow_proposals E rho hrec mono crossing writes hgst hphase hhead hgate hx
        hgw hst hres hBC hel hjx hSlow hCut hProposal
    · exact healing_slow_output E rho hrec mono crossing writes hgst hphase hhead hgate hguard
        hx hgw hst hres hBC hel hjx hSlow hCut i z hz

/-- The local permanence adapter returns Transfers after its actual phase arguments. -/
theorem healing_tPerm_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) (hbody : PhaseBody p c E rho s B) :
    Transfers p c E rho s B v :=
  healing_phase_transfers E rho hrec mono crossing writes hready hphase hServices
    hhead hgate hbody

/-- Universal permanence from sleep recovery and the exact bounded phase services.
The service factory remains OPEN/P-H1; this wrapper consumes it. -/
theorem healing_tPerm [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    (services : ∀ u v m J contested, recoveryStart p E ≤ u →
      PhaseInterval p c E rho u v m J contested →
      SupportPermanenceServices E rho u v m J contested) : TPerm p c E rho := by
  intro u v m J contested s B hready hphase hhead hgate hbody
  exact healing_tPerm_at E rho hrec mono crossing writes hready hphase
    (services u v m J contested hready hphase) hhead hgate hbody

end AvailableChain.FGSA.Run
end

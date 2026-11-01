module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetService -- shake: keep (J6)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetGate -- shake: keep (J6-2 H6 example)
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases -- shake: keep (last-write)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJointStep -- shake: keep (J6-3 step)

set_option linter.privateModule false

public section

/-! S5 J6 / J6-2 tests. The short-horizon example inhabits only the cone. The
applications below use an actual honest proposal and consume the exact
HEAD and retained-carrier conclusions. S2 uses the named service field.
The S1 carrier producer remains stopped. The S3 adapter is applied below. -/

namespace AvailableChain.FGSA.Run.Tests.HealingPostResetService
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- A1: only a HEAD horizon below the first relevant label makes this trivial.
example (w : HealingWitness)
    (hshort : rho.horizon < SA.voteTime p.toParams (w.sStar + 2)) :
    PostResetRetainedCone p c E rho w :=
  postResetRetainedCone_of_horizon_lt p c E rho w hshort

-- A1: apply the definition without asking for a walk or service field.
example (w : HealingWitness) (hcone : PostResetRetainedCone p c E rho w)
    (s : Slot) (hs : w.sStar + 2 ≤ s)
    (hHeadHorizon : SA.voteTime p.toParams s ≤ rho.horizon)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip) :
    ∃ D : FGBlock (Fin p.n), ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D := by
  rw [postResetRetainedCone_iff] at hcone
  exact hcone s hs hHeadHorizon hx hip hseat N hem

-- D1: the HEAD at sStar + 1 is inside the horizon, but no cone input is asked.
example (w : HealingWitness)
    (hAtPriorHead : rho.horizon = SA.voteTime p.toParams (w.sStar + 1)) :
    PostResetRetainedCone p c E rho w := by
  apply postResetRetainedCone_of_horizon_lt p c E rho w
  rw [hAtPriorHead]
  change 4 * p.Δ * ((w.sStar + 1 : Nat) : Int) + p.Δ <
    4 * p.Δ * ((w.sStar + 2 : Nat) : Int) + p.Δ
  push_cast
  nlinarith [p.deltaPos]

-- S2: apply the service field at the exact boundary, with all three cut bounds.
example (w : HealingWitness) (i : Nat)
    (hservice : PostResetService p c E rho w i) {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) (w.sStar + 2) Q)
    (hProposalCut : timeIdx rho (SA.proposalTime p.toParams (w.sStar + 2)) ≤ i)
    (hHeadCut : timeIdx rho (SA.voteTime p.toParams (w.sStar + 2)) ≤ i)
    (hGateCut : afterTicksIdx rho (SA.gateTime p.toParams (w.sStar + 2)) ≤ i) :
    ExactService p c E rho (w.sStar + 2) Q :=
  healing_postReset_exactService_at_cut E rho w i hservice hp le_rfl
    hProposalCut (fun _ => hHeadCut) (fun _ => hGateCut)

-- S2: a complete cut can exceed the event list's length.
example (w : HealingWitness)
    (hservice : PostResetService p c E rho w (rho.events.length + 1)) {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) (w.sStar + 2) Q) :
    ExactService p c E rho (w.sStar + 2) Q :=
  healing_postReset_exactService E rho w (rho.events.length + 1)
    (Nat.le_succ _) hservice _ Q hp le_rfl

-- Risk 6: the exact boundary has a source bound of v - 2 and uses q_(sStar).
example (w : HealingWitness) :
    w.sStar ≤ (w.sStar + 2) - 2 ∧
    SA.releaseTime p.toParams w.sStar ≤ SA.proposalTime p.toParams (w.sStar + 2) - p.Δ :=
  ⟨postReset_source_label_le_sub_two w le_rfl, postReset_release_before_proposal p w le_rfl⟩

-- H0Reset supplies synchrony at the boundary; no QStar data are needed.
example (w : HealingWitness) (hreset : H0Reset p c E rho w) :
    E.t_GST ≤ SA.proposalTime p.toParams (w.sStar + 2) - p.Δ :=
  postReset_synchronous_window p c E rho w hreset le_rfl

variable [Fintype V]

-- A3: consume the HEAD conclusion as equality of a supplied HEAD with Q.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    {v : Slot} {Q H : Block} (hp : HonestProposal E rho (fgsaInterface p c) v Q)
    (hv : w.sStar + 2 ≤ v)
    (hHeadHorizon : SA.voteTime p.toParams v ≤ rho.horizon)
    {y : V} (hy : y ∈ rho.honest) (hH : headAtLabel p c E rho y v = some H) : H = Q := by
  have hQ := healing_postReset_exactHead E rho hrec mono w hreset hcone v Q hp hv hHeadHorizon y hy
  exact Option.some.inj (hH.symm.trans hQ)

-- T: at v = sStar + 2, consume both exact HEAD and its retained carrier.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) (w.sStar + 2) Q)
    (hHeadHorizon : SA.voteTime p.toParams (w.sStar + 2) ≤ rho.horizon)
    {y : V} {ih : Nat} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (w.sStar + 2)))) :
    headAtLabel p c E rho y (w.sStar + 2) = some Q ∧
    ∃ C : FGBlock (Fin p.n), eraseFG C = Q ∧
      C ∈ domainR p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (w.sStar + 2)))
        (voterBlocks p (clock p (rho.stateBefore E ih y).st
          (SA.voteTime p.toParams (w.sStar + 2))) (w.sStar + 2)) :=
  ⟨healing_postReset_exactHead E rho hrec mono w hreset hcone _ Q hp le_rfl hHeadHorizon y hy,
    healing_postReset_headCarrier E rho hrec mono w hreset hcone hp le_rfl hHeadHorizon hy hih⟩

-- Risk 4: a closed HEAD deadline still works when the later gate is outside.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) {v : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hAtHead : rho.horizon = SA.voteTime p.toParams v) :
    rho.horizon < SA.gateTime p.toParams v ∧
      ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q := by
  refine ⟨?_, healing_postReset_exactHead E rho hrec mono w hreset hcone v Q hp hv hAtHead.ge⟩
  rw [hAtHead]
  change 4 * p.Δ * (v : Int) + p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
  linarith [p.deltaPos]

-- Risk 4: use the named gate-to-HEAD guard when the gate is in the horizon.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) {v : Slot} {Q : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (hGateHorizon : SA.gateTime p.toParams v ≤ rho.horizon) :
    ∀ y ∈ rho.honest, headAtLabel p c E rho y v = some Q :=
  healing_postReset_exactHead E rho hrec mono w hreset hcone v Q hp hv
    (postReset_head_horizon p c rho hGateHorizon)


-- S3: apply H6 at sStar. No cone or honest proposal is supplied at this label.
-- The INLINE `writes` input is discharged by its producer fgsa_leaseOrigins_lastWrite.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness)
    (hrawTransfer : PostResetRawTransfer p c E rho w (rho.events.length + 1))
    (D : Block) (hgst : recoveryStart p E ≤ SA.voteTime p.toParams w.sStar)
    (hGateHorizon : SA.gateTime p.toParams w.sStar ≤ rho.horizon) (hne : D ≠ .genesis)
    (hheads : ∀ x ∈ rho.honest, ∃ H,
      headAtLabel p c E rho x w.sStar = some H ∧ Block.Preceq D H)
    (hfloor : ∀ x st, x ∈ rho.honest → gateIn p c E rho x w.sStar = some st →
      Block.Preceq (eraseFG st.fg.F) D)
    {x : V} (hx : x ∈ rho.honest) :
    (∃ C, gateResult p c E rho x w.sStar = some (some C) ∧ Block.Preceq D C) ∧
    (∃ j, IsGateTick p c rho j x w.sStar ∧ gatePassedAt p c E rho j) ∧
    (∃ nd d, postClock E rho x (SA.gateTime p.toParams w.sStar) = some nd ∧
      D ∈ (fastWriteAt nd.st w.sStar).getD [] ∧ leaseOf nd.st D = some d ∧
      SA.gateTime p.toParams w.sStar + L p ≤ d ∧ SA.gateTime p.toParams w.sStar < d) :=
  healing_postReset_h6GateService E rho hrec mono w (rho.events.length + 1)
    (Nat.le_succ _) hrawTransfer
    (fgsa_leaseOrigins_lastWrite p c E rho hrec.base.valid.toScheduleWellFormed)
    w.sStar D le_rfl hgst hGateHorizon hne
    hheads hfloor x hx

-- J6-3 O1 partial: stored lift at the new tick of the cut, without service.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) (i : Nat)
    {x : V} {v : Slot} {Q : Block} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    ∃ D : FGBlock (Fin p.n), eraseFG D = Q ∧ D ∈ st.fg.TF :=
  healing_postReset_opening_clock_stored E rho hrec mono w hreset hcone hp hv hx ht r hr

-- J6-3 O2 partial: opening_domain at cut i + 1 covers tick i.
example (w : HealingWitness) (i : Nat)
    (hopening : PostResetOpeningDomain p c E rho w (i + 1))
    {x : V} {v : Slot} {Q : Block} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v) :
    ∀ r, v = r * p.R →
      let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
      ∃ D, eraseFG D = Q ∧ D ∈ domainR p st (treeT p st) :=
  healing_postReset_gate_opening_domain E rho w (i + 1) hopening
    (Nat.lt_succ_self i) hx ht hp hv

-- J6-3 O2 partial: opening target_floor at a cut uses exact HEAD.
example {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w) (i : Nat)
    (hopening : PostResetOpeningDomain p c E rho w (i + 1))
    {x : V} {v : Slot} {Q : Block} (hx : x ∈ rho.honest)
    (ht : IsGateTick p c rho i x v)
    (hp : HonestProposal E rho (fgsaInterface p c) v Q) (hv : w.sStar + 2 ≤ v)
    (r : Nat) (hr : v = r * p.R) (q : Fin p.n)
    (hy : rho.seatOf (.base (.head v)) q ∈ rho.honest)
    (haw : E.awake (rho.seatOf (.base (.head v)) q) (SA.voteTime p.toParams v) = true)
    (K : Block) (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head v)) q)
      (ofHead p ⟨.seat (.head v) q, K.root⟩) (SA.voteTime p.toParams v) K) :
    Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams v)).fg.F) K :=
  healing_postReset_opening_target_floor E rho hrec mono w hreset hcone (i + 1) hopening
    (Nat.lt_succ_self i) hx ht hp hv r hr q hy haw K he

section J63CutApplication
variable {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

variable (mono : RMonoAll p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉
          @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
            (actView pre) w C)

include hrec hreset hcone cap rowCovered mono writes

-- J6-3 O2: the producer gives both service conjuncts at any cut i.
example (i : Nat) (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i) :
    PostResetService p c E rho w i :=
  healing_postReset_service_step E rho hrec w hreset hcone cap rowCovered mono writes
    i hfp hraw hopening

-- JOINT-IND: the service step holds at every cut, pre-reset cuts included.
example : ∀ i, PostResetServiceStep p c E rho w i :=
  healing_postReset_serviceStep E rho hrec w hreset hcone cap rowCovered mono writes

end J63CutApplication

section J63OpeningCutApplication
variable {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (hreset : H0Reset p c E rho w)
    (hcone : PostResetRetainedCone p c E rho w)
    (cap : RCap p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

variable (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
include hrec mono hreset hcone cap rowCovered xing origin

-- J6-3 O1: apply the full successor at cut i, before service.
example (i : Nat) (hhigh : PostResetHighCompatible p c E rho w i)
    (hfp : PostResetFProv p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (hopening : PostResetOpeningDomain p c E rho w i) :
    PostResetOpeningDomain p c E rho w (i + 1) :=
  healing_postReset_openingDomain_step E rho hrec mono w hreset hcone cap rowCovered xing origin
    i hhigh hfp hraw hopening

-- JOINT-IND: the opening-domain step holds at every cut, pre-reset cuts included.
example : ∀ i, PostResetOpeningDomainStep p c E rho w i :=
  healing_postReset_openingDomainStep E rho hrec w hreset hcone cap rowCovered mono xing origin

end J63OpeningCutApplication

end AvailableChain.FGSA.Run.Tests.HealingPostResetService
end

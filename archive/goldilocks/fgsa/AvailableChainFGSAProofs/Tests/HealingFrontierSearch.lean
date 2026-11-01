module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTail
-- shake: keep (example uses)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchTop
-- shake: keep (example uses)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchBudget
-- shake: keep (example uses)

public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a -- shake: keep (examples)

public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchFull -- shake: keep (S5 tests)

set_option linter.privateModule false

/-! HG.3 phase applications, finite interrupts, phase-order progress,
HG.4 exact-height row service, and aligned terminal-horizon STOP tests.
HG.4 rise and HG.5 full applications remain stopped at the terminal interface. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
example (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .gap = E_gF p ΔF G ρbar :=
  interruptedRepairBudget_gap p G ΔF ρbar

omit [DecidableEq V] in
example (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .topJ = E_jF p ΔF G ρbar :=
  interruptedRepairBudget_topJ p G ΔF ρbar

omit [DecidableEq V] in
example (G ΔF ρbar : Time) :
    interruptedRepairBudget p G ΔF ρbar .contest = ρbar + 3 * p.Δ :=
  interruptedRepairBudget_contest p G ΔF ρbar

-- Height one retains the full frozen seed before projection.
example {t : Time} (h : StrongServed p c E rho 1 t) : ServedFrontier p c E rho 1 t :=
  h.toServedFrontier

-- An actual interrupt at the closed horizon forces the first-event arm.
example (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {ev : V2.Event V (Obj p)}
    (hij : i < j) (hj : rho.events[j]? = some ev) (ht : ev.time = rho.horizon)
    (heff : EffectiveEvent p c E rho j) : FirstEffectiveBy p c E rho i rho.horizon := by
  rcases frontierSearch_first_effective_split p c E rho hs i rho.horizon with h | hquiet
  · exact h
  · exact (hquiet j hij (healing_phase_lt_timeIdx p c E rho hs hj ht.le) heff).elim

-- An ordinary attempt stops at this event; frontier-only service can continue.
example {j : Nat} (heff : EffectiveEvent p c E rho j)
    (hsame : frontierAtIdx p c E rho j = frontierAtIdx p c E rho (j + 1)) :
    EffectiveEvent p c E rho j ∧
      ¬ frontierAtIdx p c E rho j < frontierAtIdx p c E rho (j + 1) := by
  exact ⟨heff, by rw [hsame]; exact lt_irrefl _⟩

-- A skip past M+1 retains its earlier honest M+1 row and event index.
example (cap : RCap p c E rho) {M i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hW : HeldAt p c E rho i x W) (hh : M + 2 ≤ (heightView p W).h) :
    ∃ j z r a e, j < i ∧ HonestRowAt p c E rho j z r a ∧
      namedEntry a.payload.height_pair = some (M + 1, e) :=
  frontierSearch_skipped_row p c E rho cap hW hh

-- Two completed allowance routes cannot select different first row rounds.
example {M r2 r1 : Nat} (h2 : HeightRow p c E rho r2 (M + 1))
    (hf2 : ∀ r, HeightRow p c E rho r (M + 1) → r2 ≤ r)
    (h1 : HeightRow p c E rho r1 (M + 1))
    (hf1 : ∀ r, HeightRow p c E rho r (M + 1) → r1 ≤ r) : r2 = r1 :=
  frontierSearch_first_row_unique p c E rho h2 hf2 h1 hf1

-- A row exactly at the closed horizon suffices for the least-row construction.
example {m r : Nat} (hr : HeightRow p c E rho r m)
    (ht : p.actionTime r = rho.horizon) : FirstHeightRowBy p c E rho m rho.horizon :=
  frontierSearch_first_row p c E rho hr ht.le

-- At m=1, HG.4 row service applies when the complete tail ends at the horizon.
example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {t : Time} (hserved : StrongServed p c E rho 1 t)
    (hhor : t + (P p - 4 * p.Δ) = rho.horizon)
    (hsame : ∃ j ev, rho.events[j]? = some ev ∧ t ≤ ev.time ∧
      ev.time ≤ rho.horizon ∧ EffectiveEvent p c E rho j ∧
      frontierAtIdx p c E rho j = frontierAtIdx p c E rho (j + 1)) :
    FirstHeightRowBy p c E rho 1 rho.horizon ∧
      ∃ j ev, rho.events[j]? = some ev ∧ t ≤ ev.time ∧
        ev.time ≤ rho.horizon ∧ EffectiveEvent p c E rho j ∧
        frontierAtIdx p c E rho j = frontierAtIdx p c E rho (j + 1) := by
  refine ⟨?_, hsame⟩
  simpa only [hhor] using
    healing_frontierTail_row E rho hrec mono crossing cap scopeProducer writes rowCoverage
      hserved hhor.le

-- Same-frontier stops advance the phase under the actual phase-order producer.
example (crossing : RXing p c E rho) (mono : RMonoAll p c E rho)
    (hs : V2.D.ScheduleWellFormed E rho) {i m : Nat} {kind : PhaseKind}
    {ev : V2.Event V (Obj p)} {deadline : Time}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hstop : FirstPhaseStopBy p c E rho i m deadline) :
    ∃ j nextEv nextKind, i < j ∧ nextEv.time ≤ deadline ∧
      FrontierSearchStart p c E rho j nextEv m nextKind ∧
      frontierSearch_phaseRank nextKind > frontierSearch_phaseRank kind :=
  frontierSearch_phase_step_of_crossing p c E rho crossing mono hs hstart hstop

section PhaseApplications
variable [Fintype V] {G ΔF ρbar : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (mono : RMonoAll p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))

-- Apply each phase lemma at the closed horizon, including height one.
example {i : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev 1 .gap)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_gF p ΔF G ρbar = rho.horizon) :
    FrontierHG3Result p c E rho i 1 ev.time rho.horizon := by
  simpa only [hhor] using frontier_hg3_gap E rho hrec crossing mono repair common hδ hbound perm
    rowsReceipt progressCoverage hfold faultQ honestQuorum hstart mode hhor.le

example (origin : RQCOrigin p c E rho) {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .topJ)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_jF p ΔF G ρbar = rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time rho.horizon := by
  simpa only [hhor] using frontier_hg3_topJ E rho hrec crossing mono origin repair common
    hδ hbound perm rowsReceipt progressCoverage hfold faultQ honestQuorum hstart mode hhor.le

example {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .contest)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + (ρbar + 3 * p.Δ) = rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time rho.horizon := by
  simpa only [hhor] using frontier_hg3_contest E rho hrec crossing mono repair hstart mode hhor.le

-- The two-sided top-J bound remains intact.
example (hF : 0 ≤ ΔF) : E_j p G ρbar ≤ E_jF p ΔF G ρbar ∧
    E_jF p ΔF G ρbar ≤ E_j p G ρbar + epsF p ΔF := E_jF_bounds p ΔF G ρbar hF
end PhaseApplications

example [Fintype V] {ΔF : Time} (_hrec : RecoverySleep₂ p c E rho (8 * p.Δ) ΔF) :
    Γ p (8 * p.Δ) = 8 * p.Δ := fgsa_gamma_eq_of_dvd p ⟨2, by ring⟩

example [Fintype V] {ΔF : Time} (_hrec : RecoverySleep₂ p c E rho (12 * p.Δ) ΔF) :
    Γ p (12 * p.Δ) = 12 * p.Δ := fgsa_gamma_eq_of_dvd p ⟨3, by ring⟩

-- GUP r2: every unaligned recovery regime supplies the internal aligned regime.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    Recovery₂Aligned p c E rho (Γ p G) ΔF := recovery₂_roundUp hrec.toRecovery₂

example : ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
    d + (2 * 8 + 8 - 9) ≤ horizon → a + 2 * 8 + 8 - 9 ≤ horizon) :=
  frontierSearch_terminal_horizon_gap8

example : ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
    d + (2 * 8 + 12 - 9) ≤ horizon → a + 2 * 8 + 12 - 9 ≤ horizon) :=
  frontierSearch_terminal_horizon_gap12

#check InterruptedRepairStatement
#check FrontierTailStatement
#check FrontierSearchStatement
#check healing_frontierTail_row
#print axioms frontier_hg3_gap
#print axioms frontier_hg3_topJ
#print axioms frontier_hg3_contest
#print axioms frontierSearch_phase_step_of_crossing
#print axioms healing_frontierTail_row
#print axioms frontierSearch_terminal_horizon_gap8
#print axioms frontierSearch_terminal_horizon_gap12

end AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
end

namespace AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
open AvailableChain.SimplexFG

-- HG4-RISE T: only the F1 slot component is applied. F1--F3 remain stopped.
section HG2aGap
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (r : Nat) (U : FGBlock (Fin p.n))
    (hgst : E.t_GST ≤ (r : Time) * P p)
    (hhor : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) = rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ)
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon := by
  obtain ⟨_, s, hlo, _, _, ht, _⟩ := frontierSearch_hg2a_gap E rho hrec r U hgst hhor.le
  exact ⟨s, hlo, ht.trans hhor.le⟩
end HG2aGap

private def hg2aParams : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

-- The old grid values now fit the age bound at the unchanged HG.4 guard.
example : max (54 + Γ hg2aParams 8 - hg2aParams.Δ + epsF hg2aParams 2)
    (44 + 2 * P hg2aParams + Γ hg2aParams 8 - 3 * hg2aParams.Δ) ≤
    50 + (2 * P hg2aParams + Γ hg2aParams 8 - 9 * hg2aParams.Δ) :=
  frontierSearch_hg2a_bound hg2aParams 8 2 50 54 44 ⟨by decide⟩ (by decide) (by decide)

example : max (54 + Γ hg2aParams 12 - hg2aParams.Δ + epsF hg2aParams 2)
    (44 + 2 * P hg2aParams + Γ hg2aParams 12 - 3 * hg2aParams.Δ) ≤
    50 + (2 * P hg2aParams + Γ hg2aParams 12 - 9 * hg2aParams.Δ) :=
  frontierSearch_hg2a_bound hg2aParams 12 2 50 54 44 ⟨by decide⟩ (by decide) (by decide)

-- Both aligned full gap windows fit. The service endpoint does not fit.
-- These are interface checks, not counterexamples to HG.4 on valid runs.
example : max (54 + (8 : Int) - 1) (44 + 2 * 8 + 8 - 3) = 65 ∧
    max (6 * 8 + 8 - 4) (44 + 2 * 8 - 4) + 8 ≤ 65 ∧
    ¬ (∃ v : Int, max (54 + 8 + 4) (44 + 2 * 8 + 8 + 2) ≤ v ∧ v ≤ 65) := by
  norm_num
  omega

example : max (54 + (12 : Int) - 1) (44 + 2 * 8 + 12 - 3) = 69 ∧
    max (6 * 8 + 8 - 4) (44 + 2 * 8 - 4) + 12 ≤ 69 ∧
    ¬ (∃ v : Int, max (54 + 12 + 4) (44 + 2 * 8 + 12 + 2) ≤ v ∧ v ≤ 69) := by
  norm_num
  omega

#check FrontierHG2aResult
#print axioms frontierSearch_hg2a_bound
#print axioms frontierSearch_hg2a_gate_cost
#print axioms frontierSearch_hg2a_gap

end AvailableChain.FGSA.Run.Tests.HealingFrontierSearch

-- Blueprint 21:1592–1800; S5 T. H1, H2, F2, and F3 producer applications.
-- DC: SAME all previous grid and interface tests remain in the file.
namespace AvailableChain.FGSA.Run.Tests.HealingFrontierSearch
open AvailableChain.SimplexFG

section CappedReceiptApplications
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
    (origin : RQCOrigin p c E rho) (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (perm : TPerm p c E rho) (frontier : TFrontier p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))

example {r m : Nat} {s : Slot} {U X : FGBlock (Fin p.n)}
    (src : PromotionSourceAt p c E rho ΔF r m U s X) : m + 1 ≤ (heightView p X).h :=
  promotion_age_advance_of_source E rho hrec.toRecovery₂ src hδ hbound rowsReceipt
    progressCoverage hfold faultQ honestQuorum

example {m : Nat} {s : Slot} {Qfg X : FGBlock (Fin p.n)}
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams s) (hQX : FGBlock.Preceq Qfg X.parent)
    (hcap : ∀ i x, i ≤ V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s + p.Δ) →
      x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    (hQm : (heightView p Qfg).h = m)
    (hhor : SA.proposalTime p.toParams s + p.Δ = rho.horizon) :
    ∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ nd.st.fg.TF) rho.horizon y := by
  simpa only [hhor] using healing_promotion_first_receipt_of_frontierCap E rho hrec.toRecovery₂
    crossing (healing_self_proposal_service hrec s) hnew hgst hQX hcap hQm hhor.le

example {u : Time} {i m r q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg U : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (he : eraseFG Qfg = Q) (hQm : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hseed : FrontierSeedQualification p E u q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hp : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqr : q ≤ r * p.R) (hU : U = (heightView p Qfg).T_h)
    (hstart : frontierAtIdx p c E rho (i + 1) ≤ m)
    (hhor : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G - 3 * p.Δ) = rho.horizon) :
    FrontierHG2aResult E rho G ΔF i m r U :=
  frontier_hg2a_receipt E rho hrec hδ hbound mono crossing frontier rowsReceipt progressCoverage
    hfold faultQ honestQuorum hgst hQ he hQm hexact hseed hu hp hqr hU hstart hhor.le

example : FrontierTailStatement p c E rho G ΔF :=
  healing_frontierTail E rho hrec mono crossing cap scopeProducer writes rowCoverage rowsReceipt
    progressCoverage hfold faultQ honestQuorum

example : FrontierSearchStatement p c E rho G ΔF :=
  healing_frontierSearch E rho hrec mono crossing cap origin repair common perm
    scopeProducer writes
    rowCoverage rowsReceipt progressCoverage hfold faultQ honestQuorum

example {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (hstart : FrontierSearchStart p c E rho i ev m kind)
    (hserved : StrongServed p c E rho m ev.time)
    (hhor : ev.time + (2 * P p + Γ p G - 9 * p.Δ) = rho.horizon) :
    FrontierRiseBy p c E rho i m rho.horizon := by
  simpa only [hhor] using healing_frontierTail_rise E rho hrec hδ hbound mono crossing frontier
    rowsReceipt progressCoverage hfold faultQ honestQuorum hstart hserved hhor.le

-- The strict cut excludes the rise event when its time is exactly D.
example (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {ev : V2.Event V (Obj p)} {D : Time}
    (hj : rho.events[j]? = some ev) (ht : ev.time = D) : V2.D.Run.idxBefore rho D ≤ j := by
  by_contra hn
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj D).mp (by omega)
  have hlt' : ev.time < D := hlt
  exact (not_lt_of_ge ht.ge) hlt'

end CappedReceiptApplications

-- Both aligned grid examples use the unchanged HG.4 horizon.
example : max (54 + Γ hg2aParams 8 - hg2aParams.Δ + epsF hg2aParams 2)
    (44 + 2 * P hg2aParams + Γ hg2aParams 8 - 3 * hg2aParams.Δ) ≤ (65 : Time) := by
  convert frontierSearch_hg2a_bound hg2aParams 8 2 50 54 44
    ⟨by decide⟩ (by decide) (by decide) using 1
  norm_num [P, Γ, hg2aParams]

example : max (54 + Γ hg2aParams 12 - hg2aParams.Δ + epsF hg2aParams 2)
    (44 + 2 * P hg2aParams + Γ hg2aParams 12 - 3 * hg2aParams.Δ) ≤ (69 : Time) := by
  convert frontierSearch_hg2a_bound hg2aParams 12 2 50 54 44
    ⟨by decide⟩ (by decide) (by decide) using 1
  norm_num [P, Γ, hg2aParams]

#print axioms promotion_age_advance_of_source
#print axioms healing_promotion_first_receipt_of_frontierCap
#print axioms frontier_hg2a_receipt
#print axioms healing_frontierTail
#print axioms healing_frontierSearch

end AvailableChain.FGSA.Run.Tests.HealingFrontierSearch

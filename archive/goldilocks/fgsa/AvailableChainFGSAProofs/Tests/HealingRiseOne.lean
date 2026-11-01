module
public import AvailableChainFGSAProofs.Proofs.Healing.HealingInputExport
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneRise -- shake: keep (M5b tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing -- shake: keep (RXing)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (RMono)
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases -- shake: keep (writes)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission -- shake: keep (rowCoverage)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService -- shake: keep (r3 row ports)
public import AvailableChainFGSAProofs.Proofs.Finality.Height -- shake: keep (hfold)
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport -- shake: keep (honestQuorum)

set_option linter.privateModule false

public section

/-! S5 M5 tests. The direct applications keep each supplier's exact binders.
The boundaries are a missing honest proposal, a rise at the horizon, and
slot one with a non-opening repair gate and explicit slow-window guards. -/

namespace AvailableChain.FGSA.Run.Tests.HealingRiseOne
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
            (actView pre) w C) :
    ∀ {u D : Time}, recoveryStart p E ≤ u → u ≤ D → D ≤ rho.horizon →
    ¬ RiseOneBy p c E rho D →
    PhaseInterval p c E rho u D 1 (some .genesis) false ∧
    ∃ β, u < SA.proposalTime p.toParams β ∧
      (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
      RepairAfter p c E rho (β + 2 * p.k - 1) D ∧
      (u + ρΓ p G ≤ D → ∃ q Q,
        SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q ∧
        SA.gateTime p.toParams q ≤ u + ρΓ p G ∧
        HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q) :=
  healing_rise_one_repair E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono) writes

example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hstop : ¬ RiseOneBy p c E rho D) {b : Nat}
    (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hkb : p.k ≤ b + 1)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) :
    RepairAfter p c E rho (b + p.k) D ∧
      (u + ρ₁ p G ≤ D → ∃ q Q,
        SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q ∧
        SA.gateTime p.toParams q < u + ρ₁ p G ∧
        HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q) :=
  healing_rise_one_repair_synchronous E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono) writes hready huD hD hstop
    hb hmin hkb hwindow

example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hstop : ¬ RiseOneBy p c E rho D) {q : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams q ≤ D)
    (hbudget : SA.gateTime p.toParams q + (P p - 4 * p.Δ) ≤ D) :
    (heightView p Qfg).h = 1 ∧ (heightView p Qfg).T_h = .genesis ∧
    ∃ r, q ≤ r * p.R ∧ (∀ r', q ≤ r' * p.R → r ≤ r') ∧ p.actionTime r ≤ D ∧
      0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 :=
  healing_rise_one_first_opening E rho hrec mono crossing
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage hready huD hD
    hstop hQ hQfg hexact hu hgate hbudget

example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hstop : ¬ RiseOneBy p c E rho D) {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R) (hrD : p.actionTime r ≤ D) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 :=
  healing_rise_one_later_opening E rho hrec mono crossing
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage hready huD hD
    hstop hQ hQfg hexact hu hqr hrD

example [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hbudget : u + ρΓ p G + (P p - 4 * p.Δ) ≤ D) :
    RiseOneBy p c E rho D ∨
    ∃ β q Q Qfg r, PhaseInterval p c E rho u D 1 (some .genesis) false ∧
      u < SA.proposalTime p.toParams β ∧
      (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
      RepairAfter p c E rho (β + 2 * p.k - 1) D ∧
      SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q ∧
      SA.gateTime p.toParams q ≤ u + ρΓ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q ∧
      eraseFG Qfg = Q ∧ (heightView p Qfg).h = 1 ∧ (heightView p Qfg).T_h = .genesis ∧
      q ≤ r * p.R ∧ (∀ r', q ≤ r' * p.R → r ≤ r') ∧ p.actionTime r ≤ D ∧
      0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 :=
  healing_rise_one_repair_opening E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono) writes rowCoverage
    hready huD hD hbudget

-- If no honest proposal exists in the finite run, the repair budget cannot fit.
example [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
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
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hstop : ¬ RiseOneBy p c E rho D)
    (hno : ∀ q Q, ¬ HonestProposal E rho (fgsaInterface p c) q Q) :
    ¬ u + ρΓ p G ≤ D := by
  intro hbudget
  obtain ⟨_, β, _, _, _, hw⟩ :=
    healing_rise_one_repair E rho hrec mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono) writes hready huD hD hstop
  obtain ⟨q, Q, _, _, hQ, _⟩ := hw hbudget
  exact hno q Q hQ

-- The bounded split itself has no honest-proposal or repair-budget premise.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hne : rho.honest.Nonempty) {u D : Time} (huD : u ≤ D) (hD : D ≤ rho.horizon) :
    RiseOneBy p c E rho D ∨ PhaseInterval p c E rho u D 1 (some .genesis) false :=
  healing_rise_one_split p c E rho hs (fgsa_rMonoAll p c E rho) hne huD hD

-- Acceptance at the horizon is enough. No phase beyond the rise is claimed.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hne : rho.honest.Nonempty)
    (hh : 2 ≤ frontierAtIdx p c E rho (timeIdx rho rho.horizon)) :
    RiseOneBy p c E rho rho.horizon :=
  healing_rise_one_of_frontier p c E rho hs hne hh

-- An actual event at the horizon is included with its post-event prefix.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {ev : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some ev) (ht : ev.time = rho.horizon)
    (hh : 2 ≤ frontierAtIdx p c E rho (i + 1)) (hne : rho.honest.Nonempty)
    (hnr : V2.D.NoRestart rho) : RiseOneBy p c E rho rho.horizon := by
  have hiD := healing_phase_lt_timeIdx p c E rho hs hi (le_of_eq ht)
  exact healing_rise_one_of_frontier p c E rho hs hne
    (hh.trans (healing_frontier_mono p c E rho hnr hiD))

-- The accepted Qfg is unique under erasure, and height one has genesis entry.
example {K K' : FGBlock (Fin p.n)} {Q : Block}
    (hK : eraseFG K = Q) (hK' : eraseFG K' = Q) : K = K' :=
  eraseFG_injective (hK.trans hK'.symm)

example (K : FGBlock (Fin p.n)) (hK : (heightView p K).h = 1) :
    (heightView p K).T_h = .genesis := healing_rise_one_entry p K hK

example (K : FGBlock (Fin p.n)) : (heightView p K).h ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp ((fgCertificateLaws p).height.one_le_h K)

-- Slot 1 cannot be an opening label rR when R >= 2.
example (r : Nat) : (1 : Nat) ≠ r * p.R := by
  have := p.RLarge
  cases r with
  | zero => simp only [Nat.zero_mul]; omega
  | succ r => rw [Nat.succ_mul]; omega

-- Its first opening is r=1. The gate and release times remain different.
example : 0 ≤ p.actionTime 1 - SA.gateTime p.toParams 1 ∧
    p.actionTime 1 - SA.gateTime p.toParams 1 ≤ P p - 4 * p.Δ := by
  apply opening_first_time_bound (p := p) 1 1
  · simpa only [Nat.one_mul] using (show 1 ≤ p.R by have := p.RLarge; omega)
  · intro r hr
    cases r with
    | zero => rw [Nat.zero_mul] at hr; omega
    | succ r => omega

example : SA.releaseTime p.toParams 1 < SA.gateTime p.toParams 1 := by
  change 4 * p.Δ * (1 : Int) + 5 * p.Δ < 4 * p.Δ * (1 : Int) + 6 * p.Δ
  linarith [p.deltaPos]

example : SA.voteTime p.toParams 2 = SA.releaseTime p.toParams 1 := by
  change 4 * p.Δ * (2 : Int) + p.Δ = 4 * p.Δ * (1 : Int) + 5 * p.Δ
  ring

-- The rhoOne guard fails at b=1 for k=3; frontier one does not repair it.
example (hk : p.k = 3) : ¬ p.k ≤ (1 : Nat) + 1 := by omega

-- At a resulting frontier of one, no effective event occurs.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hnr : V2.D.NoRestart rho) {i : Nat}
    (hf : frontierAtIdx p c E rho (i + 1) = 1) : ¬ EffectiveEvent p c E rho i :=
  boot_not_effective_one p c E rho hnr hf

-- The exact earlier-or-current covered row has one strict common receipt cut.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {DeltaF : Time} (receipt : TRowsReceipt p c E rho DeltaF)
    {r : Nat} {Q : Block} (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + DeltaF ≤ rho.horizon)
    (hcovered : OpeningCovered p c E rho r Q) (hentry : OpeningEntry p c E rho r 1) :
    ∀ x ∈ rho.honest, ∃ K j rSent a,
      actionSourceFG p c E rho x r = some (some K) ∧ rSent ≤ r ∧
      HonestRowAt p c E rho j x rSent a ∧
      namedEntry a.payload.height_pair = some (1, (FGBlock.genesis : FGBlock (Fin p.n)).root) ∧
      ∀ z ∈ rho.honest, HeldBefore p c E rho z a (p.actionTime r + DeltaF) :=
  healing_rise_one_rows_received p c E rho hs hnr receipt hgst hhor hcovered hentry

-- The stopped branch has the exact genesis frame, including lo=0.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hne : rho.honest.Nonempty) {D : Time} (hstop : ¬ RiseOneBy p c E rho D)
    {i : Nat} (hi : i ≤ timeIdx rho D) {x : V} (hx : x ∈ rho.honest) :
    (R_at p c E rho i x).H = 1 ∧ (R_at p c E rho i x).j = 0 ∧
      (R_at p c E rho i x).J = .genesis ∧ (R_at p c E rho i x).contest = false ∧
      (R_at p c E rho i x).rootIsJ = true ∧ (R_at p c E rho i x).lo = 0 :=
  boot_height_one p c E rho hx
    (healing_rise_one_frontier p c E rho hs (fgsa_rMonoAll p c E rho) hne hstop hi)


-- Apply B3 with every INLINE port discharged by its existing producer.
private theorem riseOneWithPorts [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (qc : RQCOrigin p c E rho) {u D : Time}
    (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hbudget : u + ρΓ p G + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) ≤ D)
    (hhor : u + ρΓ p G + (P p - 4 * p.Δ) +
      (2 * P p + Γ p G - 4 * p.Δ) ≤ rho.horizon) :
    RiseOneBy p c E rho D ∨
      ∃ r s X, p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) ∧
        HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
        (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
        SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
        2 ≤ (heightView p X).h ∧ SA.proposalTime p.toParams s + p.Δ ≤ D ∧
        ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x := by
  let mono := fgsa_rMonoAll p c E rho
  let crossing := fgsa_rXing (hroots := hrec.base.idealization) p c E rho hrec.base.linked
    (fgsa_faultX_count_rec p hrec.fault) hrec.base.valid.toUnforgeableSignatures
  exact healing_rise_one_rise E rho hrec hδ hbound mono crossing qc
    (healing_repair_service_scopes_recovery E rho hrec mono)
    (healing_opening_service_scopes_recovery E rho hrec mono)
    (fun _ _ _ _ _ hv hx hip hem hSync hhor hCompat =>
      healing_proposal_receipt_recovery p c E rho hrec hv hx hip hem hSync hhor hCompat)
    (fgsa_leaseOrigins_lastWrite p c E rho hrec.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho hrec.base hrec.fault)
    (fgsa_tRowsReceipt_sleep p c E rho ΔF hrec.base.delta hrec.base.valid
      hrec.suffixNoRestart hrec.sync hrec.deltaF hrec.awake)
    (fgsa_batchCoverage p ΔF .progress c E rho)
    (fgsa_foldTrichotomy_progress p) (fgsa_faultQ_of_count p hrec.fault)
    (kmid_honest_quorum p c rho hrec.base.linked hrec.fault)
    hready huD hD hbudget hhor

-- Genesis top J gives strict receipt for every honest receiver.
example [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) {u : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) 1
      (some .genesis) false) :
    ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x :=
  healing_rise_one_receipt_all p c E rho hrec.toRecovery₂ crossing
    (fun _ _ _ _ hv hx hip hem hSync hhor hCompat =>
      healing_proposal_receipt_recovery p c E rho hrec hv hx hip hem hSync hhor hCompat)
    hnew hu hready hp

-- B2 includes an event at D_event and retains the actual first rise.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hne : rho.honest.Nonempty) {i : Nat} {ev : V2.Event V (Obj p)} {D_event : Time}
    (hi : rho.events[i]? = some ev) (ht : ev.time = D_event)
    (heff : EffectiveEvent p c E rho i) : RiseOneBy p c E rho D_event :=
  healing_rise_one_of_effective p c E rho hs (fgsa_rMonoAll p c E rho) hne hi ht.le heff

-- A strict receipt deadline can equal the finite horizon.
example [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) {u : Time} {s : Slot} {X : FGBlock (Fin p.n)}
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
    (hu : u ≤ SA.proposalTime p.toParams s) (hready : recoveryStart p E ≤ u)
    (hhorizon : SA.proposalTime p.toParams s + p.Δ = rho.horizon) :
    RiseOneBy p c E rho rho.horizon ∨
      ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x :=
  healing_rise_one_accept p c E rho hrec.toRecovery₂ (fgsa_rMonoAll p c E rho) crossing
    (fun _ _ _ _ hv hx hip hem hSync hhor hCompat =>
      healing_proposal_receipt_recovery p c E rho hrec hv hx hip hem hSync hhor hCompat)
    hnew hu hready hhorizon.le le_rfl

-- The full gap horizon is five Delta beyond the terminal deadline.
example (G u : Time) :
    u + ρΓ p G + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) <
      u + ρΓ p G + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) := by
  linarith [p.deltaPos]

end AvailableChain.FGSA.Run.Tests.HealingRiseOne
end

namespace AvailableChain.FGSA.Run.Tests.HealingRiseOne
open AvailableChain.SimplexFG

private def riseOneParams : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

-- The same r3 W bound permits DeltaF = 6 > Delta = 1.
example : riseOneParams.Δ < (6 : Time) ∧ LivenessBoundW riseOneParams 6 :=
  ⟨by decide, ⟨by decide⟩⟩

example : EntryAt riseOneParams (.genesis : FGBlock (Fin 4)) 1 := ⟨rfl, rfl⟩

-- The row deadline precedes the mature proposal; its strict receipt fits the event cut.
example : riseOneParams.actionTime 1 + 6 ≤ carrierTimeW riseOneParams 6 1 ∧
    carrierTimeW riseOneParams 6 1 < (1 : Time) * P riseOneParams + 2 * P riseOneParams ∧
    SA.proposalTime riseOneParams.toParams 10 + riseOneParams.Δ ≤
      riseOneParams.actionTime 1 + 2 * P riseOneParams + Γ riseOneParams 10 -
        9 * riseOneParams.Δ := by
  decide


-- Apply the full proof with DeltaF > Delta, then locate the accepted first rise.
example {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa riseOneParams c))
    (hrec : RecoverySleep₂ riseOneParams c E rho 10 6) (qc : RQCOrigin riseOneParams c E rho)
    {u D : Time} (hready : recoveryStart riseOneParams E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hbudget : u + ρΓ riseOneParams 10 + (P riseOneParams - 4 * riseOneParams.Δ) +
      (2 * P riseOneParams + Γ riseOneParams 10 - 9 * riseOneParams.Δ) ≤ D)
    (hhor : u + ρΓ riseOneParams 10 + (P riseOneParams - 4 * riseOneParams.Δ) +
      (2 * P riseOneParams + Γ riseOneParams 10 - 4 * riseOneParams.Δ) ≤ rho.horizon) :
    RiseOneBy riseOneParams c E rho D := by
  rcases riseOneWithPorts E rho hrec rfl ⟨by decide⟩ qc hready huD hD hbudget hhor with
    hrise | ⟨_, _, X, _, hnew, _, _, _, hh, hd, hreceipt⟩
  · exact hrise
  · exact healing_rise_one_of_receipt riseOneParams c E rho
      hrec.base.valid.toScheduleWellFormed (fgsa_rMonoAll riseOneParams c E rho)
      hnew.1.2 hh
      (hreceipt _ hnew.1.2) hd

end AvailableChain.FGSA.Run.Tests.HealingRiseOne

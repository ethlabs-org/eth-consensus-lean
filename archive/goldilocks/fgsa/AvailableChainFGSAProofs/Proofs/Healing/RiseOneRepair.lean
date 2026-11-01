module
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOne
public import AvailableChainFGSAProofs.Proofs.Healing.Repair
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceOne

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! S5 H-PHASE M5, plan A steps 2 and 4. H-REPAIR supplies the repair gate.
H-GATE supplies each opening. INLINE writes: fgsa_leaseOrigins_lastWrite.
INLINE rowCoverage: rowPermission_covered. Assembly supplies these exact
bodies and the R-ports. No TCommon or TFrontier premise is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem rise_one_honest_nonempty [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  have hc : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hle := Finset.card_le_univ rho.honest
    rw [hn] at hle
    omega
  have hf := hrec.fault
  have hp := p.nPos
  exact Finset.card_pos.mp (by omega)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A step 2. DC: SAME least mathematical proposal-grid label after u.
This proves no emission and makes no read of a future proposal. -/
theorem healing_rise_one_grid (p : Params) (u : Time) :
    ∃ β, u < SA.proposalTime p.toParams β ∧
      ∀ b, u < SA.proposalTime p.toParams b → β ≤ b := by
  have hex : ∃ β, u < SA.proposalTime p.toParams β := by
    refine ⟨u.toNat + 1, ?_⟩
    have hu : u ≤ (u.toNat : Int) := Int.self_le_toNat u
    have hn : (0 : Int) ≤ u.toNat := Int.natCast_nonneg _
    have hd : (1 : Int) ≤ p.Δ := by
      have hd0 : (0 : Int) < p.Δ := p.deltaPos
      omega
    change u < 4 * p.Δ * ((u.toNat + 1 : Nat) : Int)
    push_cast
    nlinarith
  exact ⟨Nat.find hex, Nat.find_spec hex, fun b hb => Nat.find_min' hex hb⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A step 2, rhoGamma arm. DC: SAME apply healing_tRepair with its
own binders at (u,D,1,some genesis,false). Existence has its finite budget. -/
theorem healing_rise_one_repair [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
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
        HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q) := by
  intro u D hgst huD hD hstop
  have hphase := healing_rise_one_phase p c E rho hrec.base.valid.toScheduleWellFormed
    mono (rise_one_honest_nonempty E rho hrec) huD hD hstop
  obtain ⟨β, hβ, hmin⟩ := healing_rise_one_grid p u
  have hrepair := (healing_tRepair E rho hrec mono crossing qc services writes) G u D 1
    (some .genesis) false (healing_proposal_gap hrec) hrec.gapPos hgst hphase
  obtain ⟨ha, hw⟩ := hrepair.1 β hβ hmin
  exact ⟨hphase, β, hβ, hmin, ha, hw⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A step 2, rhoOne arm. DC: SAME the shorter branch retains all
explicit slow-window premises, including k <= b+1. It is not inferred at s=1. -/
theorem healing_rise_one_repair_synchronous [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
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
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
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
        HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hphase := healing_rise_one_phase p c E rho hrec.base.valid.toScheduleWellFormed
    mono (rise_one_honest_nonempty E rho hrec) huD hD hstop
  exact ((healing_tRepair E rho hrec mono crossing qc services writes) G u D 1
    (some .genesis) false (healing_proposal_gap hrec) hrec.gapPos hready hphase).2 b hb hmin hkb
      hwindow

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A step 4. DC: SAME choose the first opening and apply H-GATE.
The stopped phase gives height one for the accepted Qfg. The opening budget
is an arithmetic bound, not a recurrence or future-run premise. -/
theorem healing_rise_one_first_opening [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (_services : RepairServiceScopes E rho)
    (opening : OpeningServiceScopes E rho)
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
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hphase := healing_rise_one_phase p c E rho hS mono
    (rise_one_honest_nonempty E rho hrec) huD hD hstop
  rcases healing_rise_one_height p c E rho hS mono hQ hQfg hexact hgate hD
    (fun x hx => healing_recovery_gate_reader hrec hx (hGST.trans hu) (hgate.trans hD))
    with hrise | ⟨hh, hentry⟩
  · exact (hstop hrise).elim
  have hex : ∃ r, q ≤ r * p.R := by
    refine ⟨q, ?_⟩
    have := p.RLarge
    nlinarith
  let r := Nat.find hex
  have hqr : q ≤ r * p.R := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨hlo, hhi⟩ := opening_first_time_bound (p := p) q r hqr hfirst
  have hrD : p.actionTime r ≤ D := by linarith
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hur : u ≤ p.actionTime r := by linarith
  have hp := opening_phase_restrict E rho hphase hur hrD
  obtain ⟨h0, h1, hc, he⟩ := opening_height_one E rho hrec mono crossing opening writes rowCoverage
    hready hQ hQfg hexact hu hqr hfirst hp
  exact ⟨hh, hentry, r, hqr, hfirst, hrD, h0, h1, hc, he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A step 4. DC: SAME apply later_opening_covered at each opening
inside the bounded stopped phase, and use the height-one entry theorem. -/
theorem healing_rise_one_later_opening [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (_services : RepairServiceScopes E rho)
    (opening : OpeningServiceScopes E rho)
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
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hstop : ¬ RiseOneBy p c E rho D) {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R) (hrD : p.actionTime r ≤ D) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hphase := healing_rise_one_phase p c E rho hS mono
    (rise_one_honest_nonempty E rho hrec) huD hD hstop
  have hqrI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hur : u ≤ p.actionTime r := by
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hp := opening_phase_restrict E rho hphase hur hrD
  exact ⟨later_opening_covered E rho hrec mono crossing opening writes rowCoverage hready hQ hQfg
    hexact hu hqr hp, opening_entry_one E rho hS hp hur⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan A steps 1--4. DC: INTENTIONAL a bounded first rise or a repaired
height-one proposal with its first covered opening. The budget ends at D.
This theorem makes no height-two production or acceptance claim. -/
theorem healing_rise_one_repair_opening [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (opening : OpeningServiceScopes E rho)
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
      OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  by_cases hstop : RiseOneBy p c E rho D
  · exact Or.inl hstop
  right
  have hd := p.deltaPos
  have hR := p.RLarge
  have hRI : (2 : Int) ≤ p.R := by exact_mod_cast hR
  have hP : 0 ≤ P p - 4 * p.Δ := by
    change 0 ≤ 4 * (p.R : Int) * p.Δ - 4 * p.Δ
    nlinarith
  have hrepairBudget : u + ρΓ p G ≤ D := by linarith
  obtain ⟨hphase, β, hβ, hmin, hafter, hwitness⟩ :=
    healing_rise_one_repair E rho hrec mono crossing qc services writes hready huD hD hstop
  obtain ⟨q, Q, hq, hgate, hQ, hexact⟩ := hwitness hrepairBudget
  have hβl : β ≤ β + 2 * p.k - 1 := by
    have hk : 1 ≤ 2 * p.k := by have := p.kLarge; omega
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hk β)
  have hβI : (β : Int) ≤ ((β + 2 * p.k - 1 : Nat) : Int) := by exact_mod_cast hβl
  have hβt : SA.proposalTime p.toParams β ≤
      SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
    change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Int)
    nlinarith
  have hu : u ≤ SA.proposalTime p.toParams q := hβ.le.trans (hβt.trans hq.le)
  have hgateD := hgate.trans hrepairBudget
  obtain ⟨j, Qfg, _hj, _hQfg, heq⟩ := healing_rise_one_gate_copy p c E rho
    hrec.base.valid.toScheduleWellFormed hexact (hgateD.trans hD) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 (hGST.trans hu) (hgateD.trans hD))
  have hopeningBudget : SA.gateTime p.toParams q + (P p - 4 * p.Δ) ≤ D := by linarith
  obtain ⟨hh, he, r, hqr, hfirst, hrD, h0, h1, hc, hentry⟩ :=
    healing_rise_one_first_opening E rho hrec mono crossing services opening writes rowCoverage
      hready huD hD hstop hQ heq hexact hu hgateD hopeningBudget
  exact ⟨β, q, Q, Qfg, r, hphase, hβ, hmin, hafter, hq, hgate, hQ, hexact,
    heq, hh, he, hqr, hfirst, hrD, h0, h1, hc, hentry⟩

end AvailableChain.FGSA.Run
end

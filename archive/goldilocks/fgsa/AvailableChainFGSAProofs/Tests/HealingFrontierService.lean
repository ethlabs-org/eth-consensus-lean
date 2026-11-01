module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService -- shake: keep (service tests)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceCover -- shake: keep (gate)

set_option linter.privateModule false

/-! HG.1 regression tests. The tests apply the production proofs to an honest q+1
proposal, the first later label q+2, the closed horizon, height one, unequal row delay,
and each seed arm. A covering gate test has no honest-proposal premise at its label.
The full frontier_service tests also consume the frozen statement and opening clauses. -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingFrontierService
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 21:1570–1574. DC: INTENTIONAL the honest q+1 proposal has all service fields. -/
theorem honest_qSucc [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hseed : FrontierSeedQualification p E u q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B :=
  frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase hHeight
    hService hu hPhase hqv hvh hCap hseed hgate hp

/-- Blueprint 21:1500–1574. DC: INTENTIONAL the first later HG.1 label has full service. -/
theorem first_later [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hgate : SA.gateTime p.toParams (q + 2) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 2) B) :
    ExactService p c E rho (q + 2) B := by
  have hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams (q + 2) := by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((q + 2 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  exact frontier_later_exactService E rho hrec mono crossing writes services hgst hQ hErase hHeight
    hService hu hPhase hqv hvh hCap hafter hgate hp

/-- Blueprint 21:1570–1574; plan §4. DC: INTENTIONAL a gate exactly at the horizon is included. -/
theorem closed_horizon [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hseed : FrontierSeedQualification p E u q) (hend : v = rho.horizon)
    (hgate : SA.gateTime p.toParams (q + 1) = rho.horizon)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B ∧
      ∀ x ∈ rho.honest, gateResult p c E rho x (q + 1) = some (some B) := by
  have hgv : SA.gateTime p.toParams (q + 1) ≤ v := by rw [hgate, hend]
  have hs := frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase
    hHeight hService hu hPhase hqv hvh hCap hseed hgv hp
  exact ⟨hs, fun x hx => (hs.2 hgate.le x hx
    (healing_recovery_gate_reader hrec hx (by
      have hGST : E.t_GST ≤ u := by
        have := healing_recovery_start_lower (p := p) E
        linarith [p.deltaPos]
      have hcut := hGST.trans hu
      change E.t_GST ≤ 4 * p.Δ * (q : Int) at hcut
      change E.t_GST ≤ 4 * p.Δ * (q + 1 : Int)
      nlinarith [p.deltaPos]) hgate.le)).1⟩

/-- Blueprint 21:1467–1468, 1570–1574; plan §4. DC: INTENTIONAL no positive J-height premise. -/
theorem height_one [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hm : m = 1) (hJ : J = some (.genesis : FGBlock (Fin p.n)))
    (hseed : FrontierSeedQualification p E u q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B := by
  cases hm
  cases hJ
  exact frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase
    hHeight
    hService hu hPhase hqv hvh hCap hseed hgate hp

/-- Plan §4. DC: INTENTIONAL row delay ΔF can be greater than Δ. -/
theorem row_delay [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (_hF : p.Δ < ΔF) (hseed : FrontierSeedQualification p E u q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B :=
  frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase hHeight
    hService hu hPhase hqv hvh hCap hseed hgate hp

/-- Blueprint 21:925–944. DC: INTENTIONAL the literal H.6 seed arm supplies full q+1 service. -/
theorem seed_H6 [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b)
    (hcut : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B :=
  frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase hHeight
    hService hu hPhase hqv hvh hCap
    ((frontierSeedQualification_iff p E u q).mpr (Or.inl ⟨β, hβ, hmin, hcut⟩)) hgate hp

/-- Blueprint 21:1004–1025. DC: INTENTIONAL the literal H.6-S seed arm supplies q+1 service. -/
theorem seed_H6S [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hkb : p.k ≤ b + 1) (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k))
    (hcut : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B :=
  frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase hHeight
    hService hu hPhase hqv hvh hCap
    ((frontierSeedQualification_iff p E u q).mpr
      (Or.inr ⟨b, hb, hmin, hkb, hwindow, hcut⟩)) hgate hp

/-- Blueprint 21:1551–1583.
DC: INTENTIONAL the covering gate has no later honest proposer premise. -/
theorem covering_gate [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (services : FrontierServiceScopes E rho q v)
    (hgst : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    {s : Slot} (hqs : q < s) (hgate : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i s x Q := by
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos])).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  exact frontier_opening_gateService_of_cover E rho hrec mono crossing writes
    (services.read (hgst.trans hu) hqv hvh) hgst hQ
    hErase hHeight hService hu hPhase hqv hvh hcap hqs hgate hx ht

-- The q+1 read is in the initial phase; its gate is later than the seed gate.
example : (4 * (10 + 1) + 1 : Int) ≤ 4 * 10 + 6 ∧
    (4 * 10 + 6 : Int) < 4 * (10 + 1) + 6 := by decide

-- Closed endpoint arithmetic from plan §4, with the v+1 consumer bound.
example : (4 * 12 + 6 : Int) = 54 ∧ (54 : Int) < 54 + 1 := by decide

#print axioms honest_qSucc
#print axioms first_later
#print axioms closed_horizon
#print axioms height_one
#print axioms row_delay
#print axioms seed_H6
#print axioms seed_H6S
#print axioms covering_gate


section FullService
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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

include hrec mono crossing scopeProducer writes rowCoverage

/-- Blueprint 21 HG.1:1500–1583. DC: SAME the full seeded statement is available. -/
theorem full_statement : TFrontier p c E rho :=
  frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage

variable {u v : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)

include hgst hQ hErase hHeight hService hu hPhase hqv hvh hCap

/-- Blueprint 21:925–944. DC: INTENTIONAL the literal H.6 arm serves all later proposals. -/
theorem full_H6 {β : Slot} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b)
    (hcut : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) :
    Transfers p c E rho q Q v ∧ RepairAfter p c E rho q v := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService (Or.inl ⟨β, hβ, hmin, hcut⟩)
    hu hPhase hqv hvh hCap
  exact ⟨h.1, h.2.1⟩

/-- Blueprint 21:1004–1025. DC: INTENTIONAL the literal H.6-S arm serves all later proposals. -/
theorem full_H6S {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hkb : p.k ≤ b + 1) (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k))
    (hcut : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q) :
    Transfers p c E rho q Q v ∧ RepairAfter p c E rho q v := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService (Or.inr ⟨b, hb, hmin, hkb, hwindow, hcut⟩)
    hu hPhase hqv hvh hCap
  exact ⟨h.1, h.2.1⟩

variable (hseed : FrontierSeedQualification p E u q)

include hseed

/-- Blueprint 21:1570–1574. DC: INTENTIONAL the full statement includes an honest q+1. -/
theorem full_qSucc (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService
    ((frontierSeedQualification_iff p E u q).mp hseed) hu hPhase hqv hvh hCap
  apply h.2.1 (q + 1) B _ hgate hp
  change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
  push_cast
  linarith [p.deltaPos]

/-- Blueprint 21:1500–1574. DC: INTENTIONAL the full statement includes the first later label. -/
theorem full_qAddTwo (hgate : SA.gateTime p.toParams (q + 2) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 2) B) :
    ExactService p c E rho (q + 2) B := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService
    ((frontierSeedQualification_iff p E u q).mp hseed) hu hPhase hqv hvh hCap
  apply h.2.1 (q + 2) B _ hgate hp
  change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 2 : Nat) : Int)
  push_cast
  linarith [p.deltaPos]

/-- Plan §4. DC: INTENTIONAL the gate at the closed horizon is included. -/
theorem full_gate_horizon (hend : v = rho.horizon) {s : Slot}
    (hqs : q < s) (hgate : SA.gateTime p.toParams s = rho.horizon)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) s B) :
    ExactService p c E rho s B ∧
      ∀ x ∈ rho.honest, gateResult p c E rho x s = some (some B) := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService
    ((frontierSeedQualification_iff p E u q).mp hseed) hu hPhase hqv hvh hCap
  have htime : SA.proposalTime p.toParams q < SA.proposalTime p.toParams s := by
    have hqsI : (q : Int) < (s : Int) := by exact_mod_cast hqs
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (s : Int)
    nlinarith [p.deltaPos]
  have hs := h.2.1 s B htime (by rw [hgate, hend]) hp
  exact ⟨hs, fun x hx => (hs.2 hgate.le x hx
    (healing_recovery_gate_reader hrec hx (by
      have hGST : E.t_GST ≤ u := by
        have := healing_recovery_start_lower (p := p) E
        linarith [p.deltaPos]
      have hcut := hGST.trans hu
      change E.t_GST ≤ 4 * p.Δ * (q : Int) at hcut
      change E.t_GST ≤ 4 * p.Δ * (s : Int)
      have hqsI : (q : Int) < (s : Int) := by exact_mod_cast hqs
      nlinarith [p.deltaPos]) hgate.le)).1⟩

/-- Plan §4. DC: INTENTIONAL a closed opening needs no honest proposal at its label. -/
theorem full_opening_horizon (hend : v = rho.horizon) {r : Nat}
    (hqr : q ≤ r * p.R) (ha : p.actionTime r = rho.horizon) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) ∧
      ((∀ r', q ≤ r' * p.R → r ≤ r') →
        p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ) := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService
    ((frontierSeedQualification_iff p E u q).mp hseed) hu hPhase hqv hvh hCap
  exact h.2.2 r hqr (by rw [ha, hend])

omit hHeight hPhase hCap in
/-- Plan §4. DC: INTENTIONAL height one with genesis J and a longer row delay is included. -/
theorem full_height_one_row_delay
    (hHeightOne : (heightView p Qfg).h = 1)
    (hPhaseOne : PhaseInterval p c E rho u (SA.gateTime p.toParams q) 1 (some .genesis) false)
    (hCapOne : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ 1)
    (_hdelay : p.Δ < ΔF) {r : Nat} (hqr : q ≤ r * p.R) (hav : p.actionTime r ≤ v) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 := by
  have h := frontier_service E rho hrec mono crossing scopeProducer writes rowCoverage u v 1
    (some .genesis) false q Q Qfg hgst hQ hErase hHeightOne hService
    ((frontierSeedQualification_iff p E u q).mp hseed) hu hPhaseOne hqv hvh hCapOne
  have hopen := h.2.2 r hqr hav
  exact ⟨hopen.1, hopen.2.1⟩

#print axioms full_statement
#print axioms full_H6
#print axioms full_H6S
#print axioms full_qSucc
#print axioms full_qAddTwo
#print axioms full_gate_horizon
#print axioms full_opening_horizon
#print axioms full_height_one_row_delay

end FullService

end AvailableChain.FGSA.Run.Tests.HealingFrontierService
end

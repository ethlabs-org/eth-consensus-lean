module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierRead -- shake: keep (F1–F7 tests)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersQ -- shake: keep (F1, F6)

set_option linter.privateModule false

/-! G-HG1 tests (plan fgsa-s5-frontier §2.2, §4). F1: the strict-stop adapter feeds
`fgsa_retainedReads_HG1` directly. F2–F6: the §4 cases m = 1, unequal floors, same-time
reads, ΔF > Δ and d_s = horizon (closed endpoint with the v + 1 sentinel). F7: grid
arithmetic of the endpoint regression and of the q+1 boundary (G5 STOP). -/

public section
namespace AvailableChain.FGSA.Run.Tests.HealingFrontierRead
open AvailableChain.SimplexFG RetainedWalk

section Signatures

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

/-- Blueprint 21:1004–1018; plan §2.1. DC: INTENTIONAL the inline `lastWrite` binder of
§2.1 (Assembly producer Foundations/Leases:392), named only in this test file. -/
private def LastWrite : Prop :=
  ∀ i x (row : Block × Nat × Time),
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
        (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView pre) w C

-- F1: the strict-stop adapter applied directly in the HG.1 consumer.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (lastWrite : LastWrite p c E rho)
    {u stop : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip : Nat} {x : V}
    {jStop : Nat} {evStop : V2.Event V (Obj p)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q (SA.gateTime p.toParams s))
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hStopEv : rho.events[jStop]? = some evStop) (hStop : stop = evStop.time)
    (hRise : m < frontierAtIdx p c E rho (jStop + 1))
    (hCapStop : ∀ i x, timeIdx rho u ≤ i → i ≤ jStop → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hqStop : SA.gateTime p.toParams q < stop) (hsStop : SA.gateTime p.toParams s < stop)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hReceipt : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg N.erase Kc :=
  fgsa_retainedReads_HG1_on (hroots := hrec.base.receiptIdealization) E rho
      hrec.base.valid s hx
    hip hseat N hem Qfg q stop hafter hsStop
    (retainedHG1Input_before_first_rise E rho hrec mono crossing lastWrite hready hQ hErase
      hHeight hService hScopes hu hPhase hStopEv hStop hRise hCapStop
      hqStop hsStop hx hip hseat N hem)
    hReceipt

-- F2: m = 1 (height-one pivot; the frame may be top J with genesis).
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (lastWrite : LastWrite p c E rho)
    {u v : Time} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip : Nat} {x : V}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = 1)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q v) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) 1 J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hHorizon : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ 1)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg :=
  retainedHG1Input_through E rho hrec mono crossing lastWrite hready hQ hErase hHeight
    hService hScopes
    hu hPhase hqv hHorizon hCap hx hip hseat N hem hafter hgate

-- F3: unequal floors: the source and target floors are bounded separately by m.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (lastWrite : LastWrite p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip ih : Nat} {x y : V}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q v) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hHorizon : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hy : y ∈ rho.honest) (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hne : (controls p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))).lo ≠
      (controls p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s))).lo) :
    (controls p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))).lo ≠
      (controls p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s))).lo ∧
    (controls p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))).lo ≤ m ∧
    (controls p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s))).lo ≤ m := by
  have h := retainedHG1Input_through E rho hrec mono crossing lastWrite hready hQ hErase hHeight
    hService hScopes hu hPhase hqv hHorizon hCap hx hip hseat N hem hafter hgate y hy ih hih
  exact ⟨hne, hHeight ▸ h.source_floor, hHeight ▸ h.target_floor⟩

-- F4: same-time reads: two HEAD ticks at v_s, in either index order, both get the input.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (lastWrite : LastWrite p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip i₁ i₂ : Nat} {x y₁ y₂ : V}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q v) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hHorizon : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hy₁ : y₁ ∈ rho.honest) (hi₁ : rho.events[i₁]? = some (.tick y₁ (SA.voteTime p.toParams s)))
    (hy₂ : y₂ ∈ rho.honest) (hi₂ : rho.events[i₂]? = some (.tick y₂ (SA.voteTime p.toParams s)))
    (h12 : i₁ < i₂) :
    i₁ < i₂ ∧
    RetainedConeInput p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E i₁ y₁).st (SA.voteTime p.toParams s)) s Qfg ∧
    RetainedConeInput p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E i₂ y₂).st (SA.voteTime p.toParams s)) s Qfg := by
  have h := retainedHG1Input_through E rho hrec mono crossing lastWrite hready hQ hErase hHeight
    hService hScopes hu hPhase hqv hHorizon hCap hx hip hseat N hem hafter hgate
  exact ⟨h12, h y₁ hy₁ i₁ hi₁, h y₂ hy₂ i₂ hi₂⟩

-- F5: ΔF > Δ: the row delay is not used by the producer.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (hΔF : p.Δ < ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (lastWrite : LastWrite p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip : Nat} {x : V}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q v) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hHorizon : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) :
    p.Δ < ΔF ∧ ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg :=
  ⟨hΔF, retainedHG1Input_through E rho hrec mono crossing lastWrite hready hQ hErase hHeight
    hService hScopes hu hPhase hqv hHorizon hCap hx hip hseat N hem hafter hgate⟩

-- F6: d_s = horizon: the closed endpoint v = horizon; the consumer takes the integer
-- sentinel stop = horizon + 1, after all bounds are proved within the horizon.
example [Fintype V] {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (lastWrite : LastWrite p c E rho)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip : Nat} {x : V}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q rho.horizon) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho rho.horizon → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hReceipt : ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      TargetReceiptService E rho N.erase (SA.voteTime p.toParams s) y)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hds : SA.gateTime p.toParams s = rho.horizon) :
    ∀ y ∈ rho.honest, ∀ (ih : Nat),
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg N.erase Kc := by
  have hd := p.deltaPos
  have hqv : SA.gateTime p.toParams q ≤ rho.horizon := by
    rw [← hds]
    refine hafter.trans ?_
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hstop : SA.gateTime p.toParams s < rho.horizon + 1 := by
    rw [hds]
    exact lt_add_one _
  exact fgsa_retainedReads_HG1_on (hroots := hrec.base.receiptIdealization) E rho
      hrec.base.valid s hx hip hseat N hem Qfg q (rho.horizon + 1) hafter hstop
    (fun y hy ih hih _ => retainedHG1Input_through E rho hrec mono crossing lastWrite hready hQ
      hErase hHeight hService hScopes hu hPhase hqv le_rfl hCap hx hip hseat N hem hafter
      hds.le y hy ih hih) hReceipt

end Signatures

section Boundary

variable (p : Params)

-- F7a: the §4 endpoint regression at Δ = 1, q = 10, s = 12, horizon = 54: d_q = 46,
-- t_s = 48, v_s = 49, d_s = 54. The strict premise d_s < stop fails for stop = horizon and
-- holds for the sentinel horizon + 1.
example (hΔ : p.Δ = 1) :
    SA.gateTime p.toParams 10 = 46 ∧ SA.proposalTime p.toParams 12 = 48 ∧
      SA.voteTime p.toParams 12 = 49 ∧ SA.gateTime p.toParams 12 = 54 ∧
      ¬ SA.gateTime p.toParams 12 < 54 ∧ SA.gateTime p.toParams 12 < 54 + 1 := by
  have h10 : SA.gateTime p.toParams 10 = 46 := by
    change 4 * p.Δ * ((10 : Nat) : Int) + 6 * p.Δ = 46
    rw [hΔ]
    norm_num
  have h12 : SA.gateTime p.toParams 12 = 54 := by
    change 4 * p.Δ * ((12 : Nat) : Int) + 6 * p.Δ = 54
    rw [hΔ]
    norm_num
  refine ⟨h10, ?_, ?_, h12, by rw [h12]; norm_num, by rw [h12]; norm_num⟩
  · change 4 * p.Δ * ((12 : Nat) : Int) = 48
    rw [hΔ]
    norm_num
  · change 4 * p.Δ * ((12 : Nat) : Int) + p.Δ = 49
    rw [hΔ]
    norm_num

-- F7b: q+1 precedes the seed gate (the G3 premise d_q ≤ t_s fails at s = q + 1 and holds
-- at s = q + 2). A lease last written at gate q − k has deadline v_(q+1): it is live at the
-- slot-(q+1) proposer read and expired at d_q (the G5 SPEC gap).
example (q : Nat) (hkq : p.k ≤ q) :
    ¬ SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams (q + 1) ∧
      SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams (q + 2) ∧
      SA.gateTime p.toParams (q - p.k) + SA.lifetime p.toParams =
        SA.voteTime p.toParams (q + 1) ∧
      SA.proposalTime p.toParams (q + 1) < SA.voteTime p.toParams (q + 1) ∧
      SA.voteTime p.toParams (q + 1) < SA.gateTime p.toParams q := by
  have hd := p.deltaPos
  have hm : p.toParams.engine.m = p.k := rfl
  have hqk : ((q - p.k : Nat) : Int) = (q : Int) - p.k := by push_cast [hkq]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ¬ 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    intro h
    linarith
  · change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((q + 2 : Nat) : Int)
    push_cast
    linarith
  · change 4 * p.Δ * ((q - p.k : Nat) : Int) + 6 * p.Δ +
        (4 * (p.toParams.engine.m : Int) - 1) * p.Δ = 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
    rw [hqk, hm]
    push_cast
    ring
  · change 4 * p.Δ * ((q + 1 : Nat) : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
    linarith
  · change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith

end Boundary

end AvailableChain.FGSA.Run.Tests.HealingFrontierRead
end

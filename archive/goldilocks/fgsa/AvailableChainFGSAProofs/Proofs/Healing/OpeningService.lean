module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceGate

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! H-GATE supplier at a later opening (plan fgsa-s5-hgate-hcommon §2.3, §3 A–D; brief S5
H-GATE O2–O3). An honest proposal Q of slot q with exact service, in a post-GST phase that
reaches the opening a_r with q ≤ rR, has fresh gate service at every honest opening tick,
and its FG block Qfg is in the actual post-clock full domain above the floor.
The served block is D = Qfg. The domain proof uses the fixed phase frame and RXing only;
no RQCOrigin descent is needed. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Read bridge. DC: SAME the post-clock read at a tick is the clock of the state before
the tick. -/
theorem opening_postClock_of_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {t : Time}
    (ht : rho.events[i]? = some (.tick x t)) :
    postClock E rho x t = some ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) t) := by
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs ht]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Frame bridge. DC: SAME the clock does not change the FG store, so the post-clock
full domain and controls are those of the state before the tick. -/
theorem opening_domain_clock (nd : Node p) (t : Time) :
    domainR p ((fgsa p c).clock nd t).st (treeT p ((fgsa p c).clock nd t).st) =
      domainR p nd.st (treeT p nd.st) ∧
    frameR p ((fgsa p c).clock nd t).st = frameR p nd.st := by
  have hfg : (FGSA.clock p nd.st t).fg = nd.st.fg := clock_fg p _ _
  constructor
  · change KitFG.filteredFromView (heightView p)
      (KitFG.treeStoreControlsView (heightView p) (FGSA.clock p nd.st t).fg)
      (FGSA.clock p nd.st t).fg.TF =
        KitFG.filteredFromView (heightView p) (KitFG.treeStoreControlsView (heightView p) nd.st.fg)
          nd.st.fg.TF
    rw [hfg]
  · change KitFG.treeStoreControlsView (heightView p) (FGSA.clock p nd.st t).fg =
      KitFG.treeStoreControlsView (heightView p) nd.st.fg
    rw [hfg]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:749–783, 918–1012 (H.7 floor); plan H-GATE §3A, gap 2.
DC: INTENTIONAL the proposal band at the actual proposal read. The proposer reads inside
the phase, so its floor is the phase floor (m in a contest, else m − 1). The parent of Qfg
is the floor witness of `healing_proposer_floor`; height monotonicity lifts the floor to
Qfg. In a top-J phase the root J is below the parent, hence below Qfg. -/
theorem opening_proposal_band (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) (hQfg : eraseFG Qfg = Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqv : SA.proposalTime p.toParams q ≤ v) :
    (if contested then m else m - 1) ≤ (heightView p Qfg).h ∧
      ∀ B, J = some B → FGBlock.Preceq B Qfg := by
  obtain ⟨⟨_, hhon⟩, o, ⟨j, hj, _⟩, _⟩ := hQ
  rw [proposalTime_fgsa p c q] at hj
  let y := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
    (SA.proposalTime p.toParams q)).st
  have hst : proposalStateAt p c E rho q = some st := by
    change (postClock E rho y (V2.D.proposalTime (fgsaInterface p c) q)).map (·.st) = some st
    rw [proposalTime_fgsa p c q, opening_postClock_of_tick E rho hs hj]
    rfl
  have hju : V2.D.Run.idxBefore rho u ≤ j := healing_support_idxBefore_le p c E rho hs hj hu
  have hjv : j ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hs hj hqv).le
  have hset := healing_settled_frame_strict p c E rho crossing u v m J contested hphase j y hju
    hjv hhon
  have hfg : st.fg = (storeAt p c E rho j y).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j y
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hhon hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, hB, heB, hlo⟩ := healing_proposer_floor p c E rho hs q Q st
    ⟨⟨by assumption, hhon⟩, o, ⟨j, by rw [proposalTime_fgsa p c q]; exact hj, by assumption⟩,
      by assumption⟩ hst hne
  have hBp : B = Qfg.parent := by
    apply eraseFG_injective
    rw [heB, ← hQfg, eraseFG_parent]
  have hBQ : FGBlock.Preceq B Qfg := by
    rw [hBp]
    cases Qfg with
    | genesis => exact KitFG.preceq_refl _
    | node P s root b rows => exact KitFG.preceq_parent_node _ _ _ _ _
  have hR : frameR p st = FGSA.controls p (storeAt p c E rho j y) := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho j y).fg
    rw [hfg]
  obtain ⟨_, _, hlo', hroot, _⟩ := hset
  rw [hR, hlo'] at hlo
  refine ⟨hlo.trans ((fgCertificateLaws p).height.h_mono hBQ), ?_⟩
  intro B0 hJ
  subst hJ
  obtain ⟨_, _, hZ, _⟩ := hroot
  have hZB : FGBlock.Preceq (frameR p st).Z B := by
    have h := ((KitFG.mem_filteredFromView _ _ _ _).mp hB).2.2.1
    exact h
  rw [hR, hZ] at hZB
  exact KitFG.preceq_trans hZB hBQ

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1003–1045 (H.7 settled frame), 1148–1252; plan H-GATE §3D.
DC: INTENTIONAL retention in the actual full domain. At an honest read inside the phase,
a stored D above Qfg is above F and the root, and is its own band witness. In an F-root
phase, RXing with the settled-frame certificate K puts F below D; in a top-J phase, F is
below J and J is below Qfg. No Kept arm and no descent is used. -/
theorem opening_domain_of_band (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hphase : PhaseInterval p c E rho u v m J contested)
    {Qfg : FGBlock (Fin p.n)}
    (hband : (if contested then m else m - 1) ≤ (heightView p Qfg).h ∧
      ∀ B, J = some B → FGBlock.Preceq B Qfg)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (hui : V2.D.Run.idxBefore rho u ≤ i)
    (hiv : i ≤ timeIdx rho v) {D : FGBlock (Fin p.n)} (hQD : FGBlock.Preceq Qfg D)
    (hD : D ∈ (storeAt p c E rho i x).fg.TF) :
    D ∈ domainR p (storeAt p c E rho i x) (treeT p (storeAt p c E rho i x)) ∧
      FGBlock.Preceq (storeAt p c E rho i x).fg.F D ∧
      (frameR p (storeAt p c E rho i x)).lo ≤ (heightView p D).h := by
  obtain ⟨_, _, hlo, hroot, _⟩ :=
    healing_settled_frame_strict p c E rho crossing u v m J contested hphase i x hui hiv hx
  have hloD : (frameR p (storeAt p c E rho i x)).lo ≤ (heightView p D).h := by
    change (FGSA.controls p (storeAt p c E rho i x)).lo ≤ _
    rw [hlo]
    exact hband.1.trans ((fgCertificateLaws p).height.h_mono hQD)
  have hFZ : FGBlock.Preceq (storeAt p c E rho i x).fg.F D ∧
      FGBlock.Preceq (frameR p (storeAt p c E rho i x)).Z D := by
    cases hJ : J with
    | some B =>
      rw [hJ] at hroot
      obtain ⟨_, _, hZ, _, _, hFB⟩ := hroot
      have hBD := KitFG.preceq_trans (hband.2 B hJ) hQD
      refine ⟨KitFG.preceq_trans hFB hBD, ?_⟩
      change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho i x)).Z D
      rw [hZ]
      exact hBD
    | none =>
      rw [hJ] at hroot
      obtain ⟨_, hZ, ⟨K, hK, hKF, hKh⟩, _⟩ := hroot
      have hF := crossing i i x x K D hx le_rfl hK hKF ⟨hx, hD⟩ (lt_of_lt_of_le hKh hloD)
      refine ⟨hF, ?_⟩
      change FGBlock.Preceq (FGSA.controls p (storeAt p c E rho i x)).Z D
      rw [hZ]
      exact hF
  refine ⟨?_, hFZ.1, hloD⟩
  exact (KitFG.mem_filteredFromView _ _ _ _).mpr
    ⟨hD, hFZ.1, hFZ.2, D, hD, KitFG.preceq_refl _, hloD⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1100–1144 (the opening read), H.22:3207–3216; plan H-GATE §2.3, §3 A–D,
gaps 1–3. DC: INTENTIONAL fresh service for Q itself and retention of Qfg at an honest
opening tick, read on the state before the tick. At q = rR the exact fast write is the
opening's own fresh write (`opening_gateService_of_fastWrite`). At q < rR, TPerm S1 from
the exact fast write covers every honest HEAD of rR, and the guard induction gives fresh
service at the actual gate (`opening_gateService_of_cover`). Retention uses the proposal
band and the fixed phase frame (`opening_domain_of_band`). -/
theorem later_opening_service [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (services : OpeningServiceScopes E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r))) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x Q ∧
      Qfg ∈ domainR p (storeAt p c E rho i x) (treeT p (storeAt p c E rho i x)) ∧
      (frameR p (storeAt p c E rho i x)).lo ≤ (heightView p Qfg).h := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hvh : p.actionTime r ≤ rho.horizon := hphase.2.1
  have htg : IsGateTick p c rho i x (r * p.R) := ht
  have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hgq : SA.gateTime p.toParams q ≤ p.actionTime r := by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith
  have hpq : SA.proposalTime p.toParams q ≤ p.actionTime r := by
    refine le_trans ?_ hgq
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith
  have hui : V2.D.Run.idxBefore rho u ≤ i :=
    healing_support_idxBefore_le p c E rho hS ht (hu.trans hpq)
  have hiv : i ≤ timeIdx rho (p.actionTime r) :=
    (healing_phase_lt_timeIdx p c E rho hS ht le_rfl).le
  obtain ⟨_, ⟨jq, ⟨hjq, _⟩, _⟩, ⟨nd, hnd, hQnd⟩, _, _⟩ :=
    hexact.2 (hgq.trans hvh) x hx
      (healing_recovery_gate_reader hrec hx (hGST.trans hu) (hgq.trans hvh))
  have hpost := (healing_support_gate_reads p c E rho hS hjq).2
  rw [hpost] at hnd
  have hnd' := Option.some.inj hnd
  subst hnd'
  have hjqi : jq ≤ i := by
    rcases Nat.lt_or_ge q (r * p.R) with hlt | hge
    · apply le_of_lt
      apply repair_idx_lt E rho hS hjq htg
      have hqI' : (q : Int) + 1 ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hlt
      change 4 * p.Δ * (q : Int) + 6 * p.Δ < 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
      nlinarith
    · have he : q = r * p.R := le_antisymm hqr hge
      subst he
      exact (fgsa_tick_unique E rho hS hjq htg).le
  obtain ⟨hQb, hQT, hne⟩ := opening_exact_stored E rho hS hQfg hjq hQnd hjqi
  have hband := opening_proposal_band E rho hS crossing hphase hQ hQfg hu hpq
  obtain ⟨hdom, hFQ, hlo⟩ := opening_domain_of_band E rho crossing hphase hband hx hui hiv
    (KitFG.preceq_refl Qfg) hQT
  have hFQe : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q :=
    hQfg ▸ eraseFG_preceq hFQ
  refine ⟨?_, hdom, hlo⟩
  rcases Nat.lt_or_ge q (r * p.R) with hlt | hge
  · have hvs : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
      linarith
    have hcov := opening_heads_cover E rho hrec mono crossing services writes hready hphase
      hexact hu
      hgq hx hlt hvs
    exact opening_gateService_of_cover E rho hrec mono crossing services writes
      hready hphase hQ hexact
      hu hlt le_rfl hx htg hFQe hcov hFQe hQb hne
  · have he : q = r * p.R := le_antisymm hqr hge
    subst he
    have hji := fgsa_tick_unique E rho hS hjq htg
    subst hji
    exact opening_gateService_of_fastWrite E rho hS htg hQnd

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1100–1144, H.22:3207–3216; plan H-GATE §2.3 (exact conclusion).
DC: INTENTIONAL the H-GATE supplier with D = Qfg, on the actual post-clock full domain of
the opening read. The clock does not change the FG store (`opening_domain_clock`).
GateService at rR and domain retention are conclusions, never premises. RQCOrigin is not
needed. -/
theorem later_opening_gateService_domain [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (services : OpeningServiceScopes E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime r)).st
    ∃ D : FGBlock (Fin p.n),
      Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x (eraseFG D) ∧
      D ∈ domainR p st (treeT p st) ∧
      FGBlock.Preceq Qfg D ∧
      (frameR p st).lo ≤ (heightView p D).h := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro st
  obtain ⟨hserv, hdom, hlo⟩ := later_opening_service E rho hrec mono crossing services writes
    hready hQ hQfg
    hexact hu hqr hphase hx ht
  have hclock := opening_domain_clock (c := c) (V2.D.Run.stateBefore E rho i x) (p.actionTime r)
  refine ⟨Qfg, hQfg ▸ hserv, ?_, KitFG.preceq_refl _, ?_⟩
  · change Qfg ∈ domainR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime r)).st (treeT p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
        (p.actionTime r)).st)
    rw [hclock.1]
    exact hdom
  · change (frameR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime r)).st).lo ≤ _
    rw [hclock.2]
    exact hlo

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2 S1, H.9:1100–1144; plan H-GATE §2.3 (opening transfer), §3B, gap 3.
DC: INTENTIONAL for q < rR, every honest HEAD of the opening label rR covers Q (TPerm S1
from the exact fast write; the HEAD v_(q+1) before d_q is included), and every honest
opening tick has fresh gate service for Q itself and saves Q in its fresh fast set. -/
theorem opening_transfer [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (services : OpeningServiceScopes E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q < r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    (∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z (r * p.R) = some K →
      Block.Preceq Q K) ∧
    ∀ i x, x ∈ rho.honest → rho.events[i]? = some (.tick x (p.actionTime r)) →
      Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x Q ∧
      Q ∈ (fastWriteAt ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
        (p.actionTime r)).st (r * p.R)).getD [] := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hqI : (q : Int) + 1 ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hgq : SA.gateTime p.toParams q ≤ p.actionTime r := by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith
  have hvs : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith
  refine ⟨fun z hz K hK => opening_heads_cover E rho hrec mono crossing services writes hready
    hphase
    hexact hu hgq hz hqr hvs z hz K hK, ?_⟩
  intro i x hx ht
  have htg : IsGateTick p c rho i x (r * p.R) := ht
  have hD := (later_opening_service E rho hrec mono crossing services writes hready hQ hQfg
    hexact hu
    hqr.le hphase hx ht).1
  have hcut : E.t_GST ≤ slotStartZ p ((r * p.R : Nat) : Int) := by
    change E.t_GST ≤ 4 * p.Δ * ((r * p.R : Nat) : Int)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith
  have enabled := healing_gate_enabled_of_recovery hrec.toRecovery₂ hx htg hphase.2.1 hcut
  exact ⟨hD, exactService_fastWrite_of_gateService E rho hS i x (r * p.R) Q htg enabled hD⟩

end AvailableChain.FGSA.Run
end

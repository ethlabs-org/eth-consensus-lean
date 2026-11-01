module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceBody
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningTicks

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! H-GATE consumers at one opening (plan fgsa-s5-hgate-hcommon §3E, §3F step 1, §4
height-one handoff; brief S5 H-GATE O5). H-GATE and the inline SO-COV coverage body
`rowCoverage` give OpeningCovered at every later opening of the phase. At frontier m = 1
the first opening also has one common entry, by the plateau with genesis. The inline body
has the exact statement form of `rowPermission_covered` (Foundations/RowPermission.lean);
Assembly supplies it. This file does not prove a first rise or the M5 bootstrap. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1131–1144 (OpeningCovered), 22 SO-COV; plan H-GATE §3E.
DC: INTENTIONAL every later opening of the phase is covered. At each honest opening read,
H-GATE serves Q and the selector returns a source K above Qfg
(`later_opening_source_extends`). K is in the full tree, its height is at least the floor
of Qfg, and the node is awake after GST (Recovery₂.awake). The inline SO-COV body then
gives the earlier-or-current signed row. -/
theorem later_opening_covered [Fintype V] (E : Generic.Env V)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    OpeningCovered p c E rho r Q := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hvh : p.actionTime r ≤ rho.horizon := hphase.2.1
  have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hpq : SA.proposalTime p.toParams q ≤ p.actionTime r := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith
  intro x hx
  have hawake := hrec.awake x hx (p.actionTime r) (hGST.trans (hu.trans hpq)) hvh
  obtain ⟨i, ht⟩ := opening_action_tick E rho hS hrec.base.delta hx r hvh hawake
  let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)
  have hnd : postClock E rho x (p.actionTime r) = some nd := opening_postClock_of_tick E rho hS ht
  obtain ⟨K, hsrc, hQK⟩ := later_opening_source_extends E rho hrec mono crossing services
    writes hready hQ
    hQfg hexact hu hqr hphase hx ht
  have hK : actionSourceFG p c E rho x r = some (some K) := by
    rw [actionSourceFG_def, hnd]
    exact congrArg some hsrc
  obtain ⟨_, hdom, _, _⟩ := opening_source_body E rho hS ht hK
  have hfull : K ∈ FGSA.fullTree p nd.st := hdom
  obtain ⟨_, _, hlo⟩ := later_opening_service E rho hrec mono crossing services writes hready hQ
    hQfg
    hexact hu hqr hphase hx ht
  have hband : (FGSA.controls p nd.st).lo ≤ (heightView p K).h := by
    change (frameR p nd.st).lo ≤ _
    rw [(opening_domain_clock (c := c) (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).2]
    exact hlo.trans ((fgCertificateLaws p).height.h_mono hQK)
  obtain ⟨j, rSent, a, hr, hrow, hentry⟩ := rowCoverage x hx r nd hnd K hK hfull hband hawake
  exact ⟨K, nd, j, rSent, a, hnd, hK, hfull, hQfg ▸ eraseFG_preceq hQK, hr, hrow, hentry⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1131–1144 (first opening); plan H-GATE §3F step 1.
DC: SAME arithmetic as the private `opening_time_bound` of Shared/OpeningSource, reproduced
in the owning lane. For the first opening r with q ≤ rR, rR < q + R. -/
theorem opening_first_time_bound (q r : Nat)
    (hle : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r') :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ := by
  have hlt : r * p.R < q + p.R := by
    by_cases hz : r = 0
    · subst r; have := p.RLarge; omega
    · have hn : ¬ q ≤ (r - 1) * p.R := by intro h; have := hfirst (r - 1) h; omega
      have he : r * p.R = (r - 1) * p.R + p.R := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
  have ha : (q : Time) ≤ (r * p.R : Nat) := by exact_mod_cast hle
  have hb : ((r * p.R : Nat) : Time) ≤ (q : Time) + (p.R : Time) - 1 := by
    have hc : r * p.R + 1 ≤ q + p.R := hlt
    exact_mod_cast (show (r * p.R : Int) ≤ (q : Int) + (p.R : Int) - 1 by omega)
  change 0 ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ -
    (4 * p.Δ * (q : Time) + 6 * p.Δ) ∧
    4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ -
    (4 * p.Δ * (q : Time) + 6 * p.Δ) ≤ 4 * (p.R : Time) * p.Δ - 4 * p.Δ
  have := p.deltaPos
  constructor <;> nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1140–1144, H.10 at m = 1 (21:1467–1468); plan H-GATE §4 height-one
handoff. DC: INTENTIONAL at frontier 1 every selected source of the opening has height 1
(positive height and the phase cap H = 1), and the plateau with genesis fixes its entry. -/
theorem opening_entry_one (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {u : Time} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {r : Nat}
    (hphase : PhaseInterval p c E rho u (p.actionTime r) 1 J contested)
    (hur : u ≤ p.actionTime r) :
    OpeningEntry p c E rho r 1 := by
  refine ⟨(heightView p .genesis).T_h.root, ?_⟩
  intro x K hx hK
  have hK0 := hK
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK0
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hK0; contradiction
  | some i =>
      have ht := V2.D.Run.tickIdx?_spec hi
      obtain ⟨_, hdom, _, _⟩ := opening_source_body E rho hs ht hK
      have hKT : K ∈ (storeAt p c E rho i x).fg.TF := by
        have h := ((KitFG.mem_filteredFromView _ _ _ _).mp hdom).1
        change K ∈ (FGSA.clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at h
        rwa [clock_fg] at h
      have hui : V2.D.Run.idxBefore rho u ≤ i := healing_support_idxBefore_le p c E rho hs ht hur
      have hiv : i ≤ timeIdx rho (p.actionTime r) :=
        (healing_phase_lt_timeIdx p c E rho hs ht le_rfl).le
      have hH := (hphase.2.2.2 i x hui hiv hx).1
      have hcap := healing_phase_height_le p c E rho hKT
      have hmax : (storeAt p c E rho i x).fg.h_max = 1 := hH
      have hlaws := (fgCertificateLaws p).height
      have hK1 : (heightView p K).h = 1 := le_antisymm (hmax ▸ hcap) (hlaws.one_le_h K)
      have hg := hlaws.h_mono (KitFG.genesis_preceq K)
      have hg1 : (heightView p .genesis).h = (heightView p K).h :=
        le_antisymm hg (hK1 ▸ hlaws.one_le_h _)
      exact ⟨hK1, by rw [hlaws.entry_plateau (KitFG.genesis_preceq K) hg1]⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1100–1144, H.10 at m = 1; plan H-GATE §4 height-one handoff (M5).
DC: INTENTIONAL the TCommon premises at frontier 1 give the time bounds of the first
opening, OpeningCovered (H-GATE with SO-COV) and one common entry at height 1. It does not
avoid fresh later service and retention: both come from H-GATE. It supplies no first rise,
row receipt, gap search or horizon. -/
theorem opening_height_one [Fintype V] (E : Generic.Env V)
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
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {u : Time} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q)
    (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R)
    (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r')
    (hphase : PhaseInterval p c E rho u (p.actionTime r) 1 J contested) :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
    p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ ∧
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r 1 := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  obtain ⟨h0, h1⟩ := opening_first_time_bound (p := p) q r hqr hfirst
  exact ⟨h0, h1, later_opening_covered E rho hrec mono crossing services writes rowCoverage
    hready hQ hQfg
    hexact hu hqr hphase, opening_entry_one E rho hrec.base.valid.toScheduleWellFormed hphase
    hphase.1⟩

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceOne -- shake: keep

-- Export named declarations; keep generated proof matchers private.
section

/-! TFrontier opening clauses, frontier plan §3.1 step 8; brief H-FRONT-OPEN.
The cap is closed at v. The initial phase need not continue to the opening.
HG.1 supplies fresh service at strict later openings. The initial ExactService
supplies the gate when q = rR. Full T_h equality follows from the height plateau.
INLINE rowCoverage is supplied by rowPermission_covered at Assembly. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Frontier plan §3.1 step 8. DC: INTENTIONAL the single later-opening input.
HG.1 / frontier_service will produce this fresh GateService for Q itself at
each honest opening tick. Its type is the service consumed by
openingSource_candidate_of_gateService and produced by
opening_gateService_of_cover / later_opening_service. It has no domain,
OpeningCovered, OpeningEntry, or entry-equality field. -/
public def FrontierOpeningServed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (r : Nat) (Q : Block) : Prop :=
  ∀ i x, x ∈ rho.honest → rho.events[i]? = some (.tick x (p.actionTime r)) →
    Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x Q

/-- Introduction rule for `FrontierOpeningServed`: its body is not exported from this
module, so HG.1 producers build the predicate through this theorem. -/
public theorem frontierOpeningServed_intro (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block}
    (h : ∀ i x, x ∈ rho.honest → rho.events[i]? = some (.tick x (p.actionTime r)) →
      Gen.AC.Duty.GateService (fgsaAC E rho) i (r * p.R) x Q) :
    FrontierOpeningServed E rho r Q :=
  h

omit [DecidableEq V] in
/-- Frontier plan §4 opening cuts. DC: SAME the opening is strictly after u,
so its read lies between the inclusive cap cuts, including a_r = v. -/
public theorem frontier_open_indices (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {u v : Time} {q r i : Nat} {x : V}
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hav : p.actionTime r ≤ v) (ht : rho.events[i]? = some (.tick x (p.actionTime r))) :
    timeIdx rho u ≤ i ∧ i ≤ timeIdx rho v := by
  have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hd := p.deltaPos
  have hpa : SA.proposalTime p.toParams q < p.actionTime r := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith
  have hui := healing_support_idxBefore_le p c E rho hs ht
    (Int.add_one_le_iff.mpr (hu.trans_lt hpa))
  refine ⟨le_trans ?_ hui, (healing_phase_lt_timeIdx p c E rho hs ht hav).le⟩
  change (rho.events.filter (fun e => decide (e.time ≤ u))).length ≤
    (rho.events.filter (fun e => decide (e.time < u + 1))).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (Int.lt_add_one_iff.mpr (of_decide_eq_true he)))

/-- Frontier plan §3.1 step 8. DC: INTENTIONAL Qfg is retained at this opening
only. ExactService stores it at q; cumulative storage and CAP give local H = m.
RXing then puts the current F and Z below Qfg, even if J or contest changed.
No phase through a_r and no general same-frontier retention port is required. -/
public theorem frontier_open_domain [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {u v : Time} {m q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R) (hav : p.actionTime r ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime r))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    Qfg ∈ domainR p st (treeT p st) ∧ (frameR p st).lo ≤ m := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro st
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hga : SA.gateTime p.toParams q ≤ p.actionTime r := by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith
  have hqh := hga.trans (hav.trans hvh)
  have hReader := healing_recovery_gate_reader hrec hx (hGST.trans hu) hqh
  obtain ⟨nd, hnd, hwrite⟩ := (hexact.2 hqh x hx hReader).2.2.1
  have htime : ((4 * q + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams q := by
    change ((4 * q + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨jq, hjq, _⟩ := fgsa_tick_total E rho hS hrec.base.delta x hx (4 * q + 6)
    (htime ▸ hqh) (by simpa only [htime] using hReader.2.1)
  rw [htime] at hjq
  rw [(healing_support_gate_reads p c E rho hS hjq).2] at hnd
  have he := Option.some.inj hnd
  subst he
  have hji : jq ≤ i := by
    rcases lt_or_eq_of_le hqr with hlt | heq
    · apply le_of_lt
      apply repair_idx_lt E rho hS hjq ht
      have hltI : (q : Int) < ((r * p.R : Nat) : Int) := by exact_mod_cast hlt
      change 4 * p.Δ * (q : Int) + 6 * p.Δ < 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
      nlinarith
    · subst heq
      exact (fgsa_tick_unique E rho hS hjq ht).le
  obtain ⟨_, hQT, _⟩ := opening_exact_stored E rho hS hQfg hjq hwrite hji
  obtain ⟨hui, hiv⟩ := frontier_open_indices E rho hS hu hqr hav ht
  have hH : (R_at p c E rho i x).H = m :=
    le_antisymm (hcap i x hui hiv hx) (hh ▸ healing_phase_height_le p c E rho hQT)
  obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hQT (hh.trans hH.symm)
  have hlo : (frameR p (storeAt p c E rho i x)).lo ≤ m := by
    change (if (R_at p c E rho i x).contest then (R_at p c E rho i x).H
      else (R_at p c E rho i x).H - 1) ≤ m
    rw [hH]
    split <;> (simp only [Height] at *; omega)
  have hdom : Qfg ∈ domainR p (storeAt p c E rho i x) (treeT p (storeAt p c E rho i x)) :=
    (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hQT, hF, hZ, Qfg, hQT, KitFG.preceq_refl _, hh ▸ hlo⟩
  have hc := opening_domain_clock (c := c) (V2.D.Run.stateBefore E rho i x) (p.actionTime r)
  exact ⟨hc.1.symm ▸ hdom, hc.2.symm ▸ hlo⟩

/-- Frontier plan §4 source identity. DC: SAME a same-height descendant has
the same full entry block. This does not require equality of the source bodies. -/
public theorem frontier_open_plateau {m : Nat} {Qfg K : FGBlock (Fin p.n)}
    (hh : (heightView p Qfg).h = m) (hQK : FGBlock.Preceq Qfg K)
    (hcap : (heightView p K).h ≤ m) :
    (heightView p K).h = m ∧ (heightView p K).T_h = (heightView p Qfg).T_h := by
  have hlaws := (fgCertificateLaws p).height
  have he : (heightView p K).h = m := le_antisymm hcap (hh ▸ hlaws.h_mono hQK)
  exact ⟨he, (hlaws.entry_plateau hQK (hh.trans he.symm)).symm⟩

section Coverage
variable [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec crossing rowCoverage

/-- Frontier plan §3.1 step 8; H-FRONT-OPEN F2 core. DC: INTENTIONAL fresh service
gives candidate membership. The cap gives full-domain membership and source height;
the selector gives Qfg ⪯ K. INLINE rowCoverage gives an earlier-or-current row. -/
public theorem frontier_open_of_served
    {u v : Time} {m q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q ≤ r * p.R) (hav : p.actionTime r ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hserved : FrontierOpeningServed E rho r Q) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hcut : E.t_GST ≤ slotStartZ p ((r * p.R : Nat) : Int) := by
    have hqrI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
    change E.t_GST ≤ 4 * p.Δ * ((r * p.R : Nat) : Int)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hsources : ∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (heightView p K).h ≤ m := by
    intro x K hx hK
    obtain ⟨i, ht⟩ := common_source_tick E rho hK
    obtain ⟨hdom, _⟩ := frontier_open_domain E rho hrec crossing hready hQfg hh hexact hu hqr hav
      hvh
      hcap hx ht
    have hcand := openingSource_candidate_of_gateService E rho hS i x r Q ht
      (healing_gate_enabled_of_recovery hrec.toRecovery₂ hx ht (hav.trans hvh) hcut)
      (hserved i x hx ht)
    obtain ⟨L, hL, hQL⟩ := openingSource_extends_served E rho i x r Qfg hdom (hQfg ▸ hcand)
    obtain ⟨hsrc, hKdom, _, _⟩ := opening_source_body E rho hS ht hK
    have he : L = K := Option.some.inj (hL.symm.trans hsrc)
    have hKT : K ∈ (storeAt p c E rho i x).fg.TF := by
      have h := ((KitFG.mem_filteredFromView _ _ _ _).mp hKdom).1
      change K ∈ (FGSA.clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at h
      rwa [clock_fg] at h
    obtain ⟨hui, hiv⟩ := frontier_open_indices E rho hS hu hqr hav ht
    exact ⟨he ▸ hQL, (healing_phase_height_le p c E rho hKT).trans (hcap i x hui hiv hx)⟩
  refine ⟨?_, common_entry_of_plateau E rho r m Qfg hh hsources, ?_⟩
  · intro x hx
    have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
    have hpa : SA.proposalTime p.toParams q ≤ p.actionTime r := by
      have hd := p.deltaPos
      change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
      nlinarith
    have hawake := hrec.awake x hx (p.actionTime r) (hGST.trans (hu.trans hpa)) (hav.trans hvh)
    obtain ⟨i, ht⟩ := opening_action_tick E rho hS hrec.base.delta hx r (hav.trans hvh) hawake
    let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)
    have hnd := opening_postClock_of_tick E rho hS ht
    obtain ⟨hdom, hlo⟩ := frontier_open_domain E rho hrec crossing hready hQfg hh hexact
      hu hqr hav hvh
      hcap hx ht
    have hcand := openingSource_candidate_of_gateService E rho hS i x r Q ht
      (healing_gate_enabled_of_recovery hrec.toRecovery₂ hx ht (hav.trans hvh) hcut)
      (hserved i x hx ht)
    obtain ⟨K, hsrc, hQK⟩ := openingSource_extends_served E rho i x r Qfg hdom (hQfg ▸ hcand)
    have hK : actionSourceFG p c E rho x r = some (some K) := by
      rw [actionSourceFG_def, hnd]
      exact congrArg some hsrc
    obtain ⟨_, hfull, _, _⟩ := opening_source_body E rho hS ht hK
    have hband : (FGSA.controls p nd.st).lo ≤ (heightView p K).h :=
      hlo.trans (hh ▸ (fgCertificateLaws p).height.h_mono hQK)
    obtain ⟨j, rSent, a, hr, hrow, hentry⟩ := rowCoverage x hx r nd hnd K hK hfull hband hawake
    exact ⟨K, nd, j, rSent, a, hnd, hK, hfull, hQfg ▸ eraseFG_preceq hQK, hr, hrow, hentry⟩
  · intro x K hx hK
    obtain ⟨hQK, hcapK⟩ := hsources x K hx hK
    exact (frontier_open_plateau hh hQK hcapK).2

/-- H-FRONT-OPEN F1; frontier plan §4 q = rR. DC: INTENTIONAL the initial
ExactService fast write gives GateService at the atomic gate/action clock.
No later-opening service hypothesis is needed. -/
public theorem frontier_open_q_eq
    {u v : Time} {m q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q = r * p.R) (hav : p.actionTime r ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  apply frontier_open_of_served E rho hrec crossing rowCoverage hready hQfg hh hexact hu hqr.le
    hav hvh hcap
  intro i x hx ht
  have hS := hrec.base.valid.toScheduleWellFormed
  have hqh : SA.gateTime p.toParams q ≤ rho.horizon := by
    rw [hqr]
    exact hav.trans hvh
  obtain ⟨_, _, ⟨nd, hnd, hwrite⟩, _, _⟩ := hexact.2 hqh x hx
    (healing_recovery_gate_reader hrec hx (hGST.trans hu) hqh)
  rw [hqr] at hnd
  change postClock E rho x (p.actionTime r) = some nd at hnd
  rw [opening_postClock_of_tick E rho hS ht] at hnd
  have he := Option.some.inj hnd
  subst he
  rw [hqr] at hwrite
  exact opening_gateService_of_fastWrite E rho hS ht hwrite

/-- H-FRONT-OPEN F2; frontier plan §3.1 step 8. DC: SAME strict later openings
use one FrontierOpeningServed input. CAP replaces any later phase premise. -/
public theorem frontier_open_later
    {u v : Time} {m q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQfg : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hqr : q < r * p.R) (hav : p.actionTime r ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hserved : FrontierOpeningServed E rho r Q) :
    OpeningCovered p c E rho r Q ∧ OpeningEntry p c E rho r m ∧
      (∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
        (heightView p K).T_h = (heightView p Qfg).T_h) :=
  frontier_open_of_served E rho hrec crossing rowCoverage hready hQfg hh hexact hu hqr.le
    hav hvh hcap hserved

end Coverage

/-- H-FRONT-OPEN F3; frontier plan §3.1 step 8. DC: SAME the first-opening
bound from H-COMMON. It has no run, cap, or service premise. -/
public theorem frontier_open_time (q r : Nat) (hqr : q ≤ r * p.R)
    (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r') :
    p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ :=
  (common_first_time_bound (p := p) q r hqr hfirst).2

end AvailableChain.FGSA.Run
end

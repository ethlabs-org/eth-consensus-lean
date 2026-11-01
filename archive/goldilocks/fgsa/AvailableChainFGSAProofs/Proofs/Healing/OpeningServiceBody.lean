module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningService
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryService

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! H-GATE body propagation to the next opening (plan fgsa-s5-hgate-hcommon §2.3 last
paragraph, §3F step 4, gap 4; brief S5 H-GATE O4). A block K selected by an honest source
at opening r is a fresh fast write of label rR, so it is a PhaseBody without an honest
proposal for K. In a phase through a_(r+1), every honest opening tick of r + 1 has fresh
gate service for K, and K is in the actual post-clock full domain above the floor. The
guard uses the exact-service context of Q; no second repair is charged. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Read monotonicity. DC: SAME the completed-time cut grows with time. -/
theorem opening_timeIdx_mono (rho : V2.D.Run V (fgsa p c)) {t t' : Time} (h : t ≤ t') :
    timeIdx rho t ≤ timeIdx rho t' := by
  change (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
    (rho.events.filter (fun e => decide (e.time ≤ t'))).length
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro e he
  exact decide_eq_true ((of_decide_eq_true he).trans h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.7:1003–1012 (inclusive phase reads). DC: SAME a phase restricts to
an earlier upper end that is still after its start. -/
theorem opening_phase_restrict (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v v' : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hphase : PhaseInterval p c E rho u v' m J contested) (huv : u ≤ v) (hvv : v ≤ v') :
    PhaseInterval p c E rho u v m J contested :=
  ⟨huv, hvv.trans hphase.2.1, hphase.2.2.1, fun i x hui hiv hx =>
    hphase.2.2.2 i x hui (hiv.trans (opening_timeIdx_mono rho hvv)) hx⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Spec 1327–1338 (the selected source); blueprint 21 H.4:628–650; plan H-GATE §3F step 4.
DC: INTENTIONAL the selected source of an honest opening is a fresh fast write of label rR
at the opening read, in the actual full domain and with a live lease. Its fast write is a
PhaseBody of rR; no HonestProposal for K is needed. -/
theorem opening_source_body (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {y : V} {r : Nat}
    (hj : rho.events[j]? = some (.tick y (p.actionTime r))) {K : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho y r = some (some K)) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y) (p.actionTime r)).st
    FGSA.fgSource p st = some K ∧ K ∈ domainR p st (treeT p st) ∧
      eraseFG K ∈ sourceCandidates p st ∧
      eraseFG K ∈ (fastWriteAt st (r * p.R)).getD [] := by
  intro st
  have hpost := opening_postClock_of_tick E rho hs hj
  rw [actionSourceFG_def, hpost] at hK
  have hsrc : FGSA.fgSource p st = some K := Option.some.inj hK
  have hsrc' := hsrc
  rw [fgSource_eq_jointSource] at hsrc'
  have hmem := Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hsrc').1
  have hcand : eraseFG K ∈ sourceCandidates p st := of_decide_eq_true hmem.2
  have hround : p.round (st.slot p) = r := (fgsa_action_slot_round (c := c) _ r).2
  have hfw : eraseFG K ∈ (fastWriteAt st (r * p.R)).getD [] := by
    have h := hcand
    rw [sourceCandidates_def] at h
    have hm := (Finset.mem_filter.mp h).1
    rw [hround] at hm
    exact List.mem_toFinset.mp hm
  exact ⟨hsrc, hmem.1, hcand, hfw⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9:1100–1144 (opening source), H.22:3207–3216; plan H-GATE §3E.
DC: INTENTIONAL the selected source of every honest opening at or after q extends Qfg:
H-GATE serves Q there, and the deepest selector keeps a served retained block below its
output (`openingSource_extends_served`). -/
theorem later_opening_source_extends [Fintype V] (E : Generic.Env V)
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
    {j : Nat} {y : V} (hy : y ∈ rho.honest)
    (hj : rho.events[j]? = some (.tick y (p.actionTime r))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y) (p.actionTime r)).st
    ∃ K, FGSA.fgSource p st = some K ∧ FGBlock.Preceq Qfg K := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro st
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hserv, hdom, _⟩ := later_opening_service E rho hrec mono crossing services writes
    hready hQ hQfg
    hexact hu hqr hphase hy hj
  have hcut : E.t_GST ≤ slotStartZ p ((r * p.R : Nat) : Int) := by
    have hqrI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
    change E.t_GST ≤ 4 * p.Δ * ((r * p.R : Nat) : Int)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have enabled := healing_gate_enabled_of_recovery hrec.toRecovery₂ hy hj hphase.2.1 hcut
  have hcand := openingSource_candidate_of_gateService E rho hS j y r Q hj enabled hserv
  have hclock := opening_domain_clock (c := c) (V2.D.Run.stateBefore E rho j y) (p.actionTime r)
  have hdom' : Qfg ∈ domainR p st (treeT p st) := by
    change Qfg ∈ domainR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
      (p.actionTime r)).st (treeT p ((fgsa p c).clock (V2.D.Run.stateBefore E rho j y)
        (p.actionTime r)).st)
    rw [hclock.1]
    exact hdom
  exact openingSource_extends_served E rho j y r Qfg hdom' (hQfg ▸ hcand)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.2 S1, H.3 (HEAD witness relay), H.9:1100–1144; plan H-GATE §2.3
last
paragraph, §3F step 4, gap 4. DC: INTENTIONAL the H-GATE supplier at the next opening for an
arbitrary selected body K of opening r, with D = K. K is a fast PhaseBody of rR
(`opening_source_body`), so TPerm S1 covers every honest HEAD of (r + 1)R. The HEAD relay
(`healing_support_frame_at`) puts K in every honest store at a_(r+1). K extends Qfg
(`later_opening_source_extends`), so the band and frame of Q retain K, and the guard of Q
holds at the next gate. K needs no HonestProposal, and the height of K is not used. -/
theorem next_opening_body_service [Fintype V] (E : Generic.Env V)
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
    (hphase : PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested)
    {y : V} {K : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K))
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[i]? = some (.tick x (p.actionTime (r + 1)))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime (r + 1))).st
    ∃ D : FGBlock (Fin p.n),
      Gen.AC.Duty.GateService (fgsaAC E rho) i ((r + 1) * p.R) x (eraseFG D) ∧
      D ∈ domainR p st (treeT p st) ∧
      FGBlock.Preceq K D ∧
      (frameR p st).lo ≤ (heightView p D).h := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro st
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hR := p.RLarge
  let s := (r + 1) * p.R
  have hvh : p.actionTime (r + 1) ≤ rho.horizon := hphase.2.1
  have htg : IsGateTick p c rho i x s := ht
  have hrs : r * p.R + 1 ≤ s := by
    change r * p.R + 1 ≤ (r + 1) * p.R
    rw [Nat.succ_mul]
    omega
  have hrsI : ((r * p.R : Nat) : Int) + 1 ≤ ((s : Nat) : Int) := by exact_mod_cast hrs
  have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have har : p.actionTime r ≤ p.actionTime (r + 1) := by
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((s : Nat) : Int) + 6 * p.Δ
    nlinarith
  have hpq : SA.proposalTime p.toParams q ≤ p.actionTime r := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    nlinarith
  have hphr := opening_phase_restrict E rho hphase (hu.trans hpq) har
  -- The source tick of y at a_r.
  have hktime : ((4 * (r * p.R) + 6 : Nat) : Time) * p.Δ = p.actionTime r := by
    change ((4 * (r * p.R) + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨jy, hjy, _⟩ := fgsa_tick_total E rho hS hDelta y hy (4 * (r * p.R) + 6)
    (hktime ▸ har.trans hvh)
    (hktime ▸ hrec.awake y hy (p.actionTime r) (hGST.trans (hu.trans hpq))
      (har.trans hvh))
  rw [hktime] at hjy
  obtain ⟨hsrcK, _, _, hfwK⟩ := opening_source_body E rho hS hjy hK
  obtain ⟨K', hsrcK', hQK'⟩ := later_opening_source_extends E rho hrec mono crossing
    services writes hready
    hQ hQfg hexact hu hqr hphr hy hjy
  have hKK : K' = K := Option.some.inj (hsrcK'.symm.trans hsrcK)
  have hQK : FGBlock.Preceq Qfg K := hKK ▸ hQK'
  have hjyg : IsGateTick p c rho jy y (r * p.R) := hjy
  obtain ⟨_, _, _, _, hneK, _, _⟩ := opening_fastWrite_spec E rho hS hjyg hfwK
  -- TPerm S1 for the fast body K of label rR.
  have hpost := (healing_support_gate_reads p c E rho hS hjyg).2
  have hbody : PhaseBody p c E rho (r * p.R) (eraseFG K) := ⟨y, hy, Or.inl ⟨_, hpost, hfwK⟩⟩
  have hurR : u ≤ SA.voteTime p.toParams (r * p.R) := by
    refine hu.trans ?_
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ
    nlinarith
  have hcovK := (healing_tPerm_at E rho hrec mono crossing writes
    hready hphase
    (services.permanence u (p.actionTime (r + 1)) m J contested hready hphase)
    hurR har hbody).1
  have hvs : SA.voteTime p.toParams s ≤ p.actionTime (r + 1) := by
    change 4 * p.Δ * ((s : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((s : Nat) : Int) + 6 * p.Δ
    linarith
  have hcov : ∀ z ∈ rho.honest, ∀ H, headAtLabel p c E rho z s = some H →
      Block.Preceq (eraseFG K) H :=
    fun z hz H hH => hcovK z s H hz hrs hvs hH
  -- The HEAD relay puts K in the store of x at a_(r+1).
  have hvsu : u ≤ SA.voteTime p.toParams s := by
    refine hurR.trans ?_
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ ≤
      4 * p.Δ * ((s : Nat) : Int) + p.Δ
    nlinarith
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hx s (hvs.trans hvh)
    (hrec.awake x hx _ (hGST.trans hvsu) (hvs.trans hvh))
  have hhl : headAtLabel p c E rho x s = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz x).st (SA.voteTime p.toParams s)) s) := by
    unfold headAtLabel
    rw [opening_postClock_of_tick E rho hS hjz]
    rfl
  have hev : SA.voteTime p.toParams s + p.Δ ≤ p.actionTime (r + 1) := by
    change 4 * p.Δ * ((s : Nat) : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((s : Nat) : Int) + 6 * p.Δ
    linarith
  have hgsu : SA.proposalTime p.toParams q ≤ p.actionTime (r + 1) := hpq.trans har
  have hui : V2.D.Run.idxBefore rho u ≤ i :=
    healing_support_idxBefore_le p c E rho hS ht (hu.trans hgsu)
  have hiv : i ≤ timeIdx rho (p.actionTime (r + 1)) :=
    (healing_phase_lt_timeIdx p c E rho hS ht le_rfl).le
  have hSourceCut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hqs : q + 1 ≤ s := by
      dsimp [s]
      rw [Nat.add_mul, Nat.one_mul]
      have hR := p.RLarge
      omega
    have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hSourceJoined := healing_vote_joined_of_recovery hrec.toRecovery₂ hx hjz
    (hvs.trans hvh) hSourceCut
  have hReadJoined : joinedNow p (clock p (storeAt p c E rho i x)
      (p.actionTime (r + 1))) = true := by
    apply healing_recovery_joinedNow hrec hx ht hvh
    have hslot : p.slotOf (p.actionTime (r + 1)) = s + 1 :=
      (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
        (fgsa_gate_slot (c := c) _ s)
    simp only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    have hqs : (q : Int) ≤ (s : Int) := by
      have hRS : r * p.R ≤ (r + 1) * p.R := Nat.mul_le_mul_right p.R (Nat.le_succ r)
      exact_mod_cast hqr.trans hRS
    change E.t_GST ≤ 4 * p.Δ * (s : Int)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  obtain ⟨W, hW, hKW, _⟩ := healing_support_frame_at (hroots := hrec.base.receiptIdealization)
    E rho (fun _ => mono) crossing hE hDelta hrec.sync
    hGST hphase hvsu hev hx hjz x
    (healing_carriers_cut_at p c E rho hrec hSourceCut
      (healing_selected_carriers_recovery E rho hrec s i x (p.actionTime (r + 1)))
      hx ht hev jz x hx hjz)
    (hcov x hx _ hhl) hx
    (healing_support_idxBefore_le p c E rho hS ht hev) hui hiv
  have hinv := cstoreInv_stateBefore E rho i x
  have hKT : K ∈ (storeAt p c E rho i x).fg.TF := by
    obtain ⟨C, hC, he⟩ := eraseFG_ancestor_mem hinv.fg.closed hW hKW
    exact (eraseFG_injective he) ▸ hC
  have hQT : Qfg ∈ (storeAt p c E rho i x).fg.TF := by
    obtain ⟨C, hC, he⟩ := eraseFG_ancestor_mem hinv.fg.closed hKT (eraseFG_preceq hQK)
    exact (eraseFG_injective he) ▸ hC
  -- Retention of K and Q in the frame of x.
  have hband := opening_proposal_band E rho hS crossing hphase hQ hQfg hu hgsu
  obtain ⟨hdom, hFK, hlo⟩ := opening_domain_of_band E rho crossing hphase hband hx hui hiv
    hQK hKT
  obtain ⟨_, hFQ, _⟩ := opening_domain_of_band E rho crossing hphase hband hx hui hiv
    (KitFG.preceq_refl Qfg) hQT
  have hFQe : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q :=
    hQfg ▸ eraseFG_preceq hFQ
  have hqs : q < s := by omega
  have hserv := opening_gateService_of_cover E rho hrec mono crossing services writes hready
    hphase hQ
    hexact hu hqs le_rfl hx htg hFQe hcov (eraseFG_preceq hFK)
    ((hinv.baseTree _).mpr ⟨K, hKT, rfl⟩) hneK
  have hclock := opening_domain_clock (c := c) (V2.D.Run.stateBefore E rho i x)
    (p.actionTime (r + 1))
  refine ⟨K, hserv, ?_, KitFG.preceq_refl _, ?_⟩
  · change K ∈ domainR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime (r + 1))).st (treeT p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
        (p.actionTime (r + 1))).st)
    rw [hclock.1]
    exact hdom
  · change (frameR p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (p.actionTime (r + 1))).st).lo ≤ _
    rw [hclock.2]
    exact hlo

end AvailableChain.FGSA.Run
end

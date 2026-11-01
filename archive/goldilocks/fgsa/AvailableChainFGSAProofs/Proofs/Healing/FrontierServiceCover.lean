module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierRead
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceGate -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceGate

public section

/-! HG.1 covering gate service at any later label (blueprint 21:1551–1583).
This is the capped version of H-GATE. It keeps the raw-result guard and the pending
write cases. It does not require an honest proposer at the later label.
INLINE writes: `fgsa_leaseOrigins_lastWrite`, discharged at Assembly. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1551–1569; plan §3.1 steps 6 and 8.
DC: INTENTIONAL the whole raw result passes the guard under the cap.
H-GATE's fixed-phase transfers are replaced by the capped fast and slow transfers. -/
theorem frontier_gate_guard_of_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hRead : FrontierReadScope E rho q v)
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hqs : q < s) (hsv : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q) :
    ∀ C, (fgsaAC E rho).raw i s x = some C →
      ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C := by
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hScope := frontier_repair_gate_scope E rho hRead hready hu hqs hsv
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
  have hgq : SA.gateTime p.toParams q ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith
  have hvq : u ≤ SA.voteTime p.toParams q := by
    refine hu.trans ?_
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := hgst.trans hvq
  have hvqs : SA.voteTime p.toParams q ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := hgstq.trans hvqs
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hsh : SA.gateTime p.toParams s ≤ rho.horizon := hsv.trans hvh
  have hcovQ := frontier_Q_heads E rho hrec mono crossing writes hgst hErase hHeight hexact
    (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hRead.seed hu hphase hqv hvh
      hcap s (Nat.succ_le_of_lt hqs) hvs
  obtain ⟨hgr, ⟨jq, ⟨hjqt, _⟩, _⟩, ⟨ndq, hndq, hQw⟩, _, _⟩ :=
    hexact.2 (hgq.trans hvh) x hx ((frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) x
      hx)
  have hQw' : Q ∈ (fastWriteAt ((fgsa p c).clock (rho.stateBefore E jq x)
      (SA.gateTime p.toParams q)).st q).getD [] := by
    have hpost := (healing_support_gate_reads p c E rho hS hjqt).2
    have he := Option.some.inj (hndq.symm.trans hpost)
    exact he ▸ hQw
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  have hrawEq : (fgsaAC E rho).raw i s x = SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F)
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s := by
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F) u s) hv
    exact he.symm
  intro C hC
  -- A block that every honest HEAD of label s covers, above F, is below C.
  have hcoverC (b : Block)
      (hcb : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq b K)
      (hFb : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) b) : Block.Preceq b C := by
    obtain ⟨C', hC', hbC'⟩ := healing_support_gate_cover E rho hrec hgsts hsh hcb ht
      (frontier_gate_scope_of_cover E rho hrec hScope hx ht hcb hFb)
      (by rw [clockPre_fg]; exact hFb)
    rw [clockPre_fg] at hC'
    have he := Option.some.inj ((hC.symm.trans hrawEq).trans hC')
    subst he
    exact hbC'
  have hQC : Block.Preceq Q C := hcoverC Q hcovQ hFQ
  have hbelowQ {b : Block} (hb : Block.Preceq b Q) : Block.Compatible b C :=
    Bool.or_eq_true_iff.mpr (Or.inl (block_preceq_trans hb hQC))
  intro lease hl
  rw [← hv] at hl
  have hl' : lease ∈ (storeAt p c E rho i x).base.obligations :=
    (clockPre_obligations_sublist p _ _).subset hl
  obtain ⟨j, hji, w, Bw, htj, hpass, hres, hbB, hkey, hdl, _, _⟩ := writes i x lease hl'
  change Block.Compatible lease.1 C
  have hwt : SA.gateTime p.toParams w < SA.gateTime p.toParams s :=
    fgsa_tick_time_strict E rho hS htj ht hji
  have hwsI : (w : Int) < (s : Int) := by
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hwt
    nlinarith
  rcases lt_trichotomy w q with hwq | hwq | hwq
  · -- An old write: the q_(q+1) release (G5), then the slot bound of the write gate.
    have hwqI : (w : Int) + 1 ≤ (q : Int) := by exact_mod_cast hwq
    have hq1v : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
      change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
      push_cast
      linarith
    have hawake := hrec.awake x hx (SA.voteTime p.toParams (q + 1)) (by
      apply hgst.trans (hu.trans _)
      change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos]) ((hq1v.trans hgq).trans hvh)
    obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hx (q + 1)
      ((hq1v.trans hgq).trans hvh) hawake
    have hjq : j < iq := by
      apply repair_idx_lt E rho hS htj hiq
      change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
      push_cast
      nlinarith
    have hqi : iq < i := by
      apply repair_idx_lt E rho hS hiq ht
      change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      nlinarith
    have hkeep := healing_lease_persist E rho hS htj (Nat.lt_succ_of_lt hjq)
      (Nat.succ_le_of_lt hqi) lease hdl hl'
    have hpost : storeAt p c E rho (iq + 1) x =
        FGSA.clock p (storeAt p c E rho iq x) (SA.voteTime p.toParams (q + 1)) := by
      change (V2.D.Run.stateBefore E rho (iq + 1) x).st = _
      rw [V2.D.Run.stateBefore_succ E rho hiq]
      simp only [V2.D.World.step, Function.update_self]
      exact tick_st (c := c) E rho _ x _
    rw [hpost] at hkeep
    have hjqi : jq ≤ i := by
      apply le_of_lt
      apply repair_idx_lt E rho hS hjqt ht
      change 4 * p.Δ * (q : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
      nlinarith
    have hFiq : Block.Preceq (eraseFG (storeAt p c E rho iq x).fg.F) Q :=
      block_preceq_trans (eraseFG_preceq (mono iq i x hx hqi.le).1) hFQ
    obtain ⟨_, _, _, _, _, _, hτ⟩ := opening_fastWrite_spec E rho hS hjqt hQw'
    have hvdq : SA.voteTime p.toParams q + E.Δ ≤ SA.gateTime p.toParams q := by
      rw [hDelta]
      change 4 * p.Δ * (q : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
      linarith
    have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
      hrec.sync (fgsaDelay_nonrow E.Δ _) hgstq hvdq (hgq.trans hvh)
    have hcq := healing_support_release_compat (hroots := hrec.base.receiptIdealization)
      E rho hE hDelta q hSync hx hx hjqt hiq
      ((hRead.seed x hx).first jq iq x hx hjqt hiq (by
        apply le_trans ?_ hqv
        change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
        push_cast; linarith [p.deltaPos])
        (healing_scope_enabled_gate hrec hx hjqt (hgst.trans hu) (hqv.trans hvh))
        (healing_recovery_joined E rho hrec hx (by
          change E.t_GST ≤ 4 * p.Δ * (((q + 1 : Nat) : Int) - 1)
          have hc := hgst.trans hu
          change E.t_GST ≤ 4 * p.Δ * (q : Int) at hc
          simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hc)
          (hgstq.trans (by
            change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
            push_cast; linarith [p.deltaPos])) (by
              apply le_trans ?_ (hqv.trans hvh)
              change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤
                4 * p.Δ * (q : Int) + 6 * p.Δ
              push_cast; linarith [p.deltaPos]))) hτ
      hFiq lease hkeep
    obtain ⟨hBm, hBs⟩ := opening_result_slot E rho hS htj hres
    have hQs := repair_proposal_slot E rho hQ
    rcases Bool.or_eq_true_iff.mp hcq with hlQ | hQl
    · exact hbelowQ hlQ
    · by_cases heq : Q = Bw
      · subst heq
        exact hbelowQ hbB
      · exfalso
        have hlt := repair_stored_slot_lt E rho hE j x hBm (block_preceq_trans hQl hbB) heq
        rw [hQs] at hlt
        have key : ∀ a b d : Nat, b < a → a < d → d ≤ b + 1 → False := by
          intro a b d h1 h2 h3
          omega
        exact key q w Bw.slot hwq hlt hBs
  · -- The write gate of label q: its exact result is Q.
    subst hwq
    have hres' : gateResult p c E rho x w = some (some Bw) :=
      (gateResultAt_eq_gateResult p c E rho hS htj).symm.trans hres
    have hBQ : Bw = Q := Option.some.inj (Option.some.inj (hres'.symm.trans hgr))
    subst hBQ
    exact hbelowQ hbB
  · -- A later write gate w with q < w < s.
    obtain ⟨_, _, _, _, hcase⟩ := healing_support_key_cases p hkey
    have hwqI : (q : Int) + 1 ≤ (w : Int) := by exact_mod_cast hwq
    have hwv : SA.gateTime p.toParams w ≤ v := hwt.le.trans hsv
    have huw : u ≤ SA.voteTime p.toParams w := by
      refine hvq.trans ?_
      change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      nlinarith
    have hbody : PhaseBody p c E rho w lease.1 ∨ Block.Preceq lease.1 Q := by
      by_cases hwin : q + p.k ≤ w + 1
      · left
        refine healing_support_phaseBody_of_write p c E rho hS hx htj hpass hres hkey ?_
        refine hgstq.trans ?_
        change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * ((w + 1 - p.k : Nat) : Int) + p.Δ
        have h1 : (q : Int) ≤ ((w + 1 - p.k : Nat) : Int) := by
          exact_mod_cast Nat.le_sub_of_add_le hwin
        nlinarith
      · rcases hcase with hfast | hslow
        · exact Or.inl (opening_phaseBody_of_fast_key E rho hS hx htj hpass hres hkey hfast)
        · -- A slow key without its window: the slow test reads the saved result of q.
          right
          unfold GridCO.slowEligible at hslow
          have hall := (Bool.and_eq_true_iff.mp hslow).2
          have hidx : w - q - 1 ∈ List.range (p.toParams.engine.m - 1) := by
            apply List.mem_range.mpr
            change w - q - 1 < p.k - 1
            have key : ∀ a b k : Nat, b < a → ¬ (b + k ≤ a + 1) → a - b - 1 < k - 1 := by
              intro a b k h1 h2
              omega
            exact key w q p.k hwq hwin
          have hj := List.all_eq_true.mp hall _ hidx
          have hwq' : w - (w - q - 1 + 1) = q := by
            have key : ∀ a b : Nat, b < a → a - (a - b - 1 + 1) = b := by
              intro a b h
              omega
            exact key w q hwq
          rw [hwq'] at hj
          have hsg : GridCO.savedGenuine (actView (clockPre p (storeAt p c E rho j x)
              (SA.gateTime p.toParams w))) q =
              GridCO.savedGenuine (storeAt p c E rho j x).base q := by
            unfold GridCO.savedGenuine
            change ((clockPre p (storeAt p c E rho j x)
              (SA.gateTime p.toParams w)).base.genuine.find? _).map _ = _
            rw [clockPre_genuine]
          rw [hsg] at hj
          cases hsv' : GridCO.savedGenuine (storeAt p c E rho j x).base q with
          | none =>
            rw [hsv'] at hj
            exact absurd hj Bool.false_ne_true
          | some o =>
            cases o with
            | none =>
              rw [hsv'] at hj
              exact absurd hj Bool.false_ne_true
            | some C' =>
              rw [hsv'] at hj
              obtain ⟨_, _, _, hgC⟩ := healing_saved_origin_on E rho hS hsv'
              have hCQ : C' = Q := Option.some.inj (Option.some.inj (hgC.symm.trans hgr))
              subst hCQ
              exact hj
    rcases hbody with hbody | hlQ
    · have hQw : ∀ l, w ≤ l → SA.voteTime p.toParams l ≤ v → ∀ z ∈ rho.honest, ∀ K,
          headAtLabel p c E rho z l = some K → Block.Preceq (eraseFG Qfg) K := by
        intro l hl hlv z hz K hK
        rw [hErase]
        exact frontier_Q_heads E rho hrec mono crossing writes hgst hErase hHeight hexact
          (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hRead.seed hu hphase hqv
            hvh hcap l (hwq.trans_le hl) hlv z hz K hK
      have hcb : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
          Block.Preceq lease.1 K := by
        obtain ⟨z, hz, hfast | hslow⟩ := hbody
        · obtain ⟨nd, hnd, hB⟩ := hfast
          exact frontier_fast_heads E rho hrec mono crossing writes hHeight hvh hcap
            (hgst.trans huw) hwv hQw hz hnd hB
            (hRead.fast w (Nat.succ_le_of_lt hwq) hwv z nd lease.1 hz hnd hB)
            (healing_gate_cut_of_batch_cut E w
              (healing_ready_vote_cutoff E (hready.trans huw))) s (by exact_mod_cast hwsI) hvs
        · obtain ⟨hwindow, st, Cw, jw, hin, hgrw, _, hBCw, hslow, hjw, _⟩ := hslow
          exact frontier_slow_heads E rho hrec mono crossing writes hHeight hvh hcap
            (hgst.trans huw) hwv hQw hz hwindow hin hgrw hBCw hslow hjw
            (hRead.slow w (Nat.succ_le_of_lt hwq) hwv hwindow z st Cw lease.1 jw hz
              hin hgrw hBCw hslow hjw)
            (healing_gate_cut_of_batch_cut E w
              (healing_ready_vote_cutoff E (hready.trans huw))) s (by exact_mod_cast hwsI) hvs
      have hawake := hrec.awake x hx (SA.voteTime p.toParams s) hgsts (hvs.trans hvh)
      obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hx s
        (hvs.trans hvh) hawake
      have hhl : headAtLabel p c E rho x s = some (headVote p (FGSA.clock p
          (V2.D.Run.stateBefore E rho jz x).st (SA.voteTime p.toParams s)) s) := by
        unfold headAtLabel
        rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjz]
        rfl
      rcases block_preceq_total_of_common (hcb x hx _ hhl) (hcovQ x hx _ hhl) with hlQ | hQl
      · exact hbelowQ hlQ
      · exact Bool.or_eq_true_iff.mpr
          (Or.inl (hcoverC lease.1 hcb (block_preceq_trans hFQ hQl)))
    · exact hbelowQ hlQ

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1551–1583; plan §3.1 step 8.
DC: INTENTIONAL H-GATE covering service under a capped frontier, at any later label. -/
theorem frontier_opening_gateService_of_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hRead : FrontierReadScope E rho q v)
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hqs : q < s) (hsv : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i s x Q := by
  have hgst : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hScope := frontier_repair_gate_scope E rho hRead hready hu hqs hsv
  have hd := p.deltaPos
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := by
    refine hgst.trans (hu.trans ?_)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hqsI : (q : Int) < (s : Int) := by exact_mod_cast hqs
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hgstq.trans ?_
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hsh : SA.gateTime p.toParams s ≤ rho.horizon := hsv.trans hvh
  have hcov := frontier_Q_heads E rho hrec mono crossing writes hgst hErase hHeight hexact
    (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hRead.seed hu hphase hqv hvh
      hcap s (Nat.succ_le_of_lt hqs) hvs
  obtain ⟨_, ⟨jq, ⟨hjq, _⟩, _⟩, ⟨nd, hnd, hfw⟩, _, _⟩ :=
    hexact.2 (hqv.trans hvh) x hx ((frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) x
      hx)
  rw [(healing_support_gate_reads p c E rho hS hjq).2] at hnd
  have he := Option.some.inj hnd
  subst he
  have hji : jq ≤ i := by
    apply le_of_lt
    apply repair_idx_lt E rho hS hjq ht
    change 4 * p.Δ * (q : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  obtain ⟨_, hQfg, _⟩ := opening_exact_stored E rho hS hErase hjq hfw hji
  have hFfg := frontier_F_below_all E rho crossing hx
    (hcap i x (healing_phase_lt_timeIdx p c E rho hS ht hsv).le hx)
    hx le_rfl hQfg (le_of_eq hHeight.symm)
  have hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q :=
    hErase ▸ eraseFG_preceq hFfg
  have hB : Q ∈ (storeAt p c E rho i x).base.blocks :=
    (cstoreInv_stateBefore E rho i x).baseTree Q |>.mpr ⟨Qfg, hQfg, hErase⟩
  have hne : Q ≠ .genesis := by
    rintro rfl
    have hslot := repair_proposal_slot E rho hQ
    exact hQ.1.1.ne' hslot.symm
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  obtain ⟨C, hC, hQC⟩ := healing_support_gate_cover E rho hrec hgsts hsh hcov ht
    (frontier_gate_scope_of_cover E rho hrec hScope hx ht hcov hFQ)
    (by rw [clockPre_fg]; exact hFQ)
  rw [clockPre_fg] at hC
  have hraw : (fgsaAC E rho).raw i s x = some C := by
    have he := congrArg (fun st => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F) st s) hv
    exact he.symm.trans hC
  have hτ := opening_gate_support E rho hrec hScope.cut hgsts hsh hcov hx ht
    (frontier_gate_scope_of_cover E rho hrec hScope hx ht hcov hFQ).toGateReceiptScope hFQ
  have hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s Q := by
    have he := congrArg (fun st => SA.Root.prefixSupport p.toParams st s Q) hv
    exact he ▸ hτ
  have hmem : Q ∈ ((fgsaAC E rho).gateView i x s).blocks := by
    rw [← hv]
    apply (actView_blocks _ Q).mpr
    refine ⟨?_, Bool.or_eq_true_iff.mpr (Or.inr ?_)⟩
    · rwa [(clockPre_fields p _ _).2.1]
    · rwa [clockPre_fg]
  exact fgsa_gate_of_coveringBatch E rho hS i s x Q ht
    (frontier_gate_scope_of_cover E rho hrec hScope hx ht hcov hFQ).enabled
    ⟨C, hraw, hQC⟩
    (frontier_gate_guard_of_cover E rho hrec mono crossing writes hRead hready hQ hErase hHeight
      hexact hu hphase hqv hvh hcap hqs hsv hx ht hFQ) hne hmem hsupport
    (opening_gate_level E rho i x s Q hsupport)

end AvailableChain.FGSA.Run
end

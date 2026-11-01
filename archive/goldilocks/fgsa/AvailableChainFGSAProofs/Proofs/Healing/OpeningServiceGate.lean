module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningGateRead
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningGateSupport

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers

public section

/-! H-GATE gate service at a later honest gate (plan fgsa-s5-hgate-hcommon §2.3, §3 B–C;
brief S5 H-GATE O2–O4). Fix an honest proposal Q of slot q with exact service, inside a
post-GST phase. At an honest gate of a label s > q in the phase, every live lease is
compatible with the ACTUAL raw result C of that gate (`opening_gate_guard`). A block that
every honest HEAD of label s covers then gets fresh gate service (`opening_gateService_of_cover`).
The standing hypotheses are Recovery₂, RMono, RXing and the inline last-write premise
`writes` (ruling B27, the binder of `healing_tPerm`). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Exact object services used by opening gates and their release readers. -/
structure OpeningServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    Prop where
  permanence : ∀ u v m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u v m J contested →
    SupportPermanenceServices E rho u v m J contested
  gates : ∀ i x s, x ∈ rho.honest → IsGateTick p c rho i x s → enabledGateAt p c E rho i x s →
    E.t_GST ≤ slotStartZ p ((s : Int) - 1) →
    SA.gateTime p.toParams s ≤ rho.horizon → ∀ B, GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B →
    GateReceiptScope E rho i x s
  transfers : ∀ u v m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u v m J contested → ∀ ix iy x s B,
    u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
    E.t_GST ≤ SA.voteTime p.toParams s →
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams s) (SA.gateTime p.toParams s) →
    B ∈ (fastWriteAt (clock p (storeAt p c E rho ix x)
      (SA.gateTime p.toParams s)) s).getD [] →
    x ∈ rho.honest → enabledGateAt p c E rho ix x s →
    rho.events[iy]? = some (.tick x (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho ix iy x x s

/-- Recovery produces opening services for the selected gate geometry. -/
theorem healing_opening_service_scopes_recovery [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) : OpeningServiceScopes E rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v m J contested hready hphase
    exact healing_support_permanence_recovery E rho hrec mono hready hphase
  · intro i x s hx _ hg hcut _ B hgeom
    exact healing_gate_receipt_scope_recovery E rho hrec mono
      (healing_window_of_cut E hcut).sync hx hg hgeom
  · intro u v m J contested _ _ ix iy x s B _ _ hsync _ _ hx hg hiy hj
    exact healing_first_transfer_scope_recovery E rho hrec mono hsync hx hx
      hg.1 hiy hg hj

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.2 S1 (permanence at later HEADs); plan H-GATE §3B (q < rR), gap 3.
DC: INTENTIONAL the exact service of Q at its gate is a fast PhaseBody, so TPerm S1 makes
Q a prefix of every honest HEAD of each label s > q whose vote time is in the phase. This
includes s = q + 1, whose HEAD v_(q+1) is before d_q: the phase reaches d_q. -/
theorem opening_heads_cover [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqv : SA.gateTime p.toParams q ≤ v)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} (hqs : q < s)
    (hvs : SA.voteTime p.toParams s ≤ v) :
    ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq Q K := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have huq : u ≤ SA.voteTime p.toParams q := by
    refine hu.trans ?_
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  obtain ⟨_, _, ⟨nd, hnd, hQnd⟩, _, _⟩ := hexact.2 (hqv.trans hphase.2.1) x hx
    (healing_recovery_gate_reader hrec hx (hGST.trans hu) (hqv.trans hphase.2.1))
  have hbody : PhaseBody p c E rho q Q := ⟨x, hx, Or.inl ⟨nd, hnd, hQnd⟩⟩
  have htr := healing_tPerm_at E rho hrec mono crossing writes
    hready hphase (services.permanence u v m J contested hready hphase)
    huq hqv hbody
  intro z hz K hK
  exact htr.1 z s K hz hqs hvs hK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.1 (release), H.2 S1, H.22 H3; plan H-GATE §3C (the
intervening-gate
induction, gaps 1 and 3). DC: INTENTIONAL every live lease at an honest gate of a label
s > q in the phase is compatible with the ACTUAL raw result C of that gate. The last write
of the lease is at a gate w < s. If w < q, the q_(q+1) release removes a target that
conflicts with Q, and the slot bound of the write gate puts the target below Q. If w = q,
the target is below the exact result Q. If w > q, a fast key, or a slow key with its
synchronous window, is a PhaseBody, so TPerm makes every honest HEAD of label s cover the
target; a slow key without the window reads the saved result Q of label q. Below Q ⪯ C
the target is compatible; above Q, the gate cover gives target ⪯ C. Compatibility with
Q alone is not used: two incomparable descendants of Q are not compatible. -/
theorem opening_gate_guard [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    {s : Slot} (hqs : q < s) (hsv : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q) :
    ∀ C, (fgsaAC E rho).raw i s x = some C →
      ∀ lease ∈ ((fgsaAC E rho).gateView i x s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hvh : v ≤ rho.horizon := hphase.2.1
  have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
  have hgq : SA.gateTime p.toParams q ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith
  have hvq : u ≤ SA.voteTime p.toParams q := by
    refine hu.trans ?_
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := hGST.trans hvq
  have hvqs : SA.voteTime p.toParams q ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := hgstq.trans hvqs
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hsv
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hsh : SA.gateTime p.toParams s ≤ rho.horizon := hsv.trans hvh
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hcovQ := opening_heads_cover E rho hrec mono crossing services writes
    hready hphase hexact hu hgq hx
    hqs hvs
  have hScope := services.gates i x s hx ht
    (healing_scope_enabled_gate hrec hx ht (hcut.trans (by
      change 4 * p.Δ * ((s : Int) - 1) ≤ 4 * p.Δ * (s : Int)
      linarith [p.deltaPos])) hsh) hcut hsh Q
    (healing_support_gate_geometry E rho hS hcovQ (by rwa [clockPre_fg]))
  obtain ⟨hgr, ⟨jq, ⟨hjqt, _⟩, _⟩, ⟨ndq, hndq, hQw⟩, _, _⟩ :=
    hexact.2 (hgq.trans hvh) x hx
      (healing_recovery_gate_reader hrec hx (hGST.trans hu) (hgq.trans hvh))
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
      (healing_support_gate_scope_of_cut E rho hrec hcut hgsts (by
        apply le_trans ?_ hsh
        change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
        linarith [p.deltaPos]) hScope)
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
      apply hGST.trans (hu.trans _)
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
      (services.transfers u v m J contested hready hphase jq iq x q Q
        (hu.trans (by
          change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
          linarith [p.deltaPos])) hgq hgstq hSync hQw' hx
        (healing_enabledGate_of_fastWrite E rho hS hjqt hQw') hiq
        (healing_recovery_joined E rho hrec hx
          (by
            change E.t_GST ≤ 4 * p.Δ * (((q + 1 : Nat) : Int) - 1)
            rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
            change u ≤ 4 * p.Δ * (q : Int) at hu
            exact hGST.trans hu)
          (by
            refine hGST.trans (hu.trans ?_)
            change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
            push_cast
            linarith)
          ((hq1v.trans hgq).trans hvh))) hτ
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
    · have hcovb := (healing_tPerm_at E rho hrec mono crossing writes
        hready hphase (services.permanence u v m J contested hready hphase) huw hwv hbody).1
      have hcb : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
          Block.Preceq lease.1 K :=
        fun z hz K hK => hcovb z s K hz (by exact_mod_cast (show (w : Int) + 1 ≤ (s : Int) by
          omega)) hvs hK
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
Blueprint 21 H.2 S1, H.22:3207–3216 (G1), spec 899–921; plan H-GATE §3C.
DC: INTENTIONAL fresh gate service at an honest gate of a label s > q in the phase, for a
stored non-genesis block B above the gate F that every honest HEAD of label s covers. The
raw result covers B (`healing_support_gate_cover`), B has release-threshold support
(`opening_gate_support`), and the guard holds for the actual raw result
(`opening_gate_guard`). GateService at s is a conclusion, never a premise. -/
theorem opening_gateService_of_cover [Fintype V] (E : Generic.Env V)
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {q : Slot} {Q : Block} (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    {s : Slot} (hqs : q < s) (hsv : SA.gateTime p.toParams s ≤ v)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x s)
    (hFQ : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) Q) {B : Block}
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K → Block.Preceq B K)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) B)
    (hB : B ∈ (storeAt p c E rho i x).base.blocks) (hne : B ≠ .genesis) :
    Gen.AC.Duty.GateService (fgsaAC E rho) i s x B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hsh : SA.gateTime p.toParams s ≤ rho.horizon := hsv.trans hphase.2.1
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hScope := services.gates i x s hx ht
    (healing_scope_enabled_gate hrec hx ht (hcut.trans (by
      change 4 * p.Δ * ((s : Int) - 1) ≤ 4 * p.Δ * (s : Int)
      linarith [p.deltaPos])) hsh) hcut hsh B
    (healing_support_gate_geometry E rho hS hcov (by rwa [clockPre_fg]))
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hGST.trans (hu.trans ?_)
    have hqsI : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast hqs
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hv : { actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) with
      early := (storeAt p c E rho i x).base.early } = (fgsaAC E rho).gateView i x s :=
    fgsa_clockPre_gateView p (storeAt p c E rho i x) s
  obtain ⟨C, hC, hBC⟩ := healing_support_gate_cover E rho hrec hgsts hsh hcov ht
    (healing_support_gate_scope_of_cut E rho hrec hcut hgsts (by
      apply le_trans ?_ hsh
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) hScope)
    (by rw [clockPre_fg]; exact hFB)
  rw [clockPre_fg] at hC
  have hraw : (fgsaAC E rho).raw i s x = some C := by
    have he := congrArg (fun u => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho i x).fg.F) u s) hv
    have he' : (fgsaAC E rho).raw i s x = SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho i x).fg.F)
        (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s := he.symm
    exact he'.trans hC
  have hτ := opening_gate_support E rho hrec hcut hgsts hsh hcov hx ht hScope hFB
  have hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView i x s) s B := by
    have he := congrArg (fun u => SA.Root.prefixSupport p.toParams u s B) hv
    exact he ▸ hτ
  have hb0 : B ∈ (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).base.blocks := by
    rw [(clockPre_fields p _ _).2.1]
    exact hB
  have hmem : B ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    refine (actView_blocks _ B).mpr ⟨hb0, ?_⟩
    rw [clockPre_fg]
    exact Bool.or_eq_true_iff.mpr (Or.inr hFB)
  have hmemw : B ∈ ((fgsaAC E rho).gateView i x s).blocks :=
    (congrArg GridCO.State.blocks hv) ▸ hmem
  have hcut : E.t_GST ≤ slotStartZ p (s : Int) := by
    have hqsI : (q : Int) ≤ (s : Int) := by exact_mod_cast hqs.le
    change E.t_GST ≤ 4 * p.Δ * (s : Int)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hEnabled := healing_gate_enabled_of_recovery hrec.toRecovery₂ hx ht hsh hcut
  exact fgsa_gate_of_coveringBatch E rho hS i s x B ht hEnabled ⟨C, hraw, hBC⟩
    (opening_gate_guard E rho hrec mono crossing services writes hready hphase hQ hexact
      hu hqs hsv hx ht
      hFQ) hne hmemw hsupport (opening_gate_level E rho i x s B hsupport)

end AvailableChain.FGSA.Run
end

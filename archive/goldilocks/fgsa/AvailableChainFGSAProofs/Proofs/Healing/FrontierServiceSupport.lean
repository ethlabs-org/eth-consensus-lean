module
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningGateRead
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceGate

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! HG.1 Transfers (blueprint 21:1500–1574; plan §3.1 steps 3–6).
The proposer proof uses the actual previous HEAD batch. The output proof uses an
induction over the run prefix and includes gates with a faulty proposer.
INLINE writes: `fgsa_leaseOrigins_lastWrite`, discharged at Assembly. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem frontier_service_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1529–1539; plan §3.1 step 3.
DC: INTENTIONAL every later honest proposal at s ≥ q+2 has a parent above the seed Q.
Only the proposal time must be within the horizon. -/
theorem frontier_proposals_cover [Fintype V] (E : Generic.Env V)
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
    (hready : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hqs : q + 2 ≤ s) (hv : SA.proposalTime p.toParams s ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) s B) :
    Block.Preceq Q B.parent := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt hp.1.1)
  have hqr : q + 1 ≤ r := Nat.le_of_succ_le_succ hqs
  have hqrI : (q : Int) + 1 ≤ (r : Int) := by exact_mod_cast hqr
  have hvp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  have hvr : SA.voteTime p.toParams r ≤ v :=
    ((le_add_of_nonneg_right hd.le).trans hvp).trans hv
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := by
    refine hGST.trans (hu.trans ?_)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hgstr : E.t_GST ≤ SA.voteTime p.toParams r := by
    refine hgstq.trans ?_
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + p.Δ
    nlinarith
  have hheads := frontier_Q_heads E rho hrec mono crossing writes hGST hErase hHeight
    hexact (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hRead.seed hu hphase
      hqv hvh hcap
  have hcover : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG Qfg) K := hErase ▸ hheads r hqr hvr
  obtain ⟨ip, x, N, heN, hx, hip, _, hem⟩ := repair_proposal_emission E rho hp
  subst B
  let st := clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1))
  have hinv : CStoreInv p st := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hfg : st.fg = (storeAt p c E rho ip x).fg := clock_fg p _ _
  obtain ⟨hQfg, hFQ, hZQ, hloQ⟩ := frontier_pivot_held E rho hrec crossing hHeight hvh hcap
    hgstr (HealingWindow.after (hGST.trans hu) hqr) hcover hx hip hvp hv
    (healing_carriers_window_at p c E rho hrec (HealingWindow.after (hGST.trans hu) hqr)
      (hRead.carriers r hqr ip x _ hv) hx hip hvp)
  have hQst : Qfg ∈ st.fg.TF := hfg ▸ hQfg
  have hc : controls p st = R_at p c E rho ip x := repair_controls_clock _ _
  have hlo : (controls p st).lo ≤ (heightView p Qfg).h := hc ▸ hloQ
  have hZ : Block.Preceq (eraseFG (controls p st).Z) Q := by
    rw [hc, ← hErase]
    exact eraseFG_preceq hZQ
  obtain ⟨_, _, ⟨nd, hnd, hfast⟩, _, _⟩ := hexact.2 (hqv.trans hvh) x hx ((frontier_seed_readers
    hrec (hready.trans hu) (hqv.trans hvh)) x hx)
  have hq1h : SA.voteTime p.toParams (q + 1) ≤ rho.horizon := by
    refine le_trans ?_ (hv.trans hvh)
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    nlinarith
  have hawake := hrec.awake x hx (SA.voteTime p.toParams (q + 1)) (by
    apply hGST.trans (hu.trans _)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]) hq1h
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hrec.base.delta hx (q + 1)
    hq1h hawake
  have hqip : iq < ip := repair_idx_lt E rho hS hiq hip (by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    nlinarith)
  have hlease : ∀ row ∈ (storeAt p c E rho ip x).base.obligations,
      Block.Compatible row.1 Q := by
    refine healing_fast_lease_at E rho hrec mono writes hgstq (hqv.trans hvh) hx hnd hfast
      hvh (hRead.seed x hx) (hGST.trans hu) ?_ hx hiq hqip ?_ ?_
    · intro w hw hwv
      have hvw : SA.voteTime p.toParams w ≤ v := by
        refine le_trans ?_ hwv
        change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
        linarith
      exact hheads w hw hvw
    · intro j t hj ht
      exact (fgsa_tick_time_strict E rho hS ht hip hj).le.trans hv
    · rw [← hErase]
      exact eraseFG_preceq hFQ
  have hanchor : Block.Compatible (liveRoot p st) Q := by
    rcases repair_liveRoot_cases st with he | ⟨row, hr, _, _, he⟩
    · rw [he]
      exact Bool.or_eq_true_iff.mpr (Or.inl hZ)
    · rw [he]
      exact hlease row (healing_lease_clock_nongate _ _ (by
        intro w hw
        have h : (4 * ((r + 1 : Nat) : Int)) * p.Δ = (4 * (w : Int) + 6) * p.Δ := by
          change 4 * p.Δ * ((r + 1 : Nat) : Int) = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
          linarith
        have h2 := Int.eq_of_mul_eq_mul_right (ne_of_gt hd) h
        push_cast at h2
        omega) row hr)
  have hpath : ∀ C, Block.Prec (liveRoot p st) C → Block.Preceq C Q →
      C ∈ erasedList st (domainR p st st.fg.TF) := by
    intro C hr hCQ
    have hr' : Block.Preceq (liveRoot p st) C := (Bool.and_eq_true_iff.mp hr).2
    obtain ⟨A, hA, heA, hAQ⟩ := eraseFG_ancestor_preceq hinv.fg.closed hQst (hErase ▸ hCQ)
    have hFA : FGBlock.Preceq st.fg.F A := frontier_service_lift
      (heA ▸ block_preceq_trans (F_preceq_liveRoot p st hinv) hr')
    have hZA : FGBlock.Preceq (controls p st).Z A := frontier_service_lift
      (heA ▸ block_preceq_trans (fgsa_Z_preceq_liveRoot p st) hr')
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    rw [domainR_def, frameR_def]
    exact (KitFG.mem_filteredFromView _ _ _ _).mpr ⟨hA, hFA, hZA, Qfg, hQst, hAQ, hlo⟩
  have hprior := frontier_prior_support E rho hrec crossing hHeight hvh hcap
    hgstr hcover
    (hheads r hqr hvr) hx hip (hRead.prior r hqr hv ip x hx hip
      (healing_recovery_joined E rho hrec hx (by
        have hc := healing_ready_proposal_cutoff E (hready.trans (hu.trans (by
          change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
          push_cast; nlinarith)))
        exact hc.trans (by
          change 4 * p.Δ * (((r + 1 : Nat) : Int) - 2) ≤
            4 * p.Δ * (((r + 1 : Nat) : Int) - 1)
          linarith [p.deltaPos])) (hGST.trans (hu.trans (by
            change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
            push_cast; nlinarith))) (hv.trans hvh)))
    (HealingWindow.after (hGST.trans hu) hqr) hv
  have hhead : Block.Preceq Q (proposerHead p st (r + 1)) := by
    have he : proposerHead p st (r + 1) = headInTree p st
        (erasedList st (domainR p st st.fg.TF)) (proposerVotes st (r + 1))
        (proposerSupport st (r + 1)) := by
      rw [fgsa_domainR_eq_treeStoreFrameView]
      rfl
    rw [he]
    exact fgsa_headInTree_covers_of_transfer p st _ _ _ Q hanchor hpath hprior.majority
      hprior.rivals
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hem
  have hpr := (fgsa_emits_proposal E rho _ x _ (r + 1) _).mp hem
  have hparent := (fgsa_walkRun_proposal_parent p st (r + 1) _ N hpr.2.2.2.2).2.2
  rw [hparent]
  exact hhead

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1539–1551; plan §3.1 step 3.
DC: INTENTIONAL the seed output persists under the cap, through every later event.
The induction includes gates with no honest proposal and reconciliation events. -/
theorem frontier_output_cover [Fintype V] (E : Generic.Env V)
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
    (hGates : ∀ s, q + 1 ≤ s → SA.gateTime p.toParams s ≤ v →
      FrontierGateScope E rho s v)
    (hready : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    (_hguard : SA.gateTime p.toParams q + 4 * p.Δ ≤ v)
    {i : Nat} {y : V} (hy : y ∈ rho.honest)
    (hai : afterTicksIdx rho (SA.gateTime p.toParams q + 4 * p.Δ) ≤ i)
    (hiv : i ≤ timeIdx rho v) : Block.Preceq Q (S_at p c E rho i y) := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  obtain ⟨_, ⟨jq, ⟨hjq, _⟩, _⟩, ⟨nd, hnd, hfast⟩, hstable, _⟩ :=
    hexact.2 (hqv.trans hvh) y hy ((frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh))
      y hy)
  have hpost := (healing_support_gate_reads p c E rho hS hjq).2
  rw [hpost] at hnd
  have he := Option.some.inj hnd
  subst he
  obtain ⟨_, hQjq, _⟩ := opening_exact_stored E rho hS hErase hjq hfast le_rfl
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := by
    refine hGST.trans (hu.trans ?_)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hF (a : Nat) (ha : jq ≤ a) (hav : a ≤ timeIdx rho v) :
      Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) Q := by
    rw [← hErase]
    exact eraseFG_preceq (frontier_F_below_all E rho crossing hy (hcap a y hav hy)
      hy ha hQjq (le_of_eq hHeight.symm))
  have hbase : S_at p c E rho (jq + 1) y = Q := by
    rw [afterTicks_node E rho hS hjq] at hstable
    change (V2.D.tick E rho (V2.D.Run.stateBefore E rho jq y) y
      (SA.gateTime p.toParams q)).1.st.base.stableRecord = Q at hstable
    change (V2.D.Run.stateBefore E rho (jq + 1) y).st.base.stableRecord = Q
    rw [(V2.D.Run.step_tick_eq E rho hjq).1]
    exact hstable
  have hjqi : jq + 1 ≤ i := by
    have hlt : jq < V2.D.Run.idxBefore rho (SA.gateTime p.toParams q + 4 * p.Δ) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hjq _).mpr
        (lt_add_of_pos_right _ (by linarith))
    have hpre := (preIdx_le_afterTicksIdx E rho hS
      (SA.gateTime p.toParams q + 4 * p.Δ)).1
    change V2.D.Run.idxBefore rho _ ≤ _ at hpre
    exact (Nat.succ_le_of_lt hlt).trans (hpre.trans hai)
  have hheads := frontier_Q_heads E rho hrec mono crossing writes hGST hErase hHeight
    hexact (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hRead.seed hu hphase
      hqv hvh hcap
  suffices hn : ∀ n, jq + 1 + n ≤ timeIdx rho v →
      Block.Preceq Q (S_at p c E rho (jq + 1 + n) y) by
    have h := hn (i - (jq + 1)) (by omega)
    rwa [Nat.add_sub_cancel' hjqi] at h
  intro n
  induction n with
  | zero => intro _; rw [Nat.add_zero, hbase]; exact block_preceq_refl _
  | succ n ih =>
    intro hn
    have hIH := ih (by omega)
    let b := jq + 1 + n
    have hFb := hF b (by omega) (by omega)
    have hFb1 := hF (b + 1) (by omega) hn
    change Block.Preceq Q (S_at p c E rho (b + 1) y)
    rcases fgsaAC_output_step E rho b y with hsame | ⟨w, hw⟩ | hrc | ⟨t, hr, _⟩
    · rw [S_at_def]
      change Block.Preceq Q ((fgsaAC E rho).output (b + 1) y)
      rw [hsame]
      exact hIH
    · have hqw : q < w := repair_slot_lt_of_time (by
        have hlt := fgsa_tick_time_strict E rho hS hjq hw (by omega)
        change 4 * p.Δ * (q : Int) + 6 * p.Δ < 4 * p.Δ * (w : Int) + 6 * p.Δ at hlt
        change 4 * p.Δ * (q : Int) < 4 * p.Δ * (w : Int)
        linarith)
      have hwv : SA.gateTime p.toParams w ≤ v := by
        have he : rho.events.filter (fun e => decide (e.time < v + 1)) =
            rho.events.filter (fun e => decide (e.time ≤ v)) :=
          List.filter_congr (fun e _ => by simp only [Int.lt_add_one_iff])
        have hb : b < V2.D.Run.idxBefore rho (v + 1) := by
          rw [V2.D.Run.idxBefore_def, he]
          change jq + 1 + (n + 1) ≤ (rho.events.filter (fun e => decide (e.time ≤ v))).length at hn
          dsimp only [b]
          omega
        exact Int.lt_add_one_iff.mp ((Gen.V2.Duty.index_lt_idxBefore_iff hS hw _).mp hb)
      have hvw : SA.voteTime p.toParams w ≤ v := by
        refine le_trans ?_ hwv
        change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
        linarith
      have hgw : E.t_GST ≤ SA.voteTime p.toParams w := by
        refine hgstq.trans ?_
        have hqwI : (q : Int) < (w : Int) := by exact_mod_cast hqw
        change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
        nlinarith
      have hScope := hGates w (Nat.succ_le_of_lt hqw) hwv
      have hgeom : GateReceiptGeometry E rho
          (clockPre p (storeAt p c E rho b y) (SA.gateTime p.toParams w)) w Q := by
        constructor
        · intro a ha _ K he
          rw [clockPre_fg]
          exact block_preceq_trans hFb (hheads w (Nat.succ_le_of_lt hqw) hvw _ ha K
            (healing_support_emitted_head E rho hS w a K _ he))
        · intro a ha _ K he
          exact hheads w (Nat.succ_le_of_lt hqw) hvw _ ha K
            (healing_support_emitted_head E rho hS w a K _ he)
      exact healing_output_gate_step E rho hrec hgw (hwv.trans hvh)
        (hheads w (Nat.succ_le_of_lt hqw) hvw) hy hw
        (hScope.gates b y hy hw (healing_recovery_gate_enabled E rho hrec hy hw
          (healing_gate_cut_of_batch_cut E w hScope.cut)) Q hgeom) hFb (Or.inl hIH)
    · obtain ⟨_, _, _, _, _, _, hout⟩ := hrc
      rw [S_at_def]
      change Block.Preceq Q ((fgsaAC E rho).output (b + 1) y)
      rw [hout, Gen.AC.normalizeOutput_def]
      have ha : Block.preceq ((fgsaAC E rho).anchor (b + 1) y)
          ((fgsaAC E rho).output b y) = true := block_preceq_trans hFb1 hIH
      simp only [ha, ↓reduceIte]
      exact hIH
    · change Block.Preceq Q (rho.stateBefore E (b + 1) y).st.base.stableRecord
      rw [rho.stateBefore_succ E hr]
      simp only [V2.D.World.step, Function.update_self]
      change Block.Preceq Q (acRestart p (rho.stateBefore E b y).st t).base.stableRecord
      rw [acRestart_stableRecord]
      exact hIH

end AvailableChain.FGSA.Run
end

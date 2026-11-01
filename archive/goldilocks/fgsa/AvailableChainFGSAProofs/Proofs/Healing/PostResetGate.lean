module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant
public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceGate -- shake: keep

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers

public section

/-! J6-2 H6 gate service. The raw-transfer field is used at its complete
cut. INLINE writes are supplied by `fgsa_leaseOrigins_lastWrite` at Assembly.
No carrier successor or honest proposal is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3040; plan J6-3 O2; B1/B17.
DC: SAME a gate tick lies before the complete post-gate cut. -/
theorem healing_postReset_tick_lt_cut
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j i : Nat} {x : V} {v : Slot}
    (ht : IsGateTick p c rho j x v)
    (hcut : afterTicksIdx rho (SA.gateTime p.toParams v) ≤ i) : j < i := by
  have hji : j < afterTicksIdx rho (SA.gateTime p.toParams v) := by
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hs
      (cutPred (SA.gateTime p.toParams v))
      (fun e f h ef => decide_eq_true (h.trans (of_decide_eq_true ef)))
      (Nat.le_of_not_gt hn) ht
    have hc : cutPred (P := fgsa p c) (SA.gateTime p.toParams v)
        (.tick x (SA.gateTime p.toParams v)) = true := decide_eq_true le_rfl
    rw [hc] at hf
    contradiction
  exact hji.trans_le hcut

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3040; plan J6-3 O2; B1/B17.
DC: SAME a strictly earlier inclusive read is before the current tick. -/
theorem healing_postReset_time_cut_le_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {v : Slot} {t : Time}
    (ht : IsGateTick p c rho j x v) (hlt : t < SA.gateTime p.toParams v) :
    timeIdx rho t ≤ j := by
  by_contra hn
  have hb := (V2.D.Engine.index_lt_read_length_iff hs t ht).mp (Nat.lt_of_not_ge hn)
  change SA.gateTime p.toParams v ≤ t at hb
  exact (not_le.mpr hlt) hb

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D4; DC: SAME HEAD cut before gate. -/
theorem healing_postReset_head_cut_le_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {x : V} {v : Slot}
    (ht : IsGateTick p c rho k x v) :
    timeIdx rho (SA.voteTime p.toParams v) ≤ k := by
  apply healing_postReset_time_cut_le_tick E rho hs ht
  change 4 * p.Δ * (v : Int) + p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
  linarith [p.deltaPos]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2946–3040; plan RE-BIND D4; DC: SAME HEAD cut before post-gate. -/
theorem healing_postReset_head_cut_le_afterTicks
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {n : Nat} {v : Slot}
    (hcut : afterTicksIdx rho (SA.gateTime p.toParams v) ≤ n) :
    timeIdx rho (SA.voteTime p.toParams v) ≤ n := by
  have htime : SA.voteTime p.toParams v < SA.gateTime p.toParams v := by
    change 4 * p.Δ * (v : Int) + p.Δ < 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hle : timeIdx rho (SA.voteTime p.toParams v) ≤
      (rho.events.filter (fun e => decide (e.time < SA.gateTime p.toParams v))).length := by
    change (rho.events.filter (fun e =>
      decide (e.time ≤ SA.voteTime p.toParams v))).length ≤ _
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true ((of_decide_eq_true he).trans_lt htime)
  exact hle.trans ((preIdx_le_afterTicksIdx E rho hs _).1.trans hcut)

private theorem postReset_clockPre_lease_live (st : State p.n) (t : Time)
    (row : Block × Nat × Time) (hrow : row ∈ (clockPre p st t).base.obligations) :
    t < row.2.2 := by
  have hsub : (clockPre p st t).base.obligations.Sublist
      (GridCO.expire { st.base with now := t } t).obligations := by
    unfold clockPre
    dsimp only
    split_ifs <;> first | exact List.Sublist.refl _ | exact List.filter_sublist
  exact of_decide_eq_true (List.mem_filter.mp (hsub.subset hrow)).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3030; plan J6-3 O2; B1/B17/B18.
DC: SAME J6-2 guard with the exact source and release cuts.
INLINE writes has producer fgsa_leaseOrigins_lastWrite at Assembly. -/
theorem healing_postReset_gate_guard_at_cut [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (i : Nat)
    (hrawTransfer : PostResetRawTransfer p c E rho w i)
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
    {s : Slot} (hs : w.sStar ≤ s)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hGateHorizon : SA.gateTime p.toParams s ≤ rho.horizon)
    {j : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho j x s)
    (hEnabled : enabledGateAt p c E rho j x s)
    (hji : j < i) (hReleaseCut : timeIdx rho (SA.releaseTime p.toParams s) ≤ i) :
    ∀ C, (fgsaAC E rho).raw j s x = some C →
      ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hv : { actView (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s)) with early := (storeAt p c E rho j x).base.early } =
      (fgsaAC E rho).gateView j x s := fgsa_clockPre_gateView p _ s
  have hrawEq : (fgsaAC E rho).raw j s x = SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s :=
    (congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hv).symm
  have hqd : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hqeq : SA.voteTime p.toParams (s + 1) = SA.releaseTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ = 4 * p.Δ * (s : Int) + 5 * p.Δ
    push_cast
    ring
  have hawake := hrec.awake x hx (SA.voteTime p.toParams (s + 1)) (by
    apply hgst.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]) (hqd.le.trans hGateHorizon)
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hrec.base.delta hx (s + 1)
    (hqd.le.trans hGateHorizon) hawake
  have hqj : iq < j := repair_idx_lt E rho hS hiq ht hqd
  intro C hC lease hl
  have hresult : gateResult p c E rho x s = some (some C) := by
    classical
    let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
    have hgateIn : gateIn p c E rho x s = some pre := by
      rw [gateIn_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS ht]
      rfl
    have hre : pre.restartTime = (storeAt p c E rho j x).restartTime := by
      dsimp [pre]; unfold clockPre; dsimp only; split_ifs <;> rfl
    have he : (match pre.restartTime with
      | none => True | some w => w ≤ 4 * p.Δ * (s : Int)) := by
      rw [hre]; exact hEnabled.2
    rw [gateResult_def, hgateIn]
    rw [Option.map_some]
    have hrawPre : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F)
        (actView pre) s = some C := by
      simpa only [pre, clockPre_fg] using hrawEq.symm.trans hC
    split_ifs with hAllow
    · exact congrArg some hrawPre
    · exact (hAllow he).elim
  rw [← hv] at hl
  have hpre : lease ∈ (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s)).base.obligations := hl
  have hlive := postReset_clockPre_lease_live _ _ lease hpre
  have hstore := (clockPre_obligations_sublist p _ _).subset hpre
  obtain ⟨k, hkj, u, B, htk, _, _, _, _, hdl, _, _⟩ := writes j x lease hstore
  have hus : u < s := by
    have hlt := fgsa_tick_time_strict E rho hS htk ht hkj
    change 4 * p.Δ * (u : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at hlt
    have h : (u : Int) < s := by nlinarith [p.deltaPos]
    exact_mod_cast h
  have hkq : k < iq := by
    apply repair_idx_lt E rho hS htk hiq
    change 4 * p.Δ * (u : Int) + 6 * p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    have h : (u : Int) + 1 ≤ (s : Int) := by exact_mod_cast hus
    push_cast
    nlinarith [p.deltaPos]
  have hkeep := healing_lease_persist E rho hS htk (Nat.lt_succ_of_lt hkq)
    (Nat.succ_le_of_lt hqj) lease hdl hstore
  let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho iq x)
    (SA.voteTime p.toParams (s + 1))
  have hpost : storeAt p c E rho (iq + 1) x = nd.st := by
    change (V2.D.Run.stateBefore E rho (iq + 1) x).st = _
    rw [V2.D.Run.stateBefore_succ E rho hiq]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho _ x _
  have hnd : postClock E rho x (SA.releaseTime p.toParams s) = some nd := by
    rw [← hqeq, postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hiq]
    rfl
  have hndlive : nd.st.base.now < lease.2.2 := by
    change (FGSA.clock p (storeAt p c E rho iq x)
      (SA.voteTime p.toParams (s + 1))).base.now < _
    rw [(clock_vn _ _).2]
    exact hqd.trans hlive
  rw [hpost] at hkeep
  rw [PostResetRawTransfer_def] at hrawTransfer
  exact (hrawTransfer j hji x s C hx hs ht hresult).1 x nd hx
    hReleaseCut hnd lease hkeep hndlive


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:3021–3030; plan J6-2/J6-3 O2; B1/B17/B18.
DC: SAME raw transfer at the source release read gives the whole-result
compatibility guard at that source's gate. A lease in the gate view has an
older write and survives through the release read. -/
theorem healing_postReset_gate_guard [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (i : Nat) (hcomplete : rho.events.length ≤ i)
    (hrawTransfer : PostResetRawTransfer p c E rho w i)
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
    {s : Slot} (hs : w.sStar ≤ s)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hGateHorizon : SA.gateTime p.toParams s ≤ rho.horizon)
    {j : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho j x s)
    (hEnabled : enabledGateAt p c E rho j x s) :
    ∀ C, (fgsaAC E rho).raw j s x = some C →
      ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C := by
  exact healing_postReset_gate_guard_at_cut E rho hrec w i hrawTransfer writes
    hs hgst hGateHorizon hx ht hEnabled ((List.getElem?_eq_some_iff.mp ht).1.trans_le hcomplete)
    ((List.length_filter_le _ _).trans hcomplete)




/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:910–986; plan J6-2 S3; B1/B17/B18.
DC: SAME H6 service from its HEAD coverage and gate-input floor.
Raw transfer is a named field at the complete cut. The cone and an honest
proposal are not needed. The covering batch gives the raw result, passed
guard, saved fast write, and live lease. -/
theorem healing_postReset_h6GateService [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (w : HealingWitness) (i : Nat) (hcomplete : rho.events.length ≤ i)
    (hrawTransfer : PostResetRawTransfer p c E rho w i)
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
    : H6GateService p c E rho w := by
  intro s D hs hready hGateHorizon hne hheads hfloor x hx
  have hgst : E.t_GST ≤ SA.voteTime p.toParams s := by
    have hlo := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have htime : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, ht, _⟩ := fgsa_tick_total E rho hS hrec.base.delta x hx (4 * s + 6)
    (htime ▸ hGateHorizon)
    (htime ▸ hrec.awake x hx (SA.gateTime p.toParams s) (by
      apply hgst.trans
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) hGateHorizon)
  rw [htime] at ht
  let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
  have hidx := fgsa_tickIdx_of_event p c E rho hS ht
  have hgateIn : gateIn p c E rho x s = some pre := by
    rw [gateIn_def, preTick_def, hidx]
    rfl
  have hFD : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) D := by
    have h := hfloor x pre hx hgateIn
    change Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s)).fg.F) D at h
    simpa only [clockPre_fg] using h
  have hcov : ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z s = some K → Block.Preceq D K := by
    intro z hz K hK
    obtain ⟨H, hH, hDH⟩ := hheads z hz
    exact Option.some.inj (hH.symm.trans hK) ▸ hDH
  have hBatchCut := healing_ready_vote_cutoff E hready
  have hcut : E.t_GST ≤ slotStartZ p (s : Int) :=
    healing_gate_cut_of_batch_cut E s hBatchCut
  have hEnabled := healing_scope_enabled_gate hrec hx ht hcut hGateHorizon
  have hgeom : GateReceiptGeometry E rho pre s D := by
    constructor
    · intro a ha _ K he
      change Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j x)
        (SA.gateTime p.toParams s)).fg.F) K
      rw [clockPre_fg]
      exact block_preceq_trans hFD (hcov _ ha K
        (healing_support_emitted_head E rho hS s a K _ he))
    · intro a ha _ K he
      exact hcov _ ha K (healing_support_emitted_head E rho hS s a K _ he)
  have hReceipt := healing_gate_receipt_scope_recovery E rho hrec mono hgst hx hEnabled hgeom
  have hScope := healing_support_gate_scope_of_cut E rho hrec hBatchCut hgst
    (by
      apply le_trans ?_ hGateHorizon
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) hReceipt
  obtain ⟨C, hconf, hDC⟩ := healing_support_gate_cover E rho hrec hgst hGateHorizon
    hcov ht hScope (by rw [clockPre_fg]; exact hFD)
  have hv : { actView pre with early := (storeAt p c E rho j x).base.early } =
      (fgsaAC E rho).gateView j x s := fgsa_clockPre_gateView p _ s
  have hrawEq : (fgsaAC E rho).raw j s x = SA.Root.confirmationFrom p.toParams
      (eraseFG pre.fg.F) (actView pre) s := by
    rw [clockPre_fg]
    exact (congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hv).symm
  have hraw : (fgsaAC E rho).raw j s x = some C := hrawEq.trans hconf
  have hinv : CStoreInv p pre := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) _
  have hCm : C ∈ pre.base.blocks := (compat_of_confirmation p pre hinv hconf).2
  obtain ⟨K, hK, heK⟩ := (hinv.baseTree C).mp hCm
  obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed hK (heK.symm ▸ hDC)
  have hDm : D ∈ pre.base.blocks := (hinv.baseTree D).mpr ⟨A, hA, heA⟩
  have hmem : D ∈ (actView pre).blocks := by
    apply (actView_blocks pre D).mpr
    exact ⟨hDm, Bool.or_eq_true_iff.mpr (Or.inr (by rw [clockPre_fg]; exact hFD))⟩
  have hmemw : D ∈ ((fgsaAC E rho).gateView j x s).blocks :=
    (congrArg GridCO.State.blocks hv) ▸ hmem
  have hsupport : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams ((fgsaAC E rho).gateView j x s) s D := by
    have h := opening_gate_support E rho hrec hBatchCut hgst hGateHorizon hcov hx ht hReceipt hFD
    exact (congrArg (fun v => SA.Root.prefixSupport p.toParams v s D) hv) ▸ h
  have hservice := fgsa_gate_of_coveringBatch E rho hS j s x D ht hEnabled
    ⟨C, hraw, hDC⟩
    (healing_postReset_gate_guard E rho hrec.toRecovery₂ w i hcomplete hrawTransfer writes
      hs hgst hGateHorizon hx ht hEnabled) hne hmemw hsupport
    (opening_gate_level E rho j x s D hsupport)
  have hservice' := hservice
  obtain ⟨B, hB, hDB, hguard, _, d, hd, hlease⟩ := hservice'
  have hconfB : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s =
      some B := hrawEq.symm.trans hB
  have hresult : gateResult p c E rho x s = some (some B) := by
    classical
    have hre : pre.restartTime = (storeAt p c E rho j x).restartTime := by
      dsimp [pre]; unfold clockPre; dsimp only; split_ifs <;> rfl
    have he : (match pre.restartTime with
      | none => True | some w => w ≤ 4 * p.Δ * (s : Int)) := by
      rw [hre]; exact hEnabled.2
    rw [gateResult_def, hgateIn]
    rw [Option.map_some]
    split_ifs with hAllow
    · exact congrArg some hconfB
    · exact (hAllow he).elim
  have hpass : gatePassedAt p c E rho j := by
    refine ⟨x, s, hEnabled, ?_, B, hconfB, ?_⟩
    · unfold GridCO.savedGenuine
      rw [clockPre_genuine]
      exact fgsa_gate_fresh E rho hS ht
    · apply List.any_eq_false.mpr
      intro lease hl
      have hlw : lease ∈ ((fgsaAC E rho).gateView j x s).obligations :=
        (congrArg GridCO.State.obligations hv) ▸ hl
      have hg : Block.compatible lease.1 B = true := hguard lease hlw
      simp only [hg, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (SA.gateTime p.toParams s)
  have hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd := by
    rw [postClock_def, preTick_def, hidx]
    rfl
  have hpost : (V2.D.Run.stateBefore E rho (j + 1) x).st = nd.st := by
    rw [V2.D.Run.stateBefore_succ E rho ht]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho _ x _
  change (D, SA.releaseThreshold p.toParams, d) ∈
    (V2.D.Run.stateBefore E rho (j + 1) x).st.base.obligations at hlease
  rw [hpost] at hlease
  have hleaseFind : nd.st.base.obligations.find? (fun row => row.1 == D) =
      some (D, SA.releaseThreshold p.toParams, d) := by
    cases he : nd.st.base.obligations.find? (fun row => row.1 == D) with
    | none => have hn := List.find?_eq_none.mp he _ hlease; simp at hn
    | some row =>
      have hk : row.1 = D := by simpa using List.find?_some he
      have heq := List.inj_on_of_nodup_map
        (storeBundle_postClock E rho j x (SA.gateTime p.toParams s)).cstore.leaseKeys.1
        (List.mem_of_find?_eq_some he) hlease hk
      exact congrArg some heq
  have hleaseOf : leaseOf nd.st D = some d := by
    change (nd.st.base.obligations.find? (fun row => row.1 == D)).map
      (fun row => row.2.2) = some d
    rw [hleaseFind]
    rfl
  have hL : 0 < L p := by
    change 0 < (4 * (p.k : Time) - 1) * p.Δ
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    exact mul_pos (by linarith) p.deltaPos
  change SA.gateTime p.toParams s + L p ≤ d at hd
  exact ⟨⟨B, hresult, hDB⟩, ⟨j, ht, hpass⟩, nd, d, hnd,
    exactService_fastWrite_of_gateService E rho hS j x s D ht hEnabled hservice,
    hleaseOf, hd, (lt_add_of_pos_right _ hL).trans_le hd⟩

end AvailableChain.FGSA.Run
end

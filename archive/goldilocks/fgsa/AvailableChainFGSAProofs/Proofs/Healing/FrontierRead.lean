module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportTransfer
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportProposal
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! G-HG1 retained cone input producer under a capped frontier (plan fgsa-s5-frontier §2.2,
§3.1 steps 1–5; blueprint 21 HG.1:1500–1574). The seed is ExactService at q; the cap is
TFrontier's closed cap. Every honest HEAD after q covers Q (`frontier_Q_heads`); every
live lease at a read of slot s ≥ q+2 is below every honest label-(s−1) HEAD
(`frontier_lease_cover`); the six cone fields follow at the actual reads. `lastWrite` is
the inline last-write premise (Assembly producer Foundations/Leases:392). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Bounded service inputs for a capped frontier cone. No retained history is inferred. -/
structure FrontierReadScope (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (q : Slot) (v : Time) : Prop where
  seed : ∀ x ∈ rho.honest, FastSupportScope E rho q v x
  first : ∀ s, q + 1 ≤ s → SA.gateTime p.toParams s ≤ v →
    E.t_GST ≤ SA.voteTime p.toParams s → ∀ i iq x,
    x ∈ rho.honest → IsGateTick p c rho i x s → enabledGateAt p c E rho i x s →
    rho.events[iq]? = some (.tick x (SA.voteTime p.toParams (s + 1))) →
    joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) →
    FirstTransferScope E rho i iq x x s
  fast : ∀ w, q + 1 ≤ w → SA.gateTime p.toParams w ≤ v →
    ∀ x nd B, x ∈ rho.honest →
    postClock E rho x (SA.gateTime p.toParams w) = some nd →
    B ∈ (fastWriteAt nd.st w).getD [] → FastSupportScope E rho w v x
  slow : ∀ w, q + 1 ≤ w → SA.gateTime p.toParams w ≤ v →
    E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k) →
    ∀ x st C B j, x ∈ rho.honest → gateIn p c E rho x w = some st →
    gateResult p c E rho x w = some (some C) → Block.Preceq B C →
    GridCO.slowEligible p.toParams.engine (actView st) w B = true →
    IsGateTick p c rho j x w → SlowSupportScope E rho w v x
  prior : ∀ r, q + 1 ≤ r → SA.proposalTime p.toParams (r + 1) ≤ v →
    ∀ ip x, x ∈ rho.honest →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))) →
    joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)) →
    ProposalSupportScope E rho ip x r (SA.proposalTime p.toParams (r + 1))
  next : ∀ r, q + 1 ≤ r → SA.voteTime p.toParams (r + 1) ≤ v →
    ∀ ih y, y ∈ rho.honest →
    rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))) →
    joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)) →
    NextTransferScope E rho ih y r
  carriers : ∀ r, q + 1 ≤ r →
    ∀ iy y t, t ≤ v → HealingCarriersAt E rho r iy y t

theorem FrontierReadScope.cut_mono {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {q : Slot} {u v : Time} (h : FrontierReadScope E rho q v) (huv : u ≤ v) :
    FrontierReadScope E rho q u :=
  ⟨fun x hx => (h.seed x hx).cut_mono huv,
    fun s hs ht hSync => h.first s hs (ht.trans huv) hSync,
    fun w hw ht x nd B hx hnd hB => (h.fast w hw (ht.trans huv) x nd B hx hnd hB).cut_mono huv,
    fun w hw ht hSync x st C B j hx hs hc hb hel hj =>
      (h.slow w hw (ht.trans huv) hSync x st C B j hx hs hc hb hel hj).cut_mono huv,
    fun r hr ht => h.prior r hr (ht.trans huv),
    fun r hr ht => h.next r hr (ht.trans huv),
    fun r hr iy y t ht => h.carriers r hr iy y t (ht.trans huv)⟩

/-- The inclusive seed-gate reader follows from the joined phase start. -/
theorem frontier_seed_readers [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {q : Slot}
    (hready : recoveryStart p E ≤ SA.proposalTime p.toParams q)
    (hhor : SA.gateTime p.toParams q ≤ rho.horizon) :
    ∀ x ∈ rho.honest, confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams q)) (SA.gateTime p.toParams q) := by
  have hSync : E.t_GST ≤ SA.proposalTime p.toParams q := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  exact fun x hx => healing_recovery_gate_reader hrec hx hSync hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1570–1574; plan §4 (q+1). DC: SAME grid arithmetic: a proposal at or after
d_q has slot at least q + 2. -/
private theorem fread_gate_prop {q s : Nat}
    (h : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s) : q + 2 ≤ s := by
  have hd := p.deltaPos
  have h1 : (4 * (q : Int) + 6) * p.Δ ≤ (4 * (s : Int)) * p.Δ := by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at h
    linarith
  have h2 := Int.le_of_mul_le_mul_right h1 hd
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:924–944; plan §3.1 step 3. DC: SAME grid arithmetic: a gate before v_s has
label at most s − 2. -/
private theorem fread_gate_vote {w s : Nat}
    (h : SA.gateTime p.toParams w < SA.voteTime p.toParams s) : w + 2 ≤ s := by
  have hd := p.deltaPos
  have h1 : (4 * (w : Int) + 6) * p.Δ < (4 * (s : Int) + 1) * p.Δ := by
    change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + p.Δ at h
    linarith
  have h2 := Int.lt_of_mul_lt_mul_right h1 hd.le
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1570–1574; plan §4. DC: SAME grid arithmetic: a gate time is never a
proposal time. -/
private theorem fread_gate_ne_prop (q s : Nat) :
    SA.gateTime p.toParams q ≠ SA.proposalTime p.toParams s := by
  intro h
  have hd := p.deltaPos
  have h1 : (4 * (q : Int) + 6) * p.Δ = (4 * (s : Int)) * p.Δ := by
    change 4 * p.Δ * (q : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) at h
    linarith
  have h2 := Int.eq_of_mul_eq_mul_right (ne_of_gt hd) h1
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:628–650; plan §3.1 step 3. DC: SAME the fast arm of
`healing_support_phaseBody_of_write` without its window premise: a fast slow-policy key at
a passed gate is in the gate's fast-write set. -/
private theorem fread_fast_write (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {w : Slot} {C B : Block} {g : Nat}
    (ht : IsGateTick p c rho j x w) (hpass : gatePassedAt p c E rho j)
    (hres : gateResultAt p c E rho j = some (some C))
    (hkey : (B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w C)
    (hfast : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w B) :
    ∃ nd, postClock E rho x (SA.gateTime p.toParams w) = some nd ∧
      B ∈ (fastWriteAt nd.st w).getD [] := by
  let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w)
  obtain ⟨hmem, hne, hBC, _, _⟩ := healing_support_key_cases p hkey
  obtain ⟨hin, hpost⟩ := healing_support_gate_reads p c E rho hs ht
  have hgr : gateResult p c E rho x w = some (some C) :=
    (gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hres
  obtain ⟨hJoined, hconf⟩ := fgsa_gate_raw_of_nonempty p c E rho hs ht hgr
  change SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C
    at hconf
  refine ⟨_, hpost, ?_⟩
  rw [healing_support_fastWrite p c E rho hs ht hJoined]
  have hF : eraseFG (storeAt p c E rho j x).fg.F = eraseFG pre.fg.F := by
    rw [clockPre_fg]
  obtain ⟨x', w', ht', _, h, hh, hguard⟩ := hpass
  obtain ⟨hxx, hw⟩ : x' = x ∧ SA.gateTime p.toParams w' = SA.gateTime p.toParams w := by
    have he := ht'.1.symm.trans ht
    simp only [Option.some.injEq, V2.Event.tick.injEq] at he
    exact he
  subst hxx
  have hww : w' = w := by
    change 4 * p.Δ * (w' : Int) + 6 * p.Δ = 4 * p.Δ * (w : Int) + 6 * p.Δ at hw
    have hd := p.deltaPos
    have he : (w' : Int) = w := by nlinarith
    exact_mod_cast he
  subst w'
  have hhC : h = C := Option.some.inj (hh.symm.trans hconf)
  subst h
  change B ∈ fastSet p (eraseFG (storeAt p c E rho j x').fg.F) (actView pre) w
  rw [hF]
  unfold fastSet
  rw [hconf]
  dsimp only
  change ((actView pre).obligations.any (fun row => !Block.compatible row.1 C)) = false
    at hguard
  simp only [hguard, Bool.false_eq_true, ite_false]
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨hne, hBC⟩, hfast⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1517–1521 (seed), Run/AC:56; plan §3.1 step 1 (G1). DC: INTENTIONAL
after an honest node's own gate tick at d_q, ExactService fixes its stable output to Q and
its time to d_q; every lease that is live at that state targets a prefix of Q
(`fgsaAC_lease_le_output`). -/
theorem frontier_seed_leases (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {q : Slot} {Q : Block}
    (hService : ExactService p c E rho q Q)
 (hqh : SA.gateTime p.toParams q ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest) {jq : Nat} (hjq : IsGateTick p c rho jq x q)
    (hReader : confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams q)) (SA.gateTime p.toParams q)) :
    S_at p c E rho (jq + 1) x = Q ∧
      (storeAt p c E rho (jq + 1) x).base.now = SA.gateTime p.toParams q ∧
      ∀ row ∈ (storeAt p c E rho (jq + 1) x).base.obligations,
        SA.gateTime p.toParams q < row.2.2 → Block.Preceq row.1 Q := by
  obtain ⟨_, _, _, hstab, _⟩ := hService.2 hqh x hx hReader
  have hstep := (V2.D.Run.step_tick_eq E rho hjq).1
  have hout : S_at p c E rho (jq + 1) x = Q := by
    rw [afterTicks_node E rho hs hjq] at hstab
    change (V2.D.tick E rho (V2.D.Run.stateBefore E rho jq x) x
      (SA.gateTime p.toParams q)).1.st.base.stableRecord = Q at hstab
    change (V2.D.Run.stateBefore E rho (jq + 1) x).st.base.stableRecord = Q
    rw [hstep]
    exact hstab
  have hnow : (storeAt p c E rho (jq + 1) x).base.now = SA.gateTime p.toParams q := by
    change (V2.D.Run.stateBefore E rho (jq + 1) x).st.base.now = _
    rw [hstep]
    exact (congrArg (fun st : State p.n => st.base.now)
      (tick_st (c := c) E rho (V2.D.Run.stateBefore E rho jq x) x
        (SA.gateTime p.toParams q))).trans (clock_vn _ _).2
  refine ⟨hout, hnow, ?_⟩
  intro row hrow hlive
  have h := fgsaAC_lease_le_output E rho (jq + 1) x hx row hrow (by
    change (storeAt p c E rho (jq + 1) x).base.now < row.2.2
    rw [hnow]
    exact hlive)
  change Block.Preceq row.1 (S_at p c E rho (jq + 1) x) at h
  rwa [hout] at h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1546–1556 (leases), H.6:928–944; plan §3.1 steps 1 and 3 (G1/G2).
DC: INTENTIONAL every live lease at an honest read between t_s and v_s, for s with
d_q ≤ t_s, targets a prefix of every honest label-(s−1) HEAD. Classify by the last write
gate w (inline `lastWrite`): an old write (w < q) survives to the node's own q-gate and is
below Q there (seed); a write at q is below Q; a later fast or synchronous-window slow
write transfers by the capped steps; a slow write whose window reaches label q is below
the saved q-result Q. -/
theorem frontier_lease_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (lastWrite : ∀ i x (row : Block × Nat × Time),
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q v) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v)
    {i : Nat} {z0 : V} {t : Time} {row : Block × Nat × Time} (hz : z0 ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick z0 t))
    (ht1 : SA.proposalTime p.toParams s ≤ t) (ht2 : t ≤ SA.voteTime p.toParams s)
    (hrow : row ∈ (storeAt p c E rho i z0).base.obligations) (hlive : t < row.2.2) :
    ∀ y ∈ rho.honest, ∀ K, headAtLabel p c E rho y (s - 1) = some K →
      Block.Preceq row.1 K := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have hHQ := frontier_Q_heads E rho hrec mono crossing lastWrite hGST hErase hHeight hService
    (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) hScopes.seed
    hu hPhase hqv hvh hcap
  have hqs : q + 2 ≤ s := fread_gate_prop hafter
  have hvs1 : SA.voteTime p.toParams (s - 1) ≤ v := by
    refine le_trans ?_ hvs
    have h : ((s - 1 : Nat) : Int) ≤ (s : Int) := by exact_mod_cast Nat.sub_le s 1
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hQcov : ∀ y ∈ rho.honest, ∀ K, headAtLabel p c E rho y (s - 1) = some K →
      Block.Preceq Q K := hHQ (s - 1) (Nat.le_sub_one_of_lt hqs) hvs1
  have hbelowQ (hQ' : Block.Preceq row.1 Q) : ∀ y ∈ rho.honest, ∀ K,
      headAtLabel p c E rho y (s - 1) = some K → Block.Preceq row.1 K :=
    fun y hy K hK => Gen.Pure.block_preceq_trans hQ' (hQcov y hy K hK)
  obtain ⟨j, hji, w, B, hjt, hpass, hres, hrowB, hkey, hdl, _, _⟩ := lastWrite i z0 row hrow
  have hdwt : SA.gateTime p.toParams w < t := fgsa_tick_time_strict E rho hS hjt hi hji
  have hws : w + 2 ≤ s := fread_gate_vote (hdwt.trans_le ht2)
  have hqh : SA.gateTime p.toParams q ≤ rho.horizon := hqv.trans hvh
  obtain ⟨hgr, ⟨jq, hjq, _⟩, _, _, _⟩ := hService.2 hqh z0 hz ((frontier_seed_readers hrec
    (hready.trans hu) (hqv.trans hvh)) z0 hz)
  have hdqt : SA.gateTime p.toParams q < t := by
    refine lt_of_lt_of_le ?_ ht1
    exact lt_of_le_of_ne hafter (fread_gate_ne_prop q s)
  rcases lt_trichotomy w q with hwq | hwq | hqw
  · -- An old write survives to the node's own q-gate, where it is below Q.
    have hdwq : SA.gateTime p.toParams w < SA.gateTime p.toParams q := by
      have h : (w : Int) < q := by exact_mod_cast hwq
      change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * (q : Int) + 6 * p.Δ
      nlinarith
    have hjjq : j < jq := repair_idx_lt E rho hS hjt hjq.1 hdwq
    have hjqi : jq < i := repair_idx_lt E rho hS hjq.1 hi hdqt
    have hpers := healing_lease_persist E rho hS hjt (Nat.lt_succ_of_lt hjjq) hjqi row hdl hrow
    obtain ⟨_, _, hle⟩ := frontier_seed_leases E rho hS hService hqh hz hjq.1
      ((frontier_seed_readers hrec (hready.trans hu) (hqv.trans hvh)) z0 hz)
    have hlt : SA.gateTime p.toParams q < row.2.2 := hdqt.trans hlive
    exact hbelowQ (hle row hpers hlt)
  · -- A write at q is below its gate result, Q.
    subst hwq
    have hgr' : gateResult p c E rho z0 w = some (some B) :=
      (gateResultAt_eq_gateResult p c E rho hS hjt).symm.trans hres
    have hBQ : B = Q := Option.some.inj (Option.some.inj (hgr'.symm.trans hgr))
    exact hbelowQ (hBQ ▸ hrowB)
  · -- A later write transfers by the capped steps.
    have hgstw : E.t_GST ≤ SA.voteTime p.toParams w := by
      refine hGST.trans (hu.trans ?_)
      have h : (q : Int) ≤ w := by exact_mod_cast hqw.le
      change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (w : Int) + p.Δ
      nlinarith
    have hgate : SA.gateTime p.toParams w ≤ v := (hdwt.le.trans ht2).trans hvs
    have hQw : ∀ i, w ≤ i → SA.voteTime p.toParams i ≤ v → ∀ z ∈ rho.honest, ∀ K,
        headAtLabel p c E rho z i = some K → Block.Preceq (eraseFG Qfg) K := by
      intro i hi hv z hz K hK
      rw [hErase]
      exact hHQ i (hqw.trans_le hi) hv z hz K hK
    obtain ⟨_, _, _, _, hcase⟩ := healing_support_key_cases p hkey
    rcases hcase with hfast | hslow
    · obtain ⟨nd, hnd, hB⟩ := fread_fast_write E rho hS hjt hpass hres hkey hfast
      exact frontier_fast_heads E rho hrec mono crossing lastWrite hHeight hvh hcap hgstw hgate
        hQw hz hnd hB
        (hScopes.fast w (Nat.succ_le_of_lt hqw) hgate z0 nd row.1 hz hnd hB)
        (healing_gate_cut_of_batch_cut E w
          (HealingWindow.after (hGST.trans hu) (Nat.succ_le_of_lt hqw)).2)
        (s - 1) (Nat.le_sub_one_of_lt hws) hvs1
    · obtain ⟨hin, _⟩ := healing_support_gate_reads p c E rho hS hjt
      have hgr' : gateResult p c E rho z0 w = some (some B) :=
        (gateResultAt_eq_gateResult p c E rho hS hjt).symm.trans hres
      by_cases hwin : q + 1 ≤ w + 1 - p.k
      · have hgw : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k) := by
          refine hGST.trans (hu.trans ?_)
          have h : (q : Int) ≤ ((w + 1 - p.k : Nat) : Int) := by
            exact_mod_cast (Nat.le_succ q).trans hwin
          change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((w + 1 - p.k : Nat) : Int) + p.Δ
          nlinarith
        exact frontier_slow_heads E rho hrec mono crossing lastWrite hHeight hvh hcap hgstw
          hgate hQw hz hgw hin hgr' hrowB hslow hjt
          (hScopes.slow w (Nat.succ_le_of_lt hqw) hgate hgw z0 _ B row.1 _
            hz hin hgr' hrowB hslow hjt)
          (healing_gate_cut_of_batch_cut E w
            (HealingWindow.after (hGST.trans hu) (Nat.succ_le_of_lt hqw)).2)
          (s - 1) (Nat.le_sub_one_of_lt hws) hvs1
      · -- The slow window reaches label q: the saved q-result Q covers the target.
        obtain ⟨C, hC, hrC⟩ := healing_slow_window E rho hS hin hslow
          (w := q) (Nat.le_of_lt_succ (Nat.lt_of_not_le hwin)) hqw
        have hCQ : C = Q := Option.some.inj (Option.some.inj (hC.symm.trans hgr))
        exact hbelowQ (hCQ ▸ hrC)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1521–1534, L4-R:2245–2262; plan §3.1 steps 2 and 5. DC:
INTENTIONAL
at an honest read after v_r + Δ under the cap, for a label r whose honest HEADs cover the
pivot, the node holds the pivot itself, and F and Z are below it with the floor at most
h(Qfg) = m (the own label-r HEAD block is the relayed witness). -/
theorem frontier_pivot_held [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {r : Slot} (hgstr : E.t_GST ≤ SA.voteTime p.toParams r)
    (hCut : HealingWindow p E 1 r)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG Qfg) K)
    {i : Nat} {y : V} {t : Time} (hy : y ∈ rho.honest) (hi : rho.events[i]? = some (.tick y t))
    (hrt : SA.voteTime p.toParams r + p.Δ ≤ t) (htv : t ≤ v)
    (hServices : ∀ j z, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams r)) →
      HeadCarrierServices E rho j z r y) :
    Qfg ∈ (storeAt p c E rho i y).fg.TF ∧
      FGBlock.Preceq (storeAt p c E rho i y).fg.F Qfg ∧
      FGBlock.Preceq (R_at p c E rho i y).Z Qfg ∧
      (R_at p c E rho i y).lo ≤ (heightView p Qfg).h := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  have hhorr : SA.voteTime p.toParams r ≤ rho.horizon :=
    (((le_add_of_nonneg_right hd.le).trans hrt).trans htv).trans hvh
  obtain ⟨jy, hjy⟩ := healing_support_vote_tick E rho hS hrec.base.delta hy r hhorr
    (hrec.awake y hy _ hgstr hhorr)
  have _hjoined := healing_recovery_joined_window E rho hrec hCut hy hhorr
  have hhl : headAtLabel p c E rho y r = some (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jy y).st (SA.voteTime p.toParams r)) r) := by
    unfold headAtLabel
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hjy]
    rfl
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams r + p.Δ) ≤ timeIdx rho v := by
    change (rho.events.filter (fun e => decide (e.time < _))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ v))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).le.trans (hrt.trans htv)))
  obtain ⟨W, _, hWe, _, hrelay⟩ := frontier_head_relay_on (hroots := hrec.base.receiptIdealization)
    E rho crossing hE hQm hcap hy hjy (hcoverQ y hy _ hhl) hcut hy
    (hServices jy y hy hjy)
  have hW : W ∈ (storeAt p c E rho i y).fg.TF :=
    (fgsa_store_durable p c E rho
      (healing_support_idxBefore_le p c E rho hS hi hrt) y).1 (hrelay)
  have hQW : Block.Preceq (eraseFG Qfg) (eraseFG W) := hWe ▸ hcoverQ y hy _ hhl
  have hinv := cstoreInv_stateBefore E rho i y
  obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed hW hQW
  have hAQ : A = Qfg := eraseFG_injective heA
  subst hAQ
  have hiv : i ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hS hi htv).le
  obtain ⟨_, hF, hZ, hlo⟩ := frontier_self_witness E rho crossing hQm hy (hcap i y hiv hy) hA
    (Gen.Pure.block_preceq_refl _)
  exact ⟨hA, hF, hZ, hlo⟩

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1500–1574, H.17:2958–3005; plan §2.2 (G3) and §3.1 step 5.
DC: INTENTIONAL the retained HG.1 cone input on the closed capped endpoint of TFrontier.
For an honest proposal of slot s with d_q ≤ t_s and d_s ≤ v, every honest HEAD read of
slot s gets all six cone fields at the actual reads: both live starts are the root or a
lease target with prior support (lease cover); the pivot has prior support; both floors
are at most h(Qfg) = m (the pivot is held); the root and the pivot have target scores.
The seed is ExactService at q with the persisting phase [u, d_q]; the cap is TFrontier's
closed cap. The proposal binders are those of `fgsa_retainedReads_HG1`. -/
theorem retainedHG1Input_through [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (lastWrite : ∀ i x (row : Block × Nat × Time),
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
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip : Nat} {x : V}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q)
    (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q v)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v)
    (hHorizon : v ≤ rho.horizon)
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
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro y hy ih hih
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith)).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  have hHQ := frontier_Q_heads E rho hrec mono crossing lastWrite hGST hErase hHeight hService
    (frontier_seed_readers hrec (hready.trans hu) (hqv.trans hHorizon)) hScopes.seed
    hu hPhase hqv hHorizon hcap
  have hqs : q + 2 ≤ s := fread_gate_prop hafter
  have hts : SA.proposalTime p.toParams s ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith
  -- The lease cover at both reads.
  have hcover (i : Nat) (z0 : V) (t : Time) (row : Block × Nat × Time) (hz : z0 ∈ rho.honest)
      (hi : rho.events[i]? = some (.tick z0 t))
      (ht : t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s)
      (hrow : row ∈ (clock p (rho.stateBefore E i z0).st t).base.obligations)
      (hlive : (clock p (rho.stateBefore E i z0).st t).base.now < row.2.2) :
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z (s - 1) = some K →
        Block.Preceq row.1 K := by
    obtain ⟨hrow', hnow⟩ := repair_read_row ht hrow
    rw [hnow] at hlive
    have ht1 : SA.proposalTime p.toParams s ≤ t := by
      rcases ht with rfl | rfl
      · exact le_rfl
      · exact htv
    have ht2 : t ≤ SA.voteTime p.toParams s := by
      rcases ht with rfl | rfl
      · exact htv
      · exact le_rfl
    exact frontier_lease_cover E rho hrec mono crossing lastWrite hready hErase hHeight
      hService hScopes
      hu hPhase hqv hHorizon hcap hafter hvs hz hi ht1 ht2 hrow' hlive
  -- Rename the slot as r + 1.
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 :=
    ⟨s - 1, (Nat.sub_add_cancel ((Nat.le_add_left 1 (q + 1)).trans hqs)).symm⟩
  simp only [Nat.add_sub_cancel] at hcover
  have hvr : SA.voteTime p.toParams r ≤ v := by
    refine le_trans ?_ hvs
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hgstr : E.t_GST ≤ SA.voteTime p.toParams r := by
    refine hGST.trans (hu.trans ?_)
    have h : (q : Int) ≤ r := by
      exact_mod_cast Nat.le_of_succ_le (Nat.le_of_succ_le_succ hqs)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (r : Int) + p.Δ
    nlinarith
  have hcovQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K →
      Block.Preceq (eraseFG Qfg) K := by
    intro z hz K hK
    rw [hErase]
    exact hHQ r (Nat.le_of_succ_le_succ hqs) hvr z hz K hK
  have hrp : SA.voteTime p.toParams r + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith
  -- The pivot is held at both reads.
  have hCut : HealingWindow p E 1 r :=
    HealingWindow.after (hGST.trans hu) (Nat.le_of_succ_le_succ hqs)
  obtain ⟨_, _, hZx, hlox⟩ := frontier_pivot_held E rho hrec crossing hHeight hHorizon hcap
    hgstr hCut hcovQ hx hip hrp hts
    (healing_carriers_window_at p c E rho hrec hCut
      (hScopes.carriers r (Nat.le_of_succ_le_succ hqs) ip x _ hts) hx hip hrp)
  obtain ⟨_, _, hZy, hloy⟩ := frontier_pivot_held E rho hrec crossing hHeight hHorizon hcap
    hgstr hCut hcovQ hy hih (hrp.trans htv) hvs
    (healing_carriers_window_at p c E rho hrec hCut
      (hScopes.carriers r (Nat.le_of_succ_le_succ hqs) ih y _ hvs) hy hih (hrp.trans htv))
  have hcs : controls p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (r + 1))) = R_at p c E rho ip x := repair_controls_clock _ _
  have hcd : controls p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (r + 1))) = R_at p c E rho ih y := repair_controls_clock _ _
  have hzsrc : Block.Preceq (z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (r + 1)))) (eraseFG Qfg) := by
    change Block.Preceq (eraseFG (controls p _).Z) _
    rw [hcs]
    exact eraseFG_preceq hZx
  have hzdst : Block.Preceq (z p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (r + 1)))) (eraseFG Qfg) := by
    change Block.Preceq (eraseFG (controls p _).Z) _
    rw [hcd]
    exact eraseFG_preceq hZy
  have hcovL {L : Block} (hL : Block.Preceq L (eraseFG Qfg)) :
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K :=
    fun z hz K hK => Gen.Pure.block_preceq_trans hL (hcovQ z hz K hK)
  have hprior {L : Block}
      (hL : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z r = some K → Block.Preceq L K) :=
    frontier_prior_support E rho hrec crossing hHeight hHorizon hcap hgstr hcovQ
      hL hx hip
      (hScopes.prior r (Nat.le_of_succ_le_succ hqs) hts ip x hx hip
        (healing_recovery_joined_proposal_next E rho hrec hCut hx hip)) hCut hts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- proposer_prior
    rcases repair_liveRoot_cases (clock p (rho.stateBefore E ip x).st
        (SA.proposalTime p.toParams (r + 1))) with he | ⟨row, hrow, hlive, _, he⟩
    · left
      change Block.Preceq (liveRoot p _) (eraseFG (controls p _).Z)
      rw [he]
      exact Gen.Pure.block_preceq_refl _
    · right
      change RetainedPriorSupport p _ _ (liveRoot p _)
      rw [he]
      exact hprior (hcover ip x _ row hx hip (Or.inl rfl) hrow hlive)
  · -- reader_prior
    right; left
    change RetainedPriorSupport p _ _ (liveRoot p _)
    rcases repair_liveRoot_cases (clock p (rho.stateBefore E ih y).st
        (SA.voteTime p.toParams (r + 1))) with he | ⟨row, hrow, hlive, _, he⟩
    · rw [he]
      exact hprior (hcovL hzdst)
    · rw [he]
      exact hprior (hcover ih y _ row hy hih (Or.inr rfl) hrow hlive)
  · -- pivot_prior
    exact Or.inr (hprior hcovQ)
  · -- source_floor
    rw [hcs]
    exact hlox
  · -- target_floor
    rw [hcd]
    exact hloy
  · -- target_scores
    intro L hL _
    have hLQ : Block.Preceq L (eraseFG Qfg) := by
      rcases hL with rfl | rfl
      · exact hzsrc
      · exact Gen.Pure.block_preceq_refl _
    exact frontier_target_scores E rho hrec crossing hHeight hHorizon hcap hgstr hcovQ
      (hcovL hLQ) hy hih (hScopes.next r (Nat.le_of_succ_le_succ hqs) hvs ih y hy hih
        (healing_recovery_joined_vote_next E rho hrec hCut hy hih)) hCut hvs

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1500–1574; plan §2.2 (G4) and §4 (first rise, endpoint regression).
DC: INTENTIONAL the strict-stop adapter. The stop is an actual event jStop at which the
honest frontier rises above m (index jStop + 1); the cap holds through jStop. With
d_q < stop and d_s < stop the closed capped endpoint is d_s, inside the cap and the
horizon; `retainedHG1Input_through` then gives the consumer-facing proposition of
`fgsa_retainedReads_HG1`. The stop is never the horizon. -/
theorem retainedHG1Input_before_first_rise [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (lastWrite : ∀ i x (row : Block × Nat × Time),
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
    {u stop : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q s : Slot} {Q : Block} {Qfg : FGBlock (Fin p.n)} {ip : Nat} {x : V}
    {jStop : Nat} {evStop : V2.Event V (Obj p)}
    (hready : recoveryStart p E ≤ u)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q)
    (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hScopes : FrontierReadScope E rho q (SA.gateTime p.toParams s))
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hStopEv : rho.events[jStop]? = some evStop) (hStop : stop = evStop.time)
    (hRise : m < frontierAtIdx p c E rho (jStop + 1))
    (hCapStop : ∀ i x, timeIdx rho u ≤ i → i ≤ jStop → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hqStop : SA.gateTime p.toParams q < stop)
    (hsStop : SA.gateTime p.toParams s < stop)
    (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip) :
    ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < stop) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  intro y hy ih hih ⟨hafter, _⟩
  have hS := hrec.base.valid.toScheduleWellFormed
  have hd := p.deltaPos
  -- The closed endpoint is d_s: it is before the stop event, so inside the horizon.
  have hstoph : stop ≤ rho.horizon := by
    rw [hStop]
    exact (hS.in_horizon evStop (List.mem_of_getElem? hStopEv)).2
  have hcut : timeIdx rho (SA.gateTime p.toParams s) ≤ jStop := by
    have h1 : timeIdx rho (SA.gateTime p.toParams s) ≤ V2.D.Run.idxBefore rho stop := by
      change (rho.events.filter (fun e => decide (e.time ≤ _))).length ≤
        (rho.events.filter (fun e => decide (e.time < stop))).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left (fun e _ he =>
        decide_eq_true ((of_decide_eq_true he).trans_lt hsStop))
    have h2 : V2.D.Run.idxBefore rho stop ≤ jStop := by
      by_contra hn
      have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hS hStopEv stop).mp (Nat.lt_of_not_le hn)
      rw [hStop] at hlt
      exact lt_irrefl _ hlt
    exact h1.trans h2
  have hqs : SA.gateTime p.toParams q ≤ SA.gateTime p.toParams s := by
    refine le_trans ?_ (le_trans hafter ?_)
    · exact le_rfl
    · change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith
  exact retainedHG1Input_through E rho hrec mono crossing lastWrite hready hQ hErase hHeight
    hService hScopes hu hPhase hqs (hsStop.le.trans hstoph)
    (fun i z hi1 hi2 hz => hCapStop i z hi1 (hi2.trans hcut) hz) hx hip hseat N hem
    hafter le_rfl y hy ih hih

end AvailableChain.FGSA.Run
end

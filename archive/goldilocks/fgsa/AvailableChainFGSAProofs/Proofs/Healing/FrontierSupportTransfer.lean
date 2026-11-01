module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSupportHeads
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow

public section

/-! G-HG1 capped label induction (plan fgsa-s5-frontier §3.1 step 3; blueprint 21
HG.1:1536–1565). From the initial exact service of the height-m pivot Q, every honest HEAD
after q covers Q until the capped endpoint. A later fast or synchronous-window slow body
B transfers from its own label by the same capped steps; the pivot cover gives the
height-m witnesses. The lease premise of each step comes from the existing phase-free
lease lemmas (`healing_fast_lease`, `healing_slow_lease`). `lastWrite` is the inline
last-write premise (Assembly producer Foundations/Leases:392). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1546–1556, H.1:673–699 (fast case); plan §3.1 step 3
(restates
`healing_first_transfer_fast`). DC: INTENTIONAL a fast body B at an honest gate d_s whose
label-s HEADs cover the pivot transfers to every honest HEAD at v_(s+1) under the cap. -/
theorem frontier_first_transfer_fast [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} {B : Block} (hgsts : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
      Block.Preceq (eraseFG Qfg) K)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams s) = some nd)
    (hB : B ∈ (fastWriteAt nd.st s).getD [])
    (hScope : FastSupportScope E rho s v x)
    (hCut : E.t_GST ≤ slotStartZ p (s : Int))
    {y : V} (hy : y ∈ rho.honest) (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    {H : Block} (hH : headAtLabel p c E rho y (s + 1) = some H) :
    Block.Preceq B H := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  -- The source gate tick.
  rw [postClock_def, preTick_def] at hnd
  cases hix' : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => rw [hix'] at hnd; cases hnd
  | some ix =>
  rw [hix'] at hnd
  have hix := V2.D.Run.tickIdx?_spec hix'
  have hnd' := Option.some.inj hnd
  subst hnd'
  rw [healing_support_fastWrite p c E rho hS hix
    (fgsa_gate_joined_of_enabled E rho (hScope.source ix hix))] at hB
  let src := actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
  -- The fast set: a genuine result h ⪰ B and the fast test at B.
  unfold fastSet at hB
  cases hconf : SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho ix x).fg.F) src
      s with
  | none => rw [hconf] at hB; exact absurd hB List.not_mem_nil
  | some h =>
  rw [hconf] at hB
  dsimp only at hB
  split at hB
  · exact absurd hB List.not_mem_nil
  obtain ⟨_, hb⟩ := List.mem_filter.mp hB
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨_, hBh⟩, hτ⟩ := hb
  have hmaj : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
        (GridCO.cleanSupport p.toParams.engine src s) B := by
    have hh : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
        2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
          (GridCO.cleanSupport p.toParams.engine src s) h := by
      change (if _ then some _ else none) = some h at hconf
      split at hconf
      · have he := Option.some.inj hconf
        subst h
        have heq (C : Block) :
            GridCO.goldfishScoreOn (GridCO.resolutionTree src) src.blocks
              (GridCO.cleanSupport p.toParams.engine src s)
              (GridCO.cleanSupport p.toParams.engine src s) C =
            GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
              (GridCO.cleanSupport p.toParams.engine src s) C :=
          actView_score p (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))
            (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho ix x) _)
            (by rw [clockPre_headDomain];
                exact base_headDomain_none p (reachable_stateBefore E rho ix x)) _ _ C
        rw [← heq _]
        assumption
      · contradiction
    have ha := Gen.AC.Root.goldfishScore_antitone src.blocks
      (GridCO.cleanSupport p.toParams.engine src s)
      (GridCO.cleanSupport p.toParams.engine src s) B h hBh
    omega
  -- The honest supporter.
  obtain ⟨k, o, hkh, ho, hko, hsup⟩ :=
    healing_support_honest_seat rho hrec.base.cstar hrec.fault src s B hτ
  -- The receiver HEAD tick.
  unfold headAtLabel at hH
  rw [postClock_def, preTick_def] at hH
  cases hiy' : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [hiy'] at hH; cases hH
  | some iy =>
  rw [hiy'] at hH
  have hiy := V2.D.Run.tickIdx?_spec hiy'
  have hHeq := Option.some.inj hH
  subst hHeq
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgsts hvd (hgate.trans hvh)
  exact frontier_first_transfer_core (hroots := hrec.base.receiptIdealization)
    E rho crossing hE hDelta hrec.sync hQm hvh hcap hgsts
    hgate hcoverQ hx hix hkh ho hko hsup hmaj hy hiy (hScope.firstOn ix iy y hy hix hiy hv
      (healing_recovery_next_vote_joined_of_cut E rho hrec hCut hy hiy)) hv
    (fun hFB => healing_support_release_compat (hroots := hrec.base.receiptIdealization)
      E rho hE hDelta s hSync hx hy hix hiy (hScope.firstOn ix iy y hy hix hiy hv
      (healing_recovery_next_vote_joined_of_cut E rho hrec hCut hy hiy)) hτ hFB)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 HG.1:1546–1556, H.4-S:650–680; plan §3.1 step 3 (restates
`healing_slow_first_transfer`). DC: INTENTIONAL a synchronous-window slow body at an honest
gate d_s whose label-s HEADs cover the pivot transfers to every honest HEAD at v_(s+1)
under the cap. The slow source result is a strict late majority with an honest supporter. -/
theorem frontier_first_transfer_slow [Fintype V] (E : Generic.Env V)
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
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} {B : Block} (hgsts : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hcoverQ : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z s = some K →
      Block.Preceq (eraseFG Qfg) K)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x s)
    (hScope : SlowSupportScope E rho s v x)
    (hCut : E.t_GST ≤ slotStartZ p (s : Int))
    {y : V} (hy : y ∈ rho.honest) (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    {H : Block} (hH : headAtLabel p c E rho y (s + 1) = some H) :
    Block.Preceq B H := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hhor : SA.gateTime p.toParams s ≤ rho.horizon := hgate.trans hvh
  have hmaj := healing_slow_majority E rho hS hjx hres hBC
  obtain ⟨k, o, hkh, ho, hko, hsup⟩ :=
    healing_slow_honest_seat E rho hrec hgsts hhor hx hjx
      (hScope.late jx hjx (hScope.phase.source jx hjx)) (hScope.phase.source jx hjx) hmaj
  unfold headAtLabel at hH
  rw [postClock_def, preTick_def] at hH
  cases hiy' : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [hiy'] at hH; cases hH
  | some iy =>
  rw [hiy'] at hH
  have hiy := V2.D.Run.tickIdx?_spec hiy'
  have hHeq := Option.some.inj hH
  subst hHeq
  obtain ⟨K, hK, _⟩ := healing_support_clean_target E rho o ho
  have hsupD := actView_support_in_domain p _
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho jx x) _) o hK hsup
  exact frontier_first_transfer_core (hroots := hrec.base.receiptIdealization)
    E rho crossing hE hDelta hrec.sync hQm hvh hcap hgsts
    hgate hcoverQ hx hjx hkh ho hko hsupD hmaj hy hiy (hScope.phase.firstOn jx iy y hy hjx hiy hv
      (healing_recovery_next_vote_joined_of_cut E rho hrec hCut hy hiy)) hv
    (healing_slow_lease E rho hrec mono lastWrite hgsts hhor hx hgw hst hres hBC
      hel le_rfl (hv.trans hvh) (hScope.cut_mono hv)
      (fun w hw1 hw2 => absurd (hw1.trans hw2) (Nat.not_succ_le_self s)) hy hiy)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1536–1565, H.2 S1:709–715; plan §3.1 step 3. DC: INTENTIONAL the
bounded capped H.2 induction on labels. From a common honest HEAD prefix B at label s+1,
every honest HEAD at a label i ≥ s+1 with v_i ≤ v covers B. Each step uses the honest batch
of the previous label and a HEAD block above the pivot as witness. The pivot cover and
the lease premise may use the cover of B at the earlier labels. -/
theorem frontier_heads_transfer [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hCut : E.t_GST ≤ slotStartZ p (s : Int))
    (hQ : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams (i + 1) ≤ v →
      (∀ w, s + 1 ≤ w → w ≤ i → ∀ z ∈ rho.honest, ∀ K,
        headAtLabel p c E rho z w = some K → Block.Preceq B K) →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K →
        Block.Preceq (eraseFG Qfg) K)
    (hbase : SA.voteTime p.toParams (s + 1) ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z (s + 1) = some K → Block.Preceq B K)
    (hNext : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams (i + 1) ≤ v →
      ∀ iy y, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
      joinedAt p E rho y (i + 1) (SA.voteTime p.toParams (i + 1)) →
      NextTransferScope E rho iy y i)
    (hlease : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams (i + 1) ≤ v →
      (∀ w, s + 1 ≤ w → w ≤ i → ∀ z ∈ rho.honest, ∀ K,
        headAtLabel p c E rho z w = some K → Block.Preceq B K) →
      ∀ iy y, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
      Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B →
      ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
        (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B) :
    ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K := by
  have hd := p.deltaPos
  have hvmono {a b : Slot} (hab : a ≤ b) :
      SA.voteTime p.toParams a ≤ SA.voteTime p.toParams b := by
    have h : (a : Int) ≤ (b : Int) := by exact_mod_cast hab
    change 4 * p.Δ * (a : Int) + p.Δ ≤ 4 * p.Δ * (b : Int) + p.Δ
    nlinarith
  suffices h : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v → ∀ w, s + 1 ≤ w → w ≤ i →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K by
    intro i hi hv
    exact h i hi hv i hi le_rfl
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro hv w hw1 hw2
    have hw : w = s + 1 := le_antisymm hw2 hw1
    subst hw
    exact hbase hv
  | succ i hi ih =>
    intro hv w hw1 hw2
    have hvi : SA.voteTime p.toParams i ≤ v := (hvmono (Nat.le_succ i)).trans hv
    by_cases hwi : w ≤ i
    · exact ih hvi w hw1 hwi
    have hw : w = i + 1 := le_antisymm hw2 (Nat.succ_le_of_lt (Nat.lt_of_not_le hwi))
    subst hw
    intro z hz K hK
    unfold headAtLabel at hK
    rw [postClock_def, preTick_def] at hK
    cases hiz' : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams (i + 1)) with
    | none => rw [hiz'] at hK; cases hK
    | some iz =>
    rw [hiz'] at hK
    have hiz := V2.D.Run.tickIdx?_spec hiz'
    have hKeq := Option.some.inj hK
    subst hKeq
    have hsi : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams i :=
      hvmono ((Nat.le_succ s).trans hi)
    exact frontier_next_transfer_core E rho hrec crossing hQm hvh hcap (hgst.trans hsi)
      (hQ i hi hv (ih hvi)) (ih hvi i hi le_rfl) hz hiz (hNext i hi hv iz z hz hiz
        (healing_recovery_joined_vote_next E rho hrec (HealingWindow.after hCut hi) hz hiz))
      (HealingWindow.after hCut hi) hv
      (hlease i hi hv (ih hvi) iz z hz hiz)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1517–1546; plan §3.1 steps 1 and 3 (G1/G2). DC: INTENTIONAL the
pivot support of TFrontier's seed: from ExactService at q, every honest HEAD at a label
after q with v_i ≤ v covers Q. Label q+1 is inside the persisting phase (v_(q+1) < d_q),
so it uses the fixed-phase H.1 step; later labels use the capped H.2 steps. The lease
premise is the phase-free fast-body lease bound for the fast write of Q at d_q. -/
theorem frontier_Q_heads [Fintype V] (E : Generic.Env V)
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
    (hGST : E.t_GST ≤ u) (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q)
    (hReaders : ∀ x ∈ rho.honest, confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams q)) (SA.gateTime p.toParams q))
    (hScopes : ∀ x ∈ rho.honest, FastSupportScope E rho q v x)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m) :
    ∀ i, q + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq Q K := by
  have hd := p.deltaPos
  have htv : SA.proposalTime p.toParams q ≤ SA.voteTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + p.Δ
    linarith
  have hgstq : E.t_GST ≤ SA.voteTime p.toParams q := hGST.trans (hu.trans htv)
  have hfast (x : V) (hx : x ∈ rho.honest) : ∃ nd : Node p,
      postClock E rho x (SA.gateTime p.toParams q) = some nd ∧
        Q ∈ (fastWriteAt nd.st q).getD [] := by
    obtain ⟨_, _, hfw, _, _⟩ := hService.2 (hqv.trans hvh) x hx (hReaders x hx)
    exact hfw
  have hv1 : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  refine frontier_heads_transfer E rho hrec crossing hHeight hvh hcap hgstq (hGST.trans hu) ?_ ?_
    (fun i hi ht iy y hy hj hJ => (hScopes y hy).next i hi ht iy y hy hj hJ) ?_
  · intro i hi _ ih
    rw [hErase]
    exact ih i hi le_rfl
  · intro _ z hz K hK
    obtain ⟨nd, hnd, hQnd⟩ := hfast z hz
    exact healing_first_transfer_fast E rho hrec.toRecovery₂ (fun _ => mono) crossing hGST hPhase
      (hu.trans htv) le_rfl hz hnd hQnd hz hv1
      (fun ix iy hi hj => (hScopes z hz).firstOn ix iy z hz hi hj (hv1.trans hqv)
        (healing_recovery_next_vote_joined_of_cut E rho hrec (hGST.trans hu) hz hj)) hK
  · intro i hi hv ih iy y hy hiy hFB
    obtain ⟨nd, hnd, hQnd⟩ := hfast y hy
    exact healing_fast_lease E rho hrec mono lastWrite hgstq hy hnd hQnd hi (hv.trans hvh)
      ((hScopes y hy).cut_mono hv) (hGST.trans hu) ih
      hy hiy hFB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1548–1552 (fast lease above Q); plan §3.1 step 3. DC: INTENTIONAL a
fast body B at an honest gate d_w, whose label-w and later HEADs cover the pivot, transfers
to every honest HEAD at a label after w with v_i ≤ v (its own honest supporter and the
height-m self-witness, then the capped H.2 steps). -/
theorem frontier_fast_heads [Fintype V] (E : Generic.Env V)
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
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {w : Slot} {B : Block} (hgstw : E.t_GST ≤ SA.voteTime p.toParams w)
    (hgate : SA.gateTime p.toParams w ≤ v)
    (hQ : ∀ i, w ≤ i → SA.voteTime p.toParams i ≤ v → ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z i = some K → Block.Preceq (eraseFG Qfg) K)
    {x : V} (hx : x ∈ rho.honest) {nd : Node p}
    (hnd : postClock E rho x (SA.gateTime p.toParams w) = some nd)
    (hB : B ∈ (fastWriteAt nd.st w).getD [])
    (hScope : FastSupportScope E rho w v x)
    (hCut : E.t_GST ≤ slotStartZ p (w : Int)) :
    ∀ i, w + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K := by
  have hd := p.deltaPos
  have hvw : SA.voteTime p.toParams w ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  refine frontier_heads_transfer E rho hrec crossing hQm hvh hcap hgstw hCut ?_ ?_ hScope.next ?_
  · intro i hi hv _
    refine hQ i ((Nat.le_succ w).trans hi) (le_trans ?_ hv)
    change 4 * p.Δ * (i : Int) + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  · intro hv z hz K hK
    exact frontier_first_transfer_fast E rho hrec crossing hQm hvh hcap hgstw hgate
      (hQ w le_rfl hvw) hx hnd hB hScope hCut hz hv hK
  · intro i hi hv ih iy y hy hiy hFB
    exact healing_fast_lease E rho hrec mono lastWrite hgstw hx hnd hB hi (hv.trans hvh)
      (hScope.cut_mono hv) hCut ih
      hy hiy hFB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1552–1558 (slow lease above Q); plan §3.1 step 3. DC: INTENTIONAL a
synchronous-window slow body B at an honest gate d_w, whose label-w and later HEADs cover
the pivot, transfers to every honest HEAD at a label after w with v_i ≤ v. -/
theorem frontier_slow_heads [Fintype V] (E : Generic.Env V)
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
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time} (hvh : v ≤ rho.horizon)
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {w : Slot} {B : Block} (hgstw : E.t_GST ≤ SA.voteTime p.toParams w)
    (hgate : SA.gateTime p.toParams w ≤ v)
    (hQ : ∀ i, w ≤ i → SA.voteTime p.toParams i ≤ v → ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z i = some K → Block.Preceq (eraseFG Qfg) K)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x w = some st) {C : Block}
    (hres : gateResult p c E rho x w = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) w B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x w)
    (hScope : SlowSupportScope E rho w v x)
    (hCut : E.t_GST ≤ slotStartZ p (w : Int)) :
    ∀ i, w + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K := by
  have hd := p.deltaPos
  have hvw : SA.voteTime p.toParams w ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  refine frontier_heads_transfer E rho hrec crossing hQm hvh hcap hgstw hCut ?_ ?_
    hScope.phase.next ?_
  · intro i hi hv _
    refine hQ i ((Nat.le_succ w).trans hi) (le_trans ?_ hv)
    change 4 * p.Δ * (i : Int) + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  · intro hv z hz K hK
    exact frontier_first_transfer_slow E rho hrec mono crossing lastWrite hQm hvh hcap hgstw
      hgate (hQ w le_rfl hvw) hx hgw hst hres hBC hel hjx hScope hCut hz hv hK
  · intro i hi hv ih iy y hy hiy hFB
    exact healing_slow_lease E rho hrec mono lastWrite hgstw (hgate.trans hvh) hx hgw hst hres
      hBC hel ((Nat.le_succ w).trans hi) (hv.trans hvh) (hScope.cut_mono hv) ih hy hiy hFB

end AvailableChain.FGSA.Run
end

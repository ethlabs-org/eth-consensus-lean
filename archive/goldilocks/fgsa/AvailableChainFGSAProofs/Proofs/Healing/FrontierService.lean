module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSeed
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceCover
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierServiceSupport
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierOpenAll
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersQ

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers

public section

/-! HG.1 exact service (blueprint 21:1500–1583; plan §3.1 steps 6–7).
The q+1 read uses the initial phase. Later reads use the closed capped endpoint.
Both routes use capped gate geometry. INLINE writes: `fgsa_leaseOrigins_lastWrite`. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Bounded retained objects and read epochs used by one frontier service interval. -/
structure FrontierServiceScopes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q : Slot) (v : Time) : Prop where
  read : recoveryStart p E ≤ SA.proposalTime p.toParams q →
    SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierReadScope E rho q v
  permanence : ∀ u t m J contested, recoveryStart p E ≤ u →
    PhaseInterval p c E rho u t m J contested → t ≤ v →
    SupportPermanenceServices E rho u t m J contested
  heads : ∀ s ip x N, q + 1 ≤ s → SA.voteTime p.toParams s ≤ v →
    E.t_GST ≤ slotStartZ p ((s : Int) - 2) →
    x ∈ rho.honest → rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
    RepairHeadServices E rho s ip x N

/-- Recovery produces the selected bounded frontier services. -/
theorem healing_frontier_service_scopes_recovery [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (q : Slot) (v : Time) :
    FrontierServiceScopes E rho q v := by
  refine ⟨?_, ?_, ?_⟩
  · intro hready hgate hhor
    exact healing_frontier_read_scope_recovery E rho hrec mono
      ((healing_ready_proposal_window E hready).prior.cut_mono (Nat.sub_le q 1)) hgate hhor
  · intro u t m J contested hready hphase _
    exact healing_support_permanence_recovery E rho hrec mono hready hphase
  · intro s ip x N _ _ hcut hx hip hem
    exact healing_repair_head_services_recovery E rho hrec mono
      (healing_window_of_cut E hcut) hx hip hem

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1551–1574; plan §3.1 step 6.
DC: INTENTIONAL the exact HEAD clause and capped gate geometry give all service fields. -/
theorem frontier_exactService_of_heads [Fintype V] (E : Generic.Env V)
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
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} {B : Block} (hqs : q < s) (hgate : SA.gateTime p.toParams s ≤ v)
    (hp : HonestProposal E rho (fgsaInterface p c) s B)
    (hhead : ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some B) :
    ExactService p c E rho s B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hd := p.deltaPos
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith)).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  have hBs := repair_proposal_slot E rho hp
  have hne : B ≠ .genesis := by
    rintro rfl
    exact hp.1.1.ne' hBs.symm
  have hgsts : E.t_GST ≤ SA.voteTime p.toParams s := by
    refine hGST.trans (hu.trans ?_)
    have hqsI : (q : Int) < (s : Int) := by exact_mod_cast hqs
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith
  have hRead := services.read (hready.trans hu) hqv hvh
  have hScope := frontier_repair_gate_scope E rho hRead hready hu hqs hgate
  have hhor : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans ?_ (hgate.trans hvh)
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hheadAll : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some B :=
    fun y hy => hhead y hy
      (healing_recovery_joined E rho hrec hy hScope.cut hgsts hhor)
  exact repair_exact_service_on E rho hrec s B hne hScope.cut hgsts (fun _ => hhead)
    (fun _ _ hx ht => frontier_gate_geometry E rho hrec mono crossing writes hRead
      hready hErase hHeight hService hu hPhase hqv hvh hcap hqs hgate hBs hheadAll hx ht)
    (fun i x hReader ht => by
      have hgeom := frontier_gate_geometry E rho hrec mono crossing writes hRead
        hready hErase hHeight hService hu hPhase hqv hvh hcap hqs hgate hBs hheadAll
        hReader.1 ht
      exact (hScope.gates i x hReader.1 ht
        (healing_scope_enabled_gate hrec hReader.1 ht
          (healing_gate_cut_of_batch_cut E s hScope.cut) (hgate.trans hvh)) B
        hgeom.toGateReceiptGeometry).toGateReceiptScope) hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1570–1574; TF-SEED Q4 step 4.
DC: INTENTIONAL an honest q+1 proposal has full service after d_q, under the cap.
The gate proof uses no phase through d_(q+1). -/
theorem frontier_seed_qSucc_exactService [Fintype V] (E : Generic.Env V)
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
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    (hseed : FrontierSeedQualification p E u q)
    (hgate : SA.gateTime p.toParams (q + 1) ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ExactService p c E rho (q + 1) B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  exact frontier_exactService_of_heads E rho hrec mono crossing writes services hready hErase
    hHeight
    hService hu hPhase hqv hvh hCap (Nat.lt_succ_self q) hgate hp
    (frontier_seed_qSucc_head E rho hrec mono crossing writes
      hready hPhase
      (services.permanence u (SA.gateTime p.toParams q) m J contested hready hPhase hqv)
      hseed
      (fun ip x N hx hip hem => services.heads (q + 1) ip x N le_rfl (by
        apply le_trans ?_ hgate
        change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤
          4 * p.Δ * ((q + 1 : Nat) : Int) + 6 * p.Δ
        linarith [p.deltaPos]) (by
        have he : ((q + 1 : Nat) : Int) - 2 = (q : Int) - 1 := by push_cast; omega
        simpa only [he] using frontier_seed_prior_cut hready hseed)
        hx hip hem) hp)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944. Class (iii).
DC: INTENTIONAL; a stored height witness supplies the supported source path. -/
private theorem frontier_source_path (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (L W : FGBlock (Fin p.n)) (hW : W ∈ src.fg.TF)
    (hLW : FGBlock.Preceq L W) (hZL : FGBlock.Preceq (controls p src).Z L)
    (hlo : (controls p src).lo ≤ (heightView p W).h) : eraseFG L ∈ S p src := by
  have hFL : FGBlock.Preceq src.fg.F L := by
    have hFZ := fgsa_F_preceq_Z p src hs
    exact KitFG.preceq_trans hFZ hZL
  obtain ⟨Q, hQ, heQ⟩ := eraseFG_ancestor_mem hs.fg.closed hW (eraseFG_preceq hLW)
  have hL : L ∈ src.fg.TF := (eraseFG_injective heQ) ▸ hQ
  exact List.mem_filter.mpr ⟨(hs.baseTree _).mpr ⟨L, hL, rfl⟩,
    decide_eq_true ⟨L, (KitFG.mem_filteredFromView (heightView p) (controls p src)
      src.fg.TF L).mpr ⟨hL, hFL, hZL, W, hW, hLW, hlo⟩, rfl⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:937–942; H.6-S:1027–1029. Class (iii).
DC: INTENTIONAL; prior support covers a lease target from the ordinary root. -/
private theorem frontier_supported_cover (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (s : Slot) (L : Block)
    (h : RetainedPriorSupport p src s L) :
    Block.Preceq L (GridCO.ghost (z p src) (S p src) (ss src s) (es p src s)) := by
  let bare : State p.n := { src with base := { src.base with obligations := [] } }
  have ha : liveRoot p bare = z p src := by rfl
  have hpath : ∀ C, Block.Prec (liveRoot p bare) C → Block.Preceq C L →
      C ∈ S p src := by
    intro C hZC hCL
    obtain ⟨W, hW, hLW, hlo⟩ := h.witness
    obtain ⟨B, hB, heB⟩ := eraseFG_ancestor_mem hs.fg.closed hW
      (block_preceq_trans hCL hLW)
    rw [← heB]
    apply frontier_source_path p src hs B W hW
    · exact eraseFG_preceq_iff.mp (heB ▸ block_preceq_trans hCL hLW)
    · apply eraseFG_preceq_iff.mp
      rw [heB]
      exact (Bool.and_eq_true_iff.mp hZC).2
    · exact hlo
  have hc := fgsa_headInTree_covers_of_transfer p bare (S p src)
    (proposerVotes src s) (proposerSupport src s) L
    (ha ▸ h.root_compatible) hpath h.majority h.rivals
  exact hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944. Class (iii).
DC: INTENTIONAL; a covered target needs no fresh support below the root. -/
private theorem frontier_prior_cover (p : Params) (src : State p.n)
    (hs : CStoreInv p src) (s : Slot) (L : Block)
    (h : Block.Preceq L (z p src) ∨ RetainedPriorSupport p src s L) :
    Block.Preceq L (GridCO.ghost (z p src) (S p src) (ss src s) (es p src s)) := by
  rcases h with h | h
  · apply walk_covers_of_dominated_suffix _ _ _ _ _ (Bool.or_eq_true_iff.mpr (Or.inr h))
    rw [DominatedSuffix_def]
    intro C hZC hCL
    have he := block_preceq_antisymm (Bool.and_eq_true_iff.mp hZC).2
      (block_preceq_trans hCL h)
    have hn := (Bool.and_eq_true_iff.mp hZC).1
    simp only [he, decide_true, Bool.not_true, Bool.false_eq_true] at hn
  · exact frontier_supported_cover p src hs s L h

/-- The retained cone proves the current receiver floor before service is used. -/
theorem healing_retained_cone_reader_floor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (mono : RMonoAll p c E rho) {s : Slot} {ip ih : Nat} {x y : V}
    (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip) (D : FGBlock (Fin p.n))
    (hi : RetainedConeInput p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) :
    Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.voteTime p.toParams s) y).st.fg.F) N.erase := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hcover := frontier_prior_cover p src hs s (ap p src) hi.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hcover
  have ho := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _) (fgsa_Z_preceq_liveRoot p src) hprefix).trans
      hparent.2.2.symm
  have hD := frontier_prior_cover p src hs s (eraseFG D) hi.pivot_prior
  rw [ho] at hD
  have hmem : N.erase.parent ∈ src.base.blocks := by
    rw [← hparent.2.2.symm]
    rcases fgsa_headInTree_mem_or_anchor p src (S p src)
      (proposerVotes src s) (proposerSupport src s) with he | hb
    · rw [show getHead p src (proposerVotes src s) (proposerSupport src s) = ap p src
        from he]
      exact liveRoot_stored p src hs
    · exact (List.mem_filter.mp hb).1
  obtain ⟨A, hA, heA⟩ := (hs.baseTree _).mp hmem
  have hDA : FGBlock.Preceq D A := eraseFG_preceq_iff.mp (heA.symm ▸ hD)
  have hfloor := hi.source_floor.trans ((fgCertificateLaws p).height.h_mono hDA)
  have hay : Block.Preceq (ay p dst) N.erase.parent := by
    rcases hi.reader_prior with h | h | h
    · exact ho ▸ frontier_prior_cover p src hs s (ay p dst) (Or.inl h)
    · exact ho ▸ frontier_prior_cover p src hs s (ay p dst) (Or.inr h)
    · exact heA ▸ h A hA hfloor
  have hFB := block_preceq_trans (F_preceq_liveRoot p dst ht)
    (block_preceq_trans hay (fgsa_parent_preceq N.erase))
  have hidx : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ ih := by
    apply Nat.le_of_not_gt
    intro hlt
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hE.toScheduleWellFormed hih _).mp hlt
    exact (lt_irrefl _ ht).elim
  have hf := (mono _ ih y hy hidx).1
  change FGBlock.Preceq (rho.stateBefore E (V2.D.Run.idxBefore rho
    (SA.voteTime p.toParams s)) y).st.fg.F (storeAt p c E rho ih y).fg.F at hf
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed] at hf
  apply block_preceq_trans (eraseFG_preceq hf)
  simpa only [dst, clock_fg, storeAt] using hFB

/-- The cap bounds the receiver's current certificate by the selected source parent.
The parent stays at its source. No receiver receipt is used to establish this floor. -/
theorem frontier_retained_reader_floor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (crossing : RXing p c E rho) {s : Slot} {ip ih : Nat} {x y : V}
    {N : NamedProposal p.n} {Qfg : FGBlock (Fin p.n)} {v : Time}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (_hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hem : (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip)
    (hvs : SA.voteTime p.toParams s ≤ v)
    (hcap : ∀ i z, i ≤ timeIdx rho v → z ∈ rho.honest →
      (storeAt p c E rho i z).fg.h_max ≤ (heightView p Qfg).h)
    (hi : RetainedConeInput p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Qfg) :
    Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.voteTime p.toParams s) y).st.fg.F) N.erase := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hparent := fgsa_walkRun_proposal_parent p src s _ N hp.2.2.2.2
  have hc := frontier_prior_cover p src hs s (ap p src) hi.proposer_prior
  have hprefix := walk_best_ancestry_of_cover _ _ _ _ _ hc
  have ho := (walk_reanchor_of_best_ancestry _ _ _ _ _
    (erasedList_rootInj p src hs _) (fgsa_Z_preceq_liveRoot p src) hprefix).trans
      hparent.2.2.symm
  have hQP := frontier_prior_cover p src hs s (eraseFG Qfg) hi.pivot_prior
  rw [ho] at hQP
  have hP : N.erase.parent ∈ src.base.blocks := by
    rw [← hparent.2.2.symm]
    rcases fgsa_headInTree_mem_or_anchor p src (S p src)
      (proposerVotes src s) (proposerSupport src s) with he | hm
    · rw [show getHead p src (proposerVotes src s) (proposerSupport src s) = ap p src from he]
      exact liveRoot_stored p src hs
    · exact (List.mem_filter.mp hm).1
  obtain ⟨A, hA, heA⟩ := (hs.baseTree _).mp hP
  have hQA : FGBlock.Preceq Qfg A := eraseFG_preceq_iff.mp (heA.symm ▸ hQP)
  have hheight : (heightView p Qfg).h ≤ (heightView p A).h :=
    (fgCertificateLaws p).height.h_mono hQA
  have hji : ip ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) :=
    ((Gen.V2.Duty.index_lt_idxBefore_iff hE.toScheduleWellFormed hip _).mpr
      (by
        change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + p.Δ
        linarith [p.deltaPos])).le
  have hA0 : A ∈ (storeAt p c E rho ip x).fg.TF := by
    simpa only [src, clock_fg, storeAt] using hA
  have hiv := (fgsa_idxBefore_mono rho hvs).trans (idxBefore_le_timeIdx rho v)
  have hFA := healing_capped_witness_reader_floor crossing hx hy hji hA0
    ((hcap _ y hiv hy).trans hheight)
  change FGBlock.Preceq (rho.stateBefore E
    (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s)) y).st.fg.F A at hFA
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed] at hFA
  exact block_preceq_trans (heA ▸ eraseFG_preceq hFA) (fgsa_parent_preceq N.erase)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:1500–1574; plan §3.1 step 6.
DC: INTENTIONAL the HG.1 retained-read chain gives exact HEADs for s ≥ q+2.
The strict consumer uses v+1 only as an integer bound; every read and gate is within v. -/
theorem frontier_later_head [Fintype V] (E : Generic.Env V)
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
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) s B) :
    ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
      headAtLabel p c E rho y s = some B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hE := hrec.base.valid
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  obtain ⟨ip, x, N, heN, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  subst B
  have hgsts : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ := by
    refine hGST.trans (hu.trans ?_)
    have htime := hafter
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at htime
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (s : Int) - p.Δ
    linarith
  have hvs : SA.voteTime p.toParams s ≤ v := by
    refine le_trans ?_ hgate
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hqs : q + 1 ≤ s := by
    have ht := hafter
    change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at ht
    have hlt : q < s := by exact_mod_cast (show (q : Int) < (s : Int) by
      nlinarith [p.deltaPos])
    exact Nat.succ_le_of_lt hlt
  have hPriorCut : E.t_GST ≤ slotStartZ p ((s : Int) - 2) := by
    have hqsI : (q : Int) + 2 ≤ (s : Int) := by
      change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at hafter
      by_contra hn
      have hle : (s : Int) ≤ (q : Int) + 1 := by omega
      nlinarith [p.deltaPos]
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 2)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have hRead := services.read (hready.trans hu) hqv hvh
  have hHeads := services.heads s ip x N hqs hvs hPriorCut hx hip hem
  have hinput := retainedHG1Input_through E rho hrec mono crossing writes hready hQ hErase
    hHeight hService hRead hu hPhase hqv hvh hCap hx hip hseat N hem hafter hgate
  have hreads := fgsa_retainedReads_HG1_joined (hroots := hrec.base.receiptIdealization)
    E rho hE s hx hip hseat N hem Qfg q (v + 1) hafter
    (lt_of_le_of_lt hgate (lt_add_of_pos_right v (show (0 : Int) < 1 by decide)))
    (fun y hy ih hih _ _ => hinput y hy ih hih)
    (fun y hy ih hih hj => hHeads.target hy hih hj
      (frontier_retained_reader_floor E rho hE crossing hx hy hip hih hem hvs
        (fun i z hiv hz => by
          simpa only [hHeight] using frontier_cap_before_on E rho mono
            (hPhase.1.trans hqv) hCap i z hiv hz) (hinput y hy ih hih)))
  have hgeom : RetainedExactHeadRunGeometryOn E rho ip x s Qfg N.erase :=
    fgsa_retainedExactHead_geometry_on_run_on E rho hE s hx hip hseat N hem Qfg hreads
      (fun y hy ih hih hj => hHeads.scopes y hy ih hih hj
      (frontier_retained_reader_floor E rho hE crossing hx hy hip hih hem hvs
        (fun i z hiv hz => by
          simpa only [hHeight] using frontier_cap_before_on E rho mono
            (hPhase.1.trans hqv) hCap i z hiv hz) (hinput y hy ih hih)))
    hrec.base.receiptIdealization
  exact exactService_head_of_retained_proposal_on E rho hE hDelta s hip N hem
    Qfg hgeom (hvs.trans hvh)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1500–1574; plan §3.1 step 6.
DC: INTENTIONAL full service for a later honest proposal whose gate is in the capped interval. -/
theorem frontier_later_exactService [Fintype V] (E : Generic.Env V)
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
    (services : FrontierServiceScopes E rho q v)
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hErase : eraseFG Qfg = Q) (hHeight : (heightView p Qfg).h = m)
    (hService : ExactService p c E rho q Q) (hu : u ≤ SA.proposalTime p.toParams q)
    (hPhase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hqv : SA.gateTime p.toParams q ≤ v) (hvh : v ≤ rho.horizon)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m)
    {s : Slot} (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) s B) :
    ExactService p c E rho s B := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hqs : q < s := by
    apply repair_slot_lt_of_time
    refine lt_of_lt_of_le ?_ hafter
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact frontier_exactService_of_heads E rho hrec mono crossing writes services hready hErase
    hHeight
    hService hu hPhase hqv hvh hCap hqs hgate hp
    (frontier_later_head E rho hrec mono crossing writes services hready hQ hErase hHeight hService
      hu hPhase hqv hvh hCap hafter hgate hp)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1333–1350, 1500–1574; plan §2.4 and §3.1.
DC: INTENTIONAL the first two frozen TFrontier conjuncts, under its seed hypotheses.
INLINE writes: `fgsa_leaseOrigins_lastWrite` (Foundations/Leases:392), supplied at Assembly.
The full opening conjunction is assembled by `frontier_service` below. -/
theorem frontier_service_core [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
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
    : ∀ u v m J contested q Q Qfg,
  recoveryStart p E ≤ u → HonestProposal E rho (fgsaInterface p c) q Q → eraseFG Qfg = Q →
  (heightView p Qfg).h = m → ExactService p c E rho q Q →
  ((∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)) →
  u ≤ SA.proposalTime p.toParams q →
  PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested →
  SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
  (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
    (storeAt p c E rho i x).fg.h_max ≤ m) →
  Transfers p c E rho q Q v ∧ RepairAfter p c E rho q v := by
  intro u v m J contested q Q Qfg hgst hQ hErase hHeight hService hseed hu hPhase hqv hvh hCap
  have hSync : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hseed := (frontierSeedQualification_iff p E u q).mpr hseed
  have services := scopeProducer q v (hgst.trans hu) hqv hvh
  have hRead := services.read (hgst.trans hu) hqv hvh
  have hd := p.deltaPos
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith)).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x i H hx hi hiv hH
      exact frontier_Q_heads E rho hrec mono crossing writes hSync hErase hHeight hService
        (frontier_seed_readers hrec (hgst.trans hu) (hqv.trans hvh)) hRead.seed hu hPhase hqv
          hvh hcap i hi hiv x hx H hH
    · intro i B hi hiv hp
      exact frontier_proposals_cover E rho hrec mono crossing writes hRead hgst
        hErase hHeight
        hService hu hPhase hqv hvh hcap hi hiv hp
    · intro i x hx hguard hai hiv
      exact frontier_output_cover E rho hrec mono crossing writes hRead
        (fun s hs ht => frontier_repair_gate_scope E rho hRead hgst hu
          (Nat.lt_of_succ_le hs) ht) hgst hErase hHeight
        hService hu hPhase hqv hvh hcap hguard hx hai hiv
  · intro s B htime hgate hp
    have hqs := repair_slot_lt_of_time htime
    by_cases heq : s = q + 1
    · subst s
      exact frontier_seed_qSucc_exactService E rho hrec mono crossing writes services hgst hErase
        hHeight hService hu hPhase hqv hvh hCap hseed hgate hp
    · have hqs2 : q + 2 ≤ s :=
        Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hqs) (Ne.symm heq))
      have hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s := by
        have hqsI : (q : Int) + 2 ≤ (s : Int) := by exact_mod_cast hqs2
        change 4 * p.Δ * (q : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int)
        nlinarith
      exact frontier_later_exactService E rho hrec mono crossing writes services hgst hQ hErase
        hHeight hService hu hPhase hqv hvh hCap hafter hgate hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1333–1350, 1500–1583; plan §2.4 and §3.1 step 8.
DC: INTENTIONAL the seeded TFrontier, in its frozen order, through the closed cap.
INLINE writes: `fgsa_leaseOrigins_lastWrite`; INLINE rowCoverage:
`rowPermission_covered E rho hrec.base hrec.fault`, both supplied at Assembly.
Later opening service follows from the covering gate, without an honest proposal
at that label or a phase through that gate. -/
theorem frontier_service [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (scopeProducer : ∀ (q : Slot) (v : Time),
      recoveryStart p E ≤ SA.proposalTime p.toParams q →
      SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon → FrontierServiceScopes E rho q v)
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
          some ((heightView p C).h, (heightView p C).T_h.root)) :
    TFrontier p c E rho := by
  intro u v m J contested q Q Qfg hgst hQ hErase hHeight hService hseed hu hPhase hqv hvh hCap
  have hseedQ := (frontierSeedQualification_iff p E u q).mpr hseed
  have services := scopeProducer q v (hgst.trans hu) hqv hvh
  have hRead := services.read (hgst.trans hu) hqv hvh
  have hcore := frontier_service_core E rho hrec mono crossing scopeProducer writes u v m J
    contested
    q Q Qfg hgst hQ hErase hHeight hService hseed hu hPhase hqv hvh hCap
  refine ⟨hcore.1, hcore.2, frontier_openings E rho hrec crossing rowCoverage
    u v m J contested q Q Qfg hgst hQ hErase hHeight hService hu hPhase hqv hvh hCap ?_⟩
  have huv : u ≤ v := (hu.trans (by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    linarith [p.deltaPos])).trans hqv
  have hcap := frontier_cap_before_on E rho mono huv hCap
  intro r hqr hav
  apply frontierOpeningServed_intro E rho
  intro i x hx ht
  exact frontier_opening_gateService_of_cover E rho hrec mono crossing writes hRead hgst hQ
    hErase hHeight hService hu hPhase hqv hvh hcap hqr hav hx ht

end AvailableChain.FGSA.Run
end

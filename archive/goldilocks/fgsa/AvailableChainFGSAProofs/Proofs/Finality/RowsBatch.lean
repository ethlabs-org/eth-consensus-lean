module
public import AvailableChainFGCompose.Proofs.ServiceTransport -- shake: keep (re-export)
public import AvailableChainFGSAProofs.Proofs.Shared.Gate
public import AvailableChainFGSAProofs.Proofs.Finality.ActionTime
public import AvailableChainFGSAProofs.Proofs.Finality.RowsFrame
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem c2b_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  have hnd' : FGCompose.postClock E rho x t = some nd := by
    rw [← (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1]
    exact hnd
  exact FGCompose.postClock_tick E rho hnd'

private def c2b_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def c2b_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private def c2b_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def c2b_reads (w : HealingWitness) : FGCompose.FGACServiceReads V where
  honest x := x ∈ rho.honest
  proposal := HonestProposal E rho (fgsaInterface p c)
  proposalTime := SA.proposalTime p.toParams
  voteTime := SA.voteTime p.toParams
  gateTime := SA.gateTime p.toParams
  gateLabel q := q * p.R
  actionHeadLabel q := q * p.R + 1
  actionTime := p.actionTime
  proposalScope s _ := w.sStar + 2 ≤ s
  sourceScope x r B := ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
    eraseFG C = B ∧ high p w C
  headScope x s := joinedAt p E rho x s (SA.voteTime p.toParams s)
  gateScope x s := confirmedReaderAtIdx p c E rho x
    (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s)
  actionScope x q := ∃ nd, postClock E rho x (p.actionTime q) = some nd
  headAtLabel := headAtLabel p c E rho
  actionHead x q := (postClock E rho x (p.actionTime q)).map
    (fun nd => (fgBlockOf nd.st (fgHead p nd.st)).map eraseFG)
  gate := gateResult p c E rho
  source := actionSource p c E rho
  parent := proposalHeadAt p c E rho
  gateFloor x s := (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F)
  frame x q B := ∀ nd, postClock E rho x (p.actionTime q) = some nd →
    ∃ D, eraseFG D = B ∧ D ∈ nd.st.fg.TF ∧
      FGBlock.Preceq (FGSA.controls p nd.st).F D ∧
      FGBlock.Preceq (FGSA.controls p nd.st).Z D ∧
      (FGSA.controls p nd.st).lo ≤ (heightView p D).h
  below := Block.Preceq

private theorem c2b_observation_laws (w : HealingWitness) :
    FGCompose.FGACServiceObservationLaws (c2b_reads p c E rho w) (c2b_timing p)
      (fgsaCoreReads p c) (c2b_observations p c) E rho (fgsaInterface p c)
      (gateResult p c E rho)
      (fun x s => (gateIn p c E rho x s).map (fun st => eraseFG st.fg.F))
      (proposalHeadAt p c E rho) (fun s _ => w.sStar + 2 ≤ s)
      (fun x r B => ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        eraseFG C = B ∧ high p w C)
      (fun x s => joinedAt p E rho x s (SA.voteTime p.toParams s))
      (fun x s => confirmedReaderAtIdx p c E rho x
        (afterTicksIdx rho (SA.gateTime p.toParams s)) (SA.gateTime p.toParams s))
      (fun x q => ∃ nd, postClock E rho x (p.actionTime q) = some nd) where
  honest_eq _ := Iff.rfl
  proposal_eq _ _ := Iff.rfl
  proposal_time _ := rfl
  duty_time _ := rfl
  vote_time _ := rfl
  gate_time _ := rfl
  action_time _ := rfl
  gate_label _ := rfl
  action_head_label _ := rfl
  head_eq _ _ := by rw [fgsaCoreReads_def]; rfl
  action_head_eq _ _ := by rw [fgsaCoreReads_def]; rfl
  source_eq x q := by
    rw [fgsaCoreReads_def]
    change ((postClock E rho x (p.actionTime q)).map
      (fun nd => FGSA.fgSource p nd.st)).map (Option.map eraseFG) = _
    rw [Option.map_map]
    rfl
  gate_eq _ _ := rfl
  parent_eq _ := rfl
  floor_eq _ _ := rfl
  below_eq _ _ := Iff.rfl
  proposal_scope _ _ := Iff.rfl
  source_scope _ _ _ := Iff.rfl
  head_scope _ _ := Iff.rfl
  gate_scope _ _ := Iff.rfl
  action_scope _ _ := Iff.rfl
  frame_eq _ _ _ := by
    dsimp only [c2b_observations, c2b_reads]
    rw [fgsaCoreReads_def]
    rfl

private theorem c2b_history_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c) (c2b_observations p c)
      (c2b_timing p) E rho (fgsaInterface p c) (c2b_point p w) horizon := by
  intro x r C hx hC hh _ v Q hQ _ hgap
  rw [fgsaCoreReads_def] at hC ⊢
  exact h x r C v Q hx hC hh hQ hgap

private theorem c2b_history_chain (w : HealingWitness) (h : THigh p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (c2b_observations p c)
      (c2b_timing p) E rho (c2b_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [fgsaCoreReads_def] at hC hD ⊢
  exact ⟨(h x y r q C D hx hy hC hD hc hd).1, (h x y r q C D hx hy hC hD hc hd).2.1⟩

private theorem c2b_service_laws (w : HealingWitness)
    (h1 : THigh p c E rho w) (h2 : TCarrier p c E rho w)
    (h2p : H2Prime p c E rho w) (h2a : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h6 : H6GateService p c E rho w) :
    FGCompose.FGACServiceLaws (c2b_reads p c E rho w) (c2b_point p w)
      (recoveryStart p E) rho.horizon where
  source_chain := by
    intro x y r q C D hx hy hc hd _ _ _ _
    obtain ⟨C', hs, he, hh⟩ := hc
    obtain ⟨D', ht, hf, hk⟩ := hd
    subst C D
    exact (h1 x y r q C' D' hx hy hs ht hh hk).1
  exact_head := by
    intro s Q x hQ hs _ hh hx hr
    exact (h3 s Q hQ hs).1 hh x hx hr
  exact_gate := by
    intro s Q x hQ hs _ hh hx hr
    exact ((h3 s Q hQ hs).2 hh x hx hr).1
  opening_source := by
    intro q Q x hQ hs _ hh hx _ hr
    exact ((h3 (q * p.R) Q hQ hs).2 hh x hx hr).2.2.2.2 q rfl
  proposal_later_head := by
    intro s Q x i H hQ hs _ hx hr hi _ hH
    exact h2p s Q hQ hs x i H ⟨hx, hr⟩ hi hH
  source_next_head := by
    intro y r C x i H hy hc _ _ hx hr hi _ hH
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact (h2a y r C' hy hs hh).1 x i H ⟨hx, hr⟩ hi hH
  covered_source := by
    intro s Q q x _ _ _ hne _ _ ht hs hGST hheads hfloor hx _ hframe
    have hcover : ∀ y ∈ rho.honest, ∃ H,
        headAtLabel p c E rho y (q * p.R) = some H ∧ Block.Preceq Q H := by
      intro y hy
      obtain ⟨H, _, hH, hQ⟩ := hheads y hy
      exact ⟨H, hH, hQ⟩
    have hF : ∀ y st, y ∈ rho.honest → gateIn p c E rho y (q * p.R) = some st →
        Block.Preceq (eraseFG st.fg.F) Q := by
      intro y st hy hst
      exact hfloor y (eraseFG st.fg.F) hy (by
        change (gateIn p c E rho y (q * p.R)).map _ = _
        rw [hst, Option.map_some])
    obtain ⟨_, _, nd, d, hnd, hwrite, hlease, _, hlive⟩ :=
      h6 (q * p.R) Q hs hGST ht.2 hne hcover hF x hx
    obtain ⟨D, hD, hmem, hFD, hZD, hlo⟩ := hframe nd hnd
    obtain ⟨j, _, hclock⟩ := c2b_clock_read p c E rho x (p.actionTime q) nd hnd
    have hkept : D ∈ domainR p nd.st (treeT p nd.st) := by
      rw [domainR_def, treeT_def, frameR_def]
      exact (KitFG.mem_filteredFromView (heightView p) _ _ D).mpr
        ⟨hmem, hFD, hZD, D, hmem, KitFG.preceq_refl D, hlo⟩
    have hround : p.round (nd.st.slot p) = q := by
      rw [← hclock]
      exact (fgsa_action_slot_round (c := c) _ q).2
    have hnow : nd.st.base.now = p.actionTime q := by
      rw [← hclock]
      exact (fgsa_postClock_slot (c := c) _ _).1
    have hserved : eraseFG D ∈ sourceCandidates p nd.st := by
      rw [sourceCandidates_def, hround, hD]
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hwrite,
        by rw [hlease]; exact decide_eq_true (hnow ▸ hlive)⟩
    rw [← hclock] at hkept hserved
    obtain ⟨C, hsource, hDC⟩ := openingSource_extends_served E rho j x q D hkept hserved
    change FGSA.fgSource p (((fgsa p c).clock _ _).st) = some C at hsource
    rw [hclock] at hsource
    refine ⟨eraseFG C, ?_, ?_⟩
    · change actionSource p c E rho x q = some (some (eraseFG C))
      change postClock E rho x (p.actionTime q) = some nd at hnd
      delta actionSource
      simp only [actionSourceFG, hnd, Option.map_some, hsource]
    · change Block.Preceq Q (eraseFG C)
      rw [← hD]
      exact eraseFG_preceq hDC
  parent_transfer := by
    intro x r C s Q hx hc _ _ hQ _ hgap _
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact h2 x r C' s Q hx hs hh hQ hgap

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1234,1251–1254: the action uses the full label-(z+1) HEAD pool.
DC: INTENTIONAL: this read identity supplies no vote admission or batch premise. -/
theorem rowsPrem_action_pools (q : Nat) (x : V) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime q) = some nd) :
    nd.st.slot p = q * p.R + 1 ∧
    (let raw := GridCO.votesAt nd.st.base (q * p.R + 1)
     let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
       | some H => decide (H.slot ≤ q * p.R + 1)
       | none => false)
     FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support) := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
  | none => rw [hi] at hnd; cases hnd
  | some i =>
    rw [hi] at hnd
    have he := Option.some.inj hnd
    have hs : nd.st.slot p = q * p.R + 1 := by
      rw [← he]
      exact (fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho i x) q).1
    refine ⟨hs, ?_⟩
    dsimp only [FGSA.fgHead]
    rw [hs]
    rfl

variable [Fintype V] {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

include hK in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1228–1234,1251–1253,1719–1722: P3 gives the actual HEAD walk batch of the
raw and support pools at action pt.r + 2, with D below every honest label HEAD.
DC: INTENTIONAL: H2′ at label (pt.r+2)R+1, honest admission at the action tick, P5's F ⪯ D. -/
theorem rowsPrem_action_walk_batch
    (hServices : FinalityActionReceipts p c E rho)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      let s := (pt.r + 2) * p.R + 1
      let raw := GridCO.votesAt nd.st.base s
      let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
        | some H => decide (H.slot ≤ s)
        | none => false)
      let seats : Finset (Fin p.n) := by
        classical
        exact Finset.univ.filter (fun k : Fin p.n => rho.seatOf (.base (.head s)) k ∈ rho.honest)
      Gen.Pure.Batch seats.card (Gen.V2.Duty.faulty rho).card ∧
      WalkBatch p c rho nd.st s raw support (eraseFG m.X_D) seats
        (Gen.V2.Duty.faulty rho).card ∧
      FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support := by
  intro x nd hx hnd
  obtain ⟨_, _, _, _, hs2, hGST, _⟩ := kmid_kernel_bounds hK
  have hf := rowsPrem_action_frame p c E rho hK m hQC hXing hNames x nd hx hnd
  have hrD : pt.r * p.R ≤ m.cD := by
    have := m.earlySlot.1
    have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
    omega
  have hservices := c2b_service_laws p c E rho pt.w hK.input.t.h1 hK.input.t.h2
    hK.input.ac.h2' hK.input.ac.h2A hK.input.ac.h3 hK.input.ac.h6
  have hserviceStart : (c2b_point p pt.w).serviceStart ≤
      (c2b_reads p c E rho pt.w).proposalTime m.cD := by
    have hstart := hK.start
    rw [kmid_period_eq] at hstart
    exact hstart.trans (kmid_slot_scale_le p hrD)
  obtain ⟨hvGST, hvte, heh, hvthor⟩ := finality_action_time_bounds p pt.r (pt.r + 2)
    (by omega) E.t_GST E.Δ rho.horizon hGST hK.set.base.delta m.actionsInRun
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hK.set.sync (fgsaDelay_nonrow E.Δ _) hvGST hvte heh
  have hcut := kmid_window_join_cut hK (s := (pt.r + 2) * p.R + 1)
    (by rw [Nat.add_mul]; omega)
  have hJoin : ∀ y ∈ rho.honest, joinedAt p E rho y
      ((pt.r + 2) * p.R + 1) (SA.voteTime p.toParams ((pt.r + 2) * p.R + 1)) :=
    fun y hy => finality_recovery_joined p c E rho hK.set hy hcut hvGST hvthor
  have hbatch := hK.set.batch hvGST hvthor
  have hawake : Gen.V2.Duty.awakeHonest E rho
      (SA.voteTime p.toParams ((pt.r + 2) * p.R + 1)) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun y hy => hK.set.awake y hy _ hvGST hvthor)
  rw [hawake] at hbatch
  have hjh := finality_recovery_joinedHonest p c E rho hK.set hcut hvthor
  rw [← hjh] at hbatch
  have hact : E.t_GST < p.actionTime (pt.r + 2) := by
    have hlt : SA.voteTime p.toParams ((pt.r + 2) * p.R + 1) <
        p.actionTime (pt.r + 2) := by
      rw [kmid_actionTime_eq]
      change 4 * p.Δ * _ + p.Δ < 4 * p.Δ * _ + 6 * p.Δ
      push_cast
      linarith [p.deltaPos]
    exact hvGST.trans_lt hlt
  refine fgsa_action_walk_batch E rho hK.set.base (pt.r + 2) hsync
    hJoin hbatch
    (eraseFG m.X_D) x nd hnd ?_ (eraseFG_preceq hf.2.2.2.2.2.2.2.2.1)
    (fun j _ => finality_recovery_readEpoch p c E rho hK.set hx hact j)
    (fun a K ha hhead => hServices.service (pt.r + 2) x hx hact hcut
      m.actionsInRun nd hnd a K ha hhead
      (Gen.Pure.block_preceq_trans (eraseFG_preceq hf.2.2.2.2.2.2.2.2.1)
        (hservices.proposal_later_head m.cD (eraseFG m.X_D) _ _ K
          m.honestD (hs2.trans hrD) hserviceStart ha (hJoin _ ha)
          (Nat.succ_le_succ m.earlySlot.2) hvthor hhead)))
  · intro y H hy hH
    exact hservices.proposal_later_head m.cD (eraseFG m.X_D) y _ H
      m.honestD (hs2.trans hrD) hserviceStart hy (hJoin y hy)
      (Nat.succ_le_succ m.earlySlot.2) hvthor hH

end AvailableChain.FGSA.Run
end

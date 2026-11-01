module
public import AvailableChainFGSAProofs.Proofs.Finality.RowsBatch
public import AvailableChainFGSAProofs.Proofs.Finality.RowsPrem
public import AvailableChainFGSAProofs.Proofs.Finality.ReceiptSuppliers -- shake: keep (axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.P0Service
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem c2g0_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ j, rho.events[j]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho j x) t = nd := by
  have hnd' : FGCompose.postClock E rho x t = some nd := by
    rw [← (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1]
    exact hnd
  exact FGCompose.postClock_tick E rho hnd'

private def c2g0_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def c2g0_point (p : Params) (w : HealingWitness) : FGCompose.FGServicePoint :=
  ⟨⟨w.rG, w.u₀, w.M, w.rStar, w.sStar, w.CStar⟩, w.u, w.QStar, tstar p w⟩

private def c2g0_observations : FGCompose.FGObservationReads (fgsaCoreReads p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def c2g0_reads (w : HealingWitness) : FGCompose.FGACServiceReads V where
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

private theorem c2g0_observation_laws (w : HealingWitness) :
    FGCompose.FGACServiceObservationLaws (c2g0_reads p c E rho w) (c2g0_timing p)
      (fgsaCoreReads p c) (c2g0_observations p c) E rho (fgsaInterface p c)
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
    dsimp only [c2g0_observations, c2g0_reads]
    simp only [fgsaCoreReads_def]
    rfl

private theorem c2g0_history_transfer (w : HealingWitness) (h : TCarrier p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighTransfer (fgsaCoreReads p c) (c2g0_observations p c)
      (c2g0_timing p) E rho (fgsaInterface p c) (c2g0_point p w) horizon := by
  intro x r C hx hC hh _ v Q hQ _ hgap
  rw [fgsaCoreReads_def] at hC ⊢
  exact h x r C v Q hx hC hh hQ hgap

private theorem c2g0_history_chain (w : HealingWitness) (h : THigh p c E rho w)
    (horizon : Time) :
    FGCompose.FGHistoricalHighChain (fgsaCoreReads p c) (c2g0_observations p c)
      (c2g0_timing p) E rho (c2g0_point p w) horizon := by
  intro x y r q C D hx hy hC hD hc hd _ _
  rw [fgsaCoreReads_def] at hC hD ⊢
  exact ⟨(h x y r q C D hx hy hC hD hc hd).1, (h x y r q C D hx hy hC hD hc hd).2.1⟩

private theorem c2g0_service_laws (w : HealingWitness)
    (h1 : THigh p c E rho w) (h2 : TCarrier p c E rho w)
    (h2p : H2Prime p c E rho w) (h2a : H2A p c E rho w)
    (h3 : H3 p c E rho w) (h6 : H6GateService p c E rho w) :
    FGCompose.FGACServiceLaws (c2g0_reads p c E rho w) (c2g0_point p w)
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
    obtain ⟨j, _, hclock⟩ := c2g0_clock_read p c E rho x (p.actionTime q) nd hnd
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
      simp only [actionSource, actionSourceFG, hnd, Option.map_some, hsource]
    · change Block.Preceq Q (eraseFG C)
      rw [← hD]
      exact eraseFG_preceq hDC
  parent_transfer := by
    intro x r C s Q hx hc _ _ hQ _ hgap _
    obtain ⟨C', hs, he, hh⟩ := hc
    subst C
    exact h2 x r C' s Q hx hs hh hQ hgap

private theorem c2g0_entry_eq (e : NamedHeightPair) :
    FGCompose.namedEntry e = namedEntry e := by cases e <;> rfl

private theorem c2g0_post_eq (x : V) (t : Time) :
    FGCompose.postClock E rho x t = postClock E rho x t :=
  (fgsa_eventReads_eq_compose E rho x t).2.2.2.2.2.1.symm

private theorem c2g0_row_eq (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (fgsaSafetyReads p c) E rho (c2g0_timing p) j y r a =
      HonestRowAt p c E rho j y r a := by
  rw [fgsaSafetyReads_def]
  rfl

-- Local adapters preserve the exact signed wire and the Node-to-State reads.
private def c2g0_carrier (p : Params) (o : Obj p) (_ : Slot) (Q : Block)
    (rows : List (RowWire p.n)) : Prop :=
  ∃ N, o.payload = .proposal N ∧ N.erase = Q ∧ N.rows = rows

private theorem c2g0_carrier_eq (s : Slot) (Q : Block) (rows : List (RowWire p.n)) :
    FGCompose.HonestCarrier E rho (fgsaInterface p c) (c2g0_carrier p) s Q rows =
      HonestCarrier p c E rho s Q rows := by
  simp only [FGCompose.HonestCarrier, HonestCarrier, c2g0_carrier,
    FGCompose.HonestProposal, HonestProposal, exists_and_left]
  rfl

private theorem c2g0_held_before_eq (x : V) (a : RowWire p.n) (d : Time) :
    FGCompose.HeldBefore (fgsaCoreReads p c) E rho
      (fun nd => FGSA.blockWireRows nd.st) x a d = HeldBefore p c E rho x a d := by
  rw [fgsaCoreReads_def]
  rfl

private theorem c2g0_held_proposal_eq (s : Slot) (a : RowWire p.n) :
    FGCompose.heldAtProposal (fgsaCoreReads p c) E rho (fgsaInterface p c)
      (fun nd => FGSA.blockWireRows nd.st) s a = heldAtProposal p c E rho s a := by
  rw [fgsaCoreReads_def]
  apply propext
  constructor
  · rintro ⟨nd, hread, hrow⟩
    exact ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hrow⟩
  · rintro ⟨st, hread, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, hnd, hrow⟩

private theorem c2g0_parent_chain_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.onParentChain E rho (fgsaInterface p c)
      (fun nd => FGSA.chainWireRows nd.st) s Q a = onParentChain p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, hread, hrow⟩
    exact ⟨nd.st, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hrow⟩
  · rintro ⟨st, hread, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, hnd, hrow⟩

private theorem c2g0_valid_parent_eq (s : Slot) (Q : Block) (a : RowWire p.n) :
    FGCompose.ValidForParent E rho (fgsaInterface p c) (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) s Q a =
      ValidForParent p c E rho s Q a := by
  apply propext
  constructor
  · rintro ⟨nd, H, hread, hparent, hrow⟩
    exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · rintro ⟨st, H, hread, hparent, hrow⟩
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hread
    exact ⟨nd, H, hnd, hparent, hrow⟩

private theorem c2g0_rows_select (h : TRowsSelect p c E rho) :
    FGCompose.TRowsSelect (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (c2g0_timing p)
      (fgsaInterface p c) (c2g0_carrier p) (fun nd => FGSA.chainWireRows nd.st)
      (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) := by
  simpa only [FGCompose.TRowsSelect, TRowsSelect, c2g0_carrier_eq, c2g0_row_eq,
    c2g0_valid_parent_eq, c2g0_held_proposal_eq, c2g0_parent_chain_eq] using h

private theorem c2g0_rows_sync (deltaF : Time) (h : TRowsSync p c E rho deltaF) :
    FGCompose.TRowsSync (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (c2g0_timing p)
      (fgsaInterface p c) (c2g0_carrier p) (fun nd => FGSA.chainWireRows nd.st)
      (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => Window.rowValidW (parentFoldState p s H)) deltaF := by
  simp only [FGCompose.TRowsSync, c2g0_carrier_eq, c2g0_row_eq,
    c2g0_valid_parent_eq, c2g0_held_before_eq, c2g0_parent_chain_eq]
  simpa only [TRowsSync, c2g0_timing] using h

private theorem c2g0_rows_receipt (deltaF : Time) (h : TRowsReceipt p c E rho deltaF) :
    FGCompose.TRowsReceipt (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho (c2g0_timing p)
      (fun nd => FGSA.blockWireRows nd.st) deltaF := by
  simp only [FGCompose.TRowsReceipt, c2g0_row_eq, c2g0_held_before_eq]
  simpa only [TRowsReceipt, c2g0_timing] using h

-- HoldsBefore retains a cut whose original event time is strictly below d.
private theorem c2g0_receipt_strict (x : V) (a : RowWire p.n) (d : Time) :
    FGCompose.HeldBefore (fgsaCoreReads p c) E rho
      (fun nd => FGSA.blockWireRows nd.st) x a d ↔
      Gen.V2.Duty.HoldsBefore E rho (fun nd => rowHeld p nd.st a) d x := by
  rw [c2g0_held_before_eq]
  rfl

private theorem c2g0_height_row_eq (r h : Nat) :
    FGCompose.HeightRow (fgsaSafetyReads p c) E rho (c2g0_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) r h =
      HeightRow p c E rho r h := by
  simp only [FGCompose.HeightRow, HeightRow, c2g0_row_eq, c2g0_entry_eq]

private theorem c2g0_mu_eq :
    FGCompose.muOf (fgsaSafetyReads p c) E rho (c2g0_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) =
      muOf p c E rho := by
  unfold FGCompose.muOf FGCompose.oldRowHeights muOf oldRowHeights
  simp only [c2g0_row_eq, c2g0_entry_eq]
  rfl

private theorem c2g0_source_eq (x : V) (r : Nat) :
    FGCompose.actionSourceFG (fgsaCoreReads p c) E rho (c2g0_timing p) x r =
      actionSourceFG p c E rho x r := by
  rw [fgsaCoreReads_def]
  rfl

private theorem c2g0_reset_iff (w : HealingWitness) :
    FGCompose.H0Reset (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (c2g0_observations p c) (c2g0_timing p)
      (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E)
      (c2g0_point p w).reset ↔ H0Reset p c E rho w := by
  constructor <;> intro h
  all_goals
    refine ⟨h.rG_after, h.rG_first, h.cut, ?_, ?_, ?_,
      h.cut_lower, h.cut_upper, ?_, ?_, h.label, ?_, h.synchronous⟩
    · simpa only [c2g0_point, FGCompose.honestFrontier, honestFrontier,
        fgsaCoreReads_def] using h.frontier
    · simpa only [c2g0_point, c2g0_row_eq, c2g0_entry_eq] using h.rowCap
    · simpa only [c2g0_point, c2g0_mu_eq] using h.mu_le
    · simpa only [c2g0_point, c2g0_height_row_eq] using h.reset_row
    · simpa only [c2g0_point, c2g0_height_row_eq] using h.reset_first
    · have hf := h.fresh
      simp only [c2g0_point, c2g0_row_eq, c2g0_entry_eq, c2g0_source_eq] at hf ⊢
      simpa only [c2g0_observations, fgsaCoreReads_def] using hf

private theorem c2g0_bounds (deltaF G allowance : Time) (r : Nat) :
    FGCompose.P (c2g0_timing p) = P p ∧
    FGCompose.Γ (c2g0_timing p) G = Γ p G ∧
    FGCompose.kappaF (c2g0_timing p) deltaF = kappaF p deltaF ∧
    FGCompose.betaF (c2g0_timing p) deltaF = betaF p deltaF ∧
    FGCompose.epsF (c2g0_timing p) deltaF = epsF p deltaF ∧
    FGCompose.E_gF (c2g0_timing p) deltaF G allowance = E_gF p deltaF G allowance ∧
    FGCompose.E_jF (c2g0_timing p) deltaF G allowance = E_jF p deltaF G allowance ∧
    FGCompose.B_cF (c2g0_timing p) deltaF G allowance = B_cF p deltaF G allowance ∧
    FGCompose.D_cF (c2g0_timing p) allowance = D_cF p allowance ∧
    FGCompose.B_resetF (c2g0_timing p) deltaF G allowance = B_resetF p deltaF G allowance ∧
    FGCompose.carrierTimeW (c2g0_timing p) deltaF r = carrierTimeW p deltaF r ∧
    FGCompose.kernelDeadlineW (c2g0_timing p) deltaF r = kernelDeadlineW p deltaF r := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The old kernel also takes hδ explicitly; Params alone does not fix δt.
private theorem c2g0_kernel [Fintype V] {G deltaF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G deltaF E rho pt) (hδ : p.δt = 2 * p.R) :
    FGCompose.KernelPrem_W (c2g0_timing p) deltaF rho.horizon (c2g0_point p pt.w)
      ⟨pt.r⟩ (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.E.q (p.E.weightOf (honestSeats p c rho)) p.δt p.K_W where
  bound := ⟨hK.bound.kappa_le_R⟩
  window := hK.window
  start := hK.start
  hhor := hK.hhor
  honest_quorum := kmid_honest_quorum p c rho hK.set.base.linked hK.set.fault
  timeout_eq := hδ
  capacity_ge := p.kWLarge

private theorem c2g0_reset_before_start (w : HealingWitness) (h : H0 p c E rho w) :
    p.actionTime w.rStar < (c2g0_point p w).serviceStart := by
  have hgap : w.rStar * p.R + 2 ≤ w.u := h.label ▸ h.proposal_lower
  have hd := p.deltaPos
  change SA.gateTime p.toParams (w.rStar * p.R) < SA.gateTime p.toParams w.u
  change 4 * p.Δ * (w.rStar * p.R : Nat) + 6 * p.Δ <
    4 * p.Δ * (w.u : Time) + 6 * p.Δ
  have hcast : (w.rStar * p.R : Time) + 2 ≤ w.u := by exact_mod_cast hgap
  push_cast
  nlinarith

private theorem c2g0_opening_high (w : HealingWitness) (h0 : H0 p c E rho w)
    (h2 : TCarrier p c E rho w) (q : Nat) (A : FGBlock (Fin p.n))
    (hA : HonestProposal E rho (fgsaInterface p c) (q * p.R) (eraseFG A))
    (hgap : w.sStar + 2 ≤ q * p.R)
    (hhor : p.actionTime w.rStar ≤ rho.horizon)
    (hprop : SA.proposalTime p.toParams (q * p.R) ≤ rho.horizon) :
    p.actionTime w.rStar < (c2g0_point p w).serviceStart ∧
      w.M + 1 ≤ (heightView p A).h := by
  obtain ⟨j, y, a, C, hrow, _, hs, _, hh⟩ := h0.fresh
  have hp := c2g0_history_transfer p c E rho w h2 rho.horizon y w.rStar C
    hrow.1 (by rw [fgsaCoreReads_def]; exact hs)
    (by change w.M + 1 ≤ (heightView p C).h; rw [hh]) hhor
    (q * p.R) (eraseFG A) hA hprop (by
      change w.rStar * p.R + 2 ≤ q * p.R
      rw [← h0.label]
      exact hgap)
  rw [fgsaCoreReads_def, eraseFG_parent] at hp
  have hCA : FGBlock.Preceq C A.parent := (eraseFG_preceq_iff).mp hp
  have hPA := kmid_parent_preceq p A
  exact ⟨c2g0_reset_before_start p c E rho w h0,
    by
      rw [← hh]
      exact ((fgCertificateLaws p).height.h_mono hCA).trans
        ((fgCertificateLaws p).height.h_mono hPA)⟩

private theorem c2g0_earlier_row_cap (w : HealingWitness) (h2 : TCarrier p c E rho w)
    (j : Nat) (x : V) (r q : Nat) (a : RowWire p.n) (C A : FGBlock (Fin p.n))
    (ha : HonestRowAt p c E rho j x r a)
    (hs : actionSourceFG p c E rho x r = some (some C))
    (hc : high p w C) (hrq : r < q)
    (hbefore : p.actionTime r < (c2g0_point p w).serviceStart)
    (hrow : rowHeight a = some (heightView p C).h)
    (hA : HonestProposal E rho (fgsaInterface p c) (q * p.R) (eraseFG A))
    (hr : p.actionTime r ≤ rho.horizon)
    (hq : SA.proposalTime p.toParams (q * p.R) ≤ rho.horizon) :
    p.actionTime r < (c2g0_point p w).serviceStart ∧
      ∃ h, rowHeight a = some h ∧ h ≤ (heightView p A).h := by
  have hgap : r * p.R + 2 ≤ q * p.R := by
    have := Nat.mul_le_mul_right p.R (Nat.succ_le_of_lt hrq)
    have := p.RLarge
    rw [Nat.succ_mul] at *
    omega
  have hp := c2g0_history_transfer p c E rho w h2 rho.horizon x r C ha.1
    (by rw [fgsaCoreReads_def]; exact hs) hc hr
    (q * p.R) (eraseFG A) hA hq hgap
  rw [fgsaCoreReads_def, eraseFG_parent] at hp
  have hCA : FGBlock.Preceq C A.parent := (eraseFG_preceq_iff).mp hp
  have hPA := kmid_parent_preceq p A
  exact ⟨hbefore, (heightView p C).h, hrow,
    ((fgCertificateLaws p).height.h_mono hCA).trans
      ((fgCertificateLaws p).height.h_mono hPA)⟩

-- Use exactly the row and source supplied by H0.fresh, at the same opening/horizon.
private theorem c2g0_fresh_row_cap (w : HealingWitness) (h0 : H0 p c E rho w)
    (h2 : TCarrier p c E rho w) (q : Nat) (A : FGBlock (Fin p.n))
    (hA : HonestProposal E rho (fgsaInterface p c) (q * p.R) (eraseFG A))
    (hgap : w.sStar + 2 ≤ q * p.R)
    (hhor : p.actionTime w.rStar ≤ rho.horizon)
    (hprop : SA.proposalTime p.toParams (q * p.R) ≤ rho.horizon) :
    ∃ j y, ∃ (a : RowWire p.n) (C : FGBlock (Fin p.n)),
      HonestRowAt p c E rho j y w.rStar a ∧
      namedEntry a.payload.height_pair = some (w.M + 1, (heightView p C).T_h.root) ∧
      actionSourceFG p c E rho y w.rStar = some (some C) ∧
      eraseFG C = w.CStar ∧ (heightView p C).h = w.M + 1 ∧
      p.actionTime w.rStar < (c2g0_point p w).serviceStart ∧
      rowHeight a = some (w.M + 1) ∧ w.M + 1 ≤ (heightView p A).h := by
  obtain ⟨j, y, a, C, ha, he, hs, hC, hh⟩ := h0.fresh
  have hrq : w.rStar < q := by
    by_contra hn
    have hm := Nat.mul_le_mul_right p.R (Nat.le_of_not_gt hn)
    rw [h0.label] at hgap
    have hbad : w.rStar * p.R + 2 ≤ w.rStar * p.R := hgap.trans hm
    omega
  have hrow : rowHeight a = some (heightView p C).h := by
    rw [hh]
    cases hp : a.payload.height_pair with
    | empty => simp [namedEntry, hp] at he
    | vote h e timeout =>
      simp only [namedEntry, hp] at he
      have heq : h = w.M + 1 := (Prod.mk.inj (Option.some.inj he)).1
      simpa only [rowHeight, hp] using congrArg some heq
  have hcap := c2g0_earlier_row_cap p c E rho w h2 j y w.rStar q a C A ha hs
    (by change w.M + 1 ≤ (heightView p C).h; rw [hh]) hrq
    (c2g0_reset_before_start p c E rho w h0) hrow hA hhor hprop
  obtain ⟨hbefore, h, hrow', hle⟩ := hcap
  have heq : h = w.M + 1 := by
    rw [hh] at hrow
    exact Option.some.inj (hrow'.symm.trans hrow)
  exact ⟨j, y, a, C, ha, he, hs, hC, hh, hbefore, heq ▸ hrow', heq ▸ hle⟩

private theorem c2g0_start_laws (w : HealingWitness) (h : H0 p c E rho w)
    (budget horizon : Time)
    (hbound : tstar p w < recoveryStart p E + budget)
    (hhor : tstar p w ≤ horizon) :
    FGCompose.FGServiceStartLaws (c2g0_timing p) (recoveryStart p E) horizon budget
      (fun reset => FGCompose.H0Reset (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
        (c2g0_observations p c) (c2g0_timing p)
        (fun a => FGCompose.namedEntry a.payload.height_pair) (recoveryStart p E) reset)
      (fun reset s B => reset.sStar + 2 ≤ s ∧
        HonestProposal E rho (fgsaInterface p c) s B ∧
        (∀ v Q, reset.sStar + 2 ≤ v →
          HonestProposal E rho (fgsaInterface p c) v Q → s ≤ v) ∧
        E.t_GST ≤ SA.gateTime p.toParams s ∧ Block.Preceq reset.source B)
      (c2g0_point p w) := by
  refine ⟨(c2g0_reset_iff p c E rho w).mpr h.toH0Reset,
    ⟨h.proposal_lower, h.proposal, h.proposal_first, h.after_gst, h.source_prefix⟩,
    h.source_prefix, ?_, ?_, hbound, hhor⟩
  · change SA.proposalTime p.toParams w.u ≤ SA.gateTime p.toParams w.u
    change 4 * p.Δ * (w.u : Time) ≤ 4 * p.Δ * (w.u : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  · have hcut : w.u₀ < p.actionTime w.rStar := by
      by_contra hn
      have hle : p.actionTime w.rStar ≤ w.u₀ := le_of_not_gt hn
      obtain ⟨j, y, a, C, hrow, he, _, _, _⟩ := h.fresh
      have := h.rowCap j y w.rStar a (w.M + 1) (heightView p C).T_h.root
        (p.actionTime w.rStar) hrow hrow.2.1 hle he
      exact Nat.not_succ_le_self w.M this
    have hperiod : 0 ≤ P p :=
      mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg _)) p.deltaPos.le
    have hstart := c2g0_reset_before_start p c E rho w h
    have hlower := h.cut_lower
    linarith

private def c2g0_receiver {o : Obj p} {send freeze : Time} {x : V}
    (h : ReceiverService E rho o send freeze x) :
    FGCompose.ReceiverService (fun o => ¬ isRowObject o) (fgsaTimely p)
      E rho o send freeze x where
  dl := h.dl
  cut := h.cut
  anchor := h.anchor
  within := h.within
  ready := h.ready
  send_le := h.send_le
  nonneg := h.nonneg
  later := h.later
  cut_le := h.cut_le
  horizon := h.horizon
  freeze_le := h.freeze_le
  history := h.history
  epoch := h.epoch
  handlers := h.handlers
  not_excluded := h.not_excluded

private def c2g0_fresh {s : Slot} {q : Fin p.n} {b : BlockId} {freeze : Time} {x : V}
    (h : FreshHeadService E rho s q b freeze x) :
    FGCompose.FreshHeadService (fun o => ¬ isRowObject o) (fgsaTimely p) (c2g0_timing p)
      (fun s q b => ofHead p ⟨.seat (.head s) q, b⟩) E rho s q b freeze x where
  dl := h.dl
  cut := h.cut
  within := h.within
  ready := h.ready
  later := h.later
  cut_le := h.cut_le
  horizon := h.horizon
  freeze_le := h.freeze_le
  epoch := h.epoch
  handlers := h.handlers
  not_excluded := h.not_excluded

private theorem c2g0_same_height (w : HealingWitness) (hh : THigh p c E rho w)
    (x y : V) (r q : Nat) (C D : FGBlock (Fin p.n))
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hc : actionSourceFG p c E rho x r = some (some C))
    (hd : actionSourceFG p c E rho y q = some (some D))
    (hC : high p w C) (hD : high p w D)
    (heq : (heightView p C).h = (heightView p D).h)
    (hr : p.actionTime r ≤ rho.horizon) (hq : p.actionTime q ≤ rho.horizon) :
    (heightView p C).T_h = (heightView p D).T_h := by
  have hc' : (FGCompose.postClock E rho x ((c2g0_timing p).action r)).map
      (fgsaCoreReads p c).source = some (some C) := by
    rw [fgsaCoreReads_def]; exact hc
  have hd' : (FGCompose.postClock E rho y ((c2g0_timing p).action q)).map
      (fgsaCoreReads p c).source = some (some D) := by
    rw [fgsaCoreReads_def]; exact hd
  have hcompat := (c2g0_history_chain p c E rho w hh rho.horizon
    x y r q C D hx hy hc' hd' hC hD hr hq).1
  rw [fgsaCoreReads_def] at hcompat
  change ((eraseFG C).preceq (eraseFG D) || (eraseFG D).preceq (eraseFG C)) = true at hcompat
  rw [Bool.or_eq_true] at hcompat
  rcases hcompat with h | h
  · exact (fgCertificateLaws p).height.entry_plateau (eraseFG_preceq_iff.mp h) heq
  · exact ((fgCertificateLaws p).height.entry_plateau (eraseFG_preceq_iff.mp h) heq.symm).symm

private theorem c2g0_next_label (w : HealingWitness) (deltaF : Time)
    (h : HealingInput p c E rho w deltaF) (x y : V) (r : Nat)
    (C : FGBlock (Fin p.n)) (H : Block) (hy : y ∈ rho.honest)
    (hs : actionSourceFG p c E rho y r = some (some C)) (hc : high p w C)
    (ht : FGCompose.InSuffix (c2g0_point p w) rho.horizon (p.actionTime r))
    (hx : x ∈ rho.honest)
    (hr : joinedAt p E rho x (r * p.R + 1) (SA.voteTime p.toParams (r * p.R + 1)))
    (hh : SA.voteTime p.toParams (r * p.R + 1) ≤ rho.horizon)
    (hH : headAtLabel p c E rho x (r * p.R + 1) = some H) :
    SA.voteTime p.toParams (r * p.R + 1) < p.actionTime r ∧
      Block.Preceq (eraseFG C) H := by
  refine ⟨?_, ?_⟩
  · change 4 * p.Δ * ((r * p.R + 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  · exact FGCompose.service_source_next
      (c2g0_service_laws p c E rho w h.t.h1 h.t.h2 h.ac.h2' h.ac.h2A h.ac.h3 h.ac.h6)
      hy ⟨C, hs, rfl, hc⟩ (by change actionSource p c E rho y r = _; rw [actionSource, hs]; rfl)
      ht hx hr (Nat.le_refl _) hh hH

private theorem c2g0_pools (q : Nat) (x : V) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime q) = some nd) :
    nd.st.slot p = q * p.R + 1 ∧
    (let raw := GridCO.votesAt nd.st.base (q * p.R + 1)
     let support := raw.filter (fun o => match GridCO.resolvedHead? (FGSA.actView nd.st) o with
       | some H => decide (H.slot ≤ q * p.R + 1)
       | none => false)
     FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support) :=
  rowsPrem_action_pools p c E rho q x nd hnd

private theorem c2g0_output_frame [Fintype V] {G deltaF : Time} {pt : KernelPt}
    {A : Block} (hK : KernelPrem_W p c G deltaF E rho pt)
    (m : KernelMiddleWitness_W p c E rho deltaF pt A)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (x : V) (nd : Node p) (hx : x ∈ rho.honest)
    (hnd : postClock E rho x (p.actionTime (pt.r + 2)) = some nd) :
    Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG m.X_D) :=
  rowsPrem_liveRoot_compatible p c E rho hK m hQC hXing hNames x nd hx hnd

-- Rebuild the old unbounded inputs from the projected laws on their service scope.
-- Outside that scope, keep the original facts. All fields use the same service point.
private theorem c2g0_consumer_input (w : HealingWitness) (deltaF : Time)
    (h : HealingInput p c E rho w deltaF) : HealingInput p c E rho w deltaF := by
  have hs := c2g0_service_laws p c E rho w h.t.h1 h.t.h2
    h.ac.h2' h.ac.h2A h.ac.h3 h.ac.h6
  have hp : H2Prime p c E rho w := by
    intro s Q hQ hscope x i H hr hi hH
    by_cases ht : (c2g0_point p w).serviceStart ≤ SA.proposalTime p.toParams s
    · by_cases hh : SA.voteTime p.toParams i ≤ rho.horizon
      · exact hs.proposal_later_head s Q x i H hQ hscope ht hr.1 hr.2 hi hh hH
      · exact h.ac.h2' s Q hQ hscope x i H hr hi hH
    · exact h.ac.h2' s Q hQ hscope x i H hr hi hH
  have ha : H2A p c E rho w := by
    intro y r C hy hC hc
    refine ⟨?_, (h.ac.h2A y r C hy hC hc).2⟩
    intro x i H hr hi hH
    by_cases ht : FGCompose.InSuffix (c2g0_point p w) rho.horizon (p.actionTime r)
    · by_cases hh : SA.voteTime p.toParams i ≤ rho.horizon
      · exact hs.source_next_head y r (eraseFG C) x i H hy ⟨C, hC, rfl, hc⟩
          (by change actionSource p c E rho y r = _; rw [actionSource, hC]; rfl)
          ht hr.1 hr.2 hi hh hH
      · exact (h.ac.h2A y r C hy hC hc).1 x i H hr hi hH
    · exact (h.ac.h2A y r C hy hC hc).1 x i H hr hi hH
  exact { h with ac := { h.ac with h2' := hp, h2A := ha } }

section Consumers
variable [Fintype V] {G deltaF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G deltaF E rho pt)
    (m : KernelMiddleWitness_W p c E rho deltaF pt A)

-- Both actual consumer labels are in the projected proposal service scope.
include hK in
private theorem c2g0_consumer_scope :
    (c2g0_point p pt.w).serviceStart ≤ SA.proposalTime p.toParams m.cD ∧
      pt.w.sStar + 2 ≤ m.cD ∧
      m.cD ≤ (pt.r + 2) * p.R ∧
      SA.voteTime p.toParams ((pt.r + 2) * p.R + 1) ≤ rho.horizon := by
  have hrD : pt.r * p.R ≤ m.cD := by
    have := m.earlySlot.1
    have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
    omega
  have hstart := hK.start
  rw [kmid_period_eq] at hstart
  obtain ⟨_, _, _, _, hs2, hGST, _⟩ := kmid_kernel_bounds hK
  have htimes := finality_action_time_bounds p pt.r (pt.r + 2) (by omega)
    E.t_GST E.Δ rho.horizon hGST hK.set.base.delta m.actionsInRun
  exact ⟨hstart.trans (kmid_slot_scale_le p hrD), hs2.trans hrD,
    m.earlySlot.2, htimes.2.2.2⟩

variable (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))

include hK hQC hXing hNames in
private theorem c2g0_source_consumer :
    ∀ x ∈ rho.honest, ∃ nd C,
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd ∧
      FGSA.fgSource p nd.st = some C ∧ FGBlock.Preceq m.X_D C ∧
      (heightView p C).h = m.d + 2 ∧
      (heightView p C).T_h = (heightView p m.X_D).T_h := by
  have hProjected : KernelPrem_W p c G deltaF E rho pt :=
    { hK with input := c2g0_consumer_input p c E rho pt.w deltaF hK.input }
  exact rowsPrem_action_source p c E rho hProjected m hQC hXing hNames

include hK hQC hXing hNames in
private theorem c2g0_batch_consumer
    (hServices : FinalityActionReceipts p c E rho) :
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
  have hProjected : KernelPrem_W p c G deltaF E rho pt :=
    { hK with input := c2g0_consumer_input p c E rho pt.w deltaF hK.input }
  exact rowsPrem_action_walk_batch p c E rho hProjected m hServices hQC hXing hNames

include hK hQC hXing hNames in
private theorem d7a4g0_pending_consumer
    (hServices : FinalityActionReceipts p c E rho) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      ∃ H : FGBlock (Fin p.n),
        FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧ FGBlock.Preceq m.X_D H ∧
        (heightView p H).h = m.d + 2 ∧ (heightView p H).J = m.U ∧
        (heightView p H).h_j = m.d + 1 ∧ (finalityView p H).h_F < m.d + 1 ∧
        (heightView p H).T_h = (heightView p m.X_D).T_h := by
  have hProjected : KernelPrem_W p c G deltaF E rho pt :=
    { hK with input := c2g0_consumer_input p c E rho pt.w deltaF hK.input }
  exact rowsPrem_pending_head p c E rho hProjected m hServices hQC hXing hNames

include hK hQC hXing hNames in
private theorem d7a4g0_fresh_consumer
    (hServices : FinalityActionReceipts p c E rho)
    (S : Finset (Fin p.n)) (hS : S ⊆ honestSeats p c rho) (hQ : p.E.IsQuorum S) :
    ∃ rows : Fin p.n → RowWire p.n,
      FreshFinalityRows_W p c E rho (pt.r + 2) (m.d + 1) m.U S rows ∧
      ∀ i ∈ S, (rows i).payload.height_pair =
        NamedHeightPair.vote (m.d + 2) (heightView p m.X_D).T_h.root false := by
  have hProjected : KernelPrem_W p c G deltaF E rho pt :=
    { hK with input := c2g0_consumer_input p c E rho pt.w deltaF hK.input }
  obtain ⟨rows, fresh, _, pair⟩ :=
    rowsPrem_fresh_rows p c E rho hProjected m hServices hQC hXing hNames S hS hQ
  exact ⟨rows, fresh, pair⟩

end Consumers

private def c2g0_decode (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem c2g0_decode_iff (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    c2g0_decode p o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold c2g0_decode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem c2g0_opening_iff (s : Slot) (A : Block) (Afg : FGBlock (Fin p.n)) :
    FGCompose.OpeningCarrier_W (c2g0_decode p) NamedProposal.erase NamedProposal.rows
      (fun nd : Node p => FGSA.parentFG nd.st) FGSA.fgBlock E rho (fgsaInterface p c)
      s A Afg ↔ OpeningCarrier_W p c E rho s A Afg := by
  rw [OpeningCarrier_W_def]
  constructor
  · rintro ⟨o, N, nd, Par, he, hN, hd, hnd, hpar, hfg⟩
    refine ⟨o, N, nd.st, Par, he, hN, (c2g0_decode_iff p o s N).mp hd, ?_, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _
    rw [hnd]
    rfl
  · rintro ⟨o, N, st, Par, he, hN, hd, hst, hpar, hfg⟩
    change (FGCompose.proposalStateAt E rho (fgsaInterface p c) s).map Node.st = _ at hst
    obtain ⟨nd, hnd, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact ⟨o, N, nd, Par, he, hN, (c2g0_decode_iff p o s N).mpr hd, hnd, hpar, hfg⟩

private theorem c2g0_result_iff (deltaF : Time) (r : Nat) :
    FGCompose.KernelConclusion_W (fgsaCoreReads p c) E rho (c2g0_observations p c)
      (c2g0_timing p) (fgsaInterface p c) (c2g0_decode p)
      NamedProposal.erase NamedProposal.rows (fun nd : Node p => FGSA.parentFG nd.st)
      FGSA.fgBlock deltaF r ↔ KernelConclusion_W p c E rho deltaF r := by
  simp only [FGCompose.KernelConclusion_W, KernelConclusion_W_def, c2g0_opening_iff,
    c2g0_timing, c2g0_observations, fgsaCoreReads_def]
  rfl

#print axioms c2g0_fresh_row_cap
#print axioms c2g0_kernel
#print axioms c2g0_rows_select
#print axioms c2g0_rows_sync
#print axioms c2g0_rows_receipt
#print axioms c2g0_receipt_strict

#print axioms c2g0_consumer_input
#print axioms c2g0_consumer_scope
#print axioms c2g0_source_consumer
#print axioms c2g0_batch_consumer
#print axioms c2g0_clock_read
#print axioms c2g0_result_iff
#print axioms c2g0_opening_iff
#print axioms c2g0_timing
#print axioms c2g0_point
#print axioms c2g0_observations
#print axioms c2g0_reads
#print axioms c2g0_observation_laws
#print axioms c2g0_history_transfer
#print axioms c2g0_history_chain
#print axioms c2g0_service_laws
#print axioms c2g0_reset_iff
#print axioms c2g0_bounds
#print axioms c2g0_reset_before_start
#print axioms c2g0_opening_high
#print axioms c2g0_earlier_row_cap
#print axioms c2g0_start_laws
#print axioms c2g0_receiver
#print axioms c2g0_fresh
#print axioms c2g0_same_height
#print axioms c2g0_next_label
#print axioms c2g0_pools
#print axioms d7a4g0_pending_consumer
#print axioms d7a4g0_fresh_consumer
#print axioms c2g0_output_frame

end AvailableChain.FGSA.Run.Tests.P0Service
end

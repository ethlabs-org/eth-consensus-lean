module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchHG2a -- shake: keep (leaf defs)
public import AvailableChainFGSAProofs.Proofs.Healing.Promotion
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.Descent
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAbove
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing
public import AvailableChainFGSAProofs.Proofs.Foundations.Counts
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGSAProofs.Proofs.Shared.HealingFixture -- shake: keep (fixture)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cTstCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private theorem p0d5cTstCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d5cTstCore p c) := by
  have h : p0d5cTstCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm
  rw [h]
  exact fgsaCoreLaws p c

private def p0d5cTstTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cTstTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cTstTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d5cTstObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d5cTstCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d5cTstObsLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d5cTstCore p c) (p0d5cTstObs p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d5cTstSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

private def p0d5cTstSigner {p : Params} (a : RowWire p.n) : Option (Fin p.n) := match a.auth with
  | .seat .fg i => some i
  | _ => none

private theorem p0d5cTstDecodeRow {p : Params} {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

private def p0d5cTstWire (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGHistoryWireReads (p0d5cTstSafety p c) where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer := p0d5cTstSigner
  decode_height a u ha := by
    delta p0d5cTstSafety at ha
    rw [p0d5cTstDecodeRow ha]
    rfl
  decode_finality a u ha := by
    delta p0d5cTstSafety at ha
    rw [p0d5cTstDecodeRow ha]
    rfl
  decode_signer a u ha := by
    delta p0d5cTstSafety at ha
    rw [p0d5cTstDecodeRow ha]
    rfl

private def p0d5cTstDecode {p : Params} (o : Obj p) : Option (Slot × NamedProposal p.n) :=
  match (toWire p o).decode with
  | some (.block s N) => some (s, N)
  | _ => none

private theorem p0d5cTstDecode_iff {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n) :
    p0d5cTstDecode o = some (s, N) ↔ (toWire p o).decode = some (.block s N) := by
  unfold p0d5cTstDecode
  cases hd : (toWire p o).decode with
  | none => simp
  | some wire => cases wire <;> simp

private theorem p0d5cTstPayload {p : Params} (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ := by
  apply toWire_injective
  rw [toWire_ofWire]
  exact decode_eq_block.mp hd

private theorem p0d5cTstSigner_iff {p : Params} (a : RowWire p.n) (i : Fin p.n) :
    p0d5cTstSigner a = some i ↔ a.auth = .seat .fg i := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => delta p0d5cTstSigner; simp
  | proposer s => delta p0d5cTstSigner; simp
  | seat label j => cases label <;> delta p0d5cTstSigner <;> simp

private def p0d5cTstWindow {p : Params} (w : Window.State (Fin p.n)) :
    SimplexFG.Window.State (Fin p.n) :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map (fun e => ⟨e.j, e.X, e.Q⟩), w.J, w.h_j, w.F, w.h_F⟩

private theorem p0d5cTstR6 {p : Params} (w : Window.State (Fin p.n)) (a : RowWire p.n) :
    Window.rowValidW w a =
      match a.toRow? with
      | none => false
      | some b => SimplexFG.Window.r6w (p0d5cTstWindow w) b := by
  rw [Window.rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
    delta p0d5cTstWindow
    cases hp : b.height_pair <;> cases hf : b.finality_pair <;>
      simp only [Window.r6w_def, Window.heightMatch_def, Window.staleUseful_def,
      Window.windowMatch_def, SimplexFG.Window.r6w_def, SimplexFG.Window.heightMatch_def,
      SimplexFG.Window.staleUseful_def, SimplexFG.Window.windowMatch_def,
      List.any_map, Function.comp_def, hp, hf]


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d5cTstKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private abbrev p0d5cTstPair (a : RowWire p.n) : NamedHeightPair := a.payload.height_pair

private theorem p0d5cTstPhase_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} :
    FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u v m J contested ↔
      PhaseInterval p c E rho u v m J contested := by
  cases J <;> exact Iff.rfl

omit [DecidableEq V] in
private theorem p0d5cTstSeed_iff (E : Generic.Env V) {u : Time} {q : Slot} :
    FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q ↔
      FrontierSeedQualification p E u q :=
  (frontierSeedQualification_iff p E u q).symm

private theorem p0d5cTstStart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {ev : V2.Event V (Obj p)} {kind : PhaseKind}
    (h : FrontierSearchStart p c E rho i ev m kind) :
    FGCompose.FrontierSearchStart (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (recoveryStart p E) i ev m (p0d5cTstKind kind) := by
  have h' := (frontierSearchStart_iff p c E rho i ev m kind).mp h
  cases kind <;> exact h'

-- The proved TFrontier route from the recovery regime (FrontierService).
private theorem p0d5cTstRoute [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) : TFrontier p c E rho :=
  frontier_service E rho hrec mono crossing
    (fun q v _ _ _ => healing_frontier_service_scopes_recovery E rho hrec mono q v)
    (fun i x row hr => fgsa_leaseOrigins_lastWrite p c E rho
      hrec.base.valid.toScheduleWellFormed i x row hr)
    (rowPermission_covered E rho hrec.base hrec.fault)

-- Proposer floor leaf: healing_proposer_floor at the proposer's phase read.
private theorem p0d5cTstFloor [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.AttemptProposalFloor (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u v m J contested q Q Qfg _ hp hu hgate hQ heq
  have hp' := (p0d5cTstPhase_iff E rho).mp hp
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _hem, hst, _hslot, _hb, _hrows⟩ :=
    healing_promotion_proposal_read p c E rho hS hQ
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x)
    (SA.proposalTime p.toParams q)).st
  have hx : x ∈ rho.honest := hQ.1.2
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hui := healing_support_idxBefore_le p c E rho hS hj hu
  have hjD := (healing_phase_lt_timeIdx p c E rho hS hj (hqg.trans hgate)).le
  obtain ⟨hH, hc, _hr⟩ := hp'.2.2.2 j x hui hjD hx
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, _hB, heB, hlo⟩ := healing_proposer_floor p c E rho hS q Q st hQ hst hne
  have he : B = Qfg.parent := eraseFG_injective (heB.trans
    (by rw [← eraseFG_parent]; exact congrArg Block.parent heq.symm))
  have hH' : st.fg.h_max = m := by rw [hfg]; exact hH
  have hc' : (FGSA.controls p st).contest = contested := by
    change (KitFG.treeStoreControlsView (heightView p) st.fg).contest = contested
    rw [hfg]
    exact hc
  change (if (FGSA.controls p st).contest then st.fg.h_max else st.fg.h_max - 1) ≤ _ at hlo
  rw [hH', hc', he] at hlo
  exact hlo

private theorem p0d5cTstWitness (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (p0d5cTstCore p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem p0d5cTstReceipts (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i m : Nat} {deadline : Time} (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (p0d5cTstCore p c) E rho (p0d5cTstObs p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, p0d5cTstWitness E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, p0d5cTstWitness E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, p0d5cTstWitness E rho hrC, p0d5cTstWitness E rho
      hrW⟩

-- The frozen repair arm gives exact service to each seed-qualified window proposal.
private theorem p0d5cTstExact [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {u v : Time} {m q : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {Q : Block}
    (hready : recoveryStart p E ≤ u) (hseed : FrontierSeedQualification p E u q)
    (hp : PhaseInterval p c E rho u v m J contested) (hg : SA.gateTime p.toParams q ≤ v)
    (hQ : HonestProposal E rho (fgsaInterface p c) q Q) : ExactService p c E rho q Q := by
  obtain ⟨l, hlq, hrep⟩ := frontierSearch_seed_repair E rho repair
    (healing_proposal_gap hrec) hrec.gapPos hready hseed (m := m) (J := J)
    (contested := contested)
  exact hrep v hp q Q hlq hg hQ

-- Gate copy leaf: the exact gate service of a repair-window proposal (RiseOne).
private theorem p0d5cTstGateCopy [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho) :
    ∀ u v m J contested q Q, recoveryStart p E ≤ u →
      FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u v m J contested →
      FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q →
      SA.gateTime p.toParams q ≤ v → HonestProposal E rho (fgsaInterface p c) q Q →
      ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧ i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.TF ∧
        (p0d5cTstCore p c).erase Qfg = Q := by
  intro u v m J contested q Q hready hp hseed hg hQ
  have hp' := (p0d5cTstPhase_iff E rho).mp hp
  have hseed' := (p0d5cTstSeed_iff E).mp hseed
  have hexact := p0d5cTstExact E rho hrec repair hready hseed' hp' hg hQ
  have hu := frontierSearch_seed_after E hseed'
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hs := hrec.base.valid.toScheduleWellFormed
  have hx := hQ.1.2
  have hgh := hg.trans hp'.2.1
  obtain ⟨j, Qfg, hj, hmem, he⟩ := healing_rise_one_gate_copy p c E rho hs hexact hgh hx
    (healing_recovery_gate_reader hrec hx (hGST.trans hu) hgh)
  have hug : u ≤ SA.gateTime p.toParams q := by
    change u ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  exact ⟨j, _, Qfg, healing_support_idxBefore_le p c E rho hs hj hug,
    (healing_phase_lt_timeIdx p c E rho hs hj hg).le, hx, hmem, he⟩

-- Continuing local service leaf: TFrontier at the exact-service seed.
private theorem p0d5cTstService [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (frontier : TFrontier p c E rho) :
    ∀ u v m J contested q Q Qfg, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q →
      (p0d5cTstCore p c).erase Qfg = Q → ((p0d5cTstObs p c).height Qfg).h = m →
      FGCompose.FrontierProposalService (p0d5cTstCore p c) E rho (p0d5cTstTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q →
      FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u (SA.gateTime p.toParams
        q)
        m J contested → SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
        (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair q Q Qfg m v := by
  intro u v m J contested q Q Qfg hready hQ he hh _ hseed hu hp hg hv hcap
  have hp' := (p0d5cTstPhase_iff E rho).mp hp
  have hseed' := (p0d5cTstSeed_iff E).mp hseed
  have hexact := p0d5cTstExact E rho hrec repair hready hseed' hp' le_rfl hQ
  obtain ⟨htransfer, hrepair, hopen⟩ := frontier u v m J contested q Q Qfg hready hQ he hh
    hexact ((frontierSeedQualification_iff p E u q).mp hseed') hu hp' hg hv hcap
  refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
  · intro s B hqs hgate hprop
    exact (hrepair s B hqs hgate hprop).1
  · intro r hqr hrt
    obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
    refine ⟨?_, hent, hheight, htime⟩
    intro x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ', hr, ha, hn⟩ := hcov x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ', hr, ha, hn⟩

-- Local repair allowance: both frozen TRepair arms at the frozen first labels.
private theorem p0d5cTstAllowance [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar u : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (mode : FrontierRepairStart p E G u ρbar) :
    FGCompose.FrontierRepairAllowance (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) p.k G ρbar u := by
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  have hG := (fgsa_gamma_bounds p G).1
  cases mode with
  | two β after least =>
    refine ⟨by
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .two β after least, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5cTstPhase_iff E rho).mp hp)).1 β after least
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2, hQ, he.1⟩
  | one b after least window sync =>
    refine ⟨by
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos], _, .one b after least window sync, ?_⟩
    intro hG4 v m J contested hready hp
    obtain ⟨hafter, hex⟩ := (repair G u v m J contested (healing_proposal_gap hrec) hG4 hready
      ((p0d5cTstPhase_iff E rho).mp hp)).2 b after least window sync
    refine ⟨fun s Q hls hg hQ => (hafter s Q hls hg hQ).1, fun hb => ?_⟩
    obtain ⟨s, Q, h1, h2, hQ, he⟩ := hex hb
    exact ⟨s, Q, h1, h2.le, hQ, he.1⟩

-- The generic saved seed of a repair-window proposal keeps its frozen exact service.
private theorem p0d5cTstServedBack [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {m : Nat} {t : Time}
    (h : FGCompose.StrongServed (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
      (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair (recoveryStart p E) p.k m t) :
    StrongServed p c E rho m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh, _, hseed, hu, hp, hg, hth, hcap,
    _⟩ := h
  have hp' := (p0d5cTstPhase_iff E rho).mp hp
  have hseed' := (p0d5cTstSeed_iff E).mp hseed
  exact (strongServed_iff p c E rho m t).mpr ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hh,
    p0d5cTstExact E rho hrec repair hready hseed' hp' le_rfl hQ, hseed', hu, hp', hg, hth, hcap⟩

private theorem p0d5cTstResultBack [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    {i m : Nat} {start dl : Time}
    (h : FGCompose.FrontierHG3Result (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
      (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair (recoveryStart p E) p.k i m start dl) :
    FrontierHG3Result p c E rho i m start dl := by
  apply (frontierHG3Result_iff p c E rho i m start dl).mpr
  rcases h with h | h | ⟨t, h1, h2, hs⟩
  · exact Or.inl ((firstPhaseStopBy_iff p c E rho i m dl).mpr h)
  · exact Or.inr (Or.inl ((firstRiseStopBy_iff p c E rho i m dl).mpr h))
  · exact Or.inr (Or.inr ⟨t, h1, h2, p0d5cTstServedBack E rho hrec repair hs⟩)


section p0d5cTstD5b
variable [Fintype V]


omit [Fintype V] in
private abbrev p0d5cTstBatch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) :=
  FGCompose.BatchPrem (p0d5cTstCore p c) (p0d5cTstSafety p c) (p0d5cTstObs p c)
    (p0d5cTstTiming p) E rho (fgsaInterface p c) (p0d5cTstWire p c) p.E
    p0d5cTstDecode NamedProposal.erase NamedProposal.rows
    (fun nd => FGSA.blockWireRows nd.st) (fun nd => FGSA.fgBlockOf nd.st)
    (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
    (fun _ s H => Window.rowValidW (parentFoldState p s H)) ΔF .progress q y U X

omit [Fintype V] in
private theorem p0d5cTstCarrierTo (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) (rows : List (RowWire p.n))
    (h : FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5cTstDecode NamedProposal.erase NamedProposal.rows)
      s Q rows) : HonestCarrier p c E rho s Q rows := by
  obtain ⟨hp, o, hemit, N, hd, he, hr⟩ := h
  have ho := p0d5cTstPayload o s N ((p0d5cTstDecode_iff o s N).mp hd)
  subst ho
  exact ⟨hp, _, N, hemit, rfl, he, hr⟩

-- The generic progress batch at these reads yields the frozen batch.
private theorem p0d5cTstBatchFrom (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y : Nat) (U X : FGBlock (Fin p.n)) (h : p0d5cTstBatch E rho ΔF q y U X) :
    BatchPrem p c E rho ΔF .progress q y U X := by
  refine ⟨base, faultQ, h.deltaF, ?_, h.horizon, ?_, h.after, ?_, h.entry, h.path, ?_⟩
  · rw [TRowsReceipt_def]
    exact h.rowsReceipt
  · obtain ⟨rows, hc, hr⟩ := h.carrier
    exact ⟨rows, p0d5cTstCarrierTo E rho _ _ rows hc, hr⟩
  · obtain ⟨Q, hh, hq, hw⟩ := h.valid
    refine ⟨Q, (fun i hi => (kmid_honestSeats_mem p c rho i).mpr (hh i hi)), hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hr, ha, hsign, hn, ht, htime, hv, hm⟩ := hw i hi
    refine ⟨j, r, a, t, hr, ha, (p0d5cTstSigner_iff a i).mp hsign, hn, ht, htime, ?_, ?_⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hv
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
    · obtain ⟨nd, H, hread, hparent, hrow⟩ := hm
      exact ⟨nd.st, H, Option.map_eq_some_iff.mpr ⟨nd, hread, rfl⟩, hparent, hrow⟩
  · intro i hi W hW hr
    exact h.above i ((kmid_honestSeats_mem p c rho i).mp hi) W hW hr

omit [Fintype V] in
private theorem p0d5cTstFoldAdvance (h : foldTrichotomy p .progress) :
    FGCompose.ProgressFoldAdvance p.E (heightView p) p.δt := by
  intro y U X hX hU hUX hc hm
  exact (h y U X hX hU hUX (fun hy => hc hy) (fun _ => hm)).1

private theorem p0d5cTstFault (rho : V2.D.Run V (fgsa p c)) {E : Generic.Env V}
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (FGCompose.historyFaulty (p0d5cTstSafety p c) rho) < p.E.q := by
  classical
  let S := p0d5cTstSafety p c
  have linked : Function.Injective (FGCompose.safetyHolder S rho) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hsub : (FGCompose.historyFaulty S rho).image (FGCompose.safetyHolder S rho) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hc := (Finset.card_image_of_injective _ linked).symm.trans_le
    (Finset.card_le_card hsub)
  have hw : p.E.weightOf (FGCompose.historyFaulty S rho) =
      (FGCompose.historyFaulty S rho).card := by
    delta Electorate.weightOf
    simp only [show ∀ i, p.E.weight i = 1 from fun _ => rfl, Finset.sum_const,
      smul_eq_mul, mul_one]
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt faultQ.lt

-- Proposal leaf: the actual carrier and the post-clock parent read (PromotionCarrier route).
private theorem p0d5cTstRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionProposalRead (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho
      (p0d5cTstObs p c) (fgsaInterface p c) p0d5cTstDecode NamedProposal.erase NamedProposal.rows
      (fun nd => FGSA.fgBlockOf nd.st)
      (fun _ s H => ((parentFoldState p s H).h, (parentFoldState p s H).T_h.root))
      (fun _ s H => Window.rowValidW (parentFoldState p s H))
      (fun _ s H => p0d5cTstWindow (parentFoldState p s H)) := by
  intro s X hQX _
  obtain ⟨Q, hXQ⟩ : ∃ Q, eraseFG X = Q := ⟨_, rfl⟩
  change HonestProposal E rho (fgsaInterface p c) s (eraseFG X) at hQX
  rw [hXQ] at hQX
  change (∃ rows, FGCompose.HonestCarrier E rho (fgsaInterface p c)
      (FGCompose.kernelCarrier p0d5cTstDecode NamedProposal.erase NamedProposal.rows) s
      (eraseFG X) rows ∧ X.rows = rows.filterMap RowWire.toRow?) ∧ _
  rw [hXQ]
  obtain ⟨j, N, heN, hj, hem, hst, _hslot, hb, hrows⟩ :=
    healing_promotion_proposal_read p c E rho hrec.base.valid.toScheduleWellFormed hQX
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v)
    (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : Q.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk Q N.rows = true := by
    rw [hb, hrows]
    exact rowsOk_node_packBody _ _ _ _ _
  have hne : Q ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st Q.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  have hXeq : X = fgBlock P Q N.rows :=
    eraseFG_injective (hXQ.trans (eraseFG_fgBlock hne (hPe.trans hpar.symm) N.rows hok).symm)
  subst hXeq
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  have hdec : p0d5cTstDecode o = some (s, N) :=
    (p0d5cTstDecode_iff o s N).mpr (decode_eq_block.mpr rfl)
  obtain ⟨nd, hnd, hndst⟩ := Option.map_eq_some_iff.mp hst
  refine ⟨⟨N.rows, ⟨hQX, o, hemit, N, hdec, heN, rfl⟩, rfl⟩, nd, hnd, ?_, rfl, rfl, rfl,
    ?_⟩
  · change FGSA.fgBlockOf nd.st (eraseFG (fgBlock P Q N.rows)).parent =
      some (fgBlock P Q N.rows).parent
    rw [hndst, hXQ, fgBlock_parent]
    exact hlook
  · intro a
    have h6 := p0d5cTstR6 (parentFoldState p s (fgBlock P Q N.rows).parent) a
    cases hd : (p0d5cTstSafety p c).decode a <;>
      (change RowWire.toRow? a = _ at hd; simpa only [hd] using h6)

-- Stored R6W leaf: healing_rows_above_entry_at_height on the stored parent.
private theorem p0d5cTstOrder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    FGCompose.PromotionRowOrder (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (fgsaInterface p c) := by
  intro s X height U hnew _ hpar hUP i W hW hn
  obtain ⟨Y, he, _, _, st, hst, hlookup⟩ := healing_promotion_carrier E rho hrec hnew
  have hYX : Y = X := eraseFG_injective he
  subst Y
  have hinv := (storeBundle_of_reachable p st
    (healing_promotion_proposal_reachable p c E rho hst)).cstore
  have hparent : X.parent ∈ st.fg.TF := ((fgBlockOf_spec p st hinv _ _).mp hlookup).1
  exact healing_rows_above_entry_at_height p st
    (healing_promotion_proposal_reachable p c E rho hst) .progress height U X.parent
    hparent hpar hUP i W hW hn

omit [Fintype V] in
-- Row leaf: honest rows decode and carry their holder's seat (linked seats).
private theorem p0d5cTstRowSigner (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho) :
    FGCompose.PromotionRowSigner (p0d5cTstSafety p c) E rho (p0d5cTstTiming p)
      (p0d5cTstWire p c) := by
  refine ⟨?_, ?_⟩
  · intro j x r a hrow
    obtain ⟨i, hauth⟩ := honestRow_auth p c rho E base.valid hrow
    cases a with
    | mk auth payload =>
      change auth = .seat .fg i at hauth
      subst auth
      exact ⟨_, rfl⟩
  · intro i j r a hrow
    obtain ⟨i', hauth⟩ := honestRow_auth p c rho E base.valid hrow
    have hseat : rho.seatOf (.base .fg) i' = rho.seatOf (.base .fg) i := by
      have hem := hrow.2.2
      cases a with
      | mk auth body =>
        change auth = .seat .fg i' at hauth
        subst auth
        exact ((fgsa_emitsAt_row E rho j _ _ hrow.2.1 i' body).mp hem).2.1
    have hii : i' = i := (base.linked.toCStar (.base .fg) trivial).1 hseat
    subst i'
    exact (p0d5cTstSigner_iff a i).mpr hauth

-- Construction leaf: healing_promotion_slot_proposal with the restart bound.
private theorem p0d5cTstSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) :
    FGCompose.PromotionSlotProposal (p0d5cTstCore p c) E rho (p0d5cTstTiming p)
      (fgsaInterface p c) := by
  intro s hslot hgsts hhor
  change E.t_GST + 4 * p.Δ ≤ SA.proposalTime p.toParams s at hgsts
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    change E.t_GST + 4 * p.Δ ≤ 4 * p.Δ * (s : Int) at hgsts
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    linarith
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ hws he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    have hwgst : w ≤ E.t_GST := by
      by_contra hn
      exact hrec.suffixNoRestart _ hslot.2 j w hj (lt_of_not_ge hn)
        ((hws.trans hhor).trans_lt (lt_add_of_pos_right _ (by decide)))
    exact hwgst.trans hcut
  obtain ⟨X, hnew, hXslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂
    hslot (by linarith [p.deltaPos]) hhor hjoin
  exact ⟨X, hnew, hXslot⟩

omit [Fintype V] in
-- Source transfer leaf: healing_promotion_source_parent (TPerm at the source body).
private theorem p0d5cTstSourceParent (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (perm : TPerm p c E rho) :
    FGCompose.PromotionSourceParent (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) := by
  intro u m J contested r s X x K hready hphase hu hgate hs hnew hx hK
  have hp := healing_promotion_source_parent E rho perm hready
    ((p0d5cTstPhase_iff E rho).mp hphase) hu hgate hx hK hs hnew
  change Block.Preceq (eraseFG K) (eraseFG X).parent at hp
  rw [eraseFG_parent] at hp
  exact eraseFG_preceq_iff.mp hp

omit [Fintype V] in
private theorem p0d5cTstCovered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {r : Nat} {Q : Block} (h : OpeningCovered p c E rho r Q) :
    FGCompose.OpeningCovered (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho
      (heightView p) (p0d5cTstTiming p) (p0d5cTstWire p c).heightPair r Q := by
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hr, ha, hn⟩ := h x hx
  have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
  exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ, hr, ha, hn⟩

omit [Fintype V] in
private theorem p0d5cTstParentSlot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hne : W ≠ .genesis) :
    W.parent.slot < W.slot := by
  have hm := ((cstoreInv_stateBefore E rho i x).baseTree (eraseFG W)).mpr ⟨W, hW, rfl⟩
  obtain ⟨w, hw, hb, j, o, t, _, hd, ho, _⟩ :=
    fgsa_stored_block_origin E rho i x (eraseFG W) hm (by
      intro he; exact hne (eraseFG_eq_genesis.mp he))
  obtain ⟨s, N, rfl, _, _, _⟩ :=
    (metaInv_stateBefore E rho i x).wireTree w hw
  have hQ : N.erase = eraseFG W := Option.some.inj hb
  have hf := hv.wire j x o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : N.erase.parent.slot < N.erase.slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rwa [hQ, eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [Fintype V] in
private theorem p0d5cTstAncestorSlot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) {U K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hUK : FGBlock.Preceq U K) :
    U.slot ≤ K.slot := by
  induction K with
  | genesis => obtain rfl := KitFG.preceq_genesis.mp hUK; exact le_rfl
  | node P s root body rows ih =>
      by_cases he : U = .node P s root body rows
      · subst U; exact le_rfl
      · have hUP := KitFG.preceq_parent_of_preceq_node hUK he
        have hP := (cstoreInv_stateBefore E rho i x).fg.closed _ hK
        exact (ih hP hUP).trans
          (p0d5cTstParentSlot E rho hv i x _ hK (by intro h; cases h)).le

private theorem p0d5cTstAncestor (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hUK : FGBlock.Preceq U K) : U.slot ≤ K.slot := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).1
    have hs := ((KitFG.mem_filteredFromView _ _ _ _).mp hm).1
    change K ∈ (clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at hs
    rw [clock_fg] at hs
    exact p0d5cTstAncestorSlot E rho hrec.base.valid i x hs hUK


-- Receipt leaf, cap form: healing_promotion_first_receipt_of_frontierCap with the
-- existing self-proposal receiver service.
private theorem p0d5cTstCapReceipt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) :
    FGCompose.PromotionCapReceipt (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (fgsaInterface p c) := by
  intro m s Qfg X hnew hgst hQX hcap hQm hhor
  exact healing_promotion_first_receipt_of_frontierCap E rho hrec.toRecovery₂ crossing
    (healing_self_proposal_service hrec s) hnew hgst hQX hcap hQm hhor


end p0d5cTstD5b

-- Common opening leaf: TCommon at the exact-service seed (CommonEntry producer).
private theorem p0d5cTstCommon [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (repair : TRepair p c E rho)
    (common : TCommon p c E rho) :
    ∀ u m J contested q Q Qfg r, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cTstCore p c).erase Qfg = Q →
      FGCompose.FrontierProposalService (p0d5cTstCore p c) E rho (p0d5cTstTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R → (∀ r', q ≤ r' * p.R → r ≤ r') →
      FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u (p.actionTime r) m J
        contested →
      FGCompose.OpeningCovered (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (heightView p)
        (p0d5cTstTiming p) p0d5cTstPair r Q ∧
      ((heightView p Qfg).h = m - 1 →
        FGCompose.OpeningEntry (p0d5cTstCore p c) E rho (heightView p) (p0d5cTstTiming p) r (m -
          1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
          (heightView p K).h = m) := by
  intro u m J contested q Q Qfg r hready hQ he _ hseed hu hqr hfirst hp
  have hp' := (p0d5cTstPhase_iff E rho).mp hp
  have hga : SA.gateTime p.toParams q ≤ p.actionTime r := by
    have := (common_first_time_bound (p := p) q r hqr hfirst).1
    linarith
  have hexact := p0d5cTstExact E rho hrec repair hready ((p0d5cTstSeed_iff E).mp hseed) hp' hga hQ
  obtain ⟨_, _, hc, _, _, hlowOr⟩ := common u m J contested q Q Qfg r hready hQ he hexact hu
    hqr hfirst hp'
  refine ⟨p0d5cTstCovered E rho hc, fun hlow => ?_⟩
  rcases hlowOr hlow with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

-- Stored-slot leaf of an honest proposal's own slot (repair_proposal_slot).
private theorem p0d5cTstProposalSlot (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    ∀ q Q K, HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cTstCore p c).erase K = Q →
      K.slot = q := by
  intro q Q K hQ he
  have h := repair_proposal_slot E rho hQ
  rw [← he] at h
  change (eraseFG K).slot = q at h
  rwa [eraseFG_slot] at h

-- Justified-source leaf: the frozen QC origin (Descent).
private theorem p0d5cTstJustified [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (origin : RQCOrigin p c E rho) :
    ∀ i x, x ∈ rho.honest → ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ FGCompose.HonestRowAt (p0d5cTstSafety p c) E rho (p0d5cTstTiming p) j y
        r a ∧
        actionSourceFG p c E rho y r = some (some K) ∧
        (heightView p K).T_h = ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.J := by
  intro i x hx hj
  obtain ⟨K, _, ⟨j, y, r, a, hji, ha, hK, _⟩, _, hT, _⟩ :=
    healing_justified_source (hroots := hrec.base.idealization) p c E rho
      hrec.base.valid.toScheduleWellFormed origin hx hj
  exact ⟨j, y, r, a, K, hji, ha, hK, hT⟩

-- Proposer frame leaf: the proposer's parent lies in its full tree above the root.
private theorem p0d5cTstParentFrame [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) :
    ∀ q Q, HonestProposal E rho (fgsaInterface p c) q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) q)
        (SA.proposalTime p.toParams q)) ∧
      ∀ Qfg, (p0d5cTstCore p c).erase Qfg = Q → FGBlock.Preceq
        ((p0d5cTstObs p c).controls (rho.stateBefore E j
          (V2.D.proposerOf rho (fgsaInterface p c) q))).Z Qfg.parent := by
  intro q Q hQ
  have hs := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j, N, _, hj, _, hst, _, _, _⟩ := healing_promotion_proposal_read p c E rho hs hQ
  refine ⟨j, hj, fun Qfg he => ?_⟩
  let x := V2.D.proposerOf rho (fgsaInterface p c) q
  let st := ((fgsa p c).clock (rho.stateBefore E j x) (SA.proposalTime p.toParams q)).st
  have hx := hQ.1.2
  have hfg : st.fg = (storeAt p c E rho j x).fg := clock_fg p _ _
  have hne : (fullTree p st).Nonempty := by
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho j x
    obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hW hh
    change (KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF).Nonempty
    rw [hfg]
    exact ⟨W, (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨hW, hF, hZ, W, hW, KitFG.preceq_refl _, hh ▸ KitFG.Controls.lo_le_H _⟩⟩
  obtain ⟨B, hB, heB⟩ := healing_proposal_full_witness p c E rho hs hQ hst hne
  have hBQ : B = Qfg.parent := eraseFG_injective
    (heB.trans (by rw [← eraseFG_parent]; exact congrArg Block.parent he.symm))
  have hZB := ((KitFG.mem_filteredFromView _ _ _ _).mp hB).2.2.1
  have hc : FGSA.controls p st = FGSA.controls p (rho.stateBefore E j x).st := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho j x).fg
    rw [hfg]
  change FGBlock.Preceq (FGSA.controls p (rho.stateBefore E j x).st).Z Qfg.parent
  rw [← hc, ← hBQ]
  exact hZB

-- Continuing local service of the frozen exact-service seed (TFrontier).
private theorem p0d5cTstLocal (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (frontier : TFrontier p c E rho) {u : Time} {m q : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hready : recoveryStart p E ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (he : eraseFG Qfg = Q) (hh : (heightView p Qfg).h = m)
    (hexact : ExactService p c E rho q Q) (hseed : FrontierSeedQualification p E u q)
    (hu : u ≤ SA.proposalTime p.toParams q)
    (hp : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested) :
    ∀ v, SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
        (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair q Q Qfg m v := by
  intro v hg hv hcap
  obtain ⟨htransfer, hrepair, hopen⟩ := frontier u v m J contested q Q Qfg hready hQ he hh
    hexact ((frontierSeedQualification_iff p E u q).mp hseed) hu hp hg hv hcap
  refine ⟨htransfer.1, htransfer.2.1, htransfer.2.2, ?_, ?_⟩
  · intro s B hqs hgate hprop
    exact (hrepair s B hqs hgate hprop).1
  · intro r hqr hrt
    obtain ⟨hcov, hent, hheight, htime⟩ := hopen r hqr hrt
    refine ⟨?_, hent, hheight, htime⟩
    intro x hx
    obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ', hr, ha, hn⟩ := hcov x hx
    have htf : K ∈ nd.st.fg.TF := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    exact ⟨K, nd, j, rSent, a, hnd, hK, htf, hQ', hr, ha, hn⟩

-- G0 (producer-backed leaves): every d5c leaf of the generic phase consumers is produced
-- by its frozen FG-SA producer (TRepair arm, RiseOne gate copy, TFrontier route, TCommon,
-- QC origin, proposer floor/frame, stored slots); none is assumed.
private theorem p0d5cTstLeaves [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF ρbar u : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (monoAll : RMonoAll p c E rho) (repair : TRepair p c E rho)
    (mode : FrontierRepairStart p E G u ρbar) :
    FGCompose.AttemptProposalFloor (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) ∧
    FGCompose.FrontierRepairAllowance (p0d5cTstCore p c) E rho (p0d5cTstObs p c) (p0d5cTstTiming p)
      (fgsaInterface p c) (recoveryStart p E) p.k G ρbar u ∧
    (∀ u v m J contested q Q, recoveryStart p E ≤ u →
      FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u v m J contested →
      FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q →
      SA.gateTime p.toParams q ≤ v → HonestProposal E rho (fgsaInterface p c) q Q →
      ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧ i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.TF ∧
        (p0d5cTstCore p c).erase Qfg = Q) ∧
    TFrontier p c E rho ∧
    (∀ q Q K, HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cTstCore p c).erase K = Q →
      K.slot = q) :=
  ⟨p0d5cTstFloor E rho hrec crossing, p0d5cTstAllowance E rho hrec repair mode,
    p0d5cTstGateCopy E rho hrec repair, p0d5cTstRoute E rho hrec monoAll crossing,
    p0d5cTstProposalSlot E rho⟩

-- G0 (producer-backed leaves, continued): the continuing local service, the common
-- opening, the justified source and the proposer frame.
private theorem p0d5cTstLeavesMore [Fintype V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (monoAll : RMonoAll p c E rho) (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (origin : RQCOrigin p c E rho) :
    (∀ u v m J contested q Q Qfg, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q →
      (p0d5cTstCore p c).erase Qfg = Q → ((p0d5cTstObs p c).height Qfg).h = m →
      FGCompose.FrontierProposalService (p0d5cTstCore p c) E rho (p0d5cTstTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q →
      FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u (SA.gateTime p.toParams
        q)
        m J contested → SA.gateTime p.toParams q ≤ v → v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FGCompose.FrontierLocalService (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
        (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, recoveryStart p E ≤ u →
      HonestProposal E rho (fgsaInterface p c) q Q → (p0d5cTstCore p c).erase Qfg = Q →
      FGCompose.FrontierProposalService (p0d5cTstCore p c) E rho (p0d5cTstTiming p) q Q →
      FGCompose.FrontierSeedQualification (p0d5cTstTiming p) p.k E.t_GST u q →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R → (∀ r', q ≤ r' * p.R → r ≤ r') →
      FGCompose.PhaseInterval (p0d5cTstCore p c) E rho (p0d5cTstObs p c) u (p.actionTime r) m J
        contested →
      FGCompose.OpeningCovered (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (heightView p)
        (p0d5cTstTiming p) p0d5cTstPair r Q ∧
      ((heightView p Qfg).h = m - 1 →
        FGCompose.OpeningEntry (p0d5cTstCore p c) E rho (heightView p) (p0d5cTstTiming p) r (m -
          1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
          (heightView p K).h = m)) ∧
    (∀ i x, x ∈ rho.honest → ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ FGCompose.HonestRowAt (p0d5cTstSafety p c) E rho (p0d5cTstTiming p) j y
        r a ∧
        actionSourceFG p c E rho y r = some (some K) ∧
        (heightView p K).T_h = ((p0d5cTstCore p c).core (rho.stateBefore E i x)).fg.J) ∧
    (∀ q Q, HonestProposal E rho (fgsaInterface p c) q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) q)
        (SA.proposalTime p.toParams q)) ∧
      ∀ Qfg, (p0d5cTstCore p c).erase Qfg = Q → FGBlock.Preceq
        ((p0d5cTstObs p c).controls (rho.stateBefore E j
          (V2.D.proposerOf rho (fgsaInterface p c) q))).Z Qfg.parent) :=
  ⟨p0d5cTstService E rho hrec repair (p0d5cTstRoute E rho hrec monoAll crossing),
    p0d5cTstCommon E rho hrec repair common, p0d5cTstJustified E rho hrec origin,
    p0d5cTstParentFrame E rho hrec crossing⟩

-- G0 (served seed both ways): a frozen saved seed gives the generic saved seed through the
-- produced TFrontier, with its actual selected non-genesis proposal and local service, and
-- the generic seed returns the frozen one through the frozen repair arm.
private theorem p0d5cTstServedRoundTrip [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) (monoAll : RMonoAll p c E rho) (repair : TRepair p c E rho)
    {m : Nat} {t : Time} (served : StrongServed p c E rho m t) :
    FGCompose.StrongServed (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
        (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair (recoveryStart p E) p.k m t ∧
      StrongServed p c E rho m t := by
  obtain ⟨u, J, contested, q, Q, Qfg, hgst, hQ, he, hh, hexact, hseed, hu, hp, hqt, hth,
    hcap⟩ := (strongServed_iff p c E rho m t).mp served
  have frontier := p0d5cTstRoute E rho hrec monoAll crossing
  have g : FGCompose.StrongServed (p0d5cTstCore p c) (p0d5cTstSafety p c) E rho (p0d5cTstObs p c)
      (p0d5cTstTiming p) (fgsaInterface p c) p0d5cTstPair (recoveryStart p E) p.k m t :=
    ⟨u, J, contested, q, Q, Qfg, hgst, hQ, he, hh, hexact.1, (p0d5cTstSeed_iff E).mpr hseed, hu,
      (p0d5cTstPhase_iff E rho).mpr hp, hqt, hth, hcap,
      p0d5cTstLocal E rho frontier hgst hQ he hh hexact hseed hu hp t hqt hth hcap⟩
  exact ⟨g, p0d5cTstServedBack E rho hrec repair g⟩

/-- The run of Tests.NonVacuity.HealingRun.run, written out: the same params, env, gap,
deltaF and the same 311-batch events (ticks 0..310), with horizon 310 (HealingRun.horizon).
HealingRun.nvRecovery and nvPerm are stated for exactly this run; HealingFixture.mkRun alone keeps
horizon 304, which no schedule with tick 310 satisfies. -/
private abbrev p0d5cTstFixtureRun : V2.D.Run (Fin 1) (fgsa HealingFixture.params unitCodec) :=
  { HealingFixture.mkRun (HealingFixture.runPrefix 311).1 with horizon := 310 }

-- Guard: the horizon is 310, and the last batch index of the 311-prefix (tick time 310) is
-- within it; the 304-horizon pairing fails the same check.
private theorem p0d5cTstFixtureRunHorizon :
    p0d5cTstFixtureRun.horizon = 310 ∧ (List.range 311).getLast? = some 310 ∧
      ((310 : Nat) : Time) ≤ p0d5cTstFixtureRun.horizon ∧ ¬ ((310 : Nat) : Time) ≤
        HealingFixture.horizon :=
  ⟨rfl, by decide, by decide, by decide⟩

-- G0 (strongest proved partial): on the fixture run, with its recovery regime (proved as
-- Tests.NonVacuity.HealingRun.nvRecovery; a Tests module cannot be imported, TEST-USE),
-- the gap slot gives an actual non-genesis honest proposal X, and the proposer-frame leaf
-- is produced at X from its actual proposer read: the root of that read is below X's
-- parent. The TFrontier route is produced on the same run.
private theorem p0d5cTstFixtureFrame
    (hrec : RecoverySleep₂ HealingFixture.params unitCodec HealingFixture.env
      p0d5cTstFixtureRun HealingFixture.gap HealingFixture.deltaF) :
    TFrontier HealingFixture.params unitCodec HealingFixture.env p0d5cTstFixtureRun ∧
    ∃ s X j, HonestProposal HealingFixture.env p0d5cTstFixtureRun
        (fgsaInterface HealingFixture.params unitCodec) s (eraseFG X) ∧ X.slot = s ∧
      X ≠ .genesis ∧
      p0d5cTstFixtureRun.events[j]? = some (.tick (V2.D.proposerOf p0d5cTstFixtureRun
        (fgsaInterface HealingFixture.params unitCodec) s)
        (SA.proposalTime HealingFixture.params.toParams s)) ∧
      FGBlock.Preceq ((p0d5cTstObs HealingFixture.params unitCodec).controls
        (p0d5cTstFixtureRun.stateBefore HealingFixture.env j (V2.D.proposerOf p0d5cTstFixtureRun
          (fgsaInterface HealingFixture.params unitCodec) s))).Z X.parent := by
  have crossing := fgsa_rXing (hroots := hrec.base.idealization) HealingFixture.params
    unitCodec HealingFixture.env p0d5cTstFixtureRun hrec.base.linked
    (fgsa_faultX_count_rec HealingFixture.params hrec.fault)
    hrec.base.valid.toUnforgeableSignatures
  have monoAll := fgsa_rMonoAll HealingFixture.params unitCodec HealingFixture.env
      p0d5cTstFixtureRun
  refine ⟨p0d5cTstRoute _ _ hrec monoAll crossing, ?_⟩
  have hd := HealingFixture.params.deltaPos
  obtain ⟨s, hlo, hhi, hslot⟩ := hrec.gap
    (HealingFixture.env.t_GST + 4 * HealingFixture.params.Δ) (by linarith)
    (by
      change 0 + 4 * HealingFixture.params.Δ + 4 ≤ 310
      have : HealingFixture.params.Δ = 1 := rfl
      rw [this]
      decide)
  rw [proposalTime_fgsa] at hlo hhi
  have hhor : SA.proposalTime HealingFixture.params.toParams s ≤ p0d5cTstFixtureRun.horizon := by
    have : HealingFixture.params.Δ = 1 := rfl
    change _ ≤ 310
    change _ ≤ 0 + 4 * HealingFixture.params.Δ + 4 at hhi
    rw [this] at hhi
    linarith
  obtain ⟨X, hnew, hXs⟩ := p0d5cTstSlot _ _ hrec s hslot hlo.le hhor
  obtain ⟨j, hj, hframe⟩ := p0d5cTstParentFrame _ _ hrec crossing s _ hnew
  refine ⟨s, X, j, hnew, hXs, ?_, hj, hframe X rfl⟩
  intro hg
  have h0 := hslot.1
  rw [← hXs, hg] at h0
  exact absurd h0 (by decide)

#print axioms p0d5cTstLeaves
#print axioms p0d5cTstLeavesMore
#print axioms p0d5cTstServedRoundTrip
#print axioms p0d5cTstFixtureRunHorizon
#print axioms p0d5cTstFixtureFrame
end AvailableChain.FGSA.Run
end

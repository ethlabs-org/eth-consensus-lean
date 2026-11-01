module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGSAProofs.Proofs.Healing.Phase
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public import AvailableChainFGCompose.Proofs.Healing.PhaseSettle

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def p0d1SettleCore (p : Params) {In : Type} (c : AppCodec In) :
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

private theorem p0d1SettleCoreEq (p : Params) {In : Type} (c : AppCodec In) :
    p0d1SettleCore p c = fgsaCoreReads p c := (fgsaCoreReads_def p c).symm

private theorem p0d1SettleCoreLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreLaws (p0d1SettleCore p c) := by
  rw [p0d1SettleCoreEq]
  exact fgsaCoreLaws p c

private theorem p0d1SettleOrder : RMonoAll p c E rho := by
  intro i j x _ hij
  let a := storeAt p c E rho i x
  apply V2.D.Engine.stateBefore_stable_restore (P := fgsa p c)
    (fun nd => FGBlock.Preceq a.fg.F nd.st.fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey (nd.st.fg.h_j, nd.st.fg.J) ∧
      a.fg.h_max ≤ nd.st.fg.h_max)
    ?_ ?_ (fun _ _ h => h) E rho hij x ?_
    ⟨KitFG.preceq_refl _, le_rfl, le_rfl⟩
  · intro nd t h
    change FGBlock.Preceq a.fg.F (clock p nd.st t).fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤ lexKey ((clock p nd.st t).fg.h_j, (clock p nd.st t).fg.J) ∧
      a.fg.h_max ≤ (clock p nd.st t).fg.h_max
    rw [clock_fg]
    exact h
  · intro nd o h
    exact ⟨KitFG.preceq_trans h.1 (process_F_mono p nd.st (toWire p o)),
      le_trans h.2.1 (process_pair_mono p nd.st (toWire p o)),
      le_trans h.2.2 (process_hmax_mono p nd.st (toWire p o))⟩
  · intro nd t h
    change FGBlock.Preceq a.fg.F (acRestart p nd.st t).fg.F ∧
      lexKey (a.fg.h_j, a.fg.J) ≤
        lexKey ((acRestart p nd.st t).fg.h_j, (acRestart p nd.st t).fg.J) ∧
      a.fg.h_max ≤ (acRestart p nd.st t).fg.h_max
    rwa [acRestart_fg]


private def p0d1SettleReads (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d1SettleCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d1SettleLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d1SettleCore p c) (p0d1SettleReads p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

private def p0d1SettleTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d1SettleKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap
  | .topJ => .topJ
  | .contest => .contest

private theorem p0d1WitnessProjection {W : FGBlock (Fin p.n)} {deadline : Time}
    (h : WitnessReceiptScope E rho W deadline) :
    FGCompose.WitnessReceiptScope (p0d1SettleCore p c) E rho
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) W deadline :=
  ⟨h.atRead⟩

private theorem p0d1PhaseReceiptsProjection {i m : Nat} {deadline : Time}
    (h : PhaseWitnessReceiptScope E rho i m deadline) :
    FGCompose.PhaseWitnessReceiptScope (p0d1SettleCore p c) E rho (p0d1SettleReads p c)
      (fun nd => joinedNow p nd.st) (TargetReceiptService E rho) i m deadline := by
  constructor
  · obtain ⟨x, W, hW, hh, hr⟩ := h.frontier
    exact ⟨x, W, hW, hh, p0d1WitnessProjection p c E rho hr⟩
  · intro ht
    obtain ⟨x, C, hC, hh, hj, hJ, hr⟩ := h.top ht
    exact ⟨x, C, hC, hh, hj, hJ, p0d1WitnessProjection p c E rho hr⟩
  · intro hc
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff, hrC, hrW⟩ := h.contest hc
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff,
      p0d1WitnessProjection p c E rho hrC, p0d1WitnessProjection p c E rho hrW⟩

/-- Blueprint 21:1003–1012, 1193–1209; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL no effective event fixes the frontier and both evidence bits.
A bit can be true later only if it is true at the first prefix. -/
theorem healing_phase_window (hnr : V2.D.NoRestart rho) {i m : Nat} {v : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hquiet : ∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) :
    ∀ k, i + 1 ≤ k → k ≤ timeIdx rho v →
      frontierAtIdx p c E rho k = m ∧
      (TopEvidence p c E rho k m → TopEvidence p c E rho (i + 1) m) ∧
      (ContestEvidence p c E rho k m → ContestEvidence p c E rho (i + 1) m) := by
  have mono : RMono p c E rho := fun _ => p0d1SettleOrder p c E rho
  exact FGCompose.healing_phase_window_all
    (R := p0d1SettleCore p c) (E := E) (rho := rho) (O := p0d1SettleReads p c)
    ⟨mono hnr⟩ hfront hquiet



/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL a held top carrier fixes the local top J below the frontier cap.
Assembly supplies RXing. A J on the carrier path is the carrier's J.
At m = 1 both J are genesis (B21). -/
theorem healing_phase_top_node (crossing : RXing p c E rho) {k m : Nat} {y : V}
    {C : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hC : C ∈ (storeAt p c E rho k y).fg.TF) (hh : (heightView p C).h = m)
    (hj : (heightView p C).h_j + 1 = m) (hcap : frontierAtIdx p c E rho k ≤ m) :
    (storeAt p c E rho k y).fg.h_max = m ∧ (storeAt p c E rho k y).fg.h_j + 1 = m ∧
      (FGBlock.Preceq (storeAt p c E rho k y).fg.J C →
        (storeAt p c E rho k y).fg.J = (heightView p C).J) := by
  exact FGCompose.phase_top_carrier
    (R := p0d1SettleCore p c) (E := E) (rho := rho) (O := p0d1SettleReads p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p) crossing hy hC hh hj hcap



/-- Blueprint 21:1012–1045; plan S20, H-PHASE r2/P3.
DC: SAME the settled frame reads only the FG store. -/
private theorem settle_frame_fg {st st' : State p.n} (h : st.fg = st'.fg)
    {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hf : SettledPhaseFrame p st m J contested) : SettledPhaseFrame p st' m J contested := by
  unfold SettledPhaseFrame FGSA.controls at *
  rw [← h]
  exact hf

/-- Blueprint 21:1003–1012, 1155–1163; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL common live controls from Δ after the event give the interval
from the strict cut at 3Δ (B25) and every frozen HEAD frame.
Assembly supplies RXing. -/
private theorem settle_finish (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) {ev : V2.Event V (Obj p)}
    {v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hu : ev.time + 3 * p.Δ ≤ v) (hv : v ≤ rho.horizon) (hm : 1 ≤ m)
    (hcore : ∀ k y, V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k → k ≤ timeIdx rho v →
      y ∈ rho.honest →
      (R_at p c E rho k y).H = m ∧ (R_at p c E rho k y).contest = contested ∧
      (match J with
        | some B => (R_at p c E rho k y).rootIsJ = true ∧ (R_at p c E rho k y).J = B
        | none => (R_at p c E rho k y).rootIsJ = false)) :
    PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m J contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st m J contested) := by
  have hs := hvalid.toScheduleWellFormed
  have hpos := p.deltaPos
  have hd3 : ev.time + p.Δ ≤ ev.time + 3 * p.Δ := by
    simp only [Time] at *
    omega
  refine ⟨⟨by simp only [Time] at *; omega, hv, hm, ?_⟩, ?_⟩
  · intro k x hk hkv hx
    exact hcore k x ((healing_phase_idxBefore_mono p c rho hd3).trans hk) hkv hx
  · intro y s nd hy hvote hvs hpost
    rw [postClock_def, preTick_def] at hpost
    cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
    | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
    | some k =>
      rw [hk] at hpost
      have hnd := Option.some.inj hpost
      subst nd
      have htick := V2.D.Run.tickIdx?_spec hk
      have hjk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k := by
        by_contra hn
        have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick (ev.time + p.Δ)).mp (by omega)
        change SA.voteTime p.toParams s < ev.time + p.Δ at hlt
        simp only [Time] at *
        omega
      have hkv : k ≤ timeIdx rho v :=
        (healing_phase_lt_timeIdx p c E rho hs htick (t := v) hvs).le
      obtain ⟨hH, hc, hr⟩ := hcore k y hjk hkv hy
      have hf := healing_phase_frame p c E rho crossing hy hm hH hc hr
      exact settle_frame_fg p (clock_fg p _ _).symm hf

/-- ROOT-DIGEST W2b. Blueprint 21:1003–1045, 1142–1209; plan S20, H-PHASE r2/P3.
DC: INTENTIONAL settlement after a start event, with live controls,
one common top J, and frozen HEAD frames. Evidence can be present at the start.
The effective-event corollary gives the third frozen RPhase clause.
Its two matches list all three kinds, where the frozen text uses a
wildcard; they agree for each kind. Assembly supplies RXing. The top-J
identity uses the global absence of contest evidence, so no fault bound is an
input. Carriers accepted before GST are relayed by GST + Δ. -/
theorem healing_settle_start (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hAwake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ i ev v m kind, rho.events[i]? = some ev →
      E.t_GST ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
          SA.voteTime p.toParams s ≤ v →
          postClock E rho y (SA.voteTime p.toParams s) = some nd →
          SettledPhaseFrame p nd.st m root contested) := by
  intro i (ev : V2.Event V (Obj p)) v m kind hi hgst hu hv hm hfront hkind hquiet
  -- Restate the event times at the object type of the relay lemmas.
  have hu : ev.time + 3 * p.Δ ≤ v := hu
  have hgst : E.t_GST ≤ ev.time := hgst
  have hs := hvalid.toScheduleWellFormed
  have hpos := p.deltaPos
  have hij0 : i < V2.D.Run.idxBefore rho (ev.time + p.Δ) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr (lt_add_of_pos_right _ hpos)
  have hdv : ev.time + p.Δ ≤ v := by
    simp only [Time] at *
    omega
  have hj0v : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ timeIdx rho v :=
    healing_phase_idx_le_time p c rho hdv
  have hhor : ev.time + p.Δ ≤ rho.horizon := hdv.trans hv
  have hwin := healing_phase_window p c E rho hnr hfront hquiet
  have hcap (k : Nat) (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k)
      (hkv : k ≤ timeIdx rho v) :
      frontierAtIdx p c E rho k = m := (hwin k (by omega) hkv).1
  -- Every carrier held at i + 1 is held by every honest node in the window.
  have relay {x : V} {W : FGBlock (Fin p.n)} (hW : HeldAt p c E rho (i + 1) x W)
      (hh : (heightView p W).h = m) {k : Nat} {y : V}
      (hk : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ k) (hy : y ∈ rho.honest) :
      W ∈ (storeAt p c E rho k y).fg.TF := by
    have h0 := healing_phase_held_receipt (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync hi
      hW.1 hgst hW.2 hhor ((hcap _ le_rfl hj0v).trans hh.symm).le hy
      (hAwake y hy _ (hgst.trans (le_add_of_nonneg_right p.deltaPos.le)) hhor)
    exact (fgsa_store_cumulative p c E rho hnr hk y).1 h0
  have wit := healing_phaseWitness p c E rho hm hfront
  have result := FGCompose.phase_settle_from_carriers
    (R := p0d1SettleCore p c) (E := E) (rho := rho) (O := p0d1SettleReads p c)
    (Ef := p.E) (obs := p0d1SettleLaws p c) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (T := p0d1SettleTiming p) (positive := p.deltaPos) (coreLaws := p0d1SettleCoreLaws p c)
    (kind := p0d1SettleKind kind) crossing hs hu hv hm (Nat.succ_le_of_lt hij0) hwin
    (by cases kind <;> exact hkind)
    (by
      obtain ⟨x, W, hW, hh⟩ := wit.frontier
      exact ⟨x, W, hW, hh, fun y hy => relay hW hh le_rfl hy⟩)
    (by
      intro ht
      obtain ⟨x, C, hC, hh, hj, hJ⟩ := wit.top ht
      exact ⟨x, C, hC, hh, hj, hJ, fun y hy => relay hC hh le_rfl hy⟩)
    (by
      intro hc
      obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff⟩ := wit.contest hc
      exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hoff,
        fun y hy => relay hC hhC le_rfl hy, fun y hy => relay hW hhW le_rfl hy⟩)
  cases kind <;> exact result


/-- ROOT-DIGEST W2b. The frozen effective-event statement follows from start settlement. -/
theorem healing_settle_event (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hAwake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ i ev v m kind, rho.events[i]? = some ev → EffectiveEvent p c E rho i →
      E.t_GST ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
          SA.voteTime p.toParams s ≤ v →
          postClock E rho y (SA.voteTime p.toParams s) = some nd →
          SettledPhaseFrame p nd.st m root contested) := by
  exact fun i ev v m kind hi _heff =>
    healing_settle_start (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync hAwake i ev v m kind hi

/-- ROOT-DIGEST W2b. Blueprint 21:1086–1278; plan S20, H-PHASE r2/P6.
DC: INTENTIONAL the five frozen RPhase clauses from P1–P5.
Assembly supplies RMono and RXing. The other inputs are Base₂ and Recovery₂
fields. No phase, service, fault-bound, or reset premise is an input. -/
theorem healing_rPhase (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hAwake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    RPhase p c E rho := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b m hab hb hm hfixed
    exact healing_phase_order_of_crossing p c E rho crossing mono hnr a b m hab hb hm hfixed
  · intro i ev x W m hi hx hready hm hfront hbefore hafter hh
    have hgst : E.t_GST ≤ ev.time := by
      have := healing_recovery_start_lower (p := p) E
      linarith [p.deltaPos]
    have he := healing_evidence_spread (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync i ev x W m
      hi hx hgst hm hfront hbefore hafter hh
    exact ⟨fun hhor y hy => he.1 hhor y hy
      (hAwake y hy _ (hgst.trans (le_add_of_nonneg_right p.deltaPos.le)) hhor), he.2⟩
  · intro i ev v m kind hi heff hready hu hv hm hfront hkind hquiet
    have hgst : E.t_GST ≤ ev.time := by
      have := healing_recovery_start_lower (p := p) E
      linarith [p.deltaPos]
    obtain ⟨J, h⟩ := healing_settle_event (hroots := hroots)
      p c E rho crossing hvalid hnr hdelta hsync hAwake
      i ev v m kind hi heff hgst hu hv hm hfront hkind hquiet
    refine ⟨J, ?_⟩
    cases kind <;> exact h
  · intro u v m J contested hready hp i x hui hiv hx
    exact healing_settled_frame_ready p c E rho crossing u v m J contested hready hp
      i x hui hiv hx
  · intro i x m X B hx hi hm hH hX hB hpath hh
    exact healing_frontier_mem p c E rho crossing i x m X B hx hi hm hH hX hB hpath hh

/-- Quiet phase windows use all-restart FG bounds. -/
theorem healing_phase_window_all (mono : RMonoAll p c E rho) {i m : Nat} {v : Time}
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hquiet : ∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) :
    ∀ k, i + 1 ≤ k → k ≤ timeIdx rho v →
      frontierAtIdx p c E rho k = m ∧
      (TopEvidence p c E rho k m → TopEvidence p c E rho (i + 1) m) ∧
      (ContestEvidence p c E rho k m → ContestEvidence p c E rho (i + 1) m) := by
  exact FGCompose.healing_phase_window_all
    (R := p0d1SettleCore p c) (E := E) (rho := rho) (O := p0d1SettleReads p c)
    ⟨mono⟩ hfront hquiet



/-- Retained settlement uses per-object local services and durable storage. -/
theorem healing_settle_start_on (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (mono : RMonoAll p c E rho)
    {G ΔF : Time} [Fintype V] (hrec : RecoverySleep₂ p c E rho G ΔF)
    (readyCut : ∀ t, recoveryStart p E ≤ t →
      E.t_GST ≤ slotStartZ p (((slotAt p t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V (Obj p)) m,
      rho.events[i]? = some ev → recoveryStart p E ≤ ev.time → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → ev.time + p.Δ ≤ rho.horizon →
      PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ))
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ i ev v m kind, rho.events[i]? = some ev →
      recoveryStart p E ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
      frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
      (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
      ∃ J,
        let root := match kind with | .gap => none | .topJ => some J | .contest => none
        let contested := match kind with | .gap => false | .topJ => false | .contest => true
        PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
        (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
          SA.voteTime p.toParams s ≤ v →
          postClock E rho y (SA.voteTime p.toParams s) = some nd →
          SettledPhaseFrame p nd.st m root contested) := by
  intro i ev v m kind hi hready hu hv hm hfront hkind hquiet
  have result := FGCompose.healing_settle_start_on
    (R := p0d1SettleCore p c) (E := E) (rho := rho) (O := p0d1SettleReads p c)
    (Ef := p.E) (obs := p0d1SettleLaws p c) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    (T := p0d1SettleTiming p) (positive := p.deltaPos) (coreLaws := p0d1SettleCoreLaws p c)
    (Jst := recoveryStart p E) (erasePreceq := fun h => eraseFG_preceq h)
    (joined := fun nd => joinedNow p nd.st) (receipt := TargetReceiptService E rho)
    crossing hvalid.toScheduleWellFormed ⟨mono⟩ hrec.base.delta
    (by have := healing_recovery_start_lower (p := p) E; linarith [p.deltaPos])
    hrec.awake
    (fun _ _ _ hy hiy hhor hcut => healing_recovery_joinedNow hrec hy hiy hhor hcut)
    readyCut
    (fun j e m hj hr hm hf hh =>
      p0d1PhaseReceiptsProjection p c E rho (hServices j e m hj hr hm hf hh))
    (fun W d y hy hr => healing_held_block_receipt_on p c E rho hvalid hroots W d y hy hr)
    i ev v m (p0d1SettleKind kind) hi hready hu hv hm hfront
    (by cases kind <;> exact hkind) hquiet
  cases kind <;> exact result



end AvailableChain.FGSA.Run
end

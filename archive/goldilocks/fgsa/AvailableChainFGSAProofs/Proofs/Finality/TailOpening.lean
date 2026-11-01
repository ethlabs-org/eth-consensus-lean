module
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-! ### Tail clock bounds -/

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Paper 22:1985–1989 (FT-Tail-W). Clock facts from the Tail premise: the
terminal carrier's HEAD read is inside the run.
DC: INTENTIONAL: the W Tail uses the row delay ΔF and stops at the terminal carrier. -/
theorem ktail_bounds {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) :
    0 ≤ ΔF ∧ 2 ≤ kappaF p ΔF ∧ kappaF p ΔF ≤ p.R ∧ 2 ≤ p.R ∧
      pt.w.sStar + 2 ≤ pt.r * p.R ∧
      E.t_GST ≤ SA.proposalTime p.toParams (pt.r * p.R) ∧
      SA.voteTime p.toParams ((pt.r + 1) * p.R + kappaF p ΔF) ≤ rho.horizon := by
  have hΔ := p.deltaPos
  have hF0 : 0 ≤ ΔF := by
    have h1 := hT.set.deltaF
    have h2 := hT.set.base.delta
    linarith
  have hκ := kappaF_ge_two p ΔF hF0
  have hκR := hT.bound.kappa_le_R
  have hstart : SA.gateTime p.toParams pt.w.u ≤ (pt.r : Time) * P p := hT.start
  rw [kmid_period_eq] at hstart
  have hu : pt.w.u < pt.r * p.R := by
    by_contra hn
    have hle := kmid_slot_scale_le p (Nat.le_of_not_gt hn)
    change 4 * p.Δ * (pt.w.u : Time) + 6 * p.Δ ≤ _ at hstart
    linarith
  have hlow := hT.input.wit.proposal_lower
  refine ⟨hF0, hκ, hκR, hκ.trans hκR, le_of_lt (lt_of_le_of_lt hlow hu), ?_, ?_⟩
  · have h1 := hT.input.wit.after_gst
    change E.t_GST ≤ SA.gateTime p.toParams pt.w.u at h1
    exact h1.trans hstart
  · have hhor := hT.hhor
    rw [kernelDeadlineW_def, kmid_period_eq, betaF_def] at hhor
    have hsplit : 4 * p.Δ * ((((pt.r + 1) * p.R + kappaF p ΔF : Nat)) : Time) =
        4 * p.Δ * ((((pt.r + 1) * p.R : Nat)) : Time) + 4 * (kappaF p ΔF : Time) * p.Δ := by
      push_cast
      ring
    change 4 * p.Δ * ((((pt.r + 1) * p.R + kappaF p ΔF : Nat)) : Time) + p.Δ ≤ _
    rw [hsplit]
    exact hhor

/-- Paper 22:1985–1989. Every slot read through the terminal carrier is inside the run;
a gate read two slots earlier is inside the run.
DC: INTENTIONAL: the W Tail horizon covers its window reads. -/
theorem ktail_slot_horizon {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hs : s ≤ (pt.r + 1) * p.R + kappaF p ΔF) :
    SA.proposalTime p.toParams s ≤ rho.horizon ∧ SA.voteTime p.toParams s ≤ rho.horizon ∧
      (s + 2 ≤ (pt.r + 1) * p.R + kappaF p ΔF → SA.gateTime p.toParams s ≤ rho.horizon) := by
  have hT' := (ktail_bounds hT).2.2.2.2.2.2
  have hle := kmid_slot_scale_le p hs
  have hΔ := p.deltaPos
  change 4 * p.Δ * (((pt.r + 1) * p.R + kappaF p ΔF : Nat) : Time) + p.Δ ≤ _ at hT'
  change 4 * p.Δ * (s : Time) ≤ _ ∧ 4 * p.Δ * (s : Time) + p.Δ ≤ _ ∧
    (_ → 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ _)
  refine ⟨by linarith, by linarith, fun h2 => ?_⟩
  have hle2 := kmid_slot_scale_le p h2
  have hsplit : 4 * p.Δ * ((s + 2 : Nat) : Time) = 4 * p.Δ * (s : Time) + 8 * p.Δ := by
    push_cast
    ring
  linarith

/-- Paper 22:1985–1989. Every slot read from the opening on is after GST.
DC: INTENTIONAL: the W Tail starts after GST. -/
theorem ktail_slot_gst {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot} (hs : pt.r * p.R ≤ s) :
    E.t_GST ≤ SA.proposalTime p.toParams s := by
  have hG := (ktail_bounds hT).2.2.2.2.2.1
  have hle := kmid_slot_scale_le p hs
  change E.t_GST ≤ 4 * p.Δ * (s : Time)
  change E.t_GST ≤ 4 * p.Δ * ((pt.r * p.R : Nat) : Time) at hG
  linarith

/-- The Tail receipt horizon contains the healing start. -/
theorem ktail_start_horizon {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) : tstar p pt.w ≤ rho.horizon := by
  have hh := (ktail_bounds hT).2.2.2.2.2.2
  have ht := hT.start
  rw [kmid_period_eq] at ht
  have hle := kmid_slot_scale_le p
    (show pt.r * p.R ≤ (pt.r + 1) * p.R + kappaF p ΔF by
      rw [Nat.add_mul]; omega)
  change 4 * p.Δ * (_ : Int) + p.Δ ≤ rho.horizon at hh
  linarith [p.deltaPos]

/-- A window suffix contains the enabled healing gate and its wake events. -/
theorem ktail_suffix_confirmed {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hsuf : HealSuffix p c rho (tstar p pt.w) i)
    (hhor : tstar p pt.w ≤ rho.horizon) : confirmedReaderIdx p c E rho x i := by
  apply finality_recovery_confirmedIdx p c E rho hT.set hx pt.w.u i
    (by
      have hsync := hT.input.wit.synchronous
      have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
        exact_mod_cast hT.input.wit.proposal_lower
      change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
      change E.t_GST ≤ 4 * p.Δ * (pt.w.u : Int)
      nlinarith [p.deltaPos]) hhor
  intro j hj
  have hjlt := kmid_tick_lt_afterTicks p c E rho hT.set.base.valid.toScheduleWellFormed
    hj le_rfl
  have hstart : afterTicksIdx rho (tstar p pt.w) ≤ i := by
    have hg : isGateTime p (tstar p pt.w) = true :=
      (isGateTime_iff p _).mpr ⟨pt.w.u, rfl⟩
    simpa only [HealSuffix_def, healStart_def, hg, ite_true] using hsuf.1
  exact hjlt.trans_le hstart

/-- The Tail healing start supplies the previous-slot join cutoff. -/
theorem ktail_window_join_cut {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hlo : pt.r * p.R ≤ s) : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
  have hstart := hT.start
  rw [kmid_period_eq] at hstart
  have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
    exact_mod_cast hT.input.wit.proposal_lower
  have hsync := hT.input.wit.synchronous
  have hle := kmid_slot_scale_le p hlo
  change 4 * p.Δ * (pt.w.u : Int) + 6 * p.Δ ≤ _ at hstart
  change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
  nlinarith [p.deltaPos]

/-- Each honest Tail HEAD read has the joined duty guard. -/
theorem ktail_window_joined {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hlo : pt.r * p.R ≤ s) (hhi : s ≤ (pt.r + 1) * p.R + kappaF p ΔF)
    {x : V} (hx : x ∈ rho.honest) :
    joinedAt p E rho x s (SA.voteTime p.toParams s) :=
  finality_recovery_joined p c E rho hT.set hx (ktail_window_join_cut hT hlo)
    ((ktail_slot_gst hT hlo).trans (by
      change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
      linarith [p.deltaPos])) (ktail_slot_horizon hT hhi).2.1

/-- The Tail window gate has run for each honest confirmed reader. -/
theorem ktail_window_confirmed {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hlo : pt.r * p.R ≤ s) (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest) :
    confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
      (SA.gateTime p.toParams s) := by
  apply finality_recovery_confirmed p c E rho hT.set hx s _ _
    (ktail_slot_gst hT hlo) le_rfl hhor
  intro j hj
  exact kmid_tick_lt_afterTicks p c E rho hT.set.base.valid.toScheduleWellFormed hj le_rfl

/-- Paper 22:1985–1989. An honest Tail slot has an actual honest proposal.
DC: INTENTIONAL: the FG-SA proposer duty always builds a block at a positive slot. -/
theorem ktail_window_proposal {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hlo : pt.r * p.R ≤ s) (hhi : s ≤ (pt.r + 1) * p.R + kappaF p ΔF) :
    ∃ b, HonestProposal E rho (fgsaInterface p c) s b := by
  have hh := (ktail_slot_horizon hT hhi).1
  exact kmid_honest_proposal_exists p c E rho hT.set.base.valid.toScheduleWellFormed
    hT.set.base.delta s hslot
    (finality_recovery_joined p c E rho hT.set hslot.2
      (ktail_window_join_cut hT hlo) (ktail_slot_gst hT hlo) hh) hh

/-- Paper 22:1988–1990. H3 serves every honest Tail proposal.
DC: INTENTIONAL: the healed AC service is an explicit input. -/
theorem ktail_window_exact {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {s : Slot} {b : Block}
    (hb : HonestProposal E rho (fgsaInterface p c) s b) (hlo : pt.r * p.R ≤ s) :
    ExactService p c E rho s b :=
  hT.input.ac.h3 s b hb ((ktail_bounds hT).2.2.2.2.1.trans hlo)

/-- Paper 22:1988–1990, 886–915. Rows of an action reach a proposal κ slots later,
inside the run. DC: INTENTIONAL: the W Tail uses the row delay ΔF. -/
theorem ktail_batch_horizon {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) {r : Nat} {s : Slot}
    (hG : E.t_GST ≤ p.actionTime r) (hs : r * p.R + kappaF p ΔF ≤ s)
    (hs' : s ≤ (pt.r + 1) * p.R + kappaF p ΔF) :
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ rho.horizon := by
  refine ⟨?_, (ktail_slot_horizon hT hs').1⟩
  rw [max_eq_left hG, kmid_actionTime_eq]
  have hcov := kmid_kappa_cover p ΔF (ktail_bounds hT).1
  have hle := kmid_slot_scale_le p hs
  have hsplit : 4 * p.Δ * ((r * p.R + kappaF p ΔF : Nat) : Time) =
      4 * p.Δ * ((r * p.R : Nat) : Time) + 4 * p.Δ * (kappaF p ΔF : Time) := by
    push_cast
    ring
  change _ ≤ 4 * p.Δ * (s : Time)
  linarith

/-! ### The Tail opening and its honest witness -/

/-- Paper 22:1985–2009 (FT-Tail-W), proof lines 1–4. The opening A₀ at rR, the
selected honest witness Q at the premise carrier, the witness crossing to e+1 and the
raw cuts of round r. Q is the premise carrier, not a new existential witness.
DC: INTENTIONAL: the W Tail keeps its chosen witnesses as data; no K-MID record. -/
structure TailOpeningWitness_W
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : TailKernelPt p) where
  A₀ : FGBlock (Fin p.n)
  Q : FGBlock (Fin p.n)
  e : Nat

  opening : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) (eraseFG A₀)
  carrierA : OpeningCarrier_W p c E rho (pt.r * p.R) (eraseFG A₀) A₀
  slotA : A₀.slot = pt.r * p.R
  honestQ : HonestProposal E rho (fgsaInterface p c) pt.carrier (eraseFG Q)
  carrierQ : OpeningCarrier_W p c E rho pt.carrier (eraseFG Q) Q
  rowsQ : ∃ rows, HonestCarrier p c E rho pt.carrier (eraseFG Q) rows ∧
    Q.rows = rows.filterMap RowWire.toRow?
  slotQ : Q.slot = pt.carrier
  serviceQ : ExactService p c E rho pt.carrier (eraseFG Q)

  heightA : (heightView p A₀).h = e
  highA : pt.w.M + 1 ≤ e
  heightQ : (heightView p Q).h = e + 1
  entryQ : EntryAt p (heightView p Q).T_h (e + 1)
  strictAQ : FGBlock.Preceq A₀ (heightView p Q).T_h ∧ A₀ ≠ (heightView p Q).T_h
  parentAQ : FGBlock.Preceq A₀ Q.parent
  justifiedBelowQ : (heightView p Q).h_j ≤ e

  sourceA : ∀ x ∈ rho.honest, actionSourceFG p c E rho x pt.r = some (some A₀)
  sourceQAtOpening : pt.carrier = (pt.r + 1) * p.R →
    ∀ x ∈ rho.honest, actionSourceFG p c E rho x (pt.r + 1) = some (some Q)

  rowsThroughOpening : ∀ j x r a h, r ≤ pt.r → HonestRowAt p c E rho j x r a →
    rowHeight a = some h → h ≤ e
  noFreshHeight : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → rowHeight a = some h →
    e + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 1) ≤ t
  noEarlyFinality : ∀ j x q a f t,
    HonestRowAt p c E rho j x q a → finHeight a = some f →
    e ≤ f → eventTime rho j = some t →
    p.actionTime (pt.r + 1) ≤ t

  actionInRun : p.actionTime (pt.r + 1) ≤ rho.horizon
  capThroughAction : ∀ i x W,
    i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) →
    HeldAt p c E rho i x W → (heightView p W).h ≤ e + 1
  finalityThroughAction : ∀ i x W,
    i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) →
    HeldAt p c E rho i x W → (finalityView p W).h_F < e
  heldQFrom : ∀ x ∈ rho.honest, ∀ k t, SA.voteTime p.toParams pt.carrier ≤ t →
    afterTicksIdx rho t ≤ k → Q ∈ (storeAt p c E rho k x).fg.TF
  chainQ : ChainRowsBefore p c E rho Q (p.actionTime (pt.r + 1))
  coverQ : FGBlock.Preceq pt.U (heightView p Q).J ∨
    FGBlock.Preceq pt.U (finalityView p Q).F

variable (p c E rho) in
/-- Paper 22:1985–2009 (FT-Tail-W), proof lines 1–4: FF1-A, FF2 and SO-COV give
the complete height-e target batch before the witness; the witness Q consumes it or
inherits a crossing, so ht(Q) = e+1, and the cap excludes an earlier row at e+1.
The Foundation facts are explicit inputs.
DC: INTENTIONAL: Assembly supplies the source names, raw origin, batch coverage and
the FF2 target coverage, as for K-MID. -/
theorem tail_opening_and_witness (G ΔF : Time) (pt : TailKernelPt p)
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false) :
    Nonempty (TailOpeningWitness_W p c E rho ΔF pt) := by
  classical
  obtain ⟨_hF0, hκ2, hκR, _hR2, hs2, _hGST, _hhorT⟩ := ktail_bounds hT
  have hs := hT.set.base.valid.toScheduleWellFormed
  have faultQ := hT.set.faultQ
  have laws := (fgCertificateLaws p).height
  have hwin := hT.window
  rw [Gen.Pure.Tail_W_def] at hwin
  obtain ⟨hwA, -, -⟩ := hwin
  obtain ⟨hc1, hc2, hwQ⟩ := hT.carrier
  have e1 : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
  have hc1' : pt.r * p.R + kappaF p ΔF ≤ (pt.carrier : Nat) := hc1
  have hc2' : (pt.carrier : Nat) ≤ (pt.r + 1) * p.R := hc2
  have n0T : pt.r * p.R ≤ (pt.r + 1) * p.R + kappaF p ΔF := by omega
  have n0Q : pt.r * p.R ≤ (pt.carrier : Nat) := by omega
  have nA2 : pt.r * p.R + 2 ≤ (pt.carrier : Nat) := by omega
  have nQT : (pt.carrier : Nat) ≤ (pt.r + 1) * p.R + kappaF p ΔF :=
    le_trans hc2' (Nat.le_add_right _ _)
  have nQ2 : (pt.carrier : Nat) + 2 ≤ (pt.r + 1) * p.R + kappaF p ΔF :=
    Nat.add_le_add hc2' hκ2
  have nA2T : pt.r * p.R + 2 ≤ (pt.r + 1) * p.R + kappaF p ΔF := by omega
  have nZ2T : (pt.r + 1) * p.R + 2 ≤ (pt.r + 1) * p.R + kappaF p ΔF :=
    Nat.add_le_add_left hκ2 _
  have hx₀ := hwA.2
  have hhorZ := (ktail_slot_horizon hT (s := (pt.r + 1) * p.R)
    (Nat.le_add_right _ _)).2.2 nZ2T
  have hhorAct : p.actionTime (pt.r + 1) ≤ rho.horizon := hhorZ
  have hGSTr : E.t_GST ≤ p.actionTime pt.r :=
    (ktail_slot_gst hT le_rfl).trans (kmid_proposal_le_action p le_rfl)
  have hawakeR : ∀ x ∈ rho.honest, E.awake x (p.actionTime pt.r) = true := fun x hx =>
    hT.set.awake x hx _ hGSTr
      (le_trans ((kmid_action_strictMono p).monotone (Nat.le_succ pt.r)) hhorAct)
  -- The opening and the witness.
  obtain ⟨a, hAp⟩ := ktail_window_proposal hT hwA le_rfl n0T
  obtain ⟨A₀, heA, carrierA, slotA, -, -⟩ := kmid_opening_carrier p c E rho hs hAp
  subst heA
  have exA := ktail_window_exact hT hAp le_rfl
  have hhA := ktail_slot_horizon hT n0T
  have sourceA : ∀ x ∈ rho.honest,
      actionSourceFG p c E rho x pt.r = some (some A₀) := fun x hx =>
    kmid_source_of_exact p c E rho exA (hhA.2.2 nA2T) pt.r rfl x hx
      (ktail_window_confirmed hT le_rfl (hhA.2.2 nA2T) hx)
  obtain ⟨q, hq⟩ := ktail_window_proposal hT hwQ n0Q nQT
  obtain ⟨Q, heQ, carrierQ, slotQ, ⟨rowsQ, hcarQ, hrowsQ⟩, stQ, hstQ, hlookQ, hparTFQ⟩ :=
    kmid_opening_carrier p c E rho hs hq
  subst heQ
  have exQ := ktail_window_exact hT hq n0Q
  have hhQ := ktail_slot_horizon hT nQT
  -- The opening is high.
  obtain ⟨_, y₀, _, C₀, hrow₀, -, hsrc₀, -, hC₀⟩ := hT.input.wit.fresh
  have hpre := hT.input.t.h2 y₀ pt.w.rStar C₀ (pt.r * p.R) (eraseFG A₀)
    ((HonestRowAt_def p c E rho _ _ _ _).mp hrow₀).1 hsrc₀
    (show pt.w.M + 1 ≤ (heightView p C₀).h by rw [hC₀]) hAp
    (by rw [← hT.input.wit.label]; exact hs2)
  rw [eraseFG_parent] at hpre
  have highA : pt.w.M + 1 ≤ (heightView p A₀).h := by
    have h1 := laws.h_mono (kmid_lift_preceq p hpre)
    have h2 := laws.h_mono (kmid_parent_preceq p A₀)
    rw [hC₀] at h1
    exact h1.trans h2
  -- Rows through action r and the raw cut at action r+1.
  have rowsQr : ∀ j x r a h, r ≤ pt.r → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h ≤ (heightView p A₀).h := by
    intro j x r a h hr ha hh
    rcases Nat.lt_or_ge r pt.r with hlt | hge
    · exact kmid_rows_below_opening p c E rho pt.w hT.input.t.h2 hNames pt.r A₀ hAp highA
        j x r a h hlt ha hh
    · obtain rfl : r = pt.r := le_antisymm hr hge
      exact (kmid_rows_at_source p c E rho hNames pt.r A₀ sourceA j x a h ha hh).le
  obtain ⟨noFreshHeight, rowsBefore⟩ :=
    kmid_rows_cut p c E rho (heightView p A₀).h pt.r rowsQr
  obtain ⟨noEarlyFinality, finBefore⟩ :=
    kmid_fin_cut p c E rho (heightView p A₀).h pt.r rowsQr
  have capQ : ∀ i x W, i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) →
      HeldAt p c E rho i x W → (heightView p W).h ≤ (heightView p A₀).h + 1 :=
    fun i x W hi hW => kmid_held_cap_afterTicks p c E rho hOrigin hT.set.base faultQ _ _
      rowsBefore i x W hi hW
  -- The witness height.
  obtain ⟨iQ, hiQ, hQTF⟩ := kmid_head_held p c E rho exQ hhQ.2.1 _ hwA.2
    (ktail_window_joined hT n0Q nQT hwA.2)
  have hQup : (heightView p Q).h ≤ (heightView p A₀).h + 1 :=
    capQ iQ _ Q ((kmid_tick_lt_afterTicks p c E rho hs hiQ
      (kmid_vote_lt_action p hc2').le).le) ⟨hwA.2, hQTF⟩
  have hpAQ := hT.input.t.h2 _ pt.r A₀ pt.carrier (eraseFG Q) hx₀
    (sourceA _ hx₀) highA hq nA2
  rw [eraseFG_parent] at hpAQ
  have parentAQ := kmid_lift_preceq p hpAQ
  have hQne : Q ≠ .genesis := by
    intro h
    rw [h] at slotQ
    have h0 : (0 : Nat) = pt.carrier := slotQ
    omega
  have hparLow : (heightView p A₀).h ≤ (heightView p Q.parent).h := laws.h_mono parentAQ
  have entryA : EntryAt p (heightView p A₀).T_h (heightView p A₀).h :=
    ⟨laws.entry_same_height A₀, laws.entry_idem A₀⟩
  have pathA : FGBlock.Preceq (heightView p A₀).T_h Q.parent :=
    preceq_trans (laws.entry_preceq A₀) parentAQ
  have batchQ : (heightView p Q.parent).h = (heightView p A₀).h →
      BatchPrem p c E rho ΔF .target pt.r (heightView p A₀).h (heightView p A₀).T_h Q := by
    intro hpar
    refine kmid_batchPrem p c E rho ΔF hT.set.base faultQ hT.set.fault hT.set.deltaF
      hT.input.t.rows.receipt pt.r _ _ Q ?_ ⟨rowsQ, by rw [slotQ]; exact hcarQ, hrowsQ⟩ stQ
      (by rw [slotQ]; exact hstQ) hlookQ hparTFQ (by rw [slotQ]; exact nA2) entryA pathA hpar ?_
    · rw [slotQ]
      exact ktail_batch_horizon hT hGSTr hc1' nQT
    · intro x hx
      obtain ⟨j, rS, a, hle, ha, hc, hp⟩ := hSOCOVTarget x hx pt.r A₀ (sourceA x hx) highA
        (hawakeR x hx)
      exact ⟨j, rS, a, hle, ha, hc, hp⟩
  have hQlow : (heightView p A₀).h + 1 ≤ (heightView p Q).h := by
    rcases Nat.eq_or_lt_of_le hparLow with heq | hlt
    · have htri := fgsa_foldTrichotomy_target p
      rw [foldTrichotomy_def] at htri
      exact (htri _ _ Q hQne entryA pathA
        (fun h => hBatch c E rho pt.r _ _ Q (batchQ h) h) (fun h => by cases h)).1
    · exact hlt.trans_le (laws.h_mono (kmid_parent_preceq p Q))
  have heightQ : (heightView p Q).h = (heightView p A₀).h + 1 := le_antisymm hQup hQlow
  -- The fresh entry of the witness.
  have entryQ : EntryAt p (heightView p Q).T_h ((heightView p A₀).h + 1) :=
    ⟨(laws.entry_same_height Q).trans heightQ, laws.entry_idem Q⟩
  have pathEQ : FGBlock.Preceq (heightView p Q).T_h Q := laws.entry_preceq Q
  have hA₀Q : FGBlock.Preceq A₀ Q := preceq_trans parentAQ (kmid_parent_preceq p Q)
  have strictAQ : FGBlock.Preceq A₀ (heightView p Q).T_h ∧ A₀ ≠ (heightView p Q).T_h := by
    rcases preceq_total_of_common hA₀Q pathEQ with h | h
    · refine ⟨h, ?_⟩
      intro he
      have h1 := entryQ.1
      rw [← he] at h1
      exact Nat.succ_ne_self _ h1.symm
    · exfalso
      have h1 := laws.h_mono h
      rw [entryQ.1] at h1
      exact Nat.not_succ_le_self _ h1
  have hjQ : (heightView p Q).h_j ≤ (heightView p A₀).h := by
    have := laws.justified_below_height Q
    simp only [Height] at *
    omega
  exact ⟨{
    A₀ := A₀
    Q := Q
    e := (heightView p A₀).h
    opening := hAp
    carrierA := carrierA
    slotA := slotA
    honestQ := hq
    carrierQ := carrierQ
    rowsQ := ⟨rowsQ, hcarQ, hrowsQ⟩
    slotQ := slotQ
    serviceQ := exQ
    heightA := rfl
    highA := highA
    heightQ := heightQ
    entryQ := entryQ
    strictAQ := strictAQ
    parentAQ := parentAQ
    justifiedBelowQ := hjQ
    sourceA := sourceA
    sourceQAtOpening := fun heq =>
      fun x hx => kmid_source_of_exact p c E rho exQ (hhQ.2.2 nQ2) (pt.r + 1) heq x hx
        (ktail_window_confirmed hT n0Q (hhQ.2.2 nQ2) hx)
    rowsThroughOpening := rowsQr
    noFreshHeight := noFreshHeight
    noEarlyFinality := noEarlyFinality
    actionInRun := hhorAct
    capThroughAction := capQ
    finalityThroughAction := fun i x W hi hW =>
      kmid_held_finality_afterTicks p c E rho hOrigin hT.set.base faultQ _ _
        ((Nat.zero_lt_succ _).trans_le highA) finBefore i x W hi hW
    heldQFrom := fun x hx k t ht hk =>
      kmid_head_held_from p c E rho hs exQ hhQ.2.1 x hx
        (ktail_window_joined hT n0Q nQT hx) k t ht hk
    chainQ := kmid_chainRows_of_head p c E rho hs exQ hhQ.2.1 _ hx₀
      (ktail_window_joined hT n0Q nQT hx₀) _
      (kmid_vote_lt_action p hc2')
    coverQ := hT.cover pt.carrier Q le_rfl hq carrierQ }⟩

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Finality.RowsPrem
public import AvailableChainFGSAProofs.Proofs.Finality.Receipt
public import AvailableChainFGSAProofs.Proofs.Finality.Accept
public import AvailableChainFGCompose.Proofs.Finality.Kernel

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289: a received wire remains held at the proposal read.
DC: SAME cumulative row storage, with the actual proposal tick. -/
private theorem kernel_held_at_proposal (base : BaseSet p c E rho)
    (s : Slot) (b : Block) (hp : HonestProposal E rho (fgsaInterface p c) s b)
    (a : RowWire p.n) (d : Time)
    (hheld : HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) s) a d)
    (hd : d ≤ SA.proposalTime p.toParams s) : heldAtProposal p c E rho s a := by
  obtain ⟨_, _, _, _, _, hread, _⟩ :=
    kmid_proposal_read p c E rho base.valid.toScheduleWellFormed hp
  exact finality_heldBefore_at_proposal p c E rho base.valid.toScheduleWellFormed
    hread hheld hd

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1304: emitted names bound rows through the final action.
DC: INTENTIONAL: each source is held at its own action tick. -/
private theorem kernel_rows_before {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ j x r a u h T timeout, HonestRowAt p c E rho j x r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (pt.r + 2 + 1) → h ≤ m.d + 2 := by
  intro j x r a u h T timeout ha hu hv hr
  have hpair : a.payload.height_pair = u.height_pair := by
    rw [kmid_wire_decode p hu]
    rfl
  obtain ⟨C, hsrc, he⟩ := hNames j x r a (h, T) ha (by rw [hpair, hv]; rfl)
  have hx := ((HonestRowAt_def p c E rho _ _ _ _).mp ha).1
  have hrq : r ≤ pt.r + 2 := by
    have := (kmid_action_strictMono p).lt_iff_lt.mp hr
    omega
  have hh : h = (heightView p C).h := congrArg Prod.fst he
  rw [hh]
  by_cases heq : r = pt.r + 2
  · subst r
    exact kernel_middle_source_cap p c E rho ΔF pt A m
      hK.set.base.valid.toScheduleWellFormed hx hsrc
  · obtain ⟨i, _, hilt, hheld⟩ := kmid_source_held_at_tick p c E rho
      hK.set.base.valid.toScheduleWellFormed hx hsrc
    have hcut := afterTicksIdx_mono rho ((kmid_action_strictMono p).monotone hrq)
    exact m.capThroughFinalAction i x C (hilt.le.trans (List.length_filter_le _ _))
      (hilt.le.trans hcut) hheld

/-- The SA slot clock as the shared FG timing (fieldwise, definitional). -/
private def d7b_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem d7b_timing_laws (p : Params) : FGCompose.FGTimingLaws (d7b_timing p) where
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1265–1289: the terminal proposal is after row delivery and before
the next action. DC: INTENTIONAL: the kernel deadline bounds the actual read.
P0d7b-a: through the generic `FGCompose.kernel_terminal_bounds_W`. -/
private theorem kernel_terminal_bounds {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) :
    max (p.actionTime (pt.r + 2)) E.t_GST + ΔF ≤
        SA.proposalTime p.toParams ((pt.r + 2) * p.R + kappaF p ΔF) ∧
      SA.proposalTime p.toParams ((pt.r + 2) * p.R + kappaF p ΔF) ≤ rho.horizon ∧
      SA.proposalTime p.toParams ((pt.r + 2) * p.R + kappaF p ΔF) <
        p.actionTime (pt.r + 2 + 1) := by
  have hG := (kmid_kernel_bounds hK).2.2.2.2.2.1
  have hGa : E.t_GST ≤ p.actionTime (pt.r + 2) :=
    hG.trans (kmid_proposal_le_action p (Nat.mul_le_mul_right p.R (by omega)))
  have hF : 0 ≤ ΔF := le_trans (le_of_lt E.Δ_pos) hK.set.deltaF
  obtain ⟨h1, h2, h3⟩ := FGCompose.kernel_terminal_bounds_W (d7b_timing p)
    (d7b_timing_laws p) (pt.r + 2) ⟨hK.bound.kappa_le_R⟩ hF hGa
  change _ = kernelDeadlineW p ΔF (pt.r + 2) at h2
  have hh := hK.hhor
  have hd := p.deltaPos
  refine ⟨h1, ?_, h3⟩
  change SA.proposalTime p.toParams ((pt.r + 2) * p.R + kappaF p ΔF) + p.Δ = _ at h2
  linarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1171–1305 (F1–F9): the forward W kernel gives a strict fresh
extension accepted by every honest node before the kernel deadline.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL: W retention, exact signed
rows, the actual receipt and its guards replace the DC confirmation pin. -/
theorem finality_kernel_W_of
    (hServices : FinalityActionReceipts p c E rho) (G ΔF : Time)
    (hδ : p.δt = 2 * p.R) (pt : KernelPt)
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    KernelConclusion_W p c E rho ΔF pt.r := by
  classical
  have hs := hK.set.base.valid.toScheduleWellFormed
  have hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) := by
    intro j x r a e ha he
    obtain ⟨C, hc, hn, _⟩ := hEmittedSource j x r a e ha he
    exact ⟨C, hc, hn⟩
  rw [KernelConclusion_W_def]
  intro A hA
  obtain ⟨m⟩ := kernel_opening_and_middle p c E rho G ΔF pt hδ hK hNames horigin hBatch
    (fun x hx r C hsrc hhigh hawake => high_target_row_covered p c E rho pt.w
      hK.input.t.h1 hQC hNames hK.set.base.linked hs x hx r C hsrc hhigh hawake) A hA
  obtain ⟨rows, hfresh, hentry, _⟩ := rowsPrem_fresh_rows p c E rho hK m hServices hQC hXing hNames
    (honestSeats p c rho) subset_rfl (kmid_honest_quorum p c rho hK.set.base.linked hK.set.fault)
  have ht := kernel_terminal_bounds p c E rho hK
  have hw := hK.window
  rw [Gen.Pure.FGoodE_W_def] at hw
  have hslot := hw.2.2.2
  have hlo : pt.r * p.R ≤ (pt.r + 2) * p.R + kappaF p ΔF :=
    (Nat.mul_le_mul_right p.R (show pt.r ≤ pt.r + 2 by omega)).trans (Nat.le_add_right _ _)
  obtain ⟨b, hb⟩ := kmid_honest_proposal_exists p c E rho hs hK.set.base.delta _ hslot
    (finality_recovery_joined p c E rho hK.set hslot.2
      (kmid_window_join_cut hK hlo) (kmid_slot_gst hK hlo) ht.2.1) ht.2.1
  obtain ⟨X, heX, _, hXs, hcar, st, hst, hlook, hpar⟩ :=
    kmid_opening_carrier p c E rho hs hb
  subst b
  have hX : HonestProposal E rho (fgsaInterface p c) X.slot (eraseFG X) := by
    rw [hXs]
    exact hb
  have hstX : proposalStateAt p c E rho X.slot = some st := by
    rw [hXs]
    exact hst
  have hne : X ≠ .genesis := by
    intro he
    have hh := hXs
    rw [he] at hh
    have hk := (kmid_kernel_bounds hK).2.1
    change 0 = (pt.r + 2) * p.R + kappaF p ΔF at hh
    omega
  have hpath : FGBlock.Preceq m.X_D X.parent := by
    let x := V2.D.proposerOf rho (fgsaInterface p c) X.slot
    have hx : x ∈ rho.honest := hX.1.2
    obtain ⟨nd, C, hnd, hsrc, hDC, hCh, _⟩ :=
      rowsPrem_action_source p c E rho hK m hQC hXing hNames x hx
    have hsource : actionSourceFG p c E rho x (pt.r + 2) = some (some C) := by
      rw [actionSourceFG_def, hnd]
      exact congrArg some hsrc
    have hhigh : high p pt.w C := by
      rw [high_def]
      rw [hCh]
      have := m.highA
      omega
    have hp := hK.input.t.h2 x (pt.r + 2) C X.slot (eraseFG X) hx hsource hhigh hX (by
      rw [hXs]
      have := (kmid_kernel_bounds hK).2.1
      omega)
    rw [eraseFG_parent] at hp
    exact preceq_trans hDC (kmid_lift_preceq p hp)
  have hcap : (heightView p X.parent).h ≤ m.d + 3 := by
    obtain ⟨j, _, _, hj, _, hread, _⟩ := kmid_proposal_read p c E rho hs hX
    have he : st = ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) X.slot))
        (SA.proposalTime p.toParams X.slot)).st := Option.some.inj (hstX.symm.trans hread)
    have hheld : HeldAt p c E rho j
        (V2.D.proposerOf rho (fgsaInterface p c) X.slot) X.parent := by
      refine ⟨hX.1.2, ?_⟩
      rw [he] at hpar
      change X.parent ∈ (FGSA.clock p _ _).fg.TF at hpar
      rw [clock_fg] at hpar
      exact hpar
    have hjcut : j ≤ V2.D.Run.idxBefore rho (p.actionTime (pt.r + 3)) := by
      apply Nat.le_of_lt
      apply (Gen.V2.Duty.index_lt_idxBefore_iff hs hj _).mpr
      rw [hXs]
      exact ht.2.2
    exact rowsPrem_anchor_cap p c E rho hK m hNames hcapBefore j _ X.parent hjcut hheld
  let carriage : TerminalCarriagePrem_W p c E rho ΔF (pt.r + 2) (m.d + 1) m.X_D m.U X := {
    base := hK.set.base
    faultQ := hK.set.faultQ
    deltaF := hK.set.deltaF
    carrier := by rw [hXs]; exact hcar
    parent := ⟨st, hstX, hlook⟩
    path := hpath
    freshHeight := m.heightD
    retainedOrCovered := rowsPrem_anchor_retained_or_covered p c E rho m X.parent hpath hcap
    horizon := by rw [hXs]; exact ⟨ht.1, ht.2.1⟩
    seats := honestSeats p c rho
    rows := rows
    fresh := hfresh
    heightEntry := hentry
    receipt := by
      intro i hi
      obtain ⟨_, _, hf⟩ := (FreshFinalityRows_W_def p c E rho _ _ _ _ _).mp hfresh
      obtain ⟨j, _, ha, _⟩ := hf i hi
      have hd : max (p.actionTime (pt.r + 2)) E.t_GST + ΔF ≤
          SA.proposalTime p.toParams X.slot := hXs ▸ ht.1
      have hh := hK.input.t.rows.receipt j _ _ (rows i) ha (hd.trans (hXs ▸ ht.2.1))
        _ hX.1.2
      exact ⟨hh, kernel_held_at_proposal p c E rho hK.set.base X.slot (eraseFG X) hX
        (rows i) _ hh hd⟩ }
  have hfinal : FGBlock.Preceq m.U (Window.derive p p.K_W X).F := by
    rcases terminalCarriage_W_of_tRowsSelect p c E rho hsel ΔF (pt.r + 2) (m.d + 1)
        m.X_D m.U X carriage with hcovered | ⟨hvalid, _⟩
    · exact ((Window.CoveredW_def p X (m.d + 1) m.U).mp
        (covered_parent_W p (m.d + 1) m.U X hcovered)).2
    · obtain ⟨e, he, hej, heU⟩ := (Window.RetainedW_def p m.X_D (m.d + 1) m.U).mp m.retainedD
      obtain ⟨B, hBD, hbirth, _⟩ := Window.window_entry_origin p p.K_W p.kWLarge m.X_D e he
      rw [hej, heU] at hbirth
      have batch : FinalityBatchPrem_W p c E rho ΔF (pt.r + 2) (m.d + 1) m.U X := {
        base := carriage.base
        faultQ := carriage.faultQ
        deltaF := carriage.deltaF
        rowsReceipt := hK.input.t.rows.receipt
        carrier := carriage.carrier
        after := by rw [hXs]
        horizon := carriage.horizon
        parent := carriage.parent
        birth := ⟨B, preceq_trans hBD hpath, hbirth⟩
        retainedOrCovered := carriage.retainedOrCovered
        batch := by
          obtain ⟨hS, hQ, hf⟩ := (FreshFinalityRows_W_def p c E rho _ _ _ _ _).mp hfresh
          refine ⟨honestSeats p c rho, hS, hQ, ?_⟩
          intro i hi
          obtain ⟨j, _, ha, hc, hauth, _, hn, _⟩ := hf i hi
          refine ⟨j, rows i, ha, hc, hauth, hn, (carriage.receipt i hi).1,
            (carriage.receipt i hi).2, fun _ => ?_⟩
          have hv := (hvalid i hi).1
          obtain ⟨st', P, hs', hP, hrow⟩ := (ValidForParent_def p c E rho _ _ _).mp hv
          have he := Option.some.inj (hstX.symm.trans hs')
          subst st'
          have heP := Option.some.inj (hlook.symm.trans hP)
          subst P
          exact ⟨hrow, hv⟩ }
      rcases finalityBatchCoverage_W_of_tRowsSelect p c E rho hsel ΔF (pt.r + 2)
          (m.d + 1) m.U X batch with hcovered | hcover
      · exact ((Window.CoveredW_def p X (m.d + 1) m.U).mp
          (covered_parent_W p (m.d + 1) m.U X hcovered)).2
      · exact (pendingFold_consume_W p (m.d + 1) m.U X ⟨hne, hcover⟩).1
  obtain ⟨accept⟩ := receipt_acceptPrem_W p c E rho G ΔF pt hK (m.d + 1) m.X_D m.U X
    carriage hXs hne hsel hI3 m.justifiedHeightD (by have := m.highA; omega) hStrat
    hEmittedSource hcapBefore (kernel_rows_before p c E rho hK m hNames)
  have hfinalView : FGBlock.Preceq m.U (finalityView p X).F := by
    simpa only [finalityView_def, Window.certificateFinality_def,
      Window.projectFinality_def] using hfinal
  have ha := fgsa_acceptBefore_W p c E rho X m.U (SA.proposalTime p.toParams X.slot)
    (kernelDeadlineW p ΔF (pt.r + 2)) { accept with finalized := hfinalView }
  refine ⟨m.A₀, m.eraseA, m.carrierA, m.heldAAtEnd, m.U, m.strictAU.1, m.strictAU.2, ?_, ha⟩
  rw [m.freshEntry.1, m.heightA]

end AvailableChain.FGSA.Run
end

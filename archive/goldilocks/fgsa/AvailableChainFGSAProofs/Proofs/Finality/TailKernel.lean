module
public import AvailableChainFGSAProofs.Proofs.Finality.TailSplit
public import AvailableChainFGSAProofs.Proofs.Finality.TailReceipt
public import AvailableChainFGSAProofs.Proofs.Finality.Accept
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun -- shake: keep (store API)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] [Fintype V] in
private theorem ktail_kernel_rowHeight {a : RowWire p.n} {row : Row (Fin p.n)} {h : Nat}
    {T : BlockId} {timeout : Bool} (hd : a.toRow? = some row)
    (hp : row.height_pair = .vote h T timeout) : rowHeight a = some h := by
  rw [kmid_wire_decode p hd]
  change (match row.height_pair with | .empty => none | .vote h _ _ => some h) = some h
  rw [hp]

private theorem ktail_kernel_F (X : FGBlock (Fin p.n)) :
    (finalityView p X).F = (Window.derive p p.K_W X).F := by
  simp only [finalityView_def, Window.certificateFinality_def, Window.projectFinality_def]

/-- Paper 22:2001–2005 (FT-Tail-W), plan §1 step 6. Every honest proposal X at the
terminal slot (r+1)R+κ has Q below its parent: H2 from a fresh source of round r+1.
This holds in both arms of the witness cover.
DC: INTENTIONAL: TCarrier transfer of a high action source. -/
theorem ktail_terminal_path {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (X : FGBlock (Fin p.n))
    (hX : HonestProposal E rho (fgsaInterface p c)
      ((pt.r + 1) * p.R + kappaF p ΔF) (eraseFG X)) :
    FGBlock.Preceq ow.Q X.parent := by
  obtain ⟨-, hκ2, -, -, -, -, -⟩ := ktail_bounds hT
  have hwin := hT.window
  rw [Gen.Pure.Tail_W_def] at hwin
  have hx₀ := hwin.1.2
  obtain ⟨nd, C, hnd, hsrc, hQC, hCh, -⟩ := ktail_action_source hT ow _ hx₀
  have hsrc' : actionSourceFG p c E rho (V2.D.proposerOf rho (fgsaInterface p c)
      (pt.r * p.R)) (pt.r + 1) = some (some C) := by
    rw [actionSourceFG_def, hnd]
    change some (FGSA.fgSource p nd.st) = some (some C)
    rw [hsrc]
  have hhighC : high p pt.w C := by
    change pt.w.M + 1 ≤ (heightView p C).h
    rw [hCh]
    exact Nat.le_succ_of_le ow.highA
  have hCX := hT.input.t.h2 _ (pt.r + 1) C _ (eraseFG X) hx₀ hsrc' hhighC hX
    (Nat.add_le_add_left hκ2 _)
  rw [eraseFG_parent] at hCX
  exact preceq_trans hQC (kmid_lift_preceq p hCX)

/-- Paper 22:1997–2000, 1290–1302. Honest rows of rounds through r+1 are at most e+1
high: through r by the opening cut, at r+1 by the fresh action sources.
DC: INTENTIONAL: the emitted-name law fixes each row height to its action source. -/
theorem ktail_rows_through_next {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ j z r a h, r ≤ pt.r + 1 → HonestRowAt p c E rho j z r a →
      rowHeight a = some h → h ≤ ow.e + 1 := by
  intro j z r a h hr ha hh
  rcases Nat.lt_or_ge r (pt.r + 1) with hlt | hge
  · exact (ow.rowsThroughOpening j z r a h (Nat.le_of_lt_succ hlt) ha hh).trans
      (Nat.le_succ _)
  · obtain rfl : r = pt.r + 1 := le_antisymm hr hge
    obtain ⟨C', hC', rfl⟩ := kmid_row_source_height p c E rho hnames ha hh
    obtain ⟨nd', C'', hnd', hsrc'', -, hC''h, -⟩ :=
      ktail_action_source hT ow z ((HonestRowAt_def p c E rho _ _ _ _).mp ha).1
    rw [actionSourceFG_def, hnd'] at hC'
    change some (FGSA.fgSource p nd'.st) = some (some C') at hC'
    rw [hsrc''] at hC'
    cases Option.some.inj (Option.some.inj hC')
    exact hC''h.le

/-- Paper 22:1997–2005 (FT-Tail-W), plan §3. In the pending arm with complete fresh rows,
the terminal carrier X finalizes the witness key K = J(Q): the general carriage at
certificate height h_j(Q) and source height e+1, then the fold or prior coverage.
DC: INTENTIONAL: W carriage with independent heights; Assembly supplies no extra input. -/
theorem ktail_terminal_final {G ΔF : Time} {pt : TailKernelPt p}
    (hT : TailKernelPrem_W p c G ΔF E rho pt) (ow : TailOpeningWitness_W p c E rho ΔF pt)
    (X : FGBlock (Fin p.n))
    (hX : HonestProposal E rho (fgsaInterface p c)
      ((pt.r + 1) * p.R + kappaF p ΔF) (eraseFG X))
    (hslot : X.slot = (pt.r + 1) * p.R + kappaF p ΔF)
    (hcarrier : ∃ wireRows, HonestCarrier p c E rho X.slot (eraseFG X) wireRows ∧
      X.rows = wireRows.filterMap RowWire.toRow?)
    (st : State p.n) (hst : proposalStateAt p c E rho X.slot = some st)
    (hlook : FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (hrc : Window.RetainedW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J ∨
      Window.CoveredW p X.parent (heightView p ow.Q).h_j (heightView p ow.Q).J)
    (rows : Fin p.n → RowWire p.n)
    (hrows : ∀ i ∈ honestSeats p c rho, ∃ j C,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) (pt.r + 1) (rows i) ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
      (rows i).auth = .seat .fg i ∧
      rowHeight (rows i) = some (ow.e + 1) ∧
      FinalityNames p (rows i) (heightView p ow.Q).h_j (heightView p ow.Q).J ∧
      actionSourceFG p c E rho (rho.seatOf (.base .fg) i) (pt.r + 1) = some (some C) ∧
      (heightView p C).h = ow.e + 1 ∧
      (rows i).payload.height_pair =
        NamedHeightPair.vote (ow.e + 1) (heightView p ow.Q).T_h.root false ∧
      (∀ j' r a h, r < pt.r + 1 →
        HonestRowAt p c E rho j' (rho.seatOf (.base .fg) i) r a →
        rowHeight a = some h → h < ow.e + 1)) :
    FGBlock.Preceq (heightView p ow.Q).J (Window.derive p p.K_W X).F := by
  have hs := hT.set.base.valid.toScheduleWellFormed
  have hGSTq : E.t_GST ≤ p.actionTime (pt.r + 1) :=
    (ktail_slot_gst hT (s := pt.r * p.R) le_rfl).trans
      ((kmid_proposal_le_action p le_rfl).trans
        (le_of_lt (kmid_action_strictMono p (Nat.lt_succ_self pt.r))))
  have hwin := (ktail_batch_horizon hT hGSTq (s := X.slot) hslot.ge hslot.le)
  have hprop : V2.D.proposerOf rho (fgsaInterface p c) X.slot ∈ rho.honest := by
    rw [hslot]
    exact hX.1.2
  have hXne : X ≠ .genesis := by
    intro hg
    rw [hg] at hslot
    obtain ⟨-, hκ2, -, -, -, -, -⟩ := ktail_bounds hT
    have h0 : (0 : Nat) = (pt.r + 1) * p.R + kappaF p ΔF := hslot
    omega
  have hcarry := terminalCarriage_general_W p c E rho hT.set.base.valid
    hT.input.t.rows.select (pt.r + 1) (heightView p ow.Q).h_j (ow.e + 1) ow.Q
    (heightView p ow.Q).J X (Nat.lt_succ_of_le ow.justifiedBelowQ) hcarrier ⟨st, hst, hlook⟩
    (ktail_terminal_path hT ow X hX) ow.heightQ hrc (honestSeats p c rho) rows
    (kmid_honest_quorum p c rho hT.set.base.linked hT.set.fault) ?_ ?_ ?_
  · rcases hcarry with hcov | ⟨-, hchild⟩
    · exact ((Window.CoveredW_def p X _ _).mp (covered_parent_W p _ _ X hcov)).2
    · exact (pendingFold_consume_W p _ _ X ⟨hXne, hchild⟩).1
  · intro i hi
    obtain ⟨j, -, ha, -, hauth, hh, hnm, -⟩ := hrows i hi
    exact ⟨j, ha, hauth, hh, hnm⟩
  · intro i hi
    obtain ⟨-, -, -, -, -, -, -, -, -, hpair, -⟩ := hrows i hi
    rw [hpair]
    rfl
  · intro i hi
    obtain ⟨j, -, ha, -⟩ := hrows i hi
    have hrec := hT.input.t.rows.receipt j _ (pt.r + 1) (rows i) ha
      (hwin.1.trans hwin.2) _ hprop
    exact finality_heldBefore_at_proposal p c E rho hs hst hrec hwin.1

/-- Paper 22:1985–2009 (FT-Tail-W), plan §1 steps 1–7 and §4. The Tail composition: the
opening and witness, the terminal carrier at (r+1)R+κ, its finalization of U, and the
two-height receipt adapter at the final action r+1. The finalized arm propagates F(Q);
the pending arm carries the witness key by complete fresh rows.
Open inputs: `hbatch` (the action walk batch, K-ROWS) and `hmixed` (the mixed arm of
ktail_pending_rows; proved by `ktail_hmixed_of_relay` in TailMixed, see
`tail_kernel_W_of_relay`). All other inputs are named Foundations facts.
DC: INTENTIONAL: W Tail kernel; Assembly supplies the named inputs. -/
theorem tail_kernel_W_of (G ΔF : Time) (pt : TailKernelPt p)
    (hT : TailKernelPrem_W p c G ΔF E rho pt)
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
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (hqc : RQCOrigin p c E rho)
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
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hbatch : ∀ ow : TailOpeningWitness_W p c E rho ΔF pt, ∀ x ∈ rho.honest, ∀ nd,
      postClock E rho x (p.actionTime (pt.r + 1)) = some nd →
      ∃ raw support seats m,
        FGSA.fgHead p nd.st = FGSA.getHead p nd.st raw support ∧
        Gen.Pure.Batch (Finset.card seats) m ∧
        WalkBatch p c rho nd.st ((pt.r + 1) * p.R + 1) raw support (eraseFG ow.Q) seats m)
    (hmixed : ∀ ow : TailOpeningWitness_W p c E rho ΔF pt, ∀ X : FGBlock (Fin p.n),
      HonestProposal E rho (fgsaInterface p c)
        ((pt.r + 1) * p.R + kappaF p ΔF) (eraseFG X) →
      (∃ x ∈ rho.honest, ∃ nd H,
        postClock E rho x (p.actionTime (pt.r + 1)) = some nd ∧
        FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st) = some H ∧
        FGBlock.Preceq ow.Q H ∧ (heightView p ow.Q).h_j < ow.e ∧
        (finalityView p H).h_F = (heightView p ow.Q).h_j ∧
        (finalityView p H).F = (heightView p ow.Q).J) →
      FGBlock.Preceq pt.U (Window.derive p p.K_W X).F) :
    ∀ x ∈ rho.honest,
      AcceptsFinalBefore p c E rho x pt.U (kernelDeadlineW p ΔF (pt.r + 1)) := by
  classical
  have hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) := by
    intro j x r a e ha he
    obtain ⟨C, h1, h2, -⟩ := hEmittedSource j x r a e ha he
    exact ⟨C, h1, h2⟩
  obtain ⟨ow⟩ := tail_opening_and_witness p c E rho G ΔF pt hT hnames hOrigin hBatch
    hSOCOVTarget
  have hs := hT.set.base.valid.toScheduleWellFormed
  have hwin := hT.window
  rw [Gen.Pure.Tail_W_def] at hwin
  have nT : pt.r * p.R ≤ (pt.r + 1) * p.R + kappaF p ΔF := by
    rw [Nat.succ_mul]
    omega
  obtain ⟨b, hb⟩ := ktail_window_proposal hT hwin.2.2 nT le_rfl
  obtain ⟨X, rfl, -, hXslot, hcarrier, st, hst, hlook, -⟩ := kmid_opening_carrier p c E rho hs hb
  have hQP := ktail_terminal_path hT ow X hb
  have hQX : FGBlock.Preceq ow.Q X := preceq_trans hQP (kmid_parent_preceq p X)
  have hXh : ow.e + 1 ≤ (heightView p X).h :=
    ow.heightQ ▸ (fgCertificateLaws p).height.h_mono hQX
  have hfinal : FGBlock.Preceq pt.U (Window.derive p p.K_W X).F := by
    by_cases hF : FGBlock.Preceq pt.U (finalityView p ow.Q).F
    · rw [← ktail_kernel_F]
      exact ktail_finalized_propagates p ow.Q X pt.U hQX hF
    · obtain ⟨-, -, -, hUJ, hrc, -⟩ := ktail_terminal_key hT ow hnames hOrigin hF X hb
      rcases ktail_pending_rows hT ow hqc hnames hF (hbatch ow) with hmix | ⟨rows, hrows⟩
      · exact hmixed ow X hb hmix
      · exact preceq_trans hUJ (ktail_terminal_final hT ow X hb hXslot
          (hXslot ▸ hcarrier) st (hXslot ▸ hst) hlook hrc rows hrows)
  obtain ⟨rowsX, hcarX, -⟩ := hcarrier
  have hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot :=
    ktail_slot_gst hT (hXslot ▸ nT)
  have hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (pt.r + 1 + 1) → h ≤ ow.e + 1 := by
    intro j z r a row h T timeout ha hd hp hlt
    exact ktail_rows_through_next hT ow hnames j z r a h
      (Nat.le_of_lt_succ ((kmid_action_strictMono p).lt_iff_lt.mp hlt)) ha
      (ktail_kernel_rowHeight hd hp)
  obtain ⟨hacc⟩ := ktail_acceptPrem_two_W p c E rho G ΔF (pt.r + 1) ow.e pt.w hT.set hT.bound
    hT.input hT.hhor pt.U X ⟨rowsX, hXslot ▸ hcarX⟩ hXslot hgst hfinal hT.high hXh hI3 hStrat
    hEmittedSource hcapBefore hrows
  exact (AcceptBefore_W_def p).mp (fgsa_acceptBefore_W p) c E rho X pt.U _ _ hacc

end AvailableChain.FGSA.Run
end

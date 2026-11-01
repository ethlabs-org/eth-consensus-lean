module
public import AvailableChainFGSAProofs.Proofs.Shared.ReceiptFacts
public import AvailableChainFGSAProofs.Proofs.Finality.Receipt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1286–1305, plan §4: the terminal carrier gives every AcceptPrem_W
field at
any final action q. This is receipt_acceptPrem_W with the kernel record replaced by its
used fields, so the Tail kernel can use q = r+1.
DC: INTENTIONAL local W receipt and same-event guards; Assembly supplies the stated
Foundations and cap inputs. -/
theorem ktail_acceptPrem_W (G ΔF : Time) (q : Nat) (w : HealingWitness)
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (hinput : HealingInput p c E rho w ΔF)
    (hhor : kernelDeadlineW p ΔF q ≤ rho.horizon)
    (y : Nat) (A U X : FGBlock (Fin p.n))
    (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X)
    (hslot : X.slot = q * p.R + kappaF p ΔF)
    (hne : X ≠ .genesis) (hsel : TRowsSelect p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hanchor : (heightView p A).h_j = y) (hfloor : w.M + 1 ≤ y)
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
    (hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (q + 1) → h ≤ y + 1) :
    Nonempty (AcceptPrem_W p c E rho X U (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF q)) := by
  have hdeadline : SA.proposalTime p.toParams X.slot + p.Δ = kernelDeadlineW p ΔF q := by
    rw [hslot, ← fgsa_grid_sa_proposalTime, fgsa_grid_carrier_timeW,
      carrierTimeW_def, kernelDeadlineW_def]
  have hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot := by
    have hFpos := E.Δ_pos.trans_le h.deltaF
    have hmax := le_max_right (p.actionTime q) E.t_GST
    have hhor' := h.horizon.1
    simp only [Time] at hmax hhor' hFpos ⊢
    omega
  have hfinal := receipt_finalized_of_carriage p c E rho hsel ΔF q y A U X hne h
  obtain ⟨rows, hcarrier, _⟩ := h.carrier
  obtain ⟨delivery⟩ := receipt_delivery p c E rho G ΔF hrec X U rows hcarrier hgst
    (hdeadline ▸ hhor) hfinal hI3
  rw [hdeadline] at delivery
  have hXp : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node P s root body rows
  have hheight : y + 1 ≤ (heightView p X).h := by
    rw [← h.freshHeight]
    exact (fgCertificateLaws p).height.h_mono (KitFG.preceq_trans h.path hXp)
  refine ⟨{ base := hrec.base
            faultBound := hrec.fault
            finalized := hfinal
            deliver := delivery
            horizon := hhor
            guards := { finCmp := ?_, jPath := ?_, cap := ?_ } }⟩
  · intro x hx
    dsimp only
    intro hready
    exact receipt_finCmp p c E rho hrec.base hrec.fault hI3
      (delivery.selected x hx).index x X U (delivery.selected x hx).time hfinal hready
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_jPath (hroots := hrec.base.idealization) p c E rho ΔF q y (delivery.selected x
      hx).index x A U X
      (delivery.selected x hx).time h w hinput hx hbound hw.1 hw.2.1
      hslot hanchor hfloor hStrat hEmittedSource
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_cap p c E rho ΔF q y (delivery.selected x hx).index x X
      (delivery.selected x hx).time hx hbound hw.1 hw.2.1 hrec.base.valid
      hheight hcapBefore hrows

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1297–1302, plan §4 (cached-J helper). A cached J of an honest receiver
is on
the terminal carrier path, or the carrier strictly improves h_j. The only input on the
carrier is its high justification height; there is no fresh-row or anchor-height input.
DC: INTENTIONAL W cached pair and action-source ancestry. Stratification and emitted-name
provenance are explicit Foundations inputs; H2 supplies the path. -/
theorem ktail_jPath (hroots : NamedRootCollisionFree p c E rho) (G ΔF : Time) (q i : Nat) (x : V)
    (X : FGBlock (Fin p.n)) (t : Time)
    (hrec : Recovery₂ p c E rho G ΔF)
    (w : HealingWitness) (hinput : HealingInput p c E rho w ΔF)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW p ΔF)
    (hcarrier : ∃ rows, HonestCarrier p c E rho X.slot (eraseFG X) rows)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW p ΔF q)
    (hslot : X.slot = q * p.R + kappaF p ΔF)
    (hJfloor : w.M + 1 ≤ (Window.derive p p.K_W X).h_j)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.J X ∨
      (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j := by
  by_cases hstrict : (storeAt p c E rho i x).fg.h_j < (Window.derive p p.K_W X).h_j
  · exact Or.inr hstrict
  have hM : 1 ≤ w.M := by
    have hmu := hinput.wit.mu_le
    rw [muOf_def] at hmu
    exact (le_max_left 1 _).trans hmu
  obtain ⟨C, hC, _hFC, hCJ, hJ⟩ := (storeBundle_stateBefore E rho i x).cstore.fg.pair.1
  change (storeAt p c E rho i x).fg.h_j = (heightView p C).h_j at hCJ
  have hCpos : (heightView p C).h_j ≠ 0 := by
    simp only [Height] at hCJ hJfloor hstrict ⊢
    omega
  have hJheight := (fgJustificationLaws p).J_height C hCpos
  have hJne : (heightView p C).J ≠ .genesis := by
    intro hg
    rw [hg] at hJheight
    have hz : (heightView p C).h_j = 1 :=
      hJheight.symm.trans (receipt_height_genesis p)
    simp only [Height] at hCJ hJfloor hstrict hz ⊢
    omega
  have hcert : (heightView p C).J ∈ certified p C := by
    rw [certified_def]
    exact ⟨C, KitFG.preceq_refl _, Or.inl rfl⟩
  obtain ⟨u, r, a, hrowBefore, hnames⟩ := hStrat i x C hx hC _ hcert hJne
  obtain ⟨j, hji, hrow⟩ := (HonestRowBefore_def p c E rho i u r a).mp hrowBefore
  obtain ⟨S, hsource, hentry, hJS⟩ := hEmittedSource j u r a _ hrow hnames
  have hJeq : (heightView p C).J = (heightView p S).T_h :=
    rootScope_eq hroots (rootScope_justified (rootScope_store hx hC))
      (rootScope_entry (rootScope_source hrow.1 hsource)) (congrArg Prod.snd hentry)
  have hhigh : high p w S := by
    change w.M + 1 ≤ (heightView p S).h
    have hheight := congrArg Prod.fst hentry
    simp only [Height] at hCJ hJfloor hstrict hJheight hheight ⊢
    omega
  have hnext := (KernelBeforeNextActionW_def p ΔF q).mp
    (kernel_before_next_actionW p ΔF q hbound)
  change Option.map V2.Event.time rho.events[i]? = some t at ht
  obtain ⟨e, he, htime⟩ := Option.map_eq_some_iff.mp ht
  have hi : i < V2.D.Run.idxBefore rho (p.actionTime (q + 1)) :=
    (Gen.V2.Duty.index_lt_idxBefore_iff hrec.base.valid.toScheduleWellFormed he _).mpr
      (htime ▸ hbefore.trans hnext)
  have hrtime := (Gen.V2.Duty.index_lt_idxBefore_iff hrec.base.valid.toScheduleWellFormed
    hrow.2.1 _).mp (hji.trans hi)
  have hrq : r ≤ q :=
    Nat.le_of_lt_succ ((receipt_actionTime_strictMono p).lt_iff_lt.mp hrtime)
  obtain ⟨rows, hcar⟩ := hcarrier
  have hproposal := ((HonestCarrier_def p c E rho _ _ rows).mp hcar).1
  have hFpos := E.Δ_pos.trans_le hrec.deltaF
  have hk := kappaF_ge_two p ΔF (le_of_lt hFpos)
  have hlabel : r * p.R + 2 ≤ X.slot := by
    rw [hslot]
    exact Nat.add_le_add (Nat.mul_le_mul_right p.R hrq) hk
  have hbasepath := hinput.t.h2 u r S X.slot (eraseFG X) hrow.1 hsource hhigh hproposal hlabel
  rw [FGSA.eraseFG_parent] at hbasepath
  have hpath : FGBlock.Preceq S X.parent :=
    eraseFG_preceq_iff.mp hbasepath
  exact Or.inl (hJ.trans hJeq ▸ KitFG.preceq_trans hJS
    (KitFG.preceq_trans hpath (receipt_parent_path p X)))

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Paper 22:1993–1996, plan §4. A high finalized target of the carrier gives a high
carrier justification: K ⪯ F(X) ⪯ J(X), and J(X) has height h_j(X).
DC: SAME certificate order; INTENTIONAL W heights. -/
theorem ktail_hj_floor (w : HealingWitness) (ΔF : Time)
    (hinput : HealingInput p c E rho w ΔF) (K X : FGBlock (Fin p.n))
    (hfinal : FGBlock.Preceq K (Window.derive p p.K_W X).F) (hhigh : high p w K) :
    w.M + 1 ≤ (Window.derive p p.K_W X).h_j := by
  have hM : 1 ≤ w.M := by
    have hmu := hinput.wit.mu_le
    rw [muOf_def] at hmu
    exact (le_max_left 1 _).trans hmu
  have hK : w.M + 1 ≤ (heightView p K).h := hhigh
  have hFJ := (fgCertificateLaws p).finalized_preceq_justified X
  rw [receipt_finality] at hFJ
  have hKJ := KitFG.preceq_trans hfinal hFJ
  rw [← receipt_height_hj]
  by_cases hz : (heightView p X).h_j = 0
  · exfalso
    rw [(fgCertificateLaws p).justified_zero X hz] at hKJ
    rw [KitFG.preceq_genesis.mp hKJ, receipt_height_genesis] at hK
    omega
  · have hh := (fgCertificateLaws p).height.h_mono hKJ
    rw [(fgJustificationLaws p).J_height X hz] at hh
    exact hK.trans hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Paper 22:1286–1305, 1993–2005; plan §4 (two-height receipt adapter). The
terminal
carrier X at slot q·R + κ, with a proved high finalized target K and the source floor
e+1 ≤ ht(X), gives every AcceptPrem_W field at the final action q. The finality key of K
is free: it can be below e. There is no TerminalCarriagePrem_W; finalization is an input,
so the carried and already-finalized cases both use this adapter.
DC: INTENTIONAL local W receipt and same-event guards; Assembly supplies I3, the
stratification, the emitted-source law and the causal cap from Foundations. -/
theorem ktail_acceptPrem_two_W (G ΔF : Time) (q e : Nat) (w : HealingWitness)
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (hinput : HealingInput p c E rho w ΔF)
    (hhor : kernelDeadlineW p ΔF q ≤ rho.horizon) (K X : FGBlock (Fin p.n))
    (hcarrier : ∃ rows, HonestCarrier p c E rho X.slot (eraseFG X) rows)
    (hslot : X.slot = q * p.R + kappaF p ΔF)
    (hgst : E.t_GST ≤ SA.proposalTime p.toParams X.slot)
    (hfinal : FGBlock.Preceq K (Window.derive p p.K_W X).F) (hhigh : high p w K)
    (hsource : e + 1 ≤ (heightView p X).h)
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
    (hrows : ∀ j z r a row h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
      p.actionTime r < p.actionTime (q + 1) → h ≤ e + 1) :
    Nonempty (AcceptPrem_W p c E rho X K (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF q)) := by
  have hdeadline : SA.proposalTime p.toParams X.slot + p.Δ = kernelDeadlineW p ΔF q := by
    rw [hslot, ← fgsa_grid_sa_proposalTime, fgsa_grid_carrier_timeW,
      carrierTimeW_def, kernelDeadlineW_def]
  have hJfloor := ktail_hj_floor p c E rho w ΔF hinput K X hfinal hhigh
  obtain ⟨rows, hcar⟩ := hcarrier
  obtain ⟨delivery⟩ := receipt_delivery p c E rho G ΔF hrec X K rows hcar hgst
    (hdeadline ▸ hhor) hfinal hI3
  rw [hdeadline] at delivery
  refine ⟨{ base := hrec.base
            faultBound := hrec.fault
            finalized := hfinal
            deliver := delivery
            horizon := hhor
            guards := { finCmp := ?_, jPath := ?_, cap := ?_ } }⟩
  · intro x hx
    dsimp only
    intro hready
    exact receipt_finCmp p c E rho hrec.base hrec.fault hI3
      (delivery.selected x hx).index x X K (delivery.selected x hx).time hfinal hready
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact ktail_jPath (hroots := hrec.base.idealization) p c E rho G ΔF q (delivery.selected x
      hx).index x X
      (delivery.selected x hx).time hrec w hinput hx hbound ⟨rows, hcar⟩ hw.1 hw.2.1
      hslot hJfloor hStrat hEmittedSource
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_cap p c E rho ΔF q e (delivery.selected x hx).index x X
      (delivery.selected x hx).time hx hbound hw.1 hw.2.1 hrec.base.valid
      hsource hcapBefore hrows

end AvailableChain.FGSA.Run
end

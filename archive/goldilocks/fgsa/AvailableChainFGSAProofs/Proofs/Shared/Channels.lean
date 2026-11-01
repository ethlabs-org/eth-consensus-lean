module
public import AvailableChainFGSAClaims.Statements.Phases
public import AvailableChainFGSARun.Proofs.EmissionWellFormed
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

/-! Channel equations for P3 F0.8a. Gen.V2.Duty.linked_holder_eq and
Gen.V2.Duty.linked_card_le_of_holders supply identity transport (Q5, S4b-14).
T7 provides `processed_stable`, `fgsa_proposal_receipt`, `fgsa_head_receipt`,
`EmitsRow`, `EmittedRowsNoSlash`, `decodeRowObject`, `honest_emit_wellFormed`,
`contentAgree_run`, and `fgsa_receiptCoverage`; this file does not restate them. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

theorem ancestorClosed_preceq (B : FGBlock (Fin p.n)) :
    AncestorClosed p (fun e => FGBlock.Preceq e B) := by
  constructor
  intro X Y hXY hYB
  exact KitFG.preceq_trans hXY hYB

theorem ancestorClosed_compatible (B : FGBlock (Fin p.n)) :
    AncestorClosed p (fun e => FGBlock.Preceq e B ∨ FGBlock.Preceq B e) := by
  constructor
  intro X Y hXY hY
  rcases hY with hYB | hBY
  · exact Or.inl (KitFG.preceq_trans hXY hYB)
  · exact KitFG.preceq_total_of_common hXY hBY

theorem srcFrame_genesis_preceq (B : FGBlock (Fin p.n)) (c₀ : Nat) :
    c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) → FGBlock.Preceq .genesis B :=
  fun _ => KitFG.genesis_preceq B

theorem srcFrame_genesis_compatible (B : FGBlock (Fin p.n)) (c₀ : Nat) :
    c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) →
      FGBlock.Preceq .genesis B ∨ FGBlock.Preceq B .genesis :=
  fun _ => Or.inl (KitFG.genesis_preceq B)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The store selector is the channel's deepest member of X_r ∩ D(Σ.T). -/
theorem fgSource_eq_jointSource (st : State p.n) :
    FGSA.fgSource p st = jointSource p st := by
  rw [jointSource_def, domainR_def, frameR_def, treeT_def]
  change FGSA.deepest ((FGSA.fullTree p st).filter _) =
    FGSA.deepest ((FGSA.fullTree p st).filter _)
  apply congrArg (FGSA.deepest (n := p.n))
  apply Finset.filter_congr
  intro B _
  rw [sourceCandidates_def, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Finset.mem_filter, List.mem_toFinset]
  cases leaseOf st (eraseFG B) <;> rfl

/-- [ROOT-DIGEST-2 W2; DC NamedBlocks] The proposal maps the exact named parent lookup.
The equation includes the missing-parent case on arbitrary stores. -/
theorem propose_head (st : State p.n) (s : Slot) (hs : s ≠ 0) :
    FGSA.propose p st s = (namedByErase? st (proposerHead p st s)).map (fun P =>
      .proposal (namedProposal p P s 0
        ((proposerVotes st s).filterMap liftHead?) ((proposerSupport st s).filterMap liftHead?)
        (proposalRows p st (proposerHead p st s)))) := by
  rw [proposerHead_def]
  change (if s = 0 then none else _) = _
  exact ite_eq_right hs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The frame reads only the FG store. -/
theorem frameR_congr_fg (st st' : State p.n) (h : st.fg = st'.fg) :
    frameR p st = frameR p st' := by
  rw [frameR_def, frameR_def]
  exact congrArg (KitFG.treeStoreControlsView (heightView p)) h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
D(X) reads the FG store and X, with no vote-pool input. -/
theorem domainR_congr_fg (st st' : State p.n) (X : Finset (FGBlock (Fin p.n)))
    (h : st.fg = st'.fg) : domainR p st X = domainR p st' X := by
  rw [domainR_def, domainR_def, frameR_congr_fg p st st' h]

/-- The canonical channel domain uses the current guarded controls. -/
theorem fgsa_domainR_eq_filtered (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    domainR p st X = filteredFrom p.E p.cfg (controls p st) X := by
  rw [domainR_def, frameR_def,
    ← KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The channel domain equals the fixed-store frame through the height bridge. -/
theorem fgsa_domainR_eq_storeFrame_of_top_retained (st : State p.n)
    (X : Finset (FGBlock (Fin p.n)))
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    domainR p st X = storeFrame p.E p.cfg st.fg X := by
  rw [domainR_def, frameR_def, fgsa_controls_eq_of_top_retained p st hF,
    ← KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
HEAD eligibility uses the live lo relaxation, then score and current slot. -/
theorem eligible_lo_live (st : State p.n) (raw sup : List (GridCO.Wire p.n .root)) (B : Block) :
    FGSA.eligible p st raw sup B =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = B.parent ∧ hOf p.E p.cfg P < (frameR p st).lo) ||
       decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup B) ||
       B.slot == st.slot p) := fgsa_eligible_eq p st raw sup B

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
All five joint selections and the finality triple ignore the own record Λ. -/
theorem jointSelections_record_irrel (st : State p.n) (Λ Λ' : RecordOnce)
    (s : Slot) (raw sup : List (GridCO.Wire p.n .root)) (B : Block) :
    let nd : Node p := ⟨st, Λ⟩
    let nd' : Node p := ⟨st, Λ'⟩
    (FGSA.liveRoot p nd.st, FGSA.eligible p nd.st raw sup B, jointSource p nd.st,
      proposerHead p nd.st s, FGSA.fgHead p nd.st, (FGSA.fgInputs p nd.st).2) =
    (FGSA.liveRoot p nd'.st, FGSA.eligible p nd'.st raw sup B, jointSource p nd'.st,
      proposerHead p nd'.st s, FGSA.fgHead p nd'.st, (FGSA.fgInputs p nd'.st).2) := rfl

/-- Plan repair 6: compatibility retains B in the guarded frame or below its root. -/
private theorem fgsa_shared_retention_of_compatible (st : State p.n) (hI : CStoreInv p st)
    (B : FGBlock (Fin p.n)) (hB : B ∈ st.fg.TF) (hFB : FGBlock.Preceq st.fg.F B)
    (hJB : FGBlock.Preceq st.fg.J B ∨ FGBlock.Preceq B st.fg.J)
    (hc : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      (heightView p U).h < (heightView p W).h →
      FGBlock.Preceq (heightView p U).T_h B ∨ FGBlock.Preceq B (heightView p U).T_h) :
    FGBlock.Preceq B (controls p st).Z ∨ B ∈ domainR p st st.fg.TF := by
  let R := controls p st
  have hL := (fgCertificateLaws p).height
  by_cases hBZ : FGBlock.Preceq B R.Z
  · exact Or.inl hBZ
  right
  have hZB : FGBlock.Preceq R.Z B := by
    change FGBlock.Preceq (if R.rootIsJ then st.fg.J else st.fg.F) B
    cases hr : R.rootIsJ
    · exact hFB
    · rcases hJB with hj | hj
      · exact hj
      · exact (hBZ (by
          change FGBlock.Preceq B (if R.rootIsJ then st.fg.J else st.fg.F)
          rw [hr]; exact hj)).elim
  apply (KitFG.mem_filteredFromView (heightView p) R st.fg.TF B).mpr
  refine ⟨hB, hFB, hZB, ?_⟩
  cases ht : R.contest with
  | true =>
    have ho := KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg ht
    have hx := KitFG.storeFrameView_contest_of_compatible_of_inv p.E (heightView p)
      hL (finalityView p) st.fg hI.fg (fgJustificationLaws p) B hJB hc ho
    obtain ⟨W, hW, _, hh, hn⟩ :=
      KitFG.treeStoreControlsView_contest_witness (heightView p) st.fg ht
    exact ⟨W, hW, hx.2 W hW hh hn, hh ▸ KitFG.Controls.lo_le_H R⟩
  | false =>
    have hlo : R.lo = st.fg.h_max - 1 := by
      unfold Controls.lo
      rw [ht]
      rfl
    by_cases hsmall : st.fg.h_max ≤ 1
    · exact ⟨B, hB, KitFG.preceq_refl B, by
        rw [hlo]; simp only [Height] at *; omega⟩
    obtain ⟨W, hW, hsup⟩ :=
      Finset.exists_mem_eq_sup st.fg.TF ⟨_, hI.fg.gen⟩ (fun W => (heightView p W).h)
    have hw : (heightView p W).h = st.fg.h_max := by
      have hm := hI.fg.hmax
      rw [hsup] at hm
      simp only [Height] at *
      omega
    obtain ⟨U, hU, hu, _⟩ := hL.height_crossing W (st.fg.h_max - 1)
      (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
    rcases hc W hW U hU (by simp only [Height] at *; omega) with heB | hBe
    · refine ⟨B, hB, KitFG.preceq_refl B, ?_⟩
      have hm := hL.h_mono heB
      rw [hL.entry_same_height] at hm
      exact hlo.trans hu.symm ▸ hm
    · exact ⟨W, hW, KitFG.preceq_trans hBe (KitFG.preceq_trans (hL.entry_preceq U) hU),
        by rw [hlo, hw]; simp only [Height] at *; omega⟩

variable {In V : Type} (c : AppCodec In) [DecidableEq V]
    (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The pre-tick and post-clock reads have the same FG frame.
The gate can still change the AC candidates. -/
theorem frame_postClock (E : Generic.Env V) (x : V) (t : Time) (nd nd' : Node p)
    (hpre : preTick E rho x t = some nd) (hpost : postClock E rho x t = some nd') :
    frameR p nd'.st = frameR p nd.st := by
  rw [postClock_def, hpre] at hpost
  have he : (fgsa p c).clock nd t = nd' := Option.some.inj hpost
  rw [← he]
  exact frameR_congr_fg p _ _ (FGSA.clock_fg p nd.st t)

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A holder alone is insufficient: the authentication must be an FG seat. -/
theorem rowSigner_iff_holder (a : RowWire p.n) (x : V) : RowSigner p c rho a x ↔
    (∃ i, a.auth = .seat .fg i) ∧ V2.D.Run.holder rho (ofRow p a).auth = some x := by
  rw [RowSigner_def]
  constructor
  · rintro ⟨i, ha, hx⟩
    refine ⟨⟨i, ha⟩, ?_⟩
    change V2.D.Run.holder rho (ofAuth p a.auth) = some x
    rw [ha]
    exact congrArg some hx
  · rintro ⟨⟨i, ha⟩, hx⟩
    refine ⟨i, ha, ?_⟩
    change V2.D.Run.holder rho (ofAuth p a.auth) = some x at hx
    rw [ha] at hx
    exact Option.some.inj hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every honest row has fixed FG authentication. -/
theorem honestRow_auth (E : Generic.Env V) (h : V2.D.ExecutionValid E rho)
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n}
    (he : HonestRowAt p c E rho j y r a) : ∃ i, a.auth = .seat .fg i := by
  obtain ⟨hy, hj, hem⟩ := he
  have hawake : E.awake y (p.actionTime r) = true := by
    by_contra hn
    have hf : E.awake y (p.actionTime r) = false := Bool.eq_false_iff.mpr hn
    rw [(V2.D.Run.step_tick_eq E rho hj).2,
      (fgsa_tick_asleep (p := p) (c := c) E rho (V2.D.Run.stateBefore E rho j y) y _ hf).1] at hem
    exact List.not_mem_nil hem
  have hv := honest_emit_wellFormed E rho h.toDeliveryWellFormed
    h.toScheduleWellFormed j y _ hj hy hawake (ofRow p a) hem
  change FGSA.wellFormed p (toWire p (ofRow p a)) = true at hv
  rw [toWire_ofRow] at hv
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases hv
  | proposer s => cases hv
  | seat l i => cases l with
    | head s => cases hv
    | fg => exact ⟨i, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. An honest signed row is released before its direct or carried handler call.
The time inequality can be non-strict; tick-before-delivery makes the index strict. -/
theorem emit_lt_handles (E : Generic.Env V) (h : V2.D.ExecutionValid E rho)
    {j k : Nat} {y x : V} {r : Nat} {a : RowWire p.n}
    (he : HonestRowAt p c E rho j y r a) (hh : HandlesRowAt p c E rho k x a) : j < k := by
  obtain ⟨seat, ha⟩ := honestRow_auth p c rho E h he
  obtain ⟨hy, hj, hem⟩ := he
  obtain ⟨u, envelope, hk, hhandle⟩ := hh
  rcases a with ⟨auth, body⟩
  dsimp only at ha
  subst auth
  have hrow := (fgsa_emitsAt_row E rho j y _ hj seat body).mp hem
  have hholder : V2.D.Run.holder rho (ofRow p ⟨.seat .fg seat, body⟩).auth = some y :=
    congrArg some hrow.2.1
  have horigin : ∃ u', u' ≤ u ∧
      V2.D.Run.emits E rho y (ofRow p ⟨.seat .fg seat, body⟩) u' := by
    rcases (fgsaHooks p c).handles_carries _ envelope _ hhandle with heq | hc
    · subst envelope
      exact h.unforgeable x _ u ⟨k, hk⟩ y hy hholder
    · exact h.carried x envelope u ⟨k, hk⟩ _ hc y hy hholder
  obtain ⟨u', hle, j', hj', hem'⟩ := horigin
  have hjj' := fgsa_emitOnceUnder E rho h seat (hrow.2.1.symm ▸ hy)
    (.row body) j j' (p.actionTime r) u'
    (hrow.2.1.symm ▸ hj) (hrow.2.1.symm ▸ hj') hem hem'
  subst j'
  have htime := (V2.Event.tick.inj (Option.some.inj (hj.symm.trans hj'))).2
  exact V2.D.Engine.tick_index_lt_delivery E rho h.toScheduleWellFormed hj hk (htime ▸ hle)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 §8.7 F2.2; bp02 §§3.1–3.5. Class B channel assembly.
DC counterparts: ChainState/FGRootWitness.lean:327,493 and
Execution/WeakGenesisGSTZeroActionSources.lean:106. The all-entry FJ bundle
and G1 differ intentionally (TS/spec/fgsa-protocol.tex:2557–2571;
TS/log.md:1475). No source existence or Clean premise is used. -/
theorem fgsa_cpPrefix_of_srcFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho)
    (hr : NamedRootCollisionFree p c E rho) (hstrat : RStrat p c E rho) :
    CPPrefix p c E rho := by
  intro i x B hx hB hrows
  let st := storeAt p c E rho i x
  have hc : ∀ W ∈ st.fg.TF, ∀ e ∈ certified p W, FGBlock.Preceq e B := by
    intro W hW e he
    by_cases hg : e = .genesis
    · subst e; exact KitFG.genesis_preceq B
    obtain ⟨y, r, a, ha, hn⟩ := hstrat i x W hx hW e he hg
    obtain ⟨X, hXB, hname⟩ := hrows y r a _ ha hn
    have heX : X = e := rootScope_eq hr (rootScope_ancestor hB hXB)
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq he))
      (congrArg Prod.snd hname)
    exact heX ▸ hXB
  have hI := (hstore i x hx).1.fg
  obtain ⟨K, hK, hKF⟩ := hI.Fcar
  have hF : FGBlock.Preceq st.fg.F B :=
    hc K hK _ ⟨K, KitFG.preceq_refl K, Or.inr (Or.inl hKF.symm)⟩
  obtain ⟨D, hD, _, _, hDJ⟩ := hI.pair.1
  have hJ : FGBlock.Preceq st.fg.J B :=
    hc D hD _ ⟨D, KitFG.preceq_refl D, Or.inl hDJ⟩
  have hZ : FGBlock.Preceq (controls p st).Z B := by
    change FGBlock.Preceq (if (controls p st).rootIsJ then
      st.fg.J else st.fg.F) B
    split <;> assumption
  have hinv := (hstore i x hx).1.fg
  have hcert := (fgCertificateLaws p).height
  have hjust := fgJustificationLaws p
  rw [heightView_eq_simplex p] at hinv hcert hjust
  have hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      hOf p.E p.cfg U < hOf p.E p.cfg W → FGBlock.Preceq (derive p.E p.cfg U).T_h B := by
    intro W hW U hU hlt
    apply hc W hW
    simp only [certified_def, heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def]
    exact ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩
  have hn := KitFG.storeFrameView_noContest_of_crossed_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv
        hjust (by
    intro W hW U hU hlt
    exact KitFG.preceq_total_of_common hJ (hcross W hW U hU hlt))
  have hlo := KitFG.storeFrameView_height_of_crossed_prefix_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv B hn hcross
  have hcontrols : R_at p c E rho i x = controls p st := rfl
  refine ⟨hc, hF, hJ, hZ, ?_, ?_⟩
  · rw [hcontrols]
    apply Bool.eq_false_iff.mpr
    intro ht
    have ho := KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg ht
    rw [heightView_eq_simplex p, hn] at ho
    contradiction
  · rw [hcontrols]
    exact (fgsa_controls_lo_le_store p st).trans (by
      simpa only [KitFG.storeControls_of_bridge p.E p.cfg (heightView p)
        (heightView_bridge p), heightView_eq_simplex p] using hlo)

theorem cpPrefix_of_srcFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hr : NamedRootCollisionFree p c E rho) (hstrat : RStrat p c E rho) :
    CPPrefix p c E rho := by
  have _hlegacyFrame := hframe
  exact fgsa_cpPrefix_of_srcFrame p c E rho hstore hr hstrat


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 §8.7 F2.2; bp02 §3.4 and P3 App. A.3 CPCompat. Class B.
DC counterpart: ChainState/FGRootWitness.lean:548 concludes root
compatibility only. Retention and EVERY contest witness are intentional FJ
extensions (TS/spec/fgsa-protocol.tex:2557–2571; TS/log.md:1475). G1 is explicit. -/
theorem fgsa_cpCompat_of_srcFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) : CPCompat p c E rho := by
  simp only [CPCompat_def, heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
  intro i x B hx hrows
  have hs := hsrc (fun e => FGBlock.Preceq e B ∨ FGBlock.Preceq B e) 0
    (ancestorClosed_compatible p B) (by
      simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using srcFrame_genesis_compatible p B 0) i x hx
    (fun y r a e ha hn _ => hrows y r a e ha (by
      simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
        using hn))
  have hc : ∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      FGBlock.Preceq e B ∨ FGBlock.Preceq B e :=
    fun W hW e he => hs.1 W hW e he (Nat.zero_le _)
  have hF := hs.2.1 (Nat.zero_le _)
  have hJ := hs.2.2.1 (Nat.zero_le _)
  let st := storeAt p c E rho i x
  have hinv := (hstore i x hx).1.fg
  have hcert := (fgCertificateLaws p).height
  have hjust := fgJustificationLaws p
  rw [heightView_eq_simplex p] at hinv hcert hjust
  have hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      hOf p.E p.cfg U < hOf p.E p.cfg W →
      FGBlock.Preceq (derive p.E p.cfg U).T_h B ∨ FGBlock.Preceq B (derive p.E p.cfg U).T_h := by
    intro W hW U hU hlt
    apply hc W hW
    simp only [certified_def, heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def]
    exact ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩
  have hcontrols : R_at p c E rho i x = controls p st := rfl
  refine ⟨hc, hF, hJ, ?_, ?_⟩
  · intro hB hFB
    have hr := fgsa_shared_retention_of_compatible p st (hstore i x hx).1 B hB hFB
      hJ (by simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def,
        KitFG.heightOf_def, hOf] using hcross)
    exact hr
  · rw [hcontrols]
    intro ht
    have ho := KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg ht
    rw [heightView_eq_simplex p] at ho
    exact KitFG.storeFrameView_contest_of_compatible_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv
        hjust B hJ hcross ho


theorem cpCompat_of_srcFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) : CPCompat p c E rho := by
  have _hlegacyFrame := hframe
  exact fgsa_cpCompat_of_srcFrame p c E rho hstore hsrc


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. The compatibility proof consumes names only for scoped entries. -/
theorem fgsa_cpCompat_of_scopedFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho)
    (hstrat : RStrat p c E rho) : ∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
    HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
    RootBlockInRun p c E rho (eraseFG e) →
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) ∧
  (let st := storeAt p c E rho i x
   let R := R_at p c E rho i x
   (FGBlock.Preceq R.F B ∨ FGBlock.Preceq B R.F) ∧
   (FGBlock.Preceq R.J B ∨ FGBlock.Preceq B R.J) ∧
   (B ∈ st.fg.TF → FGBlock.Preceq R.F B →
     FGBlock.Preceq B R.Z ∨ B ∈ domainR p st st.fg.TF) ∧
   (R.contest = true → FGBlock.Preceq B R.J ∧
     ∀ W ∈ st.fg.TF, (heightView p W).h = R.H → ¬ FGBlock.Preceq R.J W →
       FGBlock.Preceq B W)) := by
  simp only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
  intro i x B hx hrows
  have hs := srcFrameAbove_scoped p c E rho hstore hstrat (fun e => FGBlock.Preceq e B ∨
    FGBlock.Preceq B e) 0
    (ancestorClosed_compatible p B) (by
      simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using srcFrame_genesis_compatible p B 0) i x hx
    (fun y r a e ha hn heScope _ => hrows y r a e ha (by
      simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
        using hn) heScope)
  have hc : ∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      FGBlock.Preceq e B ∨ FGBlock.Preceq B e :=
    fun W hW e he => hs.1 W hW e he (Nat.zero_le _)
  have hF := hs.2.1 (Nat.zero_le _)
  have hJ := hs.2.2.1 (Nat.zero_le _)
  let st := storeAt p c E rho i x
  have hinv := (hstore i x hx).1.fg
  have hcert := (fgCertificateLaws p).height
  have hjust := fgJustificationLaws p
  rw [heightView_eq_simplex p] at hinv hcert hjust
  have hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      hOf p.E p.cfg U < hOf p.E p.cfg W →
      FGBlock.Preceq (derive p.E p.cfg U).T_h B ∨ FGBlock.Preceq B (derive p.E p.cfg U).T_h := by
    intro W hW U hU hlt
    apply hc W hW
    simp only [certified_def, heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def]
    exact ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩
  have hcontrols : R_at p c E rho i x = controls p st := rfl
  refine ⟨hc, hF, hJ, ?_, ?_⟩
  · intro hB hFB
    have hr := fgsa_shared_retention_of_compatible p st (hstore i x hx).1 B hB hFB
      hJ (by simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def,
        KitFG.heightOf_def, hOf] using hcross)
    exact hr
  · rw [hcontrols]
    intro ht
    have ho := KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg ht
    rw [heightView_eq_simplex p] at ho
    exact KitFG.storeFrameView_contest_of_compatible_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv
        hjust B hJ hcross ho

theorem cpCompat_of_scopedFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hstrat : RStrat p c E rho) : ∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
    HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
    RootBlockInRun p c E rho (eraseFG e) →
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) ∧
  (let st := storeAt p c E rho i x
   let R := R_at p c E rho i x
   (FGBlock.Preceq R.F B ∨ FGBlock.Preceq B R.F) ∧
   (FGBlock.Preceq R.J B ∨ FGBlock.Preceq B R.J) ∧
   (B ∈ st.fg.TF → FGBlock.Preceq R.F B →
     FGBlock.Preceq B R.Z ∨ B ∈ domainR p st st.fg.TF) ∧
   (R.contest = true → FGBlock.Preceq B R.J ∧
     ∀ W ∈ st.fg.TF, (heightView p W).h = R.H → ¬ FGBlock.Preceq R.J W →
       FGBlock.Preceq B W)) := by
  have _hlegacyFrame := hframe
  exact fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan item 4. DC: INTENTIONAL exact retained entry, then prefix coverage.
This is the pure window_finality_of_cover adapter; genesis is excluded. -/
theorem pendingFold_consume_W (p : Params) (y : Nat) (U X : FGBlock (Fin p.n))
    (h : PendingFold_W p y U X) :
    FGBlock.Preceq U (Window.derive p p.K_W X).F ∧
      y ≤ (Window.derive p p.K_W X).h_F := by
  rcases h with ⟨child, e, he, hj, hX, Q, hQ, cover⟩
  cases X with
  | genesis => exact (child rfl).elim
  | node P s root body rows =>
      have hc : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ row ∈ rows,
          row.signer = i ∧ row.finality_pair = some ⟨e.j, e.X.root⟩ := by
        simpa only [FinRowNames_def, hj, hX, FGBlock.rows] using cover
      simpa only [hj, hX] using
        Window.window_finality_of_cover p p.K_W p.kWLarge P s root body rows e he Q hQ hc

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. DC: INTENTIONAL separate prior coverage, extended by W monotonicity. -/
theorem covered_parent_W (p : Params) (y : Nat) (U X : FGBlock (Fin p.n))
    (h : Window.CoveredW p X.parent y U) : Window.CoveredW p X y U := by
  have path : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node P s root body rows => exact KitFG.preceq_parent_node P s root body rows
  exact ⟨h.1.trans (Window.window_hF_mono p p.K_W p.kWLarge _ _ path),
    KitFG.preceq_trans h.2 (Window.window_F_mono p p.K_W p.kWLarge _ _ path)⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan item 3 optional corollary. DC: INTENTIONAL prior coverage or a ready key.
The complex batch producer remains a contract supplied as hbatch. -/
theorem finalityBatch_covered_W (p : Params) (ΔF : Time)
    (hbatch : FinalityBatchCoverage_W p ΔF) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q y : Nat) (U X : FGBlock (Fin p.n)) (child : X ≠ .genesis)
    (h : FinalityBatchPrem_W p c E rho ΔF q y U X) : Window.CoveredW p X y U := by
  rcases hbatch c E rho q y U X h with prior | ready
  · exact covered_parent_W p y U X prior
  · have hc := pendingFold_consume_W p y U X ⟨child, ready⟩
    exact ⟨hc.2, hc.1⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan item 5. DC: INTENTIONAL strict β+Δ acceptance with the same receipt.
AcceptBefore_W is supplied by fgsa_acceptBefore_W in Clean/AcceptBefore. -/
theorem finalizePending_of_acceptBefore_W (p : Params) (ΔF : Time)
    (haccept : AcceptBefore_W p) : FinalizePending_W p ΔF := by
  intro V _ _ In c E rho q y U X _slot h
  exact haccept c E rho X U _ _
    ⟨h.base, h.faultBound, (pendingFold_consume_W p y U X h.fold).1,
      h.deliver, h.guards, h.horizon⟩

end AvailableChain.FGSA.Run
end

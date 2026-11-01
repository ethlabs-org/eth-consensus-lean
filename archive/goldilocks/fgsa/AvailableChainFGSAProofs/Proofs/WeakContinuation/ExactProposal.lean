module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Proposal
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.ExactReceipts

public section

/-! WC J3, plan §6.10; DC exact proposal adoption.
The comparison uses the finite suffix pivot and the original proposal metadata. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

omit [Fintype V] in
/-- WC J3, plan §6.10; DC strict relay: both comparison windows are after GST. -/
private theorem wc_proposalWindows (hseed : WCSeed p c E rho w iStar)
    (s : Slot) (hstart : w.u + 2 ≤ s)
    (hgate : SA.gateTime p.toParams s ≤ rho.horizon) :
    E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ ∧
      SA.voteTime p.toParams s ≤ rho.horizon := by
  have hd := p.deltaPos
  have hcast : (w.u : Time) + 2 ≤ (s : Time) := by exact_mod_cast hstart
  constructor
  · refine hseed.firstVoteAfterGST.trans ?_
    change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (s : Time) - p.Δ
    push_cast
    nlinarith
  · refine le_trans ?_ hgate
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith

/-- WC J3, plan §6.10; DC score suffix: produce the retained cone from the pivot.
Both support counts come from the previous honest HEAD batch. -/
theorem wc_retainedReads
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.RestartsAtWakes E rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedReceiptRootCollisionFree p c E rho) (hmono : RMonoAll p c E rho)
    (hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
    (hseed : WCSeed p c E rho w iStar) (pt : PtSP) (D0 : Block)
    (hstart : w.u + 2 ≤ pt.s)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hpivot : WCProposalPivot p c E rho w iStar pt D0) :
    ∃ (ip : Nat) (N : NamedProposal p.n) (D : FGBlock (Fin p.n)), N.erase = pt.P ∧
      rho.events[ip]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
        (SA.proposalTime p.toParams pt.s)) ∧
      (⟨.seat (.prop pt.s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip ∧
      ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams pt.s)) →
        joinedAt p E rho y pt.s (SA.voteTime p.toParams pt.s) →
        ∃ Kc, RetainedReadPremises p
          (clock p (rho.stateBefore E ip
            (V2.D.proposerOf rho (fgsaInterface p c) pt.s)).st
            (SA.proposalTime p.toParams pt.s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams pt.s))
          pt.s D N.erase Kc := by
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨ip, N, hN, hip, hem, _⟩ := proposal_read_named p c E rho hs hprop
  let x := V2.D.proposerOf rho (fgsaInterface p c) pt.s
  let src := clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams pt.s)
  have hduty : WCDutyInput p c E rho ip x (.proposal pt.s) src :=
    ⟨(List.getElem?_eq_some_iff.mp hip).1, (by
      have hm := hem
      rw [(rho.step_tick_eq E hip).2] at hm
      exact ((fgsa_emits_proposal E rho _ _ _ pt.s _).mp hm).2.2.2.1), ⟨_, hip, Or.inl
        ⟨pt.s, rfl, rfl, rfl⟩⟩⟩
  obtain ⟨hf, hap⟩ := hpivot.proposalFrame ip x src hduty rfl
  obtain ⟨D, hDsrc, hD, _⟩ := hpivot.proposalPath ip x src hduty rfl
  have hs2 : 2 ≤ pt.s := by simp only [Slot] at hstart ⊢; omega
  obtain ⟨q, hsq⟩ : ∃ q : Slot, pt.s = q + 2 :=
    ⟨pt.s - 2, by simp only [Slot] at hs2 ⊢; omega⟩
  have hprevLabel : pt.s - 1 = q + 1 := by rw [hsq]; simp only [Slot]; omega
  have huq : w.u ≤ q := by simp only [Slot] at hstart hsq ⊢; omega
  have hGST : E.t_GST ≤ SA.voteTime p.toParams (q + 1) := by
    refine hseed.firstVoteAfterGST.trans ?_
    change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * ((q + 1 : Nat) : Time) + p.Δ
    have hc : (w.u : Time) ≤ q := Nat.cast_le.mpr huq
    push_cast
    nlinarith [p.deltaPos]
  obtain ⟨hGSTp, hhor⟩ := wc_proposalWindows hseed pt.s hstart hgate
  have hhorQ : SA.voteTime p.toParams (q + 2) ≤ rho.horizon := hsq ▸ hhor
  have hpartPrev := hpart (SA.voteTime p.toParams (q + 1)) (by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
    have hh := Int.ofNat_le.mpr huq
    push_cast
    nlinarith [p.deltaPos]) (by
    refine le_trans ?_ hhorQ
    change 4 * p.Δ * ((q + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * ((q + 2 : Nat) : Time) + p.Δ
    push_cast
    nlinarith [p.deltaPos])
  have hprev : ∀ y ∈ rho.honest,
      joinedAt p E rho y (q + 1) (SA.voteTime p.toParams (q + 1)) → ∃ k, WCHeadRead p c E
        rho k y (q + 1) D0 := by
    simpa only [hprevLabel] using hpivot.previousHeads
  have hcounts := wc_proposalCounts hvalid hnr hdelta hcstar hroots hmono hcumul ΔF hsync q D0
    hGST hpartPrev hhorQ hprev hprop.1.2
    (by simpa only [← hsq] using hip)
    (by simpa only [hsq] using wc_duty_joinedAt hvalid hip rfl (Or.inl rfl) hduty.joined)
    (by simpa only [← hsq] using hf)
  have hcountsS : ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes src pt.s) < 2 * RetainedWalk.ss src pt.s L ∧
      ∀ B, Block.compatible L B = false →
        RetainedWalk.ss src pt.s B < RetainedWalk.ss src pt.s L := by
    simpa only [← hsq] using hcounts
  have hfloor : (controls p src).lo ≤ (heightView p D).h := by
    obtain ⟨D', hD', hlo⟩ := hf.floor
    have he : D' = D := eraseFG_injective (hD'.trans hD.symm)
    exact he ▸ hlo
  have hprior : ∀ L, Block.Preceq L D0 → RetainedPriorSupport p src pt.s L := by
    intro L hL
    obtain ⟨hmaj, hrival⟩ := hcountsS L hL
    exact ⟨block_compatible_of_common hf.rootBelow hL,
      ⟨D, (Finset.mem_filter.mp hDsrc).1, hD ▸ hL, hfloor⟩, hmaj, hrival⟩
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.proposalTime p.toParams pt.s - p.Δ) (SA.voteTime p.toParams pt.s)
    hsync (fgsaDelay_nonrow E.Δ ΔF) hGSTp (by
      rw [hdelta]
      change 4 * p.Δ * (pt.s : Time) - p.Δ + p.Δ ≤
        4 * p.Δ * (pt.s : Time) + p.Δ
      nlinarith [p.deltaPos]) hhor
  refine ⟨ip, N, D, hN, hip, hem, ?_⟩
  apply fgsa_retainedReads_H17_joined E rho hvalid pt.s hprop.1.2 hip rfl N hem D
    ?_ ?_ hroots
  · intro y hy ih hih hJ
    let dst := clock p (storeAt p c E rho ih y) (SA.voteTime p.toParams pt.s)
    have hdy : WCDutyInput p c E rho ih y (.head pt.s) dst :=
      ⟨(List.getElem?_eq_some_iff.mp hih).1,
        fgsa_head_joined_of_joinedAt E rho hs hih hJ, ⟨_, hih, Or.inr (Or.inl ⟨pt.s, rfl,
        rfl, rfl⟩)⟩⟩
    obtain ⟨hfy, hay⟩ := hpivot.headFrame ih y dst hy hdy
    obtain ⟨D', hDy, hD', _⟩ := hpivot.headPath ih y dst hy hdy
    have heD : D' = D := eraseFG_injective (hD'.trans hD.symm)
    have hfloorY : (controls p dst).lo ≤ (heightView p D).h := by
      obtain ⟨Dy, hDy', hlo⟩ := hfy.floor
      exact eraseFG_injective (hDy'.trans hD.symm) ▸ hlo
    have hcs := wc_headCounts hvalid hnr hdelta hcstar hroots hmono hcumul ΔF hsync q D0
      hGST hpartPrev hhorQ hprev hy (by simpa only [hsq] using hih)
      (by simpa only [hsq] using hJ) (by simpa only [← hsq] using hfy)
    have hcsS : ∀ L, Block.Preceq L D0 → RetainedTargetScores p dst pt.s L := by
      intro L hL
      simpa only [← hsq] using (hcs L hL).1
    refine ⟨Or.inr (hprior _ hap), Or.inr (Or.inl (hprior _ hay)),
      Or.inr (hprior _ (hD ▸ block_preceq_refl D0)), hfloor, hfloorY, ?_⟩
    intro L hL _
    rcases hL with rfl | rfl
    · exact hcsS _ hf.rootBelow
    · exact hcsS _ (hD ▸ block_preceq_refl D0)
  · intro y hy ih hih hJ
    let dst := clock p (storeAt p c E rho ih y) (SA.voteTime p.toParams pt.s)
    have hdy : WCDutyInput p c E rho ih y (.head pt.s) dst :=
      ⟨(List.getElem?_eq_some_iff.mp hih).1,
        fgsa_head_joined_of_joinedAt E rho hs hih hJ,
        ⟨_, hih, Or.inr (Or.inl ⟨pt.s, rfl, rfl, rfl⟩)⟩⟩
    have hfd := (hpivot.headFrame ih y dst hy hdy).1
    have hFN : Block.Preceq (F_at p c E rho ih y) N.erase := by
      have hpar : Block.Preceq pt.P.parent pt.P := by
        cases pt.P <;> first | exact block_preceq_refl _ |
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
      have hb := block_preceq_trans hfd.finalRoot
        (block_preceq_trans hfd.rootBelow (block_preceq_trans hpivot.parent hpar))
      change Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) N.erase
      simpa only [dst, clock_fg, hN] using hb
    exact fgsa_target_service_of_proposal E rho pt.s N _ _ y
      (wc_emitted_proposal_service hvalid hdelta hsync hmono hprop.1.2 hy hip hih hem hJ
        (hGSTp.trans (sub_le_self _ p.deltaPos.le)) hFN)

/-- WC J3, plan §6.10; DC exact proposal: the retained suffix and endpoint give P.
The proof matches the reviewed exact-adoption Statement. -/
theorem wc_exactProposal (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCExactProposalStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot hadmission
  obtain ⟨ip, N, Dfg, hN, hip, hem, hreads⟩ := wc_retainedReads hvalid hnr hdelta
    hcstar hroots hmono hcumul ΔF hsync hpart hseed pt D hstart hprop hgate hpivot
  obtain ⟨hGST, hhor⟩ := wc_proposalWindows hseed pt.s hstart hgate
  have htime : SA.proposalTime p.toParams pt.s - p.Δ + E.Δ ≤
      SA.proposalTime p.toParams pt.s := by rw [hdelta]; exact le_of_eq (sub_add_cancel _ _)
  have hpv : SA.proposalTime p.toParams pt.s ≤ SA.voteTime p.toParams pt.s := by
    change 4 * p.Δ * (pt.s : Time) ≤ 4 * p.Δ * (pt.s : Time) + p.Δ
    linarith [p.deltaPos]
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.proposalTime p.toParams pt.s - p.Δ) (SA.proposalTime p.toParams pt.s)
    hsync (fgsaDelay_nonrow E.Δ ΔF) hGST htime (hpv.trans hhor)
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o)
    (SA.proposalTime p.toParams pt.s - p.Δ) (SA.voteTime p.toParams pt.s)
    hsync (fgsaDelay_nonrow E.Δ ΔF) hGST (htime.trans hpv) hhor
  have hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams pt.s)) →
      joinedAt p E rho y pt.s (SA.voteTime p.toParams pt.s) →
      RetainedServiceScope E rho ip ih (V2.D.proposerOf rho (fgsaInterface p c) pt.s) y pt.s N := by
    intro y hy ih hih hJ
    have hm := hem
    rw [(rho.step_tick_eq E hip).2] at hm
    have hp := (fgsa_emits_proposal E rho _ _ _ pt.s _).mp hm
    have hX := wc_duty_joinedAt hvalid hip rfl (Or.inl rfl) hp.2.2.2.1
    obtain ⟨Kc, hr⟩ := hreads y hy ih hih hJ
    have hFN : Block.Preceq (F_at p c E rho ih y) N.erase := by
      have ht := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y)
        (SA.voteTime p.toParams pt.s)
      have hb := block_preceq_trans (F_preceq_liveRoot p _ ht) hr.target_parent
      have hpar : Block.Preceq N.erase.parent N.erase := by
        cases N.erase <;> first | exact block_preceq_refl _ |
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
      change Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) N.erase
      simpa only [clock_fg, storeAt] using block_preceq_trans hb hpar
    refine ⟨wc_emitted_proposal_service hvalid hdelta hsync hmono hprop.1.2 hy hip hih hem hJ
      (hGST.trans (sub_le_self _ p.deltaPos.le)) hFN, ?_⟩
    intro C hgeom
    have hspos : 0 < pt.s := hprop.1.1
    have hsucc : pt.s - 1 + 1 = pt.s := by simp only [Slot] at hspos ⊢; omega
    have hGSTprev : E.t_GST ≤ SA.voteTime p.toParams (pt.s - 1) := by
      apply hseed.firstVoteAfterGST.trans
      have hc : w.u + 1 ≤ pt.s - 1 := by simp only [Slot] at hstart ⊢; omega
      change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((pt.s - 1 : Nat) : Int) + p.Δ
      have hh := Int.ofNat_le.mpr hc
      nlinarith [p.deltaPos]
    have hScope := wc_retained_score_scope hvalid hnr hdelta hsync hmono
      (ip := ip) (ih := ih) (r := pt.s - 1) hprop.1.2 hy
      (by simpa only [hsucc] using hip) (by simpa only [hsucc] using hih)
      (by simpa only [hsucc] using hX) (by simpa only [hsucc] using hJ)
      hGSTprev C (by simpa only [storeAt, hsucc] using hgeom)
    simpa only [hsucc] using hScope
  have hg := fgsa_retainedExactHead_geometry_on_run_on E rho hvalid pt.s
    hprop.1.2 hip rfl N hem Dfg hreads hScopes hroots
  simpa only [hN] using
    exactService_head_of_retained_proposal_on E rho hvalid hdelta pt.s hip N hem Dfg hg hhor

omit [Fintype V] in
/-- WC J3, plan §6.10; DC named receipt: decode preserves the complete signed body. -/
private theorem wc_blockObject {o : Obj p} {B : Block} (h : blockOf? p o = some B) :
    ∃ s N, o = ofWire p ⟨.proposer s, .proposal N⟩ ∧ N.erase = B := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i s N
    refine ⟨s, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- WC J3, plan §6.10; DC full admission: retain the exact emitted named proposal.
The delivery and stamp are strict before the HEAD tick, also for sleeping readers. -/
theorem wc_proposalAdmission (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCProposalAdmissionStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX
    hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hseed pt D hstart hprop hgate hpivot x hx hJ
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨ip, N, hN, hip, hem, _⟩ := proposal_read_named p c E rho hs hprop
  obtain ⟨hGST, hhor⟩ := wc_proposalWindows hseed pt.s hstart hgate
  have hGSTp : E.t_GST ≤ SA.proposalTime p.toParams pt.s :=
    hGST.trans (sub_le_self _ p.deltaPos.le)
  have hvt : ((4 * pt.s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams pt.s := by
    push_cast
    change (4 * (pt.s : Time) + 1) * p.Δ = 4 * p.Δ * (pt.s : Time) + p.Δ
    ring
  obtain ⟨ih, hih, _⟩ := fgsa_tick_total E rho hs hdelta x hx (4 * pt.s + 1)
    (hvt ▸ hhor) (hvt ▸ hJ.1)
  rw [hvt] at hih
  let st := clock p (storeAt p c E rho ih x) (SA.voteTime p.toParams pt.s)
  have hduty : WCDutyInput p c E rho ih x (.head pt.s) st :=
    ⟨(List.getElem?_eq_some_iff.mp hih).1,
      fgsa_head_joined_of_joinedAt E rho hs hih hJ, ⟨_, hih, Or.inr (Or.inl ⟨pt.s, rfl, rfl, rfl⟩)⟩⟩
  have hF := block_preceq_trans (hpivot.headFrame ih x st hx hduty).1.finalRoot
    (block_preceq_trans (hpivot.headFrame ih x st hx hduty).1.rootBelow hpivot.parent)
  have hpar : Block.Preceq pt.P.parent pt.P := by
    cases pt.P <;> first | exact block_preceq_refl _ |
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
  have hFN : Block.Preceq (F_at p c E rho ih x) N.erase := by
    change Block.Preceq (eraseFG (storeAt p c E rho ih x).fg.F) N.erase
    simpa only [st, clock_fg, hN] using block_preceq_trans hF hpar
  obtain ⟨hService⟩ := wc_emitted_proposal_service hvalid hdelta hsync hmono hprop.1.2 hx
    hip hih hem hJ hGSTp hFN
  obtain ⟨Y, hY, hYB⟩ := hService.proposal hs hx hroots
  let k := V2.D.Run.idxBefore rho (SA.voteTime p.toParams pt.s)
  have hstored : N.erase ∈ (storeAt p c E rho k x).base.blocks := by
    apply ((cstoreInv_stateBefore E rho k x).baseTree _).mpr
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact ⟨Y, hY, hYB⟩
  have hscope : NamedProposalInRun p c E rho N := by
    apply proposal_processed_in_scope E rho hroots hx k pt.s N
      (namedReceiptScope_emitted E rho hprop.1.2 ⟨ip, hip, hem⟩ rfl (named_preceq_refl N))
    have hh := hService.processed hs hx (by change ¬ False; exact not_false)
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hh
    exact hh
  have hmEmit := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hmEmit
  have hp := (fgsa_emits_proposal E rho _ _ _ pt.s _).mp hmEmit
  have hslot := (fgsa_scoreRun_proposal_pools p _ pt.s _ N hp.2.2.2.2).1
  have hne : N.erase ≠ .genesis := by
    intro he
    have hzero : N.erase.slot = 0 := he ▸ rfl
    simp only [Slot] at hslot hstart hzero
    omega
  obtain ⟨j, hj, t, o', ho', ha⟩ :=
    fgsa_block_accepted_origin E rho k x N.erase hne hstored
  obtain ⟨s', M, rfl, hM⟩ := wc_blockObject ho'
  have hdecode : (toWire p (ofWire p ⟨.proposer s', .proposal M⟩)).decode =
      some (.block s' M) := by rw [toWire_ofWire]; rfl
  obtain ⟨parent, he, hh⟩ := ha.1
  have heparent := proposal_handlesS_direct _ parent _ s' M hdecode hh
  subst parent
  have hMscope := proposal_handle_in_scope E rho _ s' M rfl j x t ha.1
  have hMN := namedScope_erase_injective E rho (hroots.toNamedRootCollisionFree E rho)
        hMscope hscope hM
  subst M
  have hwf := hvalid.wire j x _ t he
  change wellFormed p (toWire p (ofWire p ⟨.proposer s', .proposal N⟩)) = true at hwf
  rw [toWire_ofWire] at hwf
  change (N.erase != .genesis && s' == N.erase.slot && _ && _ && _ && _ && _) = true at hwf
  have h6 := (Bool.and_eq_true_iff.mp hwf).1
  have h5 := (Bool.and_eq_true_iff.mp h6).1
  have h4 := (Bool.and_eq_true_iff.mp h5).1
  have h3 := (Bool.and_eq_true_iff.mp h4).1
  have h2 := (Bool.and_eq_true_iff.mp h3).1
  have hlabel : s' = pt.s :=
    (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h2).2).trans hslot
  subst s'
  have hbefore := (Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hj
  refine ⟨⟨N, j, _, t, rfl, hN, he, hbefore, Or.inl ha,
    ⟨_, ip, rfl, hip, hem⟩, ?_⟩⟩
  intro i st' hd
  obtain ⟨hi, rfl⟩ := wc_headInput hd
  have hki : k ≤ i := by
    by_contra hn
    have hc := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp (Nat.lt_of_not_ge hn)
    exact lt_irrefl _ hc
  have hJ' := wc_duty_joinedAt hvalid hi rfl (Or.inr rfl) hd.joined
  have hspos : 0 < pt.s := hprop.1.1
  have hsucc : pt.s - 1 + 1 = pt.s := by simp only [Slot] at hspos ⊢; omega
  obtain ⟨hBound, _⟩ := wc_duty_receiver hvalid (r := pt.s - 1) hi (by simpa only [hsucc] using hJ')
  have hRF : V2.D.restartFree rho x k i := by
    intro l w hkl hli hl
    have hb := hBound l w hli hl
    have hpv : SA.proposalTime p.toParams (pt.s - 1) < SA.voteTime p.toParams pt.s := by
      rw [← hsucc]
      change 4 * p.Δ * ((pt.s - 1 : Nat) : Int) <
        4 * p.Δ * ((pt.s - 1 + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos]
    have hlk := (Gen.V2.Duty.index_lt_idxBefore_iff hs hl _).mpr (hb.trans_lt hpv)
    omega
  have hc := fgsa_store_cumulative_on p c E rho hki x hRF
  have hmem := hc.2.1.subset hstored
  obtain ⟨M, hM, hMB⟩ := (namedBodies_erase_domain p _ (cstoreInv_stateBefore E rho i x)
    (metaInv_stateBefore E rho i x) N.erase).mp hmem
  have hMN := namedScope_erase_injective E rho (hroots.toNamedRootCollisionFree E rho)
    (namedScope_held E rho hx i hM) hscope hMB
  have hpath : ∀ A, Block.Preceq A pt.P → A ∈ (storeAt p c E rho i x).base.blocks := by
    intro A hA
    obtain ⟨W, hW, hWB⟩ := ((cstoreInv_stateBefore E rho i x).baseTree _).mp hmem
    obtain ⟨Af, hAf, hAfA⟩ := eraseFG_ancestor_mem
      (cstoreInv_stateBefore E rho i x).fg.closed hW (hWB ▸ hN.symm ▸ hA)
    exact ((cstoreInv_stateBefore E rho i x).baseTree A).mpr ⟨Af, hAf, hAfA⟩
  refine ⟨hj.trans_le hki, ?_, ?_, ?_⟩
  · rw [clock_namedBodies]
    exact hMN ▸ hM
  · intro A hA
    rw [clock_base_blocks]
    exact hpath A hA
  · have ht : 0 < SA.voteTime p.toParams pt.s := by
      change 0 < 4 * p.Δ * (pt.s : Time) + p.Δ
      nlinarith [p.deltaPos, Nat.cast_nonneg (α := Int) pt.s]
    rw [← hN]
    have hstamp := fgsa_block_stamp_before_read E rho hs x (SA.voteTime p.toParams pt.s)
      ht N.erase (by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
        exact hstored)
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hstamp
    have hkeysK : N.erase ∈ (storeAt p c E rho k x).base.blockStamp.map Prod.fst := by
      change _ ∈ (rho.stateBefore E k x).st.base.blockStamp.map Prod.fst
      rw [(metaInv_stateBefore E rho k x).stampKeys]
      exact hstored
    have hsaved := inclusion_stampBlock_of_prefix hc.2.2.1 hkeysK
    change GridCO.stampBlock (storeAt p c E rho i x).base N.erase =
      GridCO.stampBlock (storeAt p c E rho k x).base N.erase at hsaved
    have hkeys : N.erase ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
      change N.erase ∈ (rho.stateBefore E i x).st.base.blockStamp.map Prod.fst
      rw [(metaInv_stateBefore E rho i x).stampKeys]
      exact hmem
    rw [inclusion_stampBlock_of_prefix (by rw [(clock_cumulative p _ _).2.2.1]) hkeys]
    exact hsaved ▸ hstamp

end AvailableChain.FGSA.Run
end

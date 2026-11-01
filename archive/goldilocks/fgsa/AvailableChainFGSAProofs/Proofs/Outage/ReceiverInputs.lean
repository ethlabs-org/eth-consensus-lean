module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingConstruction
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch
public import AvailableChainFGSAProofs.Proofs.Outage.GoodVotes
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionServices

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Prefix transport gives the exact early HEAD service at a joined reader.
The cut can precede the consuming gate, as required by the pending batch. -/
theorem outage_prefix_head_service {cut : Time}
    (hBase : Base₂ p c E rho)
    (hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) cut)
    {x y : V} {s : Slot} {C R : Time} {q : Fin p.n} {b : BlockId}
    (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hC : SA.earlyTime p.toParams s ≤ C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hCut : C ≤ cut)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    Nonempty (FreshHeadService E rho s q b C x) := by
  have hd := p.deltaPos
  have hv0 : 0 ≤ SA.voteTime p.toParams s := by rw [arming_vote_eq]; positivity
  have hstart : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith
  have hve := (arming_vote_lt_early p s).1
  have hRF := outage_restored_reader_epoch hBase.valid.toScheduleWellFormed hJ
    hstart (hve.trans_le (hC.trans hCR))
  have hdl : SA.voteTime p.toParams s + p.Δ =
      SA.earlyTime p.toParams s := arming_vote_add p s
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := cut
    within := ?_
    ready := ?_
    later := by simpa only [hdl] using hve
    cut_le := by simpa only [hdl] using hC.trans hCut
    horizon := by simpa only [hdl] using hC.trans hhor
    freeze_le := by simpa only [hdl] using hC
    epoch := hRF.mono le_rfl (fgsa_idxBefore_mono rho hCR)
    handlers := by simpa only [hdl] using arming_head_handlers hBase.valid hBase.delta s q b x
    not_excluded := by simpa only [hdl] using outage_fresh_head_not_excluded hBase.valid hy he }⟩
  · exact hDelivery
  · rw [hdl]
    refine ⟨y, hy, Or.inl he, ?_⟩
    intro u hvu hue
    exact outage_restored_reader_awake hJ (hv0.trans hvu) (hstart.trans hvu)
      (hue.le.trans (hC.trans hCR))

private theorem outage_proposal_direct (st : State p.n) (parent o : Obj p)
    {s : Slot} {N : NamedProposal p.n} (hd : (toWire p o).decode = some (.block s N))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r M =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofHead] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofRow] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd

/-- Original proposal emission or acceptance drives service at a public anchor.
Durable proposal history supplies HistorySafeAt after an earlier restart.
The transport cut is explicit. -/
theorem outage_prefix_proposal_service {cut : Time}
    (hBase : Base₂ p c E rho)
    (hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) cut)
    {x y : V} {s q : Slot} {N : NamedProposal p.n} {send a C R : Time}
    (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hStart : slotStartZ p (s : Int) ≤ a) (hPub : V2.PublicTime E a)
    (hDeadline : a + p.Δ = C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hCut : C ≤ cut) (ht : send ≤ a)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E C x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩) send C x) := by
  have hV := hBase.valid
  have ha0 : 0 ≤ a := le_trans (by
    change 0 ≤ 4 * p.Δ * (s : Int); have := p.deltaPos; positivity) hStart
  have haC : a < C := hDeadline ▸ lt_add_of_pos_right a p.deltaPos
  have hdl : a + p.Δ = C := hDeadline
  have hAct : fgsaAdmissionTime p (ofWire p ⟨.proposer q, .proposal N⟩) ≤ send := by
    rcases he with ⟨k, hk, hem⟩ | ⟨k, hacc⟩
    · rw [(V2.D.Run.step_tick_eq E rho hk).2] at hem
      exact ((fgsa_emits_proposal E rho _ y send q (.proposal N)).mp hem).2.1.le
    · have hbound := timely_of_relay_retained E rho (fgsaTimelyClock p c)
        (fgsaAdmitSound p c) hV.toScheduleWellFormed
        (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
        (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
          fgsa_admissionTime_public p E hBase.delta obj) y k _ send hacc
      rw [fgsaTimelyClock_actTime] at hbound
      exact hbound.trans (Gen.V2.Duty.pubFloor_le E send)
  have hRF := outage_restored_reader_epoch hV.toScheduleWellFormed hJ hStart
    (haC.trans_le hCR)
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := cut
    anchor := a
    within := ?_
    ready := ?_
    send_le := ht
    nonneg := ha0
    later := by simpa only [hdl] using haC
    cut_le := by simpa only [hdl] using hCut
    horizon := by simpa only [hdl] using hhor
    freeze_le := by rw [hdl]
    history := fgsa_historySafeAt_of_proposal x _ a rfl
    epoch := hRF.mono le_rfl (fgsa_idxBefore_mono rho hCR)
    handlers := ?_
    not_excluded := by simpa only [hdl] using hNX }⟩
  · exact hDelivery
  · rw [hdl]
    refine ⟨y, hy, he, ?_⟩
    intro u hau huC
    exact outage_restored_reader_awake hJ (ha0.trans hau) (hStart.trans hau)
      (huC.le.trans hCR)
  · intro j u hau hud hh
    obtain ⟨parent, hj, hp⟩ := hh
    have hEq := outage_proposal_direct _ parent _ rfl hp
    subst parent
    refine ⟨hV.wire j x _ u hj, hV.deps j x _ u hj, ?_⟩
    have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hV hj hPub ha0 hau
    change fgsaAdmissionTime p _ ≤ (rho.stateBefore E j x).st.base.now
    rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
    exact (hAct.trans ht).trans hn

private theorem outage_target_decode {o : Obj p} {K : Block}
    (h : blockOf? p o = some K) :
    ∃ q N, o = ofWire p ⟨.proposer q, .proposal N⟩ ∧ N.erase = K := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i q N
    refine ⟨q, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- A joined honest reader gets a full batch at the exact public deadline.
Incompatible targets keep the public finality alternative. Compatible targets
use their original acceptance and durable proposal history. -/
theorem outage_prefix_batch_service {cut : Time}
    (hBase : Base₂ p c E rho)
    (hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) cut)
    {x : V} {s : Slot} {a C R : Time} (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hC : SA.earlyTime p.toParams s ≤ C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hCut : C ≤ cut)
    (hva : SA.voteTime p.toParams s ≤ a) (hPub : V2.PublicTime E a)
    (hDeadline : a + p.Δ = C) : ArmingBatchReceiptService E rho x s C := by
  classical
  have hV := hBase.valid
  have hS := hV.toScheduleWellFormed
  have hStart : slotStartZ p (s : Int) ≤ a := le_trans (by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]) hva
  constructor
  · intro y o q b hy he hd
    have ho : o = ofHead p ⟨.seat (.head s) q, b⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    subst o
    obtain ⟨k, hk, hem⟩ := he
    have he' := hem
    rw [(V2.D.Run.step_tick_eq E rho hk).2] at he'
    have hf := (fgsa_emits_head E rho _ y _ s q b).mp he'
    let K := headVote p (FGSA.clock p (rho.stateBefore E k y).st
      (SA.voteTime p.toParams s)) s
    have hroot : K.root = b := hf.2.2.2.2.symm
    have hTarget : HeadTargetAtEmission p c E rho y
        (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s) K := by
      refine ⟨k, s, q, hk, hem, ?_, rfl⟩
      rw [hroot]
    refine ⟨K, hTarget, ?_⟩
    by_cases hbad : ¬ Block.Compatible K (eraseFG (rho.stateBeforeTime E C x).st.fg.F)
    · exact Or.inl hbad
    right
    refine ⟨outage_prefix_head_service hBase hDelivery hx hy hJ hC hCR hhor hCut
      ⟨k, hk, hem⟩, ?_⟩
    by_cases hgen : K = .genesis
    · exact hgen ▸ fgsa_target_service_genesis E rho C x
    have hK : K ∈ (storeAt p c E rho k y).base.blocks := by
      have hm := headVote_stored p _
        (storeBundle_postClock E rho k y (SA.voteTime p.toParams s)).cstore s
      change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
      rwa [clock_base_blocks] at hm
    obtain ⟨j, hjk, send, obj, hobj, hacc⟩ := fgsa_block_accepted_origin E rho k y K hgen hK
    obtain ⟨q', N, rfl, hNK⟩ := outage_target_decode hobj
    have hsend : send ≤ SA.voteTime p.toParams s := by
      obtain ⟨parent, hj, _⟩ := hacc.1
      by_contra hn
      have hkj := V2.D.Engine.tick_index_lt_delivery E rho hS hk hj (le_of_not_ge hn)
      omega
    have hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer q', .proposal N⟩) send :=
      Or.inr ⟨y, hy, j, hacc⟩
    have hNX : (fgsa p c).excludes (rho.stateBeforeTime E C x)
        (ofWire p ⟨.proposer q', .proposal N⟩) = false := by
      change (blockExcluded _ N.erase || invalidForParent p _ N) = false
      rw [fgsa_trigger_invalid_false E rho _ send q' N hT rfl]
      change (!activeCompatible _ N.erase || false) = false
      have hc : activeCompatible (rho.stateBeforeTime E C x).st N.erase = true := by
        change Block.compatible N.erase (eraseFG (rho.stateBeforeTime E C x).st.fg.F) = true
        rw [hNK]
        exact not_not.mp hbad
      rw [hc]
      rfl
    exact hNK ▸ fgsa_target_service_of_proposal E rho q' N send C x
      (outage_prefix_proposal_service hBase hDelivery hx hy hJ hStart hPub hDeadline
        hCR hhor hCut (hsend.trans hva) (Or.inr ⟨j, hacc⟩) hNX)
  · intro y o m q N hy he htime hNX hd
    have ho : o = ofWire p ⟨.proposer q, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    subst o
    exact outage_prefix_proposal_service hBase hDelivery hx hy hJ hStart hPub hDeadline
      hCR hhor hCut (htime.trans hva) (Or.inl he) hNX

/-- The healthy prefix supplies service at every enabled pending receiver,
including W. Only the early deadline must be inside the prefix. -/
theorem outage_pending_receipt_scope [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1)) : GateReceiptScope E rho i x (l + 1) := by
  have hs := h.base.valid.toScheduleWellFormed
  have hJ := outage_enabled_gate_joined h.base.valid hx hG
  have heg : SA.earlyTime p.toParams (l + 1) ≤ SA.gateTime p.toParams (l + 1) := by
    rw [arming_early_eq, arming_gate_eq]
    linarith [p.deltaPos]
  have hecut : SA.earlyTime p.toParams (l + 1) ≤ b₀ :=
    (arming_early_next p l).trans_le hc.gate_le_cut
  have hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) b₀ := by
    simpa only [h.base.delta] using Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy
      E rho b₀ h.healthy (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  have hPub : V2.PublicTime E (SA.voteTime p.toParams (l + 1)) := by
    refine ⟨4 * (l + 1) + 1, ?_⟩
    rw [h.base.delta, arming_vote_nat]
  have hBatch := outage_prefix_batch_service h.base hDelivery hx hJ le_rfl heg
    (hecut.trans h.cut.2) hecut le_rfl hPub (arming_vote_add p (l + 1))
  refine ⟨hG, hJ, outage_enabled_gate_read_epoch hs hG ?_, ?_⟩
  · change 4 * p.Δ * ((l + 1 : Nat) : Int) <
      4 * p.Δ * ((l + 1 : Nat) : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · intro q K hy hTarget
    obtain ⟨k, hk, hem⟩ : V2.D.Run.emits E rho
        (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
        (SA.voteTime p.toParams (l + 1)) := by
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
      exact ⟨k, hk, hem⟩
    obtain ⟨K', hTarget', hbad | hService⟩ := hBatch.heads _ _ q K.root hy
      ⟨k, hk, hem⟩ (by rw [toWire_ofHead]; rfl)
    all_goals have heq : K = K' := headTargetAtEmission_unique E rho hs hTarget hTarget'
    · have hDK := arming_head_ge_on hs htransfer hc.max_mem hy
        (fgsa_joinedAt_of_emitted_head E rho h.base.valid hk hem) hk
      change Block.Preceq D (headVote p (clock p (rho.stateBefore E k
        (rho.seatOf (.base (.head (l + 1))) q)).st (SA.voteTime p.toParams (l + 1)))
          (l + 1)) at hDK
      rw [← headTargetAtEmission_at_tick E rho hs hTarget hk rfl] at hDK
      have hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
          (SA.earlyTime p.toParams (l + 1)) x).st.fg.F) D := by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
        exact hc.f_below _ x (fgsa_idxBefore_mono rho heg) hx
      exact (hbad (heq ▸ block_compatible_of_common (block_preceq_refl K)
        (block_preceq_trans hFloor hDK))).elim
    · simpa only [← heq] using hService

/-- The complete joined Clean batch makes every enabled pending result compatible.
The receiver can be in W; the prefix service has no covered-node premise. -/
theorem outage_pending_result_compatible [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {i : Nat} {x : V} {C : Block} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1))
    (hC : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  have hv0 : 0 ≤ SA.voteTime p.toParams (l + 1) := by
    rw [arming_vote_eq]
    have := p.deltaPos
    positivity
  have hvcut : SA.voteTime p.toParams (l + 1) < b₀ :=
    (arming_vote_lt_early p _).1.trans_le
      ((arming_early_next p l).trans_le hc.gate_le_cut)
  obtain ⟨H, hH, hbatch⟩ := inclusion_joined_head_seats E rho h.base.cstar (l + 1)
    ⟨h.joinedPartBefore _ hv0 hvcut⟩
  have hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (l + 1))))
        (l + 1))).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
    apply inclusion_joined_rest_bound E rho h.base.cstar h.base.valid (l + 1) H
      (fun k hh hj => (hH k).mpr ⟨hh, hj⟩)
    intro o ho k hk
    obtain ⟨hm, hl⟩ := List.mem_filter.mp (List.mem_filter.mp ho).1
    change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
    rw [(Internal.clockPre_vn _ _).1] at hm
    exact ⟨i, x, o, hm, beq_iff_eq.mp hl, hk⟩
  have hraw := inclusion_gate_raw_at_tick E rho h.base.valid.toScheduleWellFormed hG
  have hresult := Option.some.inj (hraw.symm.trans hC)
  exact outageV_gate_of_good_service E rho h.base i x (l + 1) B C hx
    H (outage_gate_scope_of_shared (outage_pending_receipt_scope h hc htransfer hx hG) H)
    (Gen.V2.Duty.faulty rho).card hbatch.lt hrest
    (fun q hq => (hH q).mp hq)
    (fun q hq K hK => outage_pending_head_targets E rho h.base.valid hc htransfer hx hG
      q K ((hH q).mp hq).1 hK) hresult

/-- Actual pending actions have compatible sources at every honest node, including W.
The source discipline supplies a passed gate; prefix service supplies its result bound. -/
theorem outage_pending_sources_compatible [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (htsrc : TSrc p c E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H) :
    ∀ y r C, y ∈ rho.honest → p.actionTime r = SA.gateTime p.toParams (l + 1) →
      actionSource p c E rho y r = some (some C) → Block.Compatible C B := by
  intro y r C hy ht hC
  obtain ⟨X, G, _, hCX, hG, hXG, _, i, hi, hpass⟩ := htsrc y r C hy hC
  have hrj : r * p.R = l + 1 := Nat.le_antisymm
    ((arming_gate_le_iff p _ _).mp ht.le) ((arming_gate_le_iff p _ _).mp ht.symm.le)
  rw [hrj] at hG hi
  have hEnabled := arming_enabled_of_pass hi hpass
  have hRes := (gateResultAt_eq_gateResult p c E rho h.base.valid.toScheduleWellFormed hi).trans hG
  exact block_compatible_of_preceq_compatible (hXG C hCX)
    (outage_pending_result_compatible h hc htransfer hy hEnabled hRes)

/-- The sleep Clean producers close the full all-ticks source seed. -/
theorem outage_arming_sources_from_prefix [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (htsrc : TSrc p c E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) :=
  outage_arming_sources_on h.base.valid.toScheduleWellFormed hc
    (outage_pending_sources_compatible h htsrc hc htransfer)

/-- Fast support above the bad-set count has an actual HEAD outside that set.
The bad set includes faults and can include W. The source itself can belong to W. -/
theorem outage_fast_supporting_head_outside [Fintype V]
    (hBase : Base₂ p c E rho)
    (bad : Finset V) (hfault : Gen.V2.Duty.faulty rho ⊆ bad)
    (hbad : bad.card < SA.releaseThreshold p.toParams)
    {x : V} {s : Slot} {C : Block} (hfast : fastAt p c E rho x s C) :
    ∃ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      rho.seatOf (.base (.head s)) q ∉ bad ∧
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩)
        (SA.voteTime p.toParams s) K ∧ Block.Preceq C K := by
  classical
  obtain ⟨st, hst, hτ⟩ := hfast
  rw [gateIn_def, preTick_def] at hst
  cases hi : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => rw [hi] at hst; cases hst
  | some i =>
    rw [hi] at hst
    have hst := Option.some.inj hst
    subst st
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    let pool := GridCO.cleanSupport p.toParams.engine v s
    let seats := (GridCO.seats p.n pool).toFinset.filter
      (fun k => Gen.AC.Root.poolSupports (GridCO.resolutionTree v) pool k C = true)
    have hcard : SA.Root.prefixSupport p.toParams v s C = seats.card := by
      rw [cleanSupport_domain_score, Gen.AC.Root.vote_pool_score_card]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro k _
      rw [fgsa_cleanSupport_no_equivocation p v s k, Bool.false_or]
    have hex : ∃ q o, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        rho.seatOf (.base (.head s)) q ∉ bad ∧ o ∈ pool ∧ GridCO.headSeat? o = some q ∧
        Gen.AC.Root.voteSupports (GridCO.resolutionTree v) C o = true := by
      by_contra hn
      have hle : seats.card ≤ bad.card := by
        apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
        · intro q hq
          by_contra hnot
          have hh : rho.seatOf (.base (.head s)) q ∈ rho.honest := by
            by_contra hn
            exact hnot (hfault (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩))
          obtain ⟨_, hs⟩ := Finset.mem_filter.mp hq
          obtain ⟨o, ho, hk, hv⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ q C).mp hs
          exact hn ⟨q, o, hh, hnot, ho, hk, hv⟩
        · intro q _ k _ he
          exact (hBase.cstar (.base (.head s)) trivial).injective he
      exact (not_lt_of_ge (hτ.trans (hcard ▸ hle))) hbad
    obtain ⟨q, o, hh, hnot, ho, hq, hsup⟩ := hex
    obtain ⟨K, hresolve, hK, _, hCK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hsup
    have hKb : K ∈ (storeAt p c E rho i x).base.blocks := by
      dsimp only [v] at hK
      rw [actView_resolutionTree] at hK
      change K ∈ (clockPre p (storeAt p c E rho i x) _).base.headDomain.getD
        (clockPre p (storeAt p c E rho i x) _).base.blocks at hK
      have hd : (storeAt p c E rho i x).base.headDomain = none :=
        base_headDomain_none p (reachable_stateBefore E rho i x)
      rw [clockPre_headDomain, hd] at hK
      simpa only [Option.getD_none, (clockPre_fields p _ _).2.1] using hK
    obtain ⟨hearly, _⟩ := List.mem_filter.mp ho
    obtain ⟨hvotes, _⟩ := List.mem_filter.mp hearly
    obtain ⟨hm, hl⟩ := List.mem_filter.mp hvotes
    have hlabel : GridCO.headLabel? o = some s := beq_iff_eq.mp hl
    have hstored : o ∈ (storeAt p c E rho i x).base.votes := by
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
      rwa [(Internal.clockPre_vn _ _).1] at hm
    have hs := hBase.valid.toScheduleWellFormed
    have hJ := fgsa_stored_honest_head_joined E rho hBase.valid i x s q o
      hstored hlabel hq hh
    have hvhor : SA.voteTime p.toParams s ≤ rho.horizon := by
      have hgate := (hs.in_horizon _ (List.mem_of_getElem? (V2.D.Run.tickIdx?_spec hi))).2
      exact (arming_vote_lt_early p s).1.le.trans
        ((by rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos]) :
          SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s) |>.trans hgate
    have hv : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
      rw [arming_vote_nat]
    obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hBase.delta _ hh
      (4 * s + 1) (hv ▸ hvhor) (hv ▸ hJ.1)
    rw [hv] at hj
    let H := headVote p (clock p (rho.stateBefore E j
      (rho.seatOf (.base (.head s)) q)).st (SA.voteTime p.toParams s)) s
    have hem : ofHead p ⟨.seat (.head s) q, H.root⟩ ∈ rho.emitsAt E j := by
      rw [(V2.D.Run.step_tick_eq E rho hj).2]
      exact (fgsa_emits_head E rho _ _ _ s q H.root).mpr
        ⟨hJ.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hj hJ, rfl⟩
    have he := fgsa_honest_head_eq_of_stored E rho hBase.valid i x s q H.root
      (SA.voteTime p.toParams s) hh ⟨j, hj, hem⟩ o hstored hlabel hq
    rw [he] at hresolve
    have hroot : K.root = H.root := (Option.some.inj (resolvedTarget_root _ _ hresolve)).symm
    have hKH := stored_eq_headVote E rho hBase.idealization i x hKb j _
      (SA.voteTime p.toParams s) s hroot
    refine ⟨q, K, hh, hnot, ?_, hCK⟩
    rw [hKH]
    exact ⟨j, s, q, hj, hem, rfl, rfl⟩

/-- The pending source route uses the faulty set alone. -/
theorem outage_fast_supporting_head [Fintype V]
    (hBase : Base₂ p c E rho)
    (hfault : (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams)
    {x : V} {s : Slot} {C : Block} (hfast : fastAt p c E rho x s C) :
    ∃ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
      Block.Preceq C K := by
  obtain ⟨q, K, hh, _, hK, hCK⟩ := outage_fast_supporting_head_outside hBase
    (Gen.V2.Duty.faulty rho) (fun _ h => h) hfault hfast
  exact ⟨q, K, hh, hK, hCK⟩

/-- The pre-cut joined majority puts the faulty count below the release level. -/
theorem outage_prefix_fault_lt_release [Fintype V] {b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {t : Time} (ht : 0 ≤ t) (hcut : t < b₀) :
    (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams := by
  classical
  let seat : Fin p.n → V := rho.seatOf (.base (.head 0))
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr (Equiv.ofBijective seat (h.base.cstar _ trivial)), Fintype.card_fin]
  have hsub : joinedHonest p E rho t ⊆ rho.honest := fun _ hx => (Finset.mem_filter.mp hx).1
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    have hle := Finset.card_le_univ rho.honest
    rw [hn] at hle
    omega
  exact outage_fault_lt_release p (h.joinedPartBefore t ht hcut)
    ((Finset.card_le_card hsub).trans (by omega))

/-- The general comparison certificate supplies the all-ticks source seed.
Actions at the pending time use fast support, including honest sources in W. -/
theorem outage_arming_sources_scoped [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (htsrc : TSrc p c E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) := by
  constructor
  intro k y r C hk hy ht hC
  have hs := h.base.valid.toScheduleWellFormed
  have htime := arming_tick_le hs ht
    (hk.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
  rcases htime.lt_or_eq with hlt | heq
  · exact block_compatible_of_common (hc.source_below y r C hy hlt hC) hc.max_read
  have hrj : r * p.R = l + 1 := Nat.le_antisymm
    ((arming_gate_le_iff p _ _).mp heq.le) ((arming_gate_le_iff p _ _).mp heq.symm.le)
  obtain ⟨X, G, _, hCX, _, _, hfast, _⟩ := htsrc y r C hy hC
  have hv0 : 0 ≤ SA.voteTime p.toParams (l + 1) := by
    rw [arming_vote_eq]; have := p.deltaPos; positivity
  have hvcut : SA.voteTime p.toParams (l + 1) < b₀ :=
    (arming_vote_lt_early p _).1.trans_le
      ((arming_early_next p l).trans_le hc.gate_le_cut)
  have hτ := outage_prefix_fault_lt_release h hv0 hvcut
  rw [hrj] at hfast
  obtain ⟨z, K, hz, hTarget, hCK⟩ := outage_fast_supporting_head h.base hτ (hfast C hCX)
  have hTarget' := hTarget
  obtain ⟨j, _, _, hj, hem, _, _⟩ := hTarget
  have hK := headTargetAtEmission_at_tick E rho hs hTarget' hj rfl
  have hDK := hc.joined_heads (rho.seatOf (.base (.head (l + 1))) z) hz
    (fgsa_joinedAt_of_emitted_head E rho h.base.valid hj hem) j hj
  change Block.Preceq D (headVote p (clock p (rho.stateBefore E j
    (rho.seatOf (.base (.head (l + 1))) z)).st (SA.voteTime p.toParams (l + 1)))
      (l + 1)) at hDK
  rw [← hK] at hDK
  exact block_compatible_of_common hCK (block_preceq_trans hc.max_read hDK)

/-- Named honest rows inherit compatibility from the general all-ticks source seed. -/
theorem outage_arming_named_scoped [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (htsrc : TSrc p c E rho)
    {B : Block} {l : Slot} {D : Block} {Dh β : FGBlock (Fin p.n)}
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B) :
    OutageNamedHistory p c E rho β (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) :=
  outage_named_of_source_history h.base.idealization hβ
    (outage_arming_sources_scoped h htsrc hc)
    hnamed

/-- The named seed discharges P-Ar's row boundary and gives scoped protection and domain. -/
theorem outage_arming_protection_scoped [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    (htsrc : TSrc p c E rho) {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      OutageProtection p B (l + 1) st ∧
        (Block.Preceq B (F_at p c E rho I y) ∨
          (∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (FGSA.controls p st).Z)) := by
  have hRows : ∀ y r (a : RowWire p.n) (e Bh : FGBlock (Fin p.n)), eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e := by
    intro y r a e Bh hBh ha he hScope
    exact (outage_arming_named_scoped h htsrc hnamed hc hBh).history y r a e ha he hScope
  intro y hy I st
  obtain ⟨hS, hF | ⟨_, _, dl, hlease, _, hlong, hdom⟩⟩ :=
    pending_gate_lease_or_F_scoped_on h.base.valid h.base.delta hf hne hc hgate hRows y hy
  · exact ⟨⟨hS, Or.inl hF⟩, Or.inl hF⟩
  exact ⟨⟨hS, Or.inr ⟨dl, outage_row_of_lease p st
    (cstoreInv_stateBefore E rho I y) hlease, hlong⟩⟩, Or.inr hdom⟩

/-- Consume the equal-cut fast producer with the actual Clean induction and provenance.
No last-label result, pending-source premise, or named-row premise is required. -/
theorem outage_fast_seed_scoped [Fintype V] {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hprov : ArmingJoinedProvenance (c := c) E rho) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ D Dh, ArmingSleepGateCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh ∧
      OutageSourceHistory p c E rho B
        (afterTicksIdx rho (SA.gateTime p.toParams (coverLabel p b₀))) := by
  obtain ⟨D, Dh, hc⟩ := fast_arming_scoped_on h hf hsrc htsrc hState hHist
    htransfer hprov hread hne
  refine ⟨D, Dh, hc, ?_⟩
  rw [hc.cover_label]
  exact outage_arming_sources_scoped h.sleepPre htsrc hc

/-- Restored transport produces service only for the selected admissible HEADs.
The receiver can be in W. Its actual enabled gate supplies join and the read epoch. -/
theorem outage_restored_good_scope {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hf : FGFoundation p c E rho) {i : Nat} {x : V} {s : Slot} {B : Block}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho i x s)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hlow : Block.Preceq (F_at p c E rho i x) B) (H : Finset (Fin p.n))
    (hTargets : ∀ q ∈ H, ∀ K, HeadTargetAtEmission p c E rho
      (rho.seatOf (.base (.head s)) q) (ofHead p ⟨.seat (.head s) q, K.root⟩)
        (SA.voteTime p.toParams s) K → Block.Preceq B K) :
    OutageGateReceiptScope E rho i x s H := by
  have hs := hBase.valid.toScheduleWellFormed
  have hJ := outage_enabled_gate_joined hBase.valid hx hG
  have heg : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hid : rho.idxBefore (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge heg.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hG.1 _).mp (lt_of_not_ge hn))
  have hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.earlyTime p.toParams s) x).st.fg.F) B := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq (hf.mono _ _ x hx hid).1) hlow
  have hPub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [hBase.delta, arming_vote_nat]
  have hBatch := outage_joined_batch_service hBase hSync hx hJ le_rfl heg.le
    (heg.le.trans hhor) hGST le_rfl hPub (arming_vote_add p s)
  refine ⟨hG, hJ, outage_enabled_gate_read_epoch hs hG ?_, ?_⟩
  · change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · intro q hq K hy hTarget
    have hTargetKeep := hTarget
    obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
    obtain ⟨K', hTarget', hbad | hService⟩ := hBatch.heads _ _ q K.root hy
      ⟨k, hk, hem⟩ (by rw [toWire_ofHead]; rfl)
    all_goals have heq : K = K' := headTargetAtEmission_unique E rho hs hTargetKeep hTarget'
    · exact (hbad (heq ▸ Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
        (Gen.Pure.block_preceq_trans hFloor (hTargets q hq K hTargetKeep)))).elim
    · simpa only [← heq] using hService

/-- Restored results use the actual E count and selected good-target history.
All receiver services are produced here. The remaining input is the joint HEAD invariant. -/
theorem outage_restored_result_of_good_targets [Fintype V] {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hf : FGFoundation p c E rho) {fast : Bool} {b₀ b₁ : Time} {r s : Slot}
    (hr : FirstRestored p b₁ r)
    (hGST : E.t_GST ≤ b₁)
    (hrs : r ≤ s)
    (hCount : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      (outageH p E rho s \ outageW p E rho fast b₀ r).card)
    {i : Nat} {x : V} {B C : Block} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x s)
    (hFB : Block.Compatible (F_at p c E rho i x) B)
    (hTargets : Block.Preceq (F_at p c E rho i x) B →
      ∀ q K, rho.seatOf (.base (.head s)) q ∈
        outageH p E rho s \ outageW p E rho fast b₀ r →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Preceq B K)
    (hresult : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  classical
  obtain ⟨H, hH, hCard⟩ := outage_good_seats E rho hBase.cstar fast b₀ r s
  have hSelected : ∀ q ∈ H, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) := by
    intro q hq
    have hm := (Finset.mem_sdiff.mp ((hH q).mp hq)).1
    have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
      slotOf_offset p s p.Δ p.deltaPos.le
        (by have := p.deltaPos; dsimp [Time] at *; omega)
    change _ ∈ rho.honest.filter
      (fun y => joinedAt p E rho y (slotAt p (SA.voteTime p.toParams s))
        (SA.voteTime p.toParams s)) at hm
    rw [hslot] at hm
    exact Finset.mem_filter.mp hm
  have hpart := hCard.symm ▸ hCount
  have hrest := outage_late_opponent_bound E rho hBase.valid hBase.cstar
    i x s fast b₀ r H hH
  have hcut := hGST.trans ((hr s).mpr hrs)
  apply outageV_gate_of_good_service_scoped E rho hBase i x s B C hx hG hFB H
    (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card hpart hrest hSelected
  · intro hlow
    exact outage_restored_good_scope hBase hSync hf hx hG hcut hlow H
      (fun q hq K hK => hTargets hlow q K ((hH q).mp hq) hK)
  · exact fun hlow q hq K hK => hTargets hlow q K ((hH q).mp hq) hK
  · exact hresult

/-- E1 supplies the fixed A union W release bound, also before recovery starts. -/
theorem outage_e1_release_bound [Fintype V] {fast : Bool} {b₀ b₁ : Time}
    (h : OutageE1 p E rho fast b₀ b₁) :
    ∃ r, FirstRestored p b₁ r ∧
      (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
        SA.releaseThreshold p.toParams := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  change _ < (p.n + 1) / 2
  omega

/-- The A union W bound selects a joined good HEAD for every actual honest source.
This supplies the source transition of the scoped joint induction. No row seed is assumed. -/
theorem outage_source_of_good_heads [Fintype V]
    (hBase : Base₂ p c E rho) (htsrc : TSrc p c E rho)
    {fast : Bool} {b₀ : Time} {r s : Slot}
    (hBound : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      SA.releaseThreshold p.toParams)
    {x : V} {a : Nat} {C B : Block} (hx : x ∈ rho.honest) (ha : a * p.R = s)
    (hC : actionSource p c E rho x a = some (some C))
    (hHeads : ∀ q K, rho.seatOf (.base (.head s)) q ∈
      outageH p E rho s \ outageW p E rho fast b₀ r →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B) : Block.Compatible C B := by
  classical
  obtain ⟨X, G, _, hCX, _, _, hfast, _⟩ := htsrc x a C hx hC
  rw [ha] at hfast
  obtain ⟨q, K, hh, hnot, hK, hCK⟩ := outage_fast_supporting_head_outside hBase
    (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r)
    (fun _ h => Finset.mem_union_left _ h) hBound
    (hfast C hCX)
  have hKkeep := hK
  obtain ⟨j, _, _, hj, hem, _, _⟩ := hK
  have hJ := fgsa_joinedAt_of_emitted_head E rho hBase.valid hj hem
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  have hGood : rho.seatOf (.base (.head s)) q ∈
      outageH p E rho s \ outageW p E rho fast b₀ r := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, fun hw => hnot (Finset.mem_union_right _ hw)⟩
    change _ ∈ rho.honest.filter (fun y => joinedAt p E rho y
      (slotAt p (SA.voteTime p.toParams s)) (SA.voteTime p.toParams s))
    rw [hslot]
    exact Finset.mem_filter.mpr ⟨hh, hJ⟩
  exact Gen.Pure.block_compatible_of_preceq_compatible hCK (hHeads q K hGood hKkeep)

/-- Restored result compatibility needs fresh HEAD service only. A target below
receiver F can remain unresolved; its received HEAD still counts in the late pool. -/
theorem outage_restored_result_of_compatible_heads [Fintype V] {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {fast : Bool} {b₀ : Time} {r s : Slot} {i : Nat} {x : V} {B C : Block}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho i x s)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hCount : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      (outageH p E rho s \ outageW p E rho fast b₀ r).card)
    (hHeads : ∀ q K, rho.seatOf (.base (.head s)) q ∈
      outageH p E rho s \ outageW p E rho fast b₀ r →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B)
    (hresult : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  classical
  have hs := hBase.valid.toScheduleWellFormed
  obtain ⟨H, hH, hCard⟩ := outage_good_seats E rho hBase.cstar fast b₀ r s
  have hJ := outage_enabled_gate_joined hBase.valid hx hG
  have heg : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hid : rho.idxBefore (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge heg.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hG.1 _).mp (lt_of_not_ge hn))
  have hRF := outage_enabled_gate_read_epoch hs hG (D := SA.earlyTime p.toParams s)
    (by rw [arming_early_eq]; change 4 * p.Δ * (s : Int) < _; linarith [p.deltaPos])
  apply outageV_gate_of_emitted_heads E rho hBase i x s B C H
    (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card (hCard.symm ▸ hCount)
    (outage_late_opponent_bound E rho hBase.valid hBase.cstar i x s fast b₀ r H hH)
    ?_ hresult hG
  intro q hq
  have hGood := (hH q).mp hq
  have hm := (Finset.mem_sdiff.mp hGood).1
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  change _ ∈ rho.honest.filter _ at hm
  obtain ⟨hy, hyJ⟩ := Finset.mem_filter.mp hm
  rw [hslot] at hyJ
  have he : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    rw [arming_vote_nat]
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hBase.delta _ hy (4 * s + 1)
    (he ▸ (fgsa_vote_lt_gate p s).le.trans hhor) (he ▸ hyJ.1)
  rw [he] at hk
  let K := headVote p (clock p (rho.stateBefore E k
    (rho.seatOf (.base (.head s)) q)).st (SA.voteTime p.toParams s)) s
  have hem : ofHead p ⟨.seat (.head s) q, K.root⟩ ∈ rho.emitsAt E k := by
    rw [(rho.step_tick_eq E hk).2]
    exact (fgsa_emits_head E rho _ _ _ s q K.root).mpr
      ⟨hyJ.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hk hyJ, rfl⟩
  have hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K :=
    ⟨k, s, q, hk, hem, rfl, rfl⟩
  obtain ⟨hHead⟩ := outage_joined_head_service hBase hSync hx hy hJ le_rfl heg.le
    (heg.le.trans hhor) hGST ⟨k, hk, hem⟩
  have hrec := hHead.receipt hBase.valid hx hk hem
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hrec
  have hv := fgsa_votes_cumulative_on p c E rho hid x hRF hrec.1
  have hkey : baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
      (storeAt p c E rho (rho.idxBefore (SA.earlyTime p.toParams s)) x).base.voteStamp.map
        Prod.fst := by
    change _ ∈ (rho.stateBefore E _ x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho]
    exact hrec.1
  have hstamp := inclusion_stampVote_of_prefix
    (fgsa_store_cumulative_on p c E rho hid x hRF).2.2.2.1 hkey
  refine ⟨K, hy, hK, hv, ?_, hHeads q K hGood hK⟩
  change GridCO.stampVote (clockPre p (storeAt p c E rho i x)
    (SA.gateTime p.toParams s)).base _ < _
  rw [inclusion_stampVote_of_prefix (st := (storeAt p c E rho i x).base)
    (st' := (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).base)
    (by rw [(clockPre_stamps p _ _).2]) (by
    change _ ∈ (rho.stateBefore E i x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho]
    exact hv), hstamp]
  exact hrec.2.trans heg

/-- Beyond E's count window the healthy joined set replaces A union W. -/
theorem outage_healthy_result_of_compatible_heads [Fintype V] {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {s : Slot} {i : Nat} {x : V} {B C : Block}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho i x s)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hCount : (Gen.V2.Duty.faulty rho).card <
      (joinedHonest p E rho (SA.voteTime p.toParams s)).card)
    (hHeads : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head s)) q) s (SA.voteTime p.toParams s) →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B)
    (hresult : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  classical
  have hs := hBase.valid.toScheduleWellFormed
  obtain ⟨H, hH, hBatch⟩ := inclusion_joined_head_seats E rho hBase.cstar s ⟨hCount⟩
  have hJ := outage_enabled_gate_joined hBase.valid hx hG
  have heg : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hid : rho.idxBefore (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge heg.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hG.1 _).mp (lt_of_not_ge hn))
  have hRF := outage_enabled_gate_read_epoch hs hG (D := SA.earlyTime p.toParams s)
    (by rw [arming_early_eq]; change 4 * p.Δ * (s : Int) < _; linarith [p.deltaPos])
  have hrest := inclusion_joined_rest_bound E rho hBase.cstar hBase.valid s H
    (fun q hy hJ => (hH q).mpr ⟨hy, hJ⟩)
    (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s) (by
      intro o ho q hq
      obtain ⟨hv, hl⟩ := List.mem_filter.mp (List.mem_filter.mp ho).1
      change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hv
      rw [(Internal.clockPre_vn _ _).1] at hv
      exact ⟨i, x, o, hv, beq_iff_eq.mp hl, hq⟩)
  apply outageV_gate_of_emitted_heads E rho hBase i x s B C H
    (Gen.V2.Duty.faulty rho).card hBatch.lt hrest ?_ hresult hG
  intro q hq
  obtain ⟨hy, hyJ⟩ := (hH q).mp hq
  have he : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    rw [arming_vote_nat]
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hBase.delta _ hy (4 * s + 1)
    (he ▸ (fgsa_vote_lt_gate p s).le.trans hhor) (he ▸ hyJ.1)
  rw [he] at hk
  let K := headVote p (clock p (rho.stateBefore E k
    (rho.seatOf (.base (.head s)) q)).st (SA.voteTime p.toParams s)) s
  have hem : ofHead p ⟨.seat (.head s) q, K.root⟩ ∈ rho.emitsAt E k := by
    rw [(rho.step_tick_eq E hk).2]
    exact (fgsa_emits_head E rho _ _ _ s q K.root).mpr
      ⟨hyJ.1, rfl, rfl, fgsa_head_joined_of_joinedAt E rho hs hk hyJ, rfl⟩
  have hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K :=
    ⟨k, s, q, hk, hem, rfl, rfl⟩
  obtain ⟨hHead⟩ := outage_joined_head_service hBase hSync hx hy hJ le_rfl heg.le
    (heg.le.trans hhor) hGST ⟨k, hk, hem⟩
  have hrec := hHead.receipt hBase.valid hx hk hem
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hrec
  have hv := fgsa_votes_cumulative_on p c E rho hid x hRF hrec.1
  have hkey : baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
      (storeAt p c E rho (rho.idxBefore (SA.earlyTime p.toParams s)) x).base.voteStamp.map
        Prod.fst := by
    change _ ∈ (rho.stateBefore E _ x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho]
    exact hrec.1
  have hstamp := inclusion_stampVote_of_prefix
    (fgsa_store_cumulative_on p c E rho hid x hRF).2.2.2.1 hkey
  refine ⟨K, hy, hK, hv, ?_, hHeads q K ⟨hy, hyJ⟩ hK⟩
  change GridCO.stampVote (clockPre p (storeAt p c E rho i x)
    (SA.gateTime p.toParams s)).base _ < _
  rw [inclusion_stampVote_of_prefix (st := (storeAt p c E rho i x).base)
    (st' := (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).base)
    (by rw [(clockPre_stamps p _ _).2]) (by
    change _ ∈ (rho.stateBefore E i x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho]
    exact hv), hstamp]
  exact hrec.2.trans heg

private theorem inclusion_frame_mono (p : Params) (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : RMonoAll p c E rho := by
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

/-- An early request has an actual joined read and an admissible target at its early tick. -/
theorem inclusion_early_services {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {r : Slot} {a : Time} {x : V}
    (hEA : SA.earlyTime p.toParams r ≤ a)
    (hhor : a ≤ rho.horizon) (hGST : E.t_GST ≤ SA.voteTime p.toParams r)
    (hx : headReader p E rho x (r + 1) a)
    {ie : Nat} (hie : rho.events[ie]? = some (.tick x (SA.earlyTime p.toParams r)))
    {q : Fin p.n} {K : Block} (hy : rho.seatOf (.base (.head r)) q ∈ rho.honest)
    (hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head r)) q)
      (ofHead p ⟨.seat (.head r) q, K.root⟩) (SA.voteTime p.toParams r) K)
    (hFloor : Block.Preceq (F_at p c E rho ie x) K) :
    Nonempty (FreshHeadService E rho r q K.root (SA.earlyTime p.toParams r) x) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams r) x := by
  have hs := hBase.valid.toScheduleWellFormed
  have hIdx : rho.idxBefore (SA.earlyTime p.toParams r) ≤ ie := by
    by_contra hn
    exact (lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs hie _).mp
      (lt_of_not_ge hn))).elim
  have hFK := block_preceq_trans (eraseFG_preceq
    (inclusion_frame_mono p c E rho _ ie x hx.1 hIdx).1) hFloor
  have hCompat : Block.Compatible K
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams r) x).st.fg.F) := by
    change Block.Preceq (eraseFG (rho.stateBefore E _ x).st.fg.F) K at hFK
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hFK
    exact block_compatible_of_common (block_preceq_refl _) hFK
  have hBatch := outage_joined_batch_service hBase hSync hx.1 hx.2 le_rfl hEA
    (hEA.trans hhor) hGST le_rfl (by
      refine ⟨4 * r + 1, ?_⟩
      rw [hBase.delta, arming_vote_nat]) (arming_vote_add p r)
  have hTarget := hK
  obtain ⟨k, _, _, hk, hem, _, _⟩ := hK
  obtain ⟨K', hK', hService⟩ := hBatch.heads _ _ q K.root hy ⟨k, hk, hem⟩ (by
    rw [toWire_ofHead]; rfl)
  have heq : K' = K := headTargetAtEmission_unique E rho hs hK' hTarget
  subst K'
  exact hService.resolve_left (not_not_intro hCompat)

/-- All retained score floors have services; only the emitted proposal needs its own floor. -/
theorem inclusion_receiver_inputs {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)) :
    InclusionReceiverInputs E rho := by
  refine ⟨?_, ?_⟩
  · intro r a x ha hhor hGST hx ie hie q K hy hK hFloor
    apply inclusion_early_services hBase hSync _ hhor hGST hx hie hy hK hFloor
    rcases ha with rfl | rfl <;> rw [arming_early_eq]
    · rw [arming_proposal_eq]; push_cast; linarith [p.deltaPos]
    · rw [arming_vote_eq]; push_cast; linarith [p.deltaPos]
  · intro s ip x N hx hGST hip hem ih y hy hih hFloor
    have hV := hBase.valid
    have hp := hem
    rw [(rho.step_tick_eq E hip).2] at hp
    have hFields := (fgsa_emits_proposal E rho _ x _ s _).mp hp
    have hpos := (fgsa_walkRun_proposal_parent p _ s _ N hFields.2.2.2.2).1
    have hsucc : s - 1 + 1 = s := by dsimp only [Slot] at *; omega
    have hX := inclusion_joinedAt_of_proposal E rho hV hip N hem
    have hGSTs : E.t_GST ≤ SA.proposalTime p.toParams s := by
      apply hGST.trans
      rw [← hsucc, arming_vote_eq, arming_proposal_eq]
      push_cast; linarith [p.deltaPos]
    refine ⟨inclusion_service_emitted_proposal_service hV hBase.delta hSync
      (inclusion_frame_mono p c E rho) hx hy.1 hip hih hem hy.2 hGSTs hFloor, ?_⟩
    intro D hgeom
    have hScope := inclusion_service_retained_score_scope hV hBase.restartsAtWakes hBase.delta hSync
      (inclusion_frame_mono p c E rho) (r := s - 1) hx hy.1
      (hsucc.symm ▸ hip) (hsucc.symm ▸ hih) (hsucc.symm ▸ hX) (hsucc.symm ▸ hy.2)
      hGST D (by simpa only [hsucc, storeAt] using hgeom)
    simpa only [hsucc] using hScope

/-- Actual enabled gates need body receipt only for targets above their current F. -/
theorem inclusion_gate_services
    {ΔF : Time} (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x s) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hTargets : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Preceq (F_at p c E rho i x) K) : GateReceiptScope E rho i x s := by
  have hs := hBase.valid.toScheduleWellFormed
  have hJ := outage_enabled_gate_joined hBase.valid hx hG
  have hEG : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos]
  have hhor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hAw := outage_restored_reader_awake hJ
    (by rw [arming_early_eq]; have := p.deltaPos; positivity)
    (by rw [arming_early_eq]; change 4 * p.Δ * (s : Int) ≤ _; linarith [p.deltaPos])
    hEG.le
  obtain ⟨ie, hie, _⟩ := fgsa_tick_total E rho hs hBase.delta x hx (4 * s + 2)
    (by rw [arming_early_nat]; exact hEG.le.trans hhor)
    (by rw [arming_early_nat]; exact hAw)
  rw [arming_early_nat] at hie
  have hei := V2.D.Engine.eventIndex_lt_of_time_lt hs hie hG.1 hEG
  refine ⟨hG, hJ, outage_enabled_gate_read_epoch hs hG (D := SA.earlyTime p.toParams s)
    (by rw [arming_early_eq]; change 4 * p.Δ * (s : Int) < _; linarith [p.deltaPos]), ?_⟩
  intro q K hy hK
  exact inclusion_early_services hBase hSync hEG.le hhor hGST ⟨hx, hJ⟩ hie hy hK
    (block_preceq_trans (eraseFG_preceq
      (inclusion_frame_mono p c E rho ie i x hx hei.le).1) (hTargets q K hy hK))

/-- The full Clean cut with GST zero supplies the full-run transport used by services. -/
theorem inclusion_clean_synchrony [Fintype V] {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) :
    Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF) := by
  constructor
  · intro v hv o t he w hw a hsend h0 hl hc hh hready hNX
    simp only [hset.gst, max_eq_left h0] at hl hc hh hready hNX ⊢
    exact hset.pre.healthy.broadcast_emitted v hv o t he w hw a hsend h0
      hl hc hh hready hNX
  · intro v hv i o t ha w hw a hsend h0 hl hc hh hready hNX
    simp only [hset.gst, max_eq_left h0] at hl hc hh hready hNX ⊢
    exact hset.pre.healthy.relay_accepted v hv i o t ha w hw a hsend h0
      hl hc hh hready hNX

/-- The complete receiver record has a named producer from the actual Clean sleep regime. -/
theorem inclusion_receiver_inputs_of_clean [Fintype V] {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) : InclusionReceiverInputs E rho :=
  inclusion_receiver_inputs hset.pre.base (inclusion_clean_synchrony hset)

/-- The continuation supplies the joined majority from the handover, at actual labels. -/
theorem outage_post_e_joined_count [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    {s : Slot} (hs : restoredLabel p b₁ + p.k + 1 ≤ s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    (Gen.V2.Duty.faulty rho).card <
      (joinedHonest p E rho (SA.voteTime p.toParams s)).card := by
  apply h.joinedPartAfter _ _ hhor
  change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤
    4 * p.Δ * (s : Int) + p.Δ
  have hcast := Int.ofNat_le.mpr hs
  push_cast at hcast ⊢
  nlinarith [p.deltaPos]

/-- The canonical restored label is the least vote at or after the recovery cut. -/
theorem outage_first_restored_label (p : Params) (b₁ : Time) :
    FirstRestored p b₁ (restoredLabel p b₁) := by
  intro s
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hdiv := Int.le_ediv_iff_mul_le hd (a := -(s : Int)) (b := p.Δ - b₁)
  change b₁ ≤ 4 * p.Δ * (s : Int) + p.Δ ↔
    (max 0 (- ((p.Δ - b₁) / (4 * p.Δ)))).toNat ≤ s
  have hs0 : 0 ≤ (s : Int) := Int.natCast_nonneg s
  constructor
  · intro hv
    have hq := hdiv.mpr (by nlinarith)
    omega
  · intro hr
    have hq : -(s : Int) ≤ (p.Δ - b₁) / (4 * p.Δ) := by omega
    have hm := hdiv.mp hq
    nlinarith

/-- All enabled gates after r use E inside its window and the healthy set after handover.
The only invariant input is compatibility of actual scoped HEADs. -/
theorem outage_continuation_result_of_head_history [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) {B : Block}
    {i : Nat} {x : V} {s : Slot} {C : Block}
    (hx : x ∈ rho.honest) (hrs : restoredLabel p b₁ < s)
    (hG : enabledGateAt p c E rho i x s)
    (hC : gateResultAt p c E rho i = some (some C))
    (hHeads : ∀ q K,
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B) : Block.Compatible C B := by
  classical
  obtain ⟨r, hr, hCount⟩ := h.protection
  have hrCanon := outage_first_restored_label p b₁
  have heq : r = restoredLabel p b₁ := by
    apply Nat.le_antisymm
    · exact (hr _).mp ((hrCanon _).mpr le_rfl)
    · exact (hrCanon _).mp ((hr _).mpr le_rfl)
  subst r
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hGST := h.gst.trans ((hr s).mpr hrs.le)
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  by_cases hWindow : s ≤ restoredLabel p b₁ + p.k + 1
  · apply outage_restored_result_of_compatible_heads h.pre.base h.sync hx hG hGST
      (hCount s hrs.le hWindow) _ hC
    intro q K hGood hK
    have hH := (Finset.mem_sdiff.mp hGood).1
    have hNW := (Finset.mem_sdiff.mp hGood).2
    change _ ∈ rho.honest.filter _ at hH
    obtain ⟨hy, hJ⟩ := Finset.mem_filter.mp hH
    have hReader : outageHeadReader p E rho fast b₀ b₁
        (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) := by
      refine ⟨⟨hy, hJ⟩, Or.inr (Or.inl ⟨hNW, ?_⟩)⟩
      rw [arming_vote_eq, arming_vote_eq]
      have hcast : (restoredLabel p b₁ : Int) + 1 ≤ (s : Int) := by
        dsimp only [Slot] at hrs; omega
      push_cast; nlinarith [p.deltaPos]
    exact hHeads q K hReader hK
  · have hAfter : restoredLabel p b₁ + p.k + 1 ≤ s := by
      dsimp only [Slot] at hWindow ⊢; omega
    have hHor := (fgsa_vote_lt_gate p s).le.trans
      (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
    apply outage_healthy_result_of_compatible_heads h.pre.base h.sync hx hG hGST
      (outage_post_e_joined_count h hAfter hHor) _ hC
    intro q K hGood hK
    have hEnd : OutageEnd p (restoredLabel p b₁) ≤ SA.voteTime p.toParams s := by
      change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤
        4 * p.Δ * (s : Int) + p.Δ
      have hcast := Int.ofNat_le.mpr hAfter
      push_cast at hcast ⊢; nlinarith [p.deltaPos]
    apply hHeads q K _ hK
    refine ⟨?_, Or.inr (Or.inr hEnd)⟩
    change _ ∈ rho.honest ∧ joinedAt p E rho _ (slotAt p (SA.voteTime p.toParams s)) _
    rw [hslot]
    exact hGood

/-- All enabled gates after r use E inside its window and the healthy set after handover.
The only invariant input is compatibility of actual scoped HEADs. -/
theorem outage_continuation_results_of_head_history [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) {B : Block}
    (hHeads : ∀ s q K, restoredLabel p b₁ < s →
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B) :
    ∀ i x s C, x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho i x s → gateResultAt p c E rho i = some (some C) →
      Block.Compatible C B := by
  intro i x s C hx hrs hG hC
  exact outage_continuation_result_of_head_history h hx hrs hG hC
    (fun q K hReader hK => hHeads s q K hrs hReader hK)

end AvailableChain.FGSA.Run
end

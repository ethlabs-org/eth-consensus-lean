module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryService -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle

public section

/-! Selected phase witnesses use their original acceptance and a recovery read anchor. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def p0d1ServiceCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d1ServiceObservations (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d1ServiceCore p c) :=
  ⟨heightView p, finalityView p, (fun nd => FGSA.controls p nd.st),
    fun nd X => domainR p nd.st X⟩

private def p0d1ServiceTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def phaseVoterBlocks (p : Params) (nd : Node p) (s : Slot) :=
  FGSA.voterBlocks p nd.st s

private theorem p0d1_voterBlocks_eq (nd : Node p) (s : Slot) :
    phaseVoterBlocks p nd s = FGSA.voterBlocks p nd.st s := rfl

private theorem phase_service_proposal_direct (st : State p.n) (parent o : Obj p)
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

/-- An arbitrary recovery anchor uses the preceding public tick for admission. -/
theorem healing_proposal_service_at_recovery_anchor {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {k : Nat} {v x : V}
    {s : Slot} {N : NamedProposal p.n} {send a : Time}
    (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hacc : rho.acceptsAt E k v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (hready : recoveryStart p E ≤ a)
    (hhor : a + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible N.erase
      (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F)) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      send (a + p.Δ) x) := by
  have hV := hrec.base.valid
  have hS := hV.toScheduleWellFormed
  have hd : (toWire p (ofWire p ⟨.proposer s, .proposal N⟩)).decode = some (.block s N) := by
    rw [toWire_ofWire]; rfl
  have hGST : E.t_GST ≤ a := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  let tick := Gen.V2.Duty.pubFloor E a
  have hta : tick ≤ a := Gen.V2.Duty.pubFloor_le E a
  have ht0 : 0 ≤ tick := by
    unfold tick
    rw [Gen.V2.Duty.pubFloor_def]
    exact mul_nonneg (Int.ediv_nonneg (E.t_GST_nonneg.trans hGST) E.Δ_pos.le) E.Δ_pos.le
  have hpub : V2.PublicTime E tick := by
    refine ⟨(a / E.Δ).toNat, ?_⟩
    dsimp [tick]
    rw [Gen.V2.Duty.pubFloor_def, Int.toNat_of_nonneg
      (Int.ediv_nonneg (E.t_GST_nonneg.trans hGST) E.Δ_pos.le)]
  have hGSTtick : E.t_GST ≤ tick := by
    have hrem := Int.emod_lt_of_pos a E.Δ_pos
    have he := Int.mul_ediv_add_emod a E.Δ
    have hlo := healing_recovery_start_lower (p := p) E
    dsimp [tick]
    rw [Gen.V2.Duty.pubFloor_def]
    rw [hrec.base.delta] at he hrem ⊢
    nlinarith [p.deltaPos]
  obtain ⟨jTick, hjTick⟩ := List.mem_iff_getElem?.mp
    (hV.tick_total x hx tick hpub ht0 (hta.trans (by linarith [p.deltaPos]))
      (hrec.awake x hx tick hGSTtick (hta.trans (by linarith [p.deltaPos]))))
  have hact := timely_of_relay_retained E rho (fgsaTimelyClock p c) (fgsaAdmitSound p c)
    hS (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
    (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
      fgsa_admissionTime_public p E hrec.base.delta obj) v k _ send hacc
  have hactTick : (fgsaTimelyClock p c).actTime (ofWire p ⟨.proposer s, .proposal N⟩) ≤ tick :=
    Gen.V2.Duty.publicTime_le_pubFloor E
      ((fgsaTimelyClock_actTime p c _).symm ▸
        fgsa_admissionTime_public p E hrec.base.delta _)
      ((hact.trans (Gen.V2.Duty.pubFloor_le E send)).trans hsa)
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
      rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
  have he : max a E.t_GST + p.Δ = a + p.Δ := by rw [max_eq_left hGST]
  have hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer s, .proposal N⟩) send :=
    Or.inr ⟨v, hv, k, hacc⟩
  apply healing_recovery_receiverService E rho hrec _ send a (a + p.Δ) x hx hGST
    (E.t_GST_nonneg.trans hGST) hsa le_rfl hhor hT
    (fgsa_historySafeAt_of_proposal x _ a hd)
  · intro j t hat htd hh
    obtain ⟨parent, hj, hp⟩ := hh
    have hai : V2.D.Run.actionCut rho tick ≤ jTick := by
      apply Nat.le_of_not_gt
      intro hn
      have hk := (V2.D.Engine.index_lt_actionCut_iff hS hjTick tick).mp hn
      rcases hk with hk | ⟨_, hk⟩
      · exact (lt_irrefl tick hk).elim
      · change (1 : Nat) = 0 at hk; cases hk
    have hRF := healing_recovery_restartFree hrec hx hGSTtick hhor
    have hparent := phase_service_proposal_direct _ parent _ hd hp
    subst parent
    refine ⟨hV.wire j x _ t hj, hV.deps j x _ t hj, ?_⟩
    apply Gen.V2.Duty.timely_of_clock E rho (fgsaTimelyClock p c) hS x _ tick jTick j
      hactTick hjTick (V2.D.Engine.tick_index_lt_delivery E rho hS hjTick hj (hta.trans hat))
    exact hRF.mono hai ((Gen.V2.Duty.index_lt_idxBefore_iff hS hj _).mpr htd).le
  · change excludesS p (rho.stateBeforeTime E (a + p.Δ) x).st
      (ofWire p ⟨.proposer s, .proposal N⟩) = false
    dsimp only [excludesS]
    rw [hd]
    change N.erase.compatible (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) = true
      at hCompat
    simp only [blockExcluded, activeCompatible, hCompat, Bool.not_true, Bool.false_or]
    exact fgsa_trigger_invalid_false E rho _ send s N hT hd _

/-- One retained phase witness is served from its original acceptance.
The source event bounds the anchor; the receiver floor is checked before receipt. -/
theorem healing_target_receipt_at_event {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {ev : V2.Event V (Obj p)}
    {x : V} {W : FGBlock (Fin p.n)} (hi : rho.events[i]? = some ev)
    (hready : recoveryStart p E ≤ ev.time)
    (hhor : ev.time + p.Δ ≤ rho.horizon) (hW : HeldAt p c E rho (i + 1) x W)
    {y : V} (hy : y ∈ rho.honest)
    (hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
      (ev.time + p.Δ) y).st.fg.F) (eraseFG W)) :
    TargetReceiptService E rho (eraseFG W) (ev.time + p.Δ) y := by
  by_cases hg : eraseFG W = .genesis
  · exact hg ▸ fgsa_target_service_genesis E rho _ y
  have hm := ((storeBundle_stateBefore E rho (i + 1) x).cstore.baseTree _).mpr
    ⟨W, hW.2, rfl⟩
  obtain ⟨j, hji, send, o, hb, hacc⟩ := fgsa_block_accepted_origin E rho (i + 1) x
    (eraseFG W) hg hm
  dsimp only [blockOf?] at hb
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at hb
  | some msg =>
    cases msg with
    | vote r q b => simp only [hd, reduceCtorEq] at hb
    | row q body => simp only [hd, reduceCtorEq] at hb
    | block s N =>
      simp only [hd, Option.some.injEq] at hb
      have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ := by
        apply toWire_injective
        rw [toWire_ofWire]
        exact decode_eq_block.mp hd
      have hsend : send ≤ ev.time := by
        obtain ⟨parent, hj, _⟩ := hacc.1
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hji) with hlt | rfl
        · obtain ⟨hjlen, hje⟩ := List.getElem?_eq_some_iff.mp hj
          obtain ⟨hilen, hie⟩ := List.getElem?_eq_some_iff.mp hi
          have hk := (List.pairwise_iff_getElem.mp
            hrec.base.valid.toScheduleWellFormed.sorted) j i hjlen hilen hlt
          rw [hje, hie] at hk
          exact V2.D.Engine.time_le_of_key_le _ _ hk
        · exact le_of_eq (congrArg V2.Event.time (Option.some.inj (hj.symm.trans hi)))
      have hservice := healing_proposal_service_at_recovery_anchor E rho hrec hW.1 hy
        (ho ▸ hacc) hsend hready hhor
        (by rw [hb]; exact block_compatible_of_common (block_preceq_refl _) hFloor)
      rw [← hb]
      exact fgsa_target_service_of_proposal E rho s N send _ y hservice

/-- The selected witness receipt is restricted to each actual joined reader. -/
theorem healing_witness_receipt_at_event {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {ev : V2.Event V (Obj p)}
    {x : V} {W : FGBlock (Fin p.n)} (hi : rho.events[i]? = some ev)
    (hready : recoveryStart p E ≤ ev.time)
    (hhor : ev.time + p.Δ ≤ rho.horizon) (hW : HeldAt p c E rho (i + 1) x W) :
    WitnessReceiptScope E rho W (ev.time + p.Δ) :=
  ⟨fun _ _ _ hy _ _ _ hf => healing_target_receipt_at_event E rho hrec hi hready hhor hW hy hf⟩

/-- Recovery supplies the selected frontier, top, and contest receipts used by settlement. -/
theorem healing_phase_witness_receipts_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (i : Nat) (ev : V2.Event V (Obj p)) (m : Nat)
    (hi : rho.events[i]? = some ev) (hready : recoveryStart p E ≤ ev.time) (hm : 1 ≤ m)
    (hfront : frontierAtIdx p c E rho (i + 1) = m)
    (hhor : ev.time + p.Δ ≤ rho.horizon) :
    PhaseWitnessReceiptScope E rho (i + 1) m (ev.time + p.Δ) := by
  have wit := healing_phaseWitness p c E rho hm hfront
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, W, hW, hh⟩ := wit.frontier
    exact ⟨x, W, hW, hh, healing_witness_receipt_at_event E rho hrec hi hready hhor hW⟩
  · intro htop
    obtain ⟨x, C, hC, hh, hj, he⟩ := wit.top htop
    exact ⟨x, C, hC, hh, hj, he, healing_witness_receipt_at_event E rho hrec hi hready hhor hC⟩
  · intro hcontest
    obtain ⟨x, C, W, hC, hW, hhC, hhW, hj, hn⟩ := wit.contest hcontest
    exact ⟨x, C, W, hC, hW, hhC, hhW, hj, hn,
      healing_witness_receipt_at_event E rho hrec hi hready hhor hC,
      healing_witness_receipt_at_event E rho hrec hi hready hhor hW⟩

private theorem phase_service_frozen_mem (crossing : RXing p c E rho)
    (hs : V2.D.ScheduleWellFormed E rho)
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF) {y : V} {W : FGBlock (Fin p.n)} {d : Time}
    (hready : recoveryStart p E ≤ d) (hdpos : 0 < d) {s : Slot} {nd : Node p}
    (hy : y ∈ rho.honest)
    (hcap : frontierAtIdx p c E rho (timeIdx rho (SA.voteTime p.toParams s)) ≤
      (heightView p W).h)
    (hdt : d ≤ SA.voteTime p.toParams s) (hdf : d ≤ SA.freezeTime p.toParams (s - 1))
    (hW : W ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) y).fg.TF)
    (hpost : postClock E rho y (SA.voteTime p.toParams s) = some nd) :
    W ∈ FGSA.voterBlocks p nd.st s := by
  rw [postClock_def, preTick_def] at hpost
  cases hk : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams s) with
  | none => simp only [hk, Option.map_none, reduceCtorEq] at hpost
  | some k =>
    rw [hk] at hpost
    have hnd := Option.some.inj hpost
    subst nd
    have htick := V2.D.Run.tickIdx?_spec hk
    have hjk : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick d).mp (by omega)
      exact (not_lt.mpr hdt) hlt
    let st := storeAt p c E rho (V2.D.Run.idxBefore rho d) y
    let st' := storeAt p c E rho k y
    have hGSTcut : E.t_GST + 1 ≤ d := by
      have := healing_recovery_start_lower (p := p) E
      have hd1 : (1 : Int) ≤ p.Δ :=
        Int.add_one_le_iff.mpr (show (0 : Int) < p.Δ from p.deltaPos)
      linarith
    have hc := fgsa_store_cumulative_on p c E rho hjk y
      (healing_recovery_epoch E rho hrec hy (fgsa_idxBefore_mono rho hGSTcut))
    have hb : eraseFG W ∈ st.base.blocks :=
      (storeBundle_stateBefore E rho _ y).cstore.baseTree _ |>.mpr ⟨W, hW, rfl⟩
    have hkeys := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho d) y).«meta».stampKeys
    have hfind : ∃ stamp, st.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      have hm : eraseFG W ∈ st.base.blockStamp.map Prod.fst := hkeys ▸ hb
      cases hf : st.base.blockStamp.find? (fun row => row.1 == eraseFG W) with
      | none =>
        obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
        have hn := List.find?_eq_none.mp hf row hr
        rw [he, beq_self_eq_true] at hn
        contradiction
      | some row =>
        have he : row.1 = eraseFG W := by simpa only [beq_iff_eq] using List.find?_some hf
        exact ⟨row.2, by simp only [← he]⟩
    obtain ⟨stamp, hf⟩ := hfind
    have hstamp : stamp < d := by
      have hm : eraseFG W ∈ (rho.stateBeforeTime E d y).st.base.blocks := by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
        exact hb
      have ht := fgsa_block_stamp_before_read E rho hs y d hdpos (eraseFG W) hm
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at ht
      change GridCO.stampBlock st.base (eraseFG W) < d at ht
      unfold GridCO.stampBlock at ht
      rw [hf] at ht
      exact ht
    have hkept : st'.base.blockStamp.find? (fun row => row.1 == eraseFG W) =
        some (eraseFG W, stamp) := by
      obtain ⟨tail, htail⟩ := hc.2.2.1
      change (storeAt p c E rho k y).base.blockStamp.find? _ = _
      rw [← htail, List.find?_append, hf]
      rfl
    change W ∈ FGSA.voterBlocks p (clock p st' (SA.voteTime p.toParams s)) s
    apply Finset.mem_filter.mpr
    refine ⟨?_, Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ?_))⟩
    · change W ∈ (clock p st' (SA.voteTime p.toParams s)).fg.TF.filter _
      apply Finset.mem_filter.mpr
      rw [clock_fg]
      refine ⟨hc.1 hW, ?_⟩
      have hktime : k ≤ timeIdx rho (SA.voteTime p.toParams s) := by
        have hklt := (Gen.V2.Duty.index_lt_idxBefore_iff hs htick
          (SA.voteTime p.toParams s + 1)).mpr (Int.lt_add_one_iff.mpr le_rfl)
        have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + 1) =
            timeIdx rho (SA.voteTime p.toParams s) := by
          dsimp only [timeIdx]
          simp only [V2.D.Run.idxBefore_def, Int.lt_add_one_iff]
        exact (hcut ▸ hklt).le
      obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho k y).cstore.fg.Fcar
      have hlt := (healing_phase_finality_le p c E rho hK hKF).trans_lt
        (healing_phase_justified_lt p c E rho k y)
      obtain ⟨Q, hQ, hhQ⟩ := healing_phase_frontier_witness p c E rho k y
      have hQ' := (fgsa_store_durable p c E rho hktime y).1 hQ
      have hb := (hhQ ▸ healing_phase_height_le p c E rho hQ').trans
        ((healing_phase_local_le_frontier p c E rho hy).trans hcap)
      exact crossing k k y y K W hy le_rfl hK hKF ⟨hy, hc.1 hW⟩ (hlt.trans_le hb)
    · have he : GridCO.stampBlock (clock p st' (SA.voteTime p.toParams s)).base (eraseFG W) =
          stamp := by
        unfold GridCO.stampBlock
        rw [(clock_cumulative p _ _).2.2.1, hkept]
        rfl
      rw [he]
      exact hstamp.trans_le hdf

/-- The strict event receipt uses durable storage and the selected receiver floor. -/
theorem healing_phase_block_receipt_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    {i : Nat} {ev : V2.Event V (Obj p)} {x : V} {W : FGBlock (Fin p.n)} {m : Nat}
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest)
    (hready : recoveryStart p E ≤ ev.time)
    (hafter : W ∈ (storeAt p c E rho (i + 1) x).fg.TF) (hh : (heightView p W).h = m)
    (hhor : ev.time + p.Δ ≤ rho.horizon) {y : V} (hy : y ∈ rho.honest) :
    let j := V2.D.Run.idxBefore rho (ev.time + p.Δ)
    i < j ∧ j ≤ rho.events.length ∧
      (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + p.Δ) ∧
      (W ∈ (storeAt p c E rho j y).fg.TF ∨ m < frontierAtIdx p c E rho j) := by
  let j := V2.D.Run.idxBefore rho (ev.time + p.Δ)
  have hs := hrec.base.valid.toScheduleWellFormed
  have hij : i < j := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr
    (lt_add_of_pos_right _ p.deltaPos)
  refine ⟨hij, List.length_filter_le .., ?_, ?_⟩
  · intro l e hl he
    exact (Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mp hl
  · by_cases hrise : m < frontierAtIdx p c E rho j
    · exact Or.inr hrise
    left
    have hWj := (fgsa_store_durable p c E rho (Nat.succ_le_of_lt hij) x).1 hafter
    obtain ⟨K, hK, hKF⟩ := (storeBundle_stateBefore E rho j y).cstore.fg.Fcar
    have hlow := (healing_phase_finality_le p c E rho hK hKF).trans_lt
      (healing_phase_justified_lt p c E rho j y)
    have hcap := healing_phase_local_le_frontier p c E rho (i := j) hy
    have hFW := crossing j j y x K W hy le_rfl hK hKF ⟨hx, hWj⟩
      (by simp only [Height] at *; omega)
    have hf : Block.Preceq (eraseFG (rho.stateBeforeTime E
        (ev.time + p.Δ) y).st.fg.F) (eraseFG W) := by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
      exact eraseFG_preceq hFW
    have hservice := healing_target_receipt_at_event E rho hrec hi hready hhor
      (show HeldAt p c E rho (i + 1) x W from ⟨hx, hafter⟩) hy hf
    have hheld := healing_held_block_receipt_on p c E rho hrec.base.valid
      hrec.base.receiptIdealization W (ev.time + p.Δ) y hy hservice
    change W ∈ (rho.stateBeforeTime E (ev.time + p.Δ) y).st.fg.TF at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hheld
    exact hheld

theorem healing_evidence_spread_recovery (crossing : RXing p c E rho)
    {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (_mono : RMonoAll p c E rho)
    (i : Nat) (ev : V2.Event V (Obj p)) (x : V) (W : FGBlock (Fin p.n)) (m : Nat)
    (hi : rho.events[i]? = some ev) (hx : x ∈ rho.honest) (hready : recoveryStart p E ≤ ev.time)
    (_hm : 1 ≤ m) (_hfront : frontierAtIdx p c E rho (i + 1) = m)
    (_hbefore : W ∉ (storeAt p c E rho i x).fg.TF)
    (hafter : W ∈ (storeAt p c E rho (i + 1) x).fg.TF) (hh : (heightView p W).h = m)
    (_hroots : NamedReceiptRootCollisionFree p c E rho) :
    (ev.time + p.Δ ≤ rho.horizon → ∀ y ∈ rho.honest,
      ∃ j, i < j ∧ j ≤ rho.events.length ∧
        (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + p.Δ) ∧
        (W ∈ (storeAt p c E rho j y).fg.TF ∨ m < frontierAtIdx p c E rho j)) ∧
    (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
      SA.voteTime p.toParams s ≤ rho.horizon →
      postClock E rho y (SA.voteTime p.toParams s) = some nd →
      (∃ j, i < j ∧ j ≤ timeIdx rho (SA.voteTime p.toParams s) ∧
        m < frontierAtIdx p c E rho j) ∨ W ∈ FGSA.voterBlocks p nd.st s) := by
  have hvalid := hrec.base.valid
  have receipt (y : V) := healing_phase_block_receipt_recovery E rho hrec crossing
    (y := y) hi hx hready hafter hh
  constructor
  · intro hhor y hy
    exact ⟨_, receipt y hhor hy⟩
  · intro y s nd hy htime hhor hpost
    have hdt : ev.time + p.Δ ≤ SA.voteTime p.toParams s := by
      have := p.deltaPos
      simp only [Time] at *
      omega
    obtain ⟨hij, _, _, hw⟩ := receipt y (hdt.trans hhor) hy
    rcases hw with hw | hrise
    · by_cases hrise : m < frontierAtIdx p c E rho (timeIdx rho (SA.voteTime p.toParams s))
      · exact Or.inl ⟨_, hij.trans_le (healing_phase_idx_le_time p c rho hdt),
          le_rfl, hrise⟩
      right
      change W ∈ phaseVoterBlocks p nd s
      apply FGCompose.healing_phase_head_inclusion
        (R := p0d1ServiceCore p c) (E := E) (rho := rho)
        (O := p0d1ServiceObservations p c) (Jst := recoveryStart p E)
        (T := p0d1ServiceTiming p) (voterBlocks := phaseVoterBlocks p)
        (fun _ _ _ _ _ hr hp hy hc ht hf hW hpost =>
          phase_service_frozen_mem E rho crossing hvalid.toScheduleWellFormed hrec
            hr hp hy hc ht hf hW hpost)
        (hready.trans (le_add_of_nonneg_right p.deltaPos.le))
        (lt_add_of_le_of_pos (hvalid.in_horizon _ (List.mem_of_getElem? hi)).1 p.deltaPos)
        hy (hh ▸ Nat.le_of_not_gt hrise) hdt ?_ hw hpost
      cases s with
      | zero =>
        change ev.time + 3 * p.Δ ≤ 4 * p.Δ * (0 : Int) + p.Δ at htime
        have hzero : (0 : Int) ≤ ev.time :=
          (hvalid.in_horizon _ (List.mem_of_getElem? hi)).1
        have hpos : (0 : Int) < p.Δ := p.deltaPos
        have htime' : (ev.time : Int) + 3 * (p.Δ : Int) ≤ p.Δ := by
          simpa only [mul_zero, zero_add] using htime
        linarith only [htime', hzero, hpos]
      | succ s =>
        change ev.time + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
        change ev.time + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at htime
        push_cast at htime
        simp only [Time] at *
        linarith
    · exact Or.inl ⟨_, hij, healing_phase_idx_le_time p c rho hdt, hrise⟩

/-- Recovery produces all five RPhase clauses across finite sleep runs.
Only the named all-restart monotonicity and crossing channels remain as inputs. -/
theorem healing_rPhase_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) : RPhase p c E rho := by
  let O : FGCompose.FGObservationReads (p0d1ServiceCore p c) :=
    ⟨heightView p, finalityView p, (fun nd => FGSA.controls p nd.st),
      fun nd X => domainR p nd.st X⟩
  have obs : FGCompose.FGObservationLaws (p0d1ServiceCore p c) O :=
    ⟨fun _ => rfl, fun _ _ => rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b m hab hb hm hfixed
    exact FGCompose.healing_phase_order_of_crossing_all
      (R := p0d1ServiceCore p c) (E := E) (rho := rho) (O := O) (Ef := p.E)
      (obs := obs) (cert := fgCertificateLaws p)
      (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
      (justif := fgJustificationLaws p)
      (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
      crossing ⟨mono⟩ a b m hab hb hm hfixed
  · intro i ev x W m hi hx hready hm hfront hbefore hafter hh
    exact healing_evidence_spread_recovery E rho crossing hrec mono i ev x W m
      hi hx hready hm hfront hbefore hafter hh hrec.base.receiptIdealization
  · intro i ev v m kind hi _heff hready hu hv hm hfront hkind hquiet
    obtain ⟨J, h⟩ := healing_settle_start_on p c E rho crossing hrec.base.valid mono hrec
      (fun _ ht => healing_ready_read_cutoff E ht)
      (healing_phase_witness_receipts_recovery E rho hrec) hrec.base.receiptIdealization
      i ev v m kind hi hready hu hv hm hfront hkind hquiet
    refine ⟨J, ?_⟩
    cases kind <;> exact h
  · intro u v m J contested hready hp i x hui hiv hx
    have result := FGCompose.healing_settled_frame_ready
      (R := p0d1ServiceCore p c) (E := E) (rho := rho) (O := O) (Ef := p.E)
      (obs := obs) (cert := fgCertificateLaws p)
      (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
      (Jst := recoveryStart p E) crossing u v m J contested hready
      (by cases J <;> exact hp) i x hui hiv hx
    cases J <;> exact result
  · intro i x m X B hx hi hm hH hX hB hpath hh
    exact FGCompose.healing_frontier_mem
      (R := p0d1ServiceCore p c) (E := E) (rho := rho) (O := O) (Ef := p.E)
      (obs := obs) (cert := fgCertificateLaws p)
      (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
      crossing i x m X B hx hi hm hH hX hB hpath hh

end AvailableChain.FGSA.Run
end

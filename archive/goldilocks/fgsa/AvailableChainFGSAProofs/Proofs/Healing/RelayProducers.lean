module
public import AvailableChainFGSAProofs.Proofs.Healing.HeadRelay
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- An accepted HEAD is served at a recovery anchor and kept until the actual read.
The original send time and the receiver's local label epoch remain explicit. -/
theorem healing_head_accepted_receipt {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i it j : Nat} {x v : V}
    {s : Slot} {q : Fin p.n} {b : BlockId} {send a T : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x T))
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hBound : ∀ k w, k < i → rho.events[k]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s)
    (hacc : rho.acceptsAt E j v (ofHead p ⟨.seat (.head s) q, b⟩) send)
    (hsa : send ≤ a) (hpa : SA.proposalTime p.toParams s ≤ a)
    (hGST : E.t_GST ≤ a) (haT : a + p.Δ ≤ T) (hslot : p.slotOf T ≤ s + 1) :
    HeadRelayLocalServiceScope E rho s q b (a + p.Δ) i x := by
  have hV := hrec.base.valid
  have hS := hV.toScheduleWellFormed
  have hh := (hV.in_horizon _ (List.mem_of_getElem? hi)).2
  have hdi : V2.D.Run.idxBefore rho (a + p.Δ) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge haT) ((Gen.V2.Duty.index_lt_idxBefore_iff hS hi _).mp
      (Nat.lt_of_not_ge hn))
  have hai : V2.D.Run.actionCut rho a ≤ i :=
    (Gen.V2.Duty.actionCut_le_idxBefore hS (lt_add_of_pos_right a p.deltaPos)).trans hdi
  have hist := fgsa_head_historySafeAt_of_tick E rho hV hrec.base.restartsAtWakes hit
    (fun k w hk he => hBound k w (hk.trans_le hai) he) q b
  have hscope : HeadRelayLocalServiceScope E rho s q b (a + p.Δ) i x := by
    refine ⟨hdi, ?_, ?_, ?_⟩
    · apply healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho ?_)
      have hpos := p.deltaPos
      dsimp [Time] at *
      omega
    · have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hS hdi x
      rw [fgsa_clock_now p c (rho.stateBefore E _ x),
        fgsa_clock_now p c (rho.stateBefore E i x),
        Gen.V2.Duty.stateBefore_idxBefore E rho (a + p.Δ) hS] at hm
      exact (Internal.slotOf_mono (p := p)
        (hm.trans (fgsa_preTick_now_le E rho hS hi))).trans hslot
    · intro hNX
      let dl := fun t => max t E.t_GST + p.Δ
      have he : dl a = a + p.Δ := by dsimp only [dl]; rw [max_eq_left hGST]
      have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
        (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
          rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
      refine Or.inr ⟨send, fgsa_head_service_at_anchor hV hrec.base.delta dl rho.horizon hx
        (Or.inr ⟨v, hv, j, hacc⟩) hD hsa (E.t_GST_nonneg.trans hGST) hpa
        (he ▸ lt_add_of_pos_right a p.deltaPos) (he ▸ haT.trans hh)
        (he ▸ haT.trans hh) he.le ?_ hist
        (healing_recovery_action_epoch hrec hx hGST _) (he ▸ hNX)⟩
      intro t hat htd
      exact hrec.awake x hx t (hGST.trans hat) (htd.le.trans (he ▸ haT.trans hh))
  exact hscope

/-- Source clean support has strict-freeze read evidence at the joined next voter. -/
theorem healing_head_forward_receipt {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {ix iy : Nat} {x y : V} {s : Slot}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hy : y ∈ rho.honest) (hG : enabledGateAt p c E rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (q : Fin p.n) (b : BlockId)
    (ho : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      GridCO.cleanSupport p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s) :
    HeadRelayLocalServiceScope E rho s q b (SA.freezeTime p.toParams s) iy y := by
  obtain ⟨j, _, send, hacc, hsend⟩ := healing_head_support_accepted
    hrec.base.valid hrec.base.restartsAtWakes hrec.base.delta hx hG q b ho
  obtain ⟨it, hit⟩ := healing_head_proposal_tick hrec.base.valid hrec.base.delta hy hiy hJ
  have he : SA.earlyTime p.toParams s + p.Δ = SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  rw [← he]
  apply healing_head_accepted_receipt E rho hrec hy hx hiy hit
    (healing_head_vote_restart_bound hrec.base.valid.toScheduleWellFormed hiy hJ)
    hacc hsend.le
  · change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · apply hSync.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  · exact ((fgsa_postClock_slot (c := c) (rho.stateBefore E iy y) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ (s + 1))).le

/-- Every stored release witness relays before the enabled source gate. -/
theorem healing_head_stored_backward_receipt {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {ix iy : Nat} {x y : V} {s : Slot}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hy : y ∈ rho.honest) (hG : enabledGateAt p c E rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (q : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      (storeAt p c E rho iy y).base.votes) :
    HeadRelayLocalServiceScope E rho s q b (SA.gateTime p.toParams s) ix x := by
  obtain ⟨j, _, send, hacc, ht⟩ := fgsa_vote_accepted_before_head_read_on E rho
    hrec.base.valid hrec.base.restartsAtWakes hrec.base.delta iy y s hiy hy hJ q b hm
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hpT : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  obtain ⟨it, hit⟩ := List.mem_iff_getElem?.mp (hrec.base.valid.tick_total x hx _ hpub hp0
    (hpT.trans (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hG.1)).2)
    (fgsa_enabledGate_awakeClosed hrec.base.valid hx hG _ hp0 le_rfl hpT))
  have he : SA.voteTime p.toParams (s + 1) + p.Δ = SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  rw [← he]
  apply healing_head_accepted_receipt E rho hrec hx hy hG.1 hit
    (healing_head_gate_restart_bound hrec.base.valid.toScheduleWellFormed hG) hacc ht.le
  · change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  · apply hSync.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  · exact he.le
  · exact ((fgsa_postClock_slot (c := c) (rho.stateBefore E ix x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)).le


private theorem relay_producer_shape (o : GridCO.Wire p.n .root) (s : Slot) (q : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hq : GridCO.headSeat? o = some q) :
    ∃ b, o = ⟨.seat s q, .head b⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r k b
  have hr := Option.some.inj hl
  have hk := Option.some.inj hq
  subst r; subst k
  exact ⟨b, rfl⟩

open V2.D.Engine in
/-- An honest recovery tick has no own restart at its time, so its strict read agrees. -/
theorem healing_tick_time_read_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {v : V} {t : Time}
    (hx : v ∈ rho.honest) (hGST : E.t_GST < t)
    (hi : rho.events[i]? = some (.tick v t)) :
    rho.stateBefore E i v = rho.stateBeforeTime E t v := by
  have hs := hrec.base.valid.toScheduleWellFormed
  let q := fun e : V2.Event V (fgsa p c).Object => decide (e.time < t)
  have hd : ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key →
      q f = true → q e = true := by
    intro e f hk hf
    exact decide_eq_true (lt_of_le_of_lt (time_le_of_key_le _ _ hk) (of_decide_eq_true hf))
  have hf := filter_eq_take hs q hd
  have hni : (rho.events.filter q).length ≤ i := by
    by_contra hc
    have hlt : i < (rho.events.filter q).length := by omega
    have hm : V2.Event.tick v t ∈ rho.events.filter q := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have ht := of_decide_eq_true (List.mem_filter.mp hm).2
    exact lt_irrefl t ht
  change _ = ((rho.events.filter q).foldl (V2.D.World.step E rho) V2.D.World.init) v
  rw [hf]
  apply stateBefore_other_node E rho hni
  intro j e hj hji hget hnode
  have hl : t ≤ e.time := by
    have := filter_false_of_index_ge hs q hd hj hget
    simpa [q] using this
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk : e.key ≤ (V2.Event.tick v t : V2.Event V (fgsa p c).Object).key := by
    simpa [hje, hie] using (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  have ht : e.time = t := le_antisymm (time_le_of_key_le _ _ hk) hl
  have he : e = .tick v t := by
    cases e with
    | restart u t' =>
        dsimp only [V2.Event.node] at hnode
        subst hnode
        have ht' : t' = t := ht
        subst t'
        have hb := healing_recovery_restart_bound E rho hrec hx hget
        exact (not_lt_of_ge hb hGST).elim
    | tick u t' =>
        dsimp only [V2.Event.node] at hnode
        dsimp only [V2.Event.time] at ht
        rw [hnode, ht]
    | deliver u o t' =>
        dsimp only [V2.Event.time] at ht
        subst t'
        dsimp only [V2.Event.key, V2.Event.time, V2.Event.phase] at hk
        simp [Prod.Lex.toLex_le_toLex] at hk
  have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
  omega

/-- Read evidence at an actual recovery tick supplies the exact RELAY-LOCAL interface. -/
theorem healing_head_local_service_of_receipt {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    {q : Fin p.n} {b : BlockId} {t : Time}
    (hx : x ∈ rho.honest) (hi : rho.events[i]? = some (.tick x t))
    (hGST : E.t_GST < t) (hslot : p.slotOf t ≤ s + 1)
    (receipt : HeadRelayReceiptScope E rho s q b t i x) :
    HeadRelayLocalServiceScope E rho s q b t i x := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have he := healing_tick_time_read_recovery E rho hrec hx hGST hi
  have hdi : V2.D.Run.idxBefore rho t ≤ i := by
    by_contra hn
    exact (lt_irrefl t) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi t).mp (Nat.lt_of_not_ge hn))
  refine ⟨hdi, ?_, ?_, ?_⟩
  · apply healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho ?_)
    dsimp [Time] at *
    omega
  · rw [← he]
    exact (Internal.slotOf_mono (p := p) (fgsa_preTick_now_le E rho hs hi)).trans hslot
  · intro hNX
    rw [← he] at hNX ⊢
    by_cases hm : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        (rho.stateBefore E i x).st.base.votes
    · exact Or.inl (decide_eq_true hm)
    · rcases receipt.service with hm' | hc
      · exact (hm hm'.1).elim
      · obtain ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩ := hc
        have put (w : GridCO.Wire p.n .root) (hw : w ∈ (rho.stateBefore E i x).st.base.votes)
            (hl : GridCO.headLabel? w = some s) :
            w ∈ GridCO.votesAt (rho.stateBefore E i x).st.base s :=
          List.mem_filter.mpr ⟨hw, by simpa only [hl] using beq_self_eq_true (some s)⟩
        have hcap := (Gen.AC.Root.cap_pair _ q).mpr
          ⟨u, put u hu hlu, v, put v hv hlv, hne, hku, hkv⟩
        change GridCO.excludes p.toParams.engine (rho.stateBefore E i x).st.base
          (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) = false at hNX
        simp only [GridCO.excludes, decide_eq_false hm, Bool.not_false, hcap,
          Bool.or_true, Bool.true_and] at hNX
        cases hNX

/-- A carried HEAD relays by its accepted vote or by both accepted cap witnesses.
The third, refused object itself needs no honest acceptance. -/
theorem healing_head_backward_receipt {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {ix iy : Nat} {x y : V} {s : Slot}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hy : y ∈ rho.honest) (hG : enabledGateAt p c E rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (q : Fin p.n) (b : BlockId)
    (ho : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        GridCO.votesAt (storeAt p c E rho iy y).base s ∨
      (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        headVotes p (clock p (storeAt p c E rho iy y)
          (SA.voteTime p.toParams (s + 1))) (s + 1)) :
    HeadRelayLocalServiceScope E rho s q b (SA.gateTime p.toParams s) ix x := by
  rcases ho with hm | ho
  · exact healing_head_stored_backward_receipt E rho hrec hSync hx hy hG hiy hJ q b
      (List.mem_filter.mp hm).1
  · have localScope := healing_head_local_receipt hrec.base.valid hrec.base.delta hy hiy hJ
      q b ho
    rcases localScope.service with hm | hc
    · exact healing_head_stored_backward_receipt E rho hrec hSync hx hy hG hiy hJ q b hm.1
    · obtain ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩ := hc
      obtain ⟨bu, rfl⟩ := relay_producer_shape u s q hlu hku
      obtain ⟨bv, rfl⟩ := relay_producer_shape v s q hlv hkv
      have hsU := healing_head_stored_backward_receipt E rho hrec hSync hx hy hG hiy hJ
        q bu hu
      have hsV := healing_head_stored_backward_receipt E rho hrec hSync hx hy hG hiy hJ
        q bv hv
      have result : HeadRelayReceiptScope E rho s q b (SA.gateTime p.toParams s) ix x := by
        constructor
        rcases (hsU.toReceiptScope E rho hrec.base.valid s q bu _ ix x hx).service with hmU | hcU
        · rcases (hsV.toReceiptScope E rho hrec.base.valid s q bv _ ix x hx).service with
            hmV | hcV
          · exact Or.inr ⟨_, hmU.1, _, hmV.1, hne, rfl, rfl, rfl, rfl, hmU.2, hmV.2⟩
          · exact Or.inr hcV
        · exact Or.inr hcU
      apply healing_head_local_service_of_receipt E rho hrec hx hG.1 _ _ result
      · apply hSync.trans_lt
        change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
        linarith [p.deltaPos]
      · exact ((fgsa_postClock_slot (c := c) (rho.stateBefore E ix x) _).2.symm.trans
          (fgsa_gate_slot (c := c) _ s)).le

/-- P2 local service permits the late processed HEAD and the refused carried cap. -/
theorem healing_head_local_service_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (q : Fin p.n) (b : BlockId)
    (ho : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      headVotes p (clock p (rho.stateBefore E i x).st
        (SA.voteTime p.toParams (s + 1))) (s + 1)) :
    HeadRelayLocalServiceScope E rho s q b (SA.voteTime p.toParams (s + 1)) i x := by
  apply healing_head_local_service_of_receipt E rho hrec hx hi _ _
    (healing_head_local_receipt hrec.base.valid hrec.base.delta hx hi hJ q b ho)
  · apply hSync.trans_lt
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  · exact ((fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ (s + 1))).le

end AvailableChain.FGSA.Run
end

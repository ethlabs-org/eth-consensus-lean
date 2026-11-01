module
public import AvailableChainFGSAProofs.Proofs.Outage.RelayKernel
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint -- shake: keep

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

theorem inclusion_service_duty_receiver (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {r : Slot} {t : Time}
    (he : rho.events[i]? = some (.tick x t))
    (hJ : joinedAt p E rho x (r + 1) t) :
    (∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams r) ∧
    AwakeClosed E x (SA.proposalTime p.toParams r) t := by
  constructor
  · intro j w hji hj
    have ht : w ≤ t := by
      by_contra hn
      have hij := V2.D.Engine.eventIndex_lt_of_time_lt hV.toScheduleWellFormed he hj
        (lt_of_not_ge hn)
      omega
    have hb := hJ.2.2 w (hV.in_horizon _ (List.mem_of_getElem? hj)).1 ht
      (List.mem_of_getElem? hj)
    change w ≤ 4 * p.Δ * (r : Int)
    change w ≤ 4 * p.Δ * (((r + 1 : Nat) : Int) - 1) at hb
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hb
  · intro u h0 hu hut
    apply fgsa_awake_of_joinedAt E rho x (r + 1) t u hJ h0 _ hut
    change 4 * p.Δ * (((r + 1 : Nat) : Int) - 1) ≤ u
    change 4 * p.Δ * (r : Int) ≤ u at hu
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hu


/-- A joined duty supplies exact proposal service at a public local anchor. -/
theorem inclusion_service_local_proposal_service (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hmono : RMonoAll p c E rho)
    {i : Nat} {x v : V} {r s : Slot} {N : NamedProposal p.n} {t send a : Time}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x t)) (hJ : joinedAt p E rho x (r + 1) t)
    (hT : rho.emits E v (ofWire p ⟨.proposer s, .proposal N⟩) send ∨
      ∃ j, rho.acceptsAt E j v (ofWire p ⟨.proposer s, .proposal N⟩) send)
    (hsa : send ≤ a) (h0 : 0 ≤ a) (hpa : SA.proposalTime p.toParams r < a)
    (hpub : V2.PublicTime E a) (hGST : E.t_GST ≤ a) (hat : a + p.Δ ≤ t)
    (hAct : fgsaAdmissionTime p (ofWire p ⟨.proposer s, .proposal N⟩) ≤ a)
    (hF : Block.Preceq (F_at p c E rho i x) N.erase) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send
      (a + p.Δ) x) := by
  have hS := hV.toScheduleWellFormed
  let o : Obj p := ofWire p ⟨.proposer s, .proposal N⟩
  have hd : (toWire p o).decode = some (.block s N) := by rw [toWire_ofWire]; rfl
  obtain ⟨hBound, hAw⟩ := inclusion_service_duty_receiver hV he hJ
  have had : a < a + p.Δ := lt_add_of_pos_right _ p.deltaPos
  have hdi : rho.idxBefore (a + p.Δ) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge hat) ((Gen.V2.Duty.index_lt_idxBefore_iff hS he _).mp
      (Nat.lt_of_not_ge hn))
  have hRF : V2.D.restartFree rho x (rho.actionCut a) (rho.idxBefore (a + p.Δ)) := by
    intro j w haj hji hj
    have hb := hBound j w (hji.trans_le hdi) hj
    have hja := (V2.D.Engine.index_lt_actionCut_iff hS hj a).mpr (Or.inl (hb.trans_lt hpa))
    omega
  have hcompat : Block.Compatible N.erase
      (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) := by
    have hb := block_preceq_trans (eraseFG_preceq (hmono _ i x hx hdi).1) hF
    change Block.Preceq (eraseFG (rho.stateBefore E (rho.idxBefore (a + p.Δ)) x).st.fg.F)
      N.erase at hb
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hb
    exact block_compatible_of_common (block_preceq_refl _) hb
  have hNX : (fgsa p c).excludes (rho.stateBeforeTime E (a + p.Δ) x) o = false := by
    change excludesS p _ o = false
    dsimp only [excludesS]
    rw [hd]
    change N.erase.compatible (eraseFG (rho.stateBeforeTime E (a + p.Δ) x).st.fg.F) =
      true at hcompat
    simp only [blockExcluded, activeCompatible, hcompat, Bool.not_true, Bool.false_or]
    exact fgsa_trigger_invalid_false E rho o send s N (hT.elim
      (fun hem => Or.inl ⟨v, hv, hem⟩) (fun ha => Or.inr ⟨v, hv, ha⟩)) hd _
  have hmax := max_eq_left hGST
  refine ⟨{
    dl := fun z => max z E.t_GST + p.Δ, cut := rho.horizon, anchor := a
    within := by
      simpa only [hDelta] using
        (Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _))
    ready := ⟨v, hv, hT, by
      intro u hau hud
      apply hAw u (h0.trans hau) (hpa.le.trans hau)
      have hh : u < a + p.Δ := by simpa only [hmax] using hud
      exact hh.le.trans hat⟩
    send_le := hsa, nonneg := h0
    later := (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos)
    cut_le := by simpa only [hmax] using hat.trans (hV.in_horizon _ (List.mem_of_getElem? he)).2
    horizon := by simpa only [hmax] using hat.trans (hV.in_horizon _ (List.mem_of_getElem? he)).2
    freeze_le := by simp only [hmax, le_refl]
    history := fgsa_historySafeAt_of_proposal x o a hd
    epoch := hRF
    handlers := by
      intro j u hau _ hh
      obtain ⟨parent, hj, hhandles⟩ := hh
      have hp := proposal_handlesS_direct _ parent o s N hd hhandles
      subst parent
      refine ⟨hV.wire j x o u hj, hV.deps j x o u hj, ?_⟩
      have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hV hj hpub h0 hau
      rw [fgsa_clock_now p c (rho.stateBefore E j x)] at hn
      exact hAct.trans hn
    not_excluded := by simpa only [hmax] using hNX }⟩

/-- An original accepted named body gives target service at the current duty. -/
theorem inclusion_service_accepted_target_service (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hmono : RMonoAll p c E rho)
    {i j : Nat} {x v : V} {r : Slot} {t send a : Time} {o : Obj p} {B : Block}
    (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    (he : rho.events[i]? = some (.tick x t)) (hJ : joinedAt p E rho x (r + 1) t)
    (hb : blockOf? p o = some B) (hacc : rho.acceptsAt E j v o send)
    (hsa : send ≤ a) (h0 : 0 ≤ a) (hpa : SA.proposalTime p.toParams r < a)
    (hpub : V2.PublicTime E a) (hGST : E.t_GST ≤ a) (hat : a + p.Δ ≤ t)
    (hF : Block.Preceq (F_at p c E rho i x) B) :
    TargetReceiptService E rho B (a + p.Δ) x := by
  have hdec : ∃ s N, o = ofWire p ⟨.proposer s, .proposal N⟩ ∧ N.erase = B := by
    unfold blockOf? at hb
    cases hd : (toWire p o).decode with
    | none => simp only [hd, reduceCtorEq] at hb
    | some m =>
      cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at hb
      rename_i s N
      refine ⟨s, N, ?_, hb⟩
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
  obtain ⟨s, N, rfl, rfl⟩ := hdec
  have hAct := timely_of_relay_retained E rho (fgsaTimelyClock p c) (fgsaAdmitSound p c)
    hV.toScheduleWellFormed (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
    (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
      fgsa_admissionTime_public p E hDelta obj) v j _ send hacc
  rw [fgsaTimelyClock_actTime] at hAct
  exact fgsa_target_service_of_proposal E rho s N send (a + p.Δ) x
    (inclusion_service_local_proposal_service hV hDelta hsync hmono hx hv he hJ
    (Or.inr ⟨j, hacc⟩) hsa h0 hpa hpub hGST hat
    (hAct.trans ((Gen.V2.Duty.pubFloor_le E send).trans hsa)) hF)

/-- Receiver services cover all retained score inputs in their actual duty epochs. -/
theorem inclusion_service_retained_score_scope (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hmono : RMonoAll p c E rho)
    {ip ih : Nat} {x y : V} {r : Slot}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (r + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (hX : joinedAt p E rho x (r + 1) (SA.proposalTime p.toParams (r + 1)))
    (hY : joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams r) (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (storeAt p c E rho ip x) (SA.proposalTime p.toParams (r + 1)))
      (clock p (storeAt p c E rho ih y) (SA.voteTime p.toParams (r + 1))) D) :
    ScoreServiceScope E rho ip ih x y (r + 1) D := by
  have hS := hV.toScheduleWellFormed
  obtain ⟨hBX, hAX⟩ := inclusion_service_duty_receiver hV hip hX
  obtain ⟨hBY, _⟩ := inclusion_service_duty_receiver hV hih hY
  have hxf : Block.Preceq (F_at p c E rho ip x) D := by
    change Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) D
    simpa only [clock_fg] using hgeom.source_floor
  have hyf : Block.Preceq (F_at p c E rho ih y) D := by
    change Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) D
    simpa only [clock_fg] using hgeom.target_floor
  have hp : SA.proposalTime p.toParams r < SA.proposalTime p.toParams (r + 1) := by
    change 4 * p.Δ * (r : Int) < 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  have hfreeze : SA.proposalTime p.toParams r < SA.freezeTime p.toParams r := by
    change 4 * p.Δ * (r : Int) < 4 * p.Δ * (r : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hpubP : V2.PublicTime E (SA.proposalTime p.toParams (r + 1)) := by
    refine ⟨4 * (r + 1), ?_⟩
    rw [hDelta]
    change 4 * p.Δ * ((r + 1 : Nat) : Int) = _
    push_cast
    ring
  have hpubF : V2.PublicTime E (SA.freezeTime p.toParams r) := by
    refine ⟨4 * r + 3, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (r : Int) + 3 * p.Δ = _
    push_cast
    ring
  have hzeroP : 0 ≤ SA.proposalTime p.toParams (r + 1) := by
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    have hd := p.deltaPos
    positivity
  have hzeroF : 0 ≤ SA.freezeTime p.toParams r := by
    change 0 ≤ 4 * p.Δ * (r : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity
  have hGSTF : E.t_GST ≤ SA.freezeTime p.toParams r := by
    apply hGST.trans
    change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hGSTP : E.t_GST ≤ SA.proposalTime p.toParams (r + 1) := by
    apply hGSTF.trans
    change 4 * p.Δ * (r : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j w hj hji he
    have hb := hBX j w hji he
    have hjp := (Gen.V2.Duty.index_lt_idxBefore_iff hS he _).mpr (hb.trans_lt hp)
    omega
  · intro seat b hm ht hNX
    obtain ⟨it, hit⟩ := inclusion_relay_vote_proposal_tick hV hDelta hy hih hY
    obtain ⟨j, _, send, ha, hsend⟩ := fgsa_vote_accepted_before_local E rho hV hR r hit
      hBY seat b (SA.freezeTime p.toParams r) hpubF hzeroF (by
        simpa only [Nat.add_sub_cancel] using hm) (by
        simpa only [Nat.add_sub_cancel] using ht)
    let a := max send (SA.voteTime p.toParams r)
    have hpa : SA.proposalTime p.toParams r < a := by
      apply lt_of_lt_of_le _ (le_max_right _ _)
      change 4 * p.Δ * (r : Int) < 4 * p.Δ * (r : Int) + p.Δ
      linarith [p.deltaPos]
    have had : a + p.Δ ≤ SA.proposalTime p.toParams (r + 1) := by
      change send < 4 * p.Δ * (r : Int) + 3 * p.Δ at hsend
      change max send (4 * p.Δ * (r : Int) + p.Δ) + p.Δ ≤
        4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      rw [← max_add_add_right]
      apply max_le <;> linarith [p.deltaPos]
    have hslot : p.slotOf (SA.proposalTime p.toParams (r + 1)) ≤ r + 1 := by
      change p.slotOf (4 * p.Δ * ((r + 1 : Nat) : Int)) ≤ r + 1
      simpa only [add_zero] using (slotOf_offset p (r + 1) 0 (by omega)
        (by have hd := p.deltaPos; dsimp [Time] at *; omega)).le
    have hScope := inclusion_relay_head_relay_scope hV hR hDelta hsync hx hy hip hBX hAX hslot
      seat b ha (le_max_left _ _) hpa had le_rfl
      (hV.in_horizon _ (List.mem_of_getElem? hip)).2 (hGST.trans (le_max_right _ _))
    simpa only [Nat.add_sub_cancel] using hScope.service hNX
  · intro B hDB hB
    by_cases hgen : B = .genesis
    · subst B; exact fgsa_target_service_genesis E rho _ _
    obtain ⟨j, hji, send, o, ho, ha⟩ := fgsa_block_accepted_origin E rho ip x B hgen hB
    have hsend : send < SA.proposalTime p.toParams (r + 1) := by
      obtain ⟨parent, hj, _⟩ := ha.1
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      obtain ⟨hpl, hpe⟩ := List.getElem?_eq_some_iff.mp hip
      have hk := List.pairwise_iff_getElem.mp hS.sorted j ip hjl hpl hji
      rw [hje, hpe] at hk
      change toLex (send, (2 : Nat)) ≤ toLex (SA.proposalTime p.toParams (r + 1), 1) at hk
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨_, h⟩
      · exact h
      · omega
    have ht : SA.proposalTime p.toParams (r + 1) + p.Δ =
        SA.voteTime p.toParams (r + 1) := rfl
    rw [← ht]
    exact inclusion_service_accepted_target_service hV hDelta hsync hmono hy hx hih hY ho ha
      hsend.le
      hzeroP hp hpubP hGSTP ht.le (block_preceq_trans hyf hDB)
  · intro B hDB hB hstamp
    by_cases hgen : B = .genesis
    · subst B; exact fgsa_target_service_genesis E rho _ _
    obtain ⟨j, _, send, o, ho, ha, hsend⟩ := fgsa_block_accepted_before E rho hV ih y B
      (SA.freezeTime p.toParams r) hgen hpubF hzeroF hB (by
        simpa only [Nat.add_sub_cancel] using hstamp)
    have ht : SA.freezeTime p.toParams r + p.Δ = SA.proposalTime p.toParams (r + 1) := by
      change 4 * p.Δ * (r : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      ring
    rw [← ht]
    exact inclusion_service_accepted_target_service hV hDelta hsync hmono hx hy hip hX ho ha
      hsend.le
      hzeroF hfreeze hpubF hGSTF ht.le (block_preceq_trans hxf hDB)

/-- An emitted proposal has receiver service through the joined HEAD read. -/
theorem inclusion_service_emitted_proposal_service (hV : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hmono : RMonoAll p c E rho)
    {ip ih : Nat} {x y : V} {s : Slot} {N : NamedProposal p.n}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip)
    (hJ : joinedAt p E rho y s (SA.voteTime p.toParams s))
    (hGST : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hF : Block.Preceq (F_at p c E rho ih y) N.erase) :
    Nonempty (ReceiverService E rho
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p)
      (SA.proposalTime p.toParams s) (SA.voteTime p.toParams s) y) := by
  have hm := hem
  rw [(rho.step_tick_eq E hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hpos : 0 < s := (fgsa_walkRun_proposal_parent p _ s _ N hp.2.2.2.2).1
  have hs : s - 1 + 1 = s := by simp only [Slot] at hpos ⊢; omega
  have h0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have hd := p.deltaPos
    positivity
  have hpa : SA.proposalTime p.toParams (s - 1) < SA.proposalTime p.toParams s := by
    rw [← hs]
    change 4 * p.Δ * ((s - 1 : Nat) : Int) < 4 * p.Δ * ((s - 1 + 1 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  exact inclusion_service_local_proposal_service hV hDelta hsync hmono hy hx hih
    (hs.symm ▸ hJ) (Or.inl ⟨ip, hip, hem⟩) le_rfl h0 hpa hpub hGST le_rfl
    (by exact le_rfl) hF

end AvailableChain.FGSA.Run
end

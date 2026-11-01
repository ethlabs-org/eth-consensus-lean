module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- One receiver is awake and has no restart after the batch label starts. -/
structure ArmingReadWindow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) (C : Time) : Prop where
  honest : x ∈ rho.honest
  awake : AwakeClosed E x (slotStartZ p (s : Int)) C
  epoch : RestartFreeTime rho x (slotStartZ p (s : Int)) C

private theorem arming_proposal_direct_local (st : State p.n) (parent o : Obj p)
    {q : Slot} {N : NamedProposal p.n} (hd : (toWire p o).decode = some (.block q N))
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
        · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofHead] at hd
          rcases w with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd
        · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofRow] at hd
          rcases w with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd


private theorem arming_source_decode_local {o : Obj p} {K : Block}
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


/-- Local services use the batch receiver window and the healthy prefix. -/
theorem arming_fresh_head_service_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} {s : Slot}
    (hw : ArmingReadWindow (c := c) E rho x s (SA.earlyTime p.toParams s))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Fin p.n} {b : BlockId}
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s))
    (hhandlers : ∀ j t, SA.voteTime p.toParams s ≤ t → t < SA.earlyTime p.toParams s →
      V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) t →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofHead p ⟨.seat (.head s) q, b⟩))
    (hnx : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x) (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    Nonempty (FreshHeadService E rho s q b (SA.earlyTime p.toParams s) x) := by
  have hp := h.sleepPre.toHealthyPrefix₂
  have hstart : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    exact le_add_of_nonneg_right p.deltaPos.le
  have hv0 : 0 ≤ SA.voteTime p.toParams s := by
    rw [arming_vote_eq]; have := p.deltaPos; positivity
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := b₀
    within := arming_nonrow_delivery h
    ready := ⟨y, hy, Or.inl he, fun t ht hte => hw.awake t
      (hv0.trans ht) (hstart.trans ht) (by rw [arming_vote_add] at hte; exact hte.le)⟩
    later := lt_add_of_pos_right _ p.deltaPos
    cut_le := by rw [arming_vote_add]; exact hcut
    horizon := by rw [arming_vote_add]; exact hcut.trans hp.cut.2
    freeze_le := (arming_vote_add p s).le
    epoch := by
      apply Gen.V2.Duty.restartFree_actionCut_idxBefore hp.base.valid.toScheduleWellFormed
        (arming_vote_lt_early p s).1
      intro k w hk hv he
      exact hw.epoch w (hstart.trans_lt hv) he.le (List.mem_of_getElem? hk)
    handlers := by simpa only [arming_vote_add] using hhandlers
    not_excluded := by simpa only [arming_vote_add] using hnx }⟩


/-- Local services use the batch receiver window and the healthy prefix. -/
theorem arming_proposal_service_trigger_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} {s : Slot}
    (hw : ArmingReadWindow (c := c) E rho x s (SA.earlyTime p.toParams s))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Slot} {N : NamedProposal p.n}
    {send a : Time} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y
      (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (hsa : send ≤ a) (hstart : slotStartZ p (s : Int) ≤ a)
    (hav : a ≤ SA.voteTime p.toParams s)
    (hhistory : Gen.V2.Duty.HistorySafeAt E rho x
      (ofWire p ⟨.proposer q, .proposal N⟩) a)
    (hhandlers : ∀ j t, a ≤ t → t < a + p.Δ → V2.D.Run.handlesAt E rho j x
      (ofWire p ⟨.proposer q, .proposal N⟩) t →
      (fgsa p c).wellFormed (ofWire p ⟨.proposer q, .proposal N⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofWire p ⟨.proposer q, .proposal N⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofWire p ⟨.proposer q, .proposal N⟩))
    (hnx : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (a + p.Δ) x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send (SA.earlyTime p.toParams s) x) := by
  have hp := h.sleepPre.toHealthyPrefix₂
  have hdeadline : a + p.Δ ≤ SA.earlyTime p.toParams s := by
    rw [← arming_vote_add]
    exact add_le_add hav le_rfl
  have ha : 0 ≤ a := le_trans (by unfold slotStartZ; have hd := p.deltaPos; positivity) hstart
  have hready : Gen.V2.Duty.ReadyTrigger E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send x a (a + p.Δ) := by
    refine ⟨y, hy, he, ?_⟩
    intro t hat htd
    exact hw.awake t (ha.trans hat) (hstart.trans hat) (htd.le.trans hdeadline)
  have hepoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) := by
    apply Gen.V2.Duty.restartFree_actionCut_idxBefore hp.base.valid.toScheduleWellFormed
      (hav.trans_lt (arming_vote_lt_early p s).1)
    intro k w hk haw hwe
    exact hw.epoch w (hstart.trans_lt haw) hwe.le (List.mem_of_getElem? hk)
  exact ⟨{
    dl := fun t => t + p.Δ
    cut := b₀
    anchor := a
    within := arming_nonrow_delivery h
    ready := hready
    send_le := hsa
    nonneg := ha
    later := lt_add_of_pos_right _ p.deltaPos
    cut_le := hdeadline.trans hcut
    horizon := (hdeadline.trans hcut).trans hp.cut.2
    freeze_le := hdeadline
    history := hhistory
    epoch := hepoch
    handlers := hhandlers
    not_excluded := hnx }⟩


/-- Local services use the batch receiver window and the healthy prefix. -/
theorem arming_proposal_anchor_service_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} {s : Slot}
    (hw : ArmingReadWindow (c := c) E rho x s (SA.earlyTime p.toParams s))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Slot} {N : NamedProposal p.n}
    {send : Time} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (ht : send ≤ SA.voteTime p.toParams s)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send (SA.earlyTime p.toParams s) x) := by
  have hV := h.pre.base.valid
  have hS := hV.toScheduleWellFormed
  have hAct : fgsaAdmissionTime p (ofWire p ⟨.proposer q, .proposal N⟩) ≤ send := by
    rcases he with ⟨k, hk, hem⟩ | ⟨k, hacc⟩
    · rw [(V2.D.Run.step_tick_eq E rho hk).2] at hem
      have hf := (fgsa_emits_proposal E rho _ y send q (.proposal N)).mp hem
      change SA.proposalTime p.toParams q ≤ send
      exact hf.2.1.le
    · have hbound := timely_of_relay_retained E rho (fgsaTimelyClock p c)
        (fgsaAdmitSound p c) hS
        (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
        (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
          fgsa_admissionTime_public p E h.pre.base.delta obj) y k _ send hacc
      rw [fgsaTimelyClock_actTime] at hbound
      exact hbound.trans (Gen.V2.Duty.pubFloor_le E send)
  have hStart : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    exact le_add_of_nonneg_right p.deltaPos.le
  apply arming_proposal_service_trigger_window h hw hcut hy he ht hStart le_rfl
    (fgsa_historySafeAt_of_proposal x _ _ rfl)
  · intro j u hvu hue hh
    obtain ⟨parent, hj, hp⟩ := hh
    have hEq := arming_proposal_direct_local _ parent _ rfl hp
    subst parent
    refine ⟨hV.wire j x _ u hj, hV.deps j x _ u hj, ?_⟩
    have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
      refine ⟨4 * s + 1, ?_⟩
      rw [h.pre.base.delta]
      change 4 * p.Δ * (s : Int) + p.Δ = _
      push_cast
      ring
    have h0 : 0 ≤ SA.voteTime p.toParams s := by
      rw [arming_vote_eq]
      have := p.deltaPos
      positivity
    have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hV hj hpub h0 hvu
    change fgsaAdmissionTime p _ ≤ (rho.stateBefore E j x).st.base.now
    rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
    exact (hAct.trans ht).trans hn
  · simpa only [arming_vote_add] using hNX


/-- Local services use the batch receiver window and the healthy prefix. -/
theorem arming_target_service_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} {s : Slot}
    (hw : ArmingReadWindow (c := c) E rho x s (SA.earlyTime p.toParams s))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {K : Block} {i : Nat}
    (hy : y ∈ rho.honest) (hi : rho.events[i]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho i y).base.blocks)
    (hCompat : Block.Compatible K
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.fg.F)) :
    TargetReceiptService E rho K (SA.earlyTime p.toParams s) x := by
  by_cases hgen : K = .genesis
  · subst K
    exact fgsa_target_service_genesis E rho _ x
  obtain ⟨j, hji, send, o, ho, hacc⟩ := fgsa_block_accepted_origin E rho i y K hgen hK
  obtain ⟨q, N, rfl, hNK⟩ := arming_source_decode_local ho
  have hsend : send ≤ SA.voteTime p.toParams s := by
    obtain ⟨parent, hj, _⟩ := hacc.1
    by_contra hn
    have hij := V2.D.Engine.tick_index_lt_delivery E rho
      h.pre.base.valid.toScheduleWellFormed hi hj (le_of_not_ge hn)
    omega
  have hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer q, .proposal N⟩) send :=
    Or.inr ⟨y, hy, j, hacc⟩
  have hNX : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false := by
    change (blockExcluded _ N.erase || invalidForParent p _ N) = false
    rw [fgsa_trigger_invalid_false E rho _ send q N hT rfl]
    change (!activeCompatible _ N.erase || false) = false
    have hc : activeCompatible
        (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st N.erase = true := by
      change Block.compatible N.erase
        (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.fg.F) = true
      rw [hNK]
      exact hCompat
    rw [hc]
    rfl
  rw [← hNK]
  exact fgsa_target_service_of_proposal E rho q N send _ x
    (arming_proposal_anchor_service_window h hw hcut hy (Or.inr ⟨j, hacc⟩) hsend hNX)


/-- Local services use the batch receiver window and the healthy prefix. -/
theorem arming_head_not_excluded_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} {s : Slot}
    (_hw : ArmingReadWindow (c := c) E rho x s (SA.earlyTime p.toParams s))
    (_hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Fin p.n} {b : BlockId}
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  have hV := h.pre.base.valid
  have hS := hV.toScheduleWellFormed
  obtain ⟨k, hk, hem⟩ := he
  have he' := hem
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at he'
  have hseat := ((fgsa_emits_head E rho _ y _ s q b).mp he').2.2.1
  have hh : rho.seatOf (.base (.head s)) q ∈ rho.honest := hseat ▸ hy
  have h0 : 0 ≤ SA.earlyTime p.toParams s := by
    rw [arming_early_eq]
    have := p.deltaPos
    positivity
  have hnow : (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.base.now ≤
      SA.earlyTime p.toParams s := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    have hSource := V2.D.Engine.stateBefore_now_source_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho (rho.idxBefore (SA.earlyTime p.toParams s)) x
    have hClock := fgsa_clock_now p c (rho.stateBefore E
      (rho.idxBefore (SA.earlyTime p.toParams s)) x)
    simp only [hClock] at hSource
    rcases hSource with hz | ⟨j, hj, hevent | hevent⟩
    · rw [hz]; exact h0
    · exact ((Gen.V2.Duty.index_lt_idxBefore_iff hS hevent _).mp hj).le
    · exact ((Gen.V2.Duty.index_lt_idxBefore_iff hS hevent _).mp hj).le
  have hwindow : (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.slot p ≤ s + 1 := by
    have hslot : p.slotOf (SA.earlyTime p.toParams s) = s :=
      slotOf_offset p s (2 * p.Δ) (by have := p.deltaPos; positivity)
        (by have := p.deltaPos; dsimp [Time] at *; omega)
    exact ((Internal.slotOf_mono (p := p) hnow).trans_eq hslot).trans (Nat.le_succ s)
  cases hNX : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) with
  | false => rfl
  | true =>
    obtain ⟨u, hu, v, hv, hne, hlu, hlv, hqu, hqv, _, _⟩ :=
      fgsa_head_excluded_before E rho hS x (SA.earlyTime p.toParams s) s q b hwindow hNX
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hu hv
    have hEmit : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s) :=
      hseat.symm ▸ ⟨k, hk, hem⟩
    have hU := fgsa_honest_head_eq_of_stored E rho hV _ x s q b _ hh hEmit u hu hlu hqu
    have hW := fgsa_honest_head_eq_of_stored E rho hV _ x s q b _ hh hEmit v hv hlv hqv
    exact (hne (hU.trans hW.symm)).elim


omit [DecidableEq V] in
/-- The receiver window gives the event epoch from the label start to a tick. -/
theorem arming_window_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {s : Slot} {C t : Time}
    (hw : ArmingReadWindow (c := c) E rho x s C) {i : Nat}
    (hi : rho.events[i]? = some (.tick x t)) (ht : t ≤ C) :
    V2.D.restartFree rho x (rho.actionCut (slotStartZ p (s : Int))) i := by
  classical
  intro k w hak hki he
  have hnot := (V2.D.Engine.index_lt_actionCut_iff hs he (slotStartZ p (s : Int))).not.mp
    (Nat.not_lt.mpr hak)
  have hw' : slotStartZ p (s : Int) < w := by
    apply lt_of_not_ge
    intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hnot (Or.inl hlt)
    · exact hnot (Or.inr ⟨heq, rfl⟩)
  have hwC : w ≤ C := by
    by_contra hn
    have hik := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he
      (ht.trans_lt (lt_of_not_ge hn))
    omega
  exact hw.epoch w hw' hwC (List.mem_of_getElem? he)

omit [DecidableEq V] in
/-- Same-time phases at the early tick also belong to the receiver window. -/
theorem arming_window_read_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {s : Slot}
    (hw : ArmingReadWindow (c := c) E rho x s (SA.earlyTime p.toParams s))
    {i : Nat} (hi : rho.events[i]? = some (.tick x (SA.earlyTime p.toParams s))) :
    V2.D.restartFree rho x (rho.idxBefore (SA.earlyTime p.toParams s)) i := by
  classical
  apply (arming_window_epoch hs hw hi le_rfl).mono ?_ le_rfl
  apply Gen.V2.Duty.actionCut_le_idxBefore hs
  change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 2 * p.Δ
  linarith [p.deltaPos]

/-- T25 at a local receiver: the regime supplies each joined vote and target service. -/
theorem arming_healthy_batch_window [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hHeads : ∀ z, z ∈ rho.honest →
      joinedAt p E rho z (l + 1) (SA.voteTime p.toParams (l + 1)) →
      ∀ k, rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1))) →
      Block.Preceq D (headVote p (clock p (storeAt p c E rho k z)
        (SA.voteTime p.toParams (l + 1))) (l + 1)))
    {x : V}
    (hw : ArmingReadWindow (c := c) E rho x (l + 1) (SA.earlyTime p.toParams (l + 1)))
    (hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams (l + 1)) x).st.fg.F) D) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
        (SA.voteTime p.toParams (l + 1)) →
      ∃ K k, rho.events[k]? = some (.tick x (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k x).base.votes ∧
        K ∈ (storeAt p c E rho k x).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k x).base
          (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
            SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k x).base K <
          SA.earlyTime p.toParams (l + 1) := by
  have hV := h.pre.base.valid
  have hS := hV.toScheduleWellFormed
  have hcut := (arming_early_next p l).trans_le hl
  apply arming_healthy_batch_heads hV h.pre.base.delta h.pre.cut hl hHeads x hw.honest
    (hw.awake _ (by rw [arming_early_eq]; have := p.deltaPos; positivity)
      (by change 4 * p.Δ * ((l + 1 : Nat) : Int) ≤
          4 * p.Δ * ((l + 1 : Nat) : Int) + 2 * p.Δ
          linarith [p.deltaPos]) le_rfl)
    (fun k hk => arming_window_read_epoch hS hw hk)
  · intro q K hq hTarget
    obtain ⟨k, hk, hem⟩ : V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) := by
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
      exact ⟨k, hk, hem⟩
    have hJoin := fgsa_joinedAt_of_emitted_head E rho hV hk hem
    have hK := headTargetAtEmission_at_tick E rho hS hTarget hk rfl
    have hDK := hHeads _ hq hJoin k hk
    change Block.Preceq D (headVote p (FGSA.clock p
      (rho.stateBefore E k (rho.seatOf (.base (.head (l + 1))) q)).st
      (SA.voteTime p.toParams (l + 1))) (l + 1)) at hDK
    rw [← hK] at hDK
    have hKm : K ∈ (storeAt p c E rho k (rho.seatOf (.base (.head (l + 1))) q)).base.blocks := by
      have hm := headVote_stored p
        (FGSA.clock p (storeAt p c E rho k (rho.seatOf (.base (.head (l + 1))) q))
          (SA.voteTime p.toParams (l + 1)))
        (cstoreInv_clock p _
          (cstoreInv_stateBefore E rho k (rho.seatOf (.base (.head (l + 1))) q))
          (SA.voteTime p.toParams (l + 1))) (l + 1)
      change headVote p (FGSA.clock p
        (rho.stateBefore E k (rho.seatOf (.base (.head (l + 1))) q)).st
        (SA.voteTime p.toParams (l + 1))) (l + 1) ∈
          (FGSA.clock p (rho.stateBefore E k (rho.seatOf (.base (.head (l + 1))) q)).st
            (SA.voteTime p.toParams (l + 1))).base.blocks at hm
      rw [← hK] at hm
      rw [clock_base_blocks] at hm
      exact hm
    exact ⟨arming_fresh_head_service_window h hw hcut hq ⟨k, hk, hem⟩
        (arming_head_handlers hV h.pre.base.delta (l + 1) q K.root x)
        (arming_head_not_excluded_window h hw hcut hq ⟨k, hk, hem⟩),
      arming_target_service_window h hw hcut hq hk hKm
        (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
          (Gen.Pure.block_preceq_trans hFloor hDK))⟩
  · exact h.pre.base.receiptIdealization

omit [DecidableEq V] in
/-- A joined duty gives its previous-label receiver window, including the start. -/
theorem arming_joined_window {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {x : V} {s : Slot} {T : Time} (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) T) : ArmingReadWindow (c := c) E rho x s T := by
  classical
  have heq : slotStartZ p (((s + 1 : Nat) : Int) - 1) = slotStartZ p (s : Int) := by
    congr 1; dsimp [Time] at *; omega
  have h0 : 0 ≤ slotStartZ p (s : Int) := by
    unfold slotStartZ; have := p.deltaPos; positivity
  refine ⟨hx, ?_, ?_⟩
  · intro t ht hstart hT
    by_contra hn
    obtain ⟨w, htw, hwT, hw⟩ := V2.D.Engine.wake_between hT
      (Bool.eq_false_iff.mpr hn) hJ.1
    have hb := hJ.2.1 w (lt_of_le_of_lt ht htw) hwT hw
    rw [heq] at hb
    exact (not_lt.mpr hb) (hstart.trans_lt htw)
  · intro w hstart hT he
    have hb := hJ.2.2 w
      (h0.trans hstart.le) hT he
    rw [heq] at hb
    exact (not_lt.mpr hb) hstart

omit [DecidableEq V] in
/-- Restrict the same receiver window to an earlier consuming time. -/
theorem arming_window_mono {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {x : V} {s : Slot} {C T : Time} (hw : ArmingReadWindow (c := c) E rho x s T)
    (hCT : C ≤ T) : ArmingReadWindow (c := c) E rho x s C :=
  ⟨hw.honest, fun t ht ha hb => hw.awake t ht ha (hb.trans hCT),
    fun w ha hb he => hw.epoch w ha (hb.trans hCT) he⟩

/-- Strict-before-cut joined participation supplies an actual enabled earlier gate. -/
theorem arming_joined_gate_before [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (s : Slot)
    (hcut : SA.gateTime p.toParams s < b₀) :
    ∃ z i, enabledGateAt p c E rho i z s := by
  classical
  have hs := h.base.valid.toScheduleWellFormed
  have h0 : 0 ≤ SA.gateTime p.toParams s := by
    rw [arming_gate_eq]; have := p.deltaPos; positivity
  have hp := h.joinedPartBefore _ h0 hcut
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hp)
  change z ∈ rho.honest.filter _ at hz
  obtain ⟨hz, hJ⟩ := Finset.mem_filter.mp hz
  have hslot : slotAt p (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (rho.stateBefore E 0 z) _).2.symm.trans
      (fgsa_gate_slot (c := c) (rho.stateBefore E 0 z) s)
  rw [hslot] at hJ
  obtain ⟨i, hi⟩ := arming_tick_exists hs h.base.delta hz (4 * s + 6)
    (arming_gate_nat p s) (hcut.le.trans h.cut.2) hJ.1
  have hbound := fgsa_restartTime_bound E rho i z (slotStartZ p (s : Int)) (by
    intro k w hki he
    have hw0 := (hs.in_horizon _ (List.mem_of_getElem? he)).1
    have hwT : w ≤ SA.gateTime p.toParams s := by
      by_contra hn
      have hik := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he (lt_of_not_ge hn)
      omega
    have hb := hJ.2.2 w hw0 hwT (List.mem_of_getElem? he)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hb)
  refine ⟨z, i, hi, ?_⟩
  cases hr : (storeAt p c E rho i z).restartTime with
  | none => trivial
  | some w => exact hbound w hr

end AvailableChain.FGSA.Run
end

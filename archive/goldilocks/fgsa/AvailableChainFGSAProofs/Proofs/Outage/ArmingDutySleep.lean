module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingConstruction
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingOutput

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Durable obligations remain bounded across local restarts before the pending gate. -/
theorem arming_leases_interval_sleep {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    {b₀ : Time} {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V) {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)))
    (h₀ : ∀ row ∈ (storeAt p c E rho (timeIdx rho b₀) y).base.obligations,
      Block.Preceq row.1 D) :
    ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le (Nat.lt_succ_self k) (hi.trans (arming_idxBefore_le_length rho _))
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    have hprev := ih (le_trans (Nat.le_succ k) hi)
    by_cases hR : ∃ t, rho.events[k]? = some (.restart y t)
    · obtain ⟨t, ht⟩ := hR
      have hr : storeAt p c E rho (k + 1) y = acRestart p (storeAt p c E rho k y) t := by
        change (rho.stateBefore E (k + 1) y).st = _
        rw [V2.D.Engine.state_after_restart ht]; rfl
      rw [hr, acRestart_obligations]
      exact hprev
    have hEpoch : V2.D.restartFree rho y k (k + 1) := by
      intro j t hkj hjk hj
      have heq : j = k := by omega
      subst j
      exact hR ⟨t, hj⟩
    rcases arming_store_succ_on (E := E) he y
      hEpoch with heq | ⟨t, het, heq⟩ | ⟨o, t, het, heq⟩
    · rw [heq]
      exact hprev
    · obtain ⟨hb, hd⟩ := arming_event_window hs he hk (lt_of_lt_of_le (Nat.lt_succ_self k) hi)
      rw [het] at hb hd
      have hoff := arming_clock_offGate_fields p (storeAt p c E rho k y) t
        (arming_offGate p l hl hb hd)
      intro row hrow
      rw [heq] at hrow
      exact hprev row (hoff.2.2.2.subset hrow)
    · intro row hrow
      rw [heq] at hrow
      rcases arming_process_lease p (storeAt p c E rho k y) (toWire p o) with h | h
      · rw [h.1] at hrow
        exact hprev row hrow
      · rw [h.1] at hrow
        exact hprev row (List.mem_filter.mp hrow).1

/-- The general certificate bounds every prefix state through the strict pending read. -/
theorem arming_prefix_sleep_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hV : V2.D.ExecutionValid E rho) (hf : FGFoundation p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (hroots : NamedRootCollisionFree p c E rho)
    {fast : Bool} {T b₀ : Time} {B : Block} {l : Slot} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i) :
    ArmingPrefixState p c E rho l D Dh := by
  have hs := hV.toScheduleWellFormed
  have hentry := arming_sleep_entry_below hs (hState _ le_rfl) hc.max_lift
    hc.gate_le_cut hc.max_le
  obtain ⟨q, _, hD⟩ := hc.max_mem
  intro i y hi _ hy
  obtain ⟨hF, hJ, hZ, hn, hlo⟩ := arming_frame_below (hroots := hroots)
    (hstrat := hf.strat) (hScope := hc.max_lift.symm ▸ rootScope_result hV hD)
    hs hf.store hf.frame.1 hsrc hc.max_lift hentry hi hy
  refine ⟨hF, hJ, hZ, hn, hlo, ?_⟩
  have hcut (k : Nat) (hk : k ≤ timeIdx rho b₀) := arming_leases_cut hs hc.cut_lt_pending
    (fun i y hi _ => (hState i hi).leases y) hc.max_le (y := y) hk hy
  rcases le_or_gt i (timeIdx rho b₀) with hle | hgt
  · exact hcut i hle
  · exact arming_leases_interval_sleep hs hc.gate_le_cut y hgt.le hi (hcut _ le_rfl)

omit [DecidableEq V] in
/-- A local joined read retains its early batch and all early ancestor stamps. -/
theorem arming_duty_epochs {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {l : Slot} {y : V} {i : Nat} {t : Time}
    (hw : ArmingReadWindow (c := c) E rho y (l + 1) t)
    (hi : rho.events[i]? = some (.tick y t))
    (het : SA.earlyTime p.toParams (l + 1) < t) :
    (∀ k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) →
      V2.D.restartFree rho y k i) ∧
    (∀ (k : Nat) (w : Time) (j : Nat), rho.events[j]? =
      some (.tick y (SA.earlyTime p.toParams (l + 1))) → k < j →
      rho.events[k]? = some (.restart y w) → w < SA.earlyTime p.toParams (l + 1)) := by
  classical
  have hstart : slotStartZ p ((l + 1 : Nat) : Int) < SA.earlyTime p.toParams (l + 1) := by
    change 4 * p.Δ * ((l + 1 : Nat) : Int) <
      4 * p.Δ * ((l + 1 : Nat) : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  constructor
  · intro k hk
    apply (arming_window_epoch hs hw hi le_rfl).mono ?_ le_rfl
    by_contra hn
    have ht := (V2.D.Engine.index_lt_actionCut_iff hs hk _).mp (lt_of_not_ge hn)
    rcases ht with ht | ⟨ht, _⟩
    · exact (not_lt.mpr hstart.le) ht
    · exact (ne_of_lt hstart) ht.symm
  · intro k w j hj hkj he
    have hji := V2.D.Engine.eventIndex_lt_of_time_lt hs hj hi het
    have hwt : w ≤ t := by
      by_contra hn
      have hik := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he (lt_of_not_ge hn)
      omega
    have hws : w ≤ slotStartZ p ((l + 1 : Nat) : Int) := by
      by_contra hn
      exact hw.epoch w (lt_of_not_ge hn) hwt (List.mem_of_getElem? he)
    exact hws.trans_lt hstart

/-- The certificate's joined HEAD bounds produce a batch at this joined duty reader. -/
theorem arming_duty_batch [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {y : V} {t : Time} (hw : ArmingReadWindow (c := c) E rho y (l + 1) t)
    (het : SA.earlyTime p.toParams (l + 1) < t) :
    ArmingJoinedBatchState p c E rho l D y := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams (l + 1)) y).st.fg.F) D := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact hc.f_below _ y (fgsa_idxBefore_mono rho (by
      rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos])) hw.honest
  exact arming_healthy_batch_window h hc.gate_le_cut hc.joined_heads
    (arming_window_mono hw het.le) hFloor

/-- Pre-pending HEAD reads use the joined batch and the receiver's own event epochs. -/
theorem arming_head_covers_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis)
    {y : V} (hy : y ∈ rho.honest) {i : Nat}
    (hi : rho.events[i]? = some (.tick y (SA.voteTime p.toParams (l + 2))))
    (hJ : joinedAt p E rho y (l + 2) (SA.voteTime p.toParams (l + 2))) :
    Block.Preceq B (headVote p (clock p (storeAt p c E rho i y)
      (SA.voteTime p.toParams (l + 2))) (l + 2)) := by
  have hw := arming_joined_window (c := c) hy hJ
  have het := (arming_duty_window p l).2.2.2.trans (arming_duty_window p l).2.1
  have hEpochs := arming_duty_epochs h.pre.base.valid.toScheduleWellFormed hw hi het
  have hDne : D ≠ .genesis := by
    intro hg
    exact hne (block_preceq_antisymm (hg ▸ hc.max_read) (block_genesis_preceq B))
  apply block_preceq_trans hc.max_read
  exact arming_head_covers_on h.pre.base.valid hf h.pre.base.cstar hc.max_lift hDne
    ⟨h.sleepPre.joinedPartBefore _ (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le
        ((arming_early_next p l).trans_le hc.gate_le_cut))⟩
    (arming_prefix_sleep_on h.pre.base.valid hf hsrc h.pre.base.idealization hc hState)
    hy (arming_duty_batch h hc hw het) hi hEpochs.1 hEpochs.2 (hprov _ _ _ hy hi hJ)

/-- Pre-pending proposal reads use joined voters and the same local receiver epoch. -/
theorem arming_proposal_covers_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {y : V} (hy : y ∈ rho.honest) {i : Nat}
    (hi : rho.events[i]? = some (.tick y (SA.proposalTime p.toParams (l + 2))))
    (hJ : joinedAt p E rho y (l + 2) (SA.proposalTime p.toParams (l + 2))) :
    Block.Preceq B (proposerHead p (clock p (storeAt p c E rho i y)
      (SA.proposalTime p.toParams (l + 2))) (l + 2)) := by
  have hw := arming_joined_window (c := c) hy hJ
  have het := (arming_duty_window p l).2.2.2
  apply block_preceq_trans hc.max_read
  exact arming_proposal_covers_on h.pre.base.valid h.pre.base.cstar hc.max_lift
    ⟨h.sleepPre.joinedPartBefore _ (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le
        ((arming_early_next p l).trans_le hc.gate_le_cut))⟩
    (arming_prefix_sleep_on h.pre.base.valid hf hsrc h.pre.base.idealization hc hState)
    hy (arming_duty_batch h hc hw het) hi
    (arming_duty_epochs h.pre.base.valid.toScheduleWellFormed hw hi het).1

/-- A joined clock guard at an actual tick gives the environment-level joined duty. -/
theorem arming_joined_of_tick_guard {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hV : V2.D.ExecutionValid E rho) {i : Nat} {y : V} {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (.tick y t)) (hslot : p.slotOf t = s)
    (haw : E.awake y t = true)
    (hguard : joinedNow p (clock p (storeAt p c E rho i y) t) = true) :
    joinedAt p E rho y s t := by
  have bound (w : Time) (_hw : 0 ≤ w) (hwt : w ≤ t)
      (hr : V2.Event.restart y w ∈ rho.events) : w ≤ slotStartZ p ((s : Int) - 1) := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hj hi hwt
      (by change 0 < (1 : Nat); decide)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hV.toScheduleWellFormed hj hji
    have hg := hguard
    change joinedNow p (clock p (V2.D.Run.stateBefore E rho i y).st _ ) = true at hg
    unfold joinedNow at hg
    rw [fgsa_clock_restartTime, hu, (clock_vn _ _).2] at hg
    have hub : u ≤ slotStartZ p ((s : Int) - 1) := by
      change decide (u ≤ 4 * p.Δ * ((p.slotOf (t) : Int) - 1)) = true at hg
      rw [hslot] at hg
      exact of_decide_eq_true hg
    exact hwu.trans hub
  refine ⟨haw, ?_, bound⟩
  intro w hw hwt hwake
  exact bound w hw.le hwt (hV.wake_restart y
    (hV.honest_only _ (List.mem_of_getElem? hi)) w hw
    (hwt.trans (hV.in_horizon _ (List.mem_of_getElem? hi)).2) hwake)

/-- Actual proposals expose the joined receiver guard as well as their parent read. -/
theorem arming_emit_proposal_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) {y : V} (hy : y ∈ rho.honest) {o : Obj p} {t : Time}
    (he : V2.D.Run.emits E rho y o t) {N : NamedProposal p.n} (hX : o.payload = .proposal N) :
    ∃ s i, s ≠ 0 ∧ t = SA.proposalTime p.toParams s ∧ rho.events[i]? = some (.tick y t) ∧
      N.parent.erase = proposerHead p (FGSA.clock p (V2.D.Run.stateBefore E rho i y).st t) s ∧
      joinedAt p E rho y s t := by
  obtain ⟨i, hi, hem⟩ := he
  have haw := arming_emit_awake hi hem
  have hw := honest_emit_wellFormed E rho hE.toDeliveryWellFormed
    hE.toScheduleWellFormed i y t hi hy haw o hem
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  rcases o with ⟨auth, m⟩
  change m = .proposal N at hX
  subst hX
  cases auth with
  | none => cases hw
  | seat l q =>
    obtain ⟨_, _, d, _, ht, ha⟩ := (V2.D.Engine.mem_tick_seat_iff E rho _ y t l q _).mp hem
    cases d with
    | headAction s =>
      change (if joinedNow p _ then some (Msg.head _) else none) = some _ at ha
      split at ha <;> cases ha
    | fgAction r =>
      change (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i y).st t)
        (V2.D.Run.stateBefore E rho i y).record ⟨0, p.nPos⟩).1.map Msg.row = some _ at ha
      obtain ⟨_, _, hm⟩ := Option.map_eq_some_iff.mp ha
      cases hm
    | propAction s =>
      change SA.proposalTime p.toParams s = t at ht
      change (if joinedNow p _ then
        (propose p (FGSA.clock p (V2.D.Run.stateBefore E rho i y).st t) s).map
          (withApp p (c.app (rho.input y t))) else none) = some _ at ha
      split at ha <;> try (cases ha)
      obtain ⟨m', hm', hw'⟩ := Option.map_eq_some_iff.mp ha
      by_cases hs0 : s = 0
      · subst hs0
        cases hm'
      · rw [propose_head (p := p) _ s hs0] at hm'
        obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm'
        cases Msg.proposal.inj hw'
        refine ⟨s, i, hs0, ht.symm, hi, (namedByErase?_sound _ _ P hP).2, ?_⟩
        have hslot : p.slotOf t = s := by
          rw [← ht, arming_proposal_eq]
          simpa only [add_zero] using slotOf_offset p s 0 (by omega)
            (by have := p.deltaPos; dsimp [Time] at *; omega)
        exact arming_joined_of_tick_guard hE hi hslot haw (by assumption)

/-- Every actual honest pre-pending duty has its joined receiver guard. -/
theorem arming_pending_duties_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis) :
    ∀ y o t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
      t < SA.gateTime p.toParams (l + 1) → V2.D.Run.emits E rho y o t →
      (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
      (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase) := by
  intro y o t hy hlt htd he
  constructor
  · intro H hH
    obtain ⟨i, s, q, hi, hem, ho, hEq⟩ := hH
    have hem' : ofHead p ⟨.seat (.head s) q, H.root⟩ ∈ rho.emitsAt E i := ho ▸ hem
    have hfields := hem'
    rw [(rho.step_tick_eq E hi).2] at hfields
    have ht := ((fgsa_emits_head E rho _ y t s q H.root).mp hfields).2.1
    subst t
    obtain rfl := arming_vote_window p l s hlt htd
    rw [hEq]
    exact arming_head_covers_sleep h hf hsrc hState hprov hc hne hy hi
      (fgsa_joinedAt_of_emitted_head E rho h.pre.base.valid hi hem')
  · intro N hX
    obtain ⟨s, i, _, rfl, hi, hpar, hJ⟩ := arming_emit_proposal_on h.pre.base.valid hy he hX
    obtain rfl := arming_proposal_window p l s hlt htd
    rw [hpar]
    exact arming_proposal_covers_sleep h hf hsrc hState hc hy hi hJ

/-- The actual in-flight HEAD is the same joined pre-pending duty. -/
theorem arming_inflight_heads_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis) :
    ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (l + 2))) q →
      HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H := by
  intro y o t q H hy he hauth hH
  obtain ⟨r, _, _, hauth', rfl, _, _⟩ := arming_emit_head h.pre.base.valid hy he hH
  rw [hauth] at hauth'
  injection hauth' with hlab
  injection hlab with hlab
  injection hlab with hlab
  subst hlab
  have ht := arming_duty_window p l
  exact (arming_pending_duties_sleep h hf hsrc hState hprov hc hne y o _ hy
    (ht.1.trans ht.2.1.le) ht.2.2.1 he).1 H hH

/-- Stable output survives restarts and normalization until the pending gate. -/
theorem arming_S_interval_sleep {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho)
    {b₀ : Time} {l : Slot} {B D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (y : V)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (h₀ : Block.Preceq B (S_at p c E rho (timeIdx rho b₀) y) ∧
      Block.Preceq (S_at p c E rho (timeIdx rho b₀) y) D)
    {i : Nat} (hi₀ : timeIdx rho b₀ ≤ i)
    (hi : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))) :
    Block.Preceq B (S_at p c E rho i y) ∧ Block.Preceq (S_at p c E rho i y) D := by
  induction i, hi₀ using Nat.le_induction with
  | base => exact h₀
  | succ k hk ih =>
    have hkd : k < V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) :=
      lt_of_lt_of_le (Nat.lt_succ_self k) hi
    obtain ⟨hB, hD⟩ := ih hkd.le
    have hkl : k < rho.events.length :=
      lt_of_lt_of_le hkd (arming_idxBefore_le_length rho _)
    have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hkl
    obtain ⟨hb, hd⟩ := arming_event_window hs he hk hkd
    rcases fgsaAC_output_step E rho k y with heq | ⟨s, hgs⟩ | ⟨o, t, b, hdel, _, _, hnorm⟩ |
        ⟨t, hrs, _⟩
    · change S_at p c E rho (k + 1) y = S_at p c E rho k y at heq
      rw [heq]
      exact ⟨hB, hD⟩
    · exfalso
      obtain ⟨hb', hd'⟩ := arming_event_window hs hgs hk hkd
      exact arming_offGate p l hl hb' hd' s rfl
    · change S_at p c E rho (k + 1) y =
        Gen.AC.normalizeOutput (F_at p c E rho (k + 1) y) (S_at p c E rho k y) at hnorm
      rw [hnorm, Gen.AC.normalizeOutput_def]
      have hFk := hF (k + 1) hi
      split
      · exact ⟨hB, hD⟩
      · next hn =>
        rcases block_preceq_total_of_common hFk hD with h | h
        · exact absurd h hn
        · exact ⟨block_preceq_trans hB h, hFk⟩
    · have heq : S_at p c E rho (k + 1) y = S_at p c E rho k y := by
        change (rho.stateBefore E (k + 1) y).st.base.stableRecord = _
        rw [V2.D.Engine.state_after_restart hrs]
        exact acRestart_stableRecord p _ t
      rw [heq]
      exact ⟨hB, hD⟩

/-- A caught-up read before the pending gate bounds every earlier restart marker. -/
theorem arming_confirmed_restart_bound {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho)
    {y : V} {t : Time} (hC : confirmedReader p c E rho y t) {l : Slot}
    (ht : t < SA.gateTime p.toParams (l + 1)) :
    ∀ k w, k < timeIdx rho t → rho.events[k]? = some (.restart y w) →
      w ≤ slotStartZ p (l : Int) := by
  intro k w hki he
  obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hs he hki
  change (storeAt p c E rho (timeIdx rho t) y).restartTime = some u at hu
  have hR := hC.2.2
  cases hm : (storeAt p c E rho (timeIdx rho t) y).restartTime with
  | none => rw [hm] at hu; cases hu
  | some z =>
    rw [hm] at hu hR
    have huz : z = u := Option.some.inj hu
    subst z
    obtain ⟨s, _, hus, hst, _⟩ := hR
    have hsl := arming_lt_pending p l s (hst.trans_lt ht)
    apply hwu.trans (hus.trans ?_)
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (l : Int)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsl) (by
      have := p.deltaPos; positivity)

/-- A protected caught-up pre-pending reader has an enabled cut-label gate. -/
theorem arming_confirmed_pre_pending_gate {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho)
    (hdelta : E.Δ = p.Δ) {fast : Bool} {T b₀ : Time} {B : Block} {l : Slot} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {y : V} (hyG : y ∈ coveredNodes p E rho fast b₀) {t : Time}
    (hC : confirmedReader p c E rho y t)
    (hlt : SA.gateTime p.toParams l ≤ t) (ht : t < SA.gateTime p.toParams (l + 1))
    (hhor : t ≤ rho.horizon) : ∃ i, enabledGateAt p c E rho i y l := by
  have hScope : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hc.cover_label]
    cases fast with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk : (1 : Int) ≤ p.k := by exact_mod_cast (show 1 ≤ p.k by have := p.kLarge; omega)
      exact ⟨by omega, le_rfl⟩
  obtain ⟨hy, hAw, _⟩ := arming_receiver_window hyG hScope
  have hstart : slotStartZ p ((l + 1 : Nat) : Int) ≤ SA.gateTime p.toParams l := by
    rw [arming_gate_eq]; change 4 * p.Δ * ((l + 1 : Nat) : Int) ≤ _
    push_cast; linarith [p.deltaPos]
  have hgate : SA.gateTime p.toParams l ≤ SA.gateTime p.toParams (coverLabel p b₀) := by
    rw [hc.cover_label]; exact (arming_gate_le_iff p _ _).mpr (Nat.le_succ l)
  obtain ⟨i, hi⟩ := arming_tick_exists hs hdelta hy (4 * l + 6) (arming_gate_nat p l)
    (hlt.trans hhor) (hAw _ (by rw [arming_gate_eq]; have := p.deltaPos; positivity) hstart hgate)
  have hic := arming_lt_of_tick hs hi hlt
  have hbound := fgsa_restartTime_bound E rho i y (slotStartZ p (l : Int))
    (fun k w hki he => arming_confirmed_restart_bound hs hC ht k w (hki.trans hic) he)
  refine ⟨i, hi, ?_⟩
  cases hm : (storeAt p c E rho i y).restartTime with
  | none => trivial
  | some w => exact hbound w hm

/-- Pre-pending stable coverage uses the actual enabled receiver gate and Clean output. -/
theorem arming_cover_sleep [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) :
    ∀ y t, y ∈ coveredNodes p E rho fast b₀ → confirmedReader p c E rho y t →
      SA.gateTime p.toParams l ≤ t → t < SA.gateTime p.toParams (l + 1) →
      t ≤ rho.horizon → Block.Preceq B (S_at p c E rho (timeIdx rho t) y) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  obtain ⟨r, C, _, hOrigin, hTime, hBC⟩ := hc.origin
  have hlabel : l = (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) := by
    have he := hc.cover_label
    change _ + 1 = l + 1 at he
    exact (Nat.add_right_cancel he).symm
  have hrl : r < l := by
    cases fast with
    | true =>
      have hg := arming_fast_gap p r T b₀ hTime h.lag
      rw [← hlabel] at hg
      dsimp only [Slot] at *; omega
    | false =>
      have hg := arming_slow_gap p r T b₀ hTime h.lag
      rw [← hlabel] at hg
      have := p.kLarge
      dsimp only [Slot] at *; omega
  intro y t hyG hC hlt htd hhor
  have hy := hC.1
  obtain ⟨i, hG⟩ := arming_confirmed_pre_pending_gate hs h.pre.base.delta hc hyG hC hlt htd hhor
  have hiCut := arming_lt_of_tick hs hG.1 hc.gate_le_cut
  obtain ⟨Cl, hCl, hClS⟩ := hOutput i y l hiCut hG
  have hBCl := block_preceq_trans hBC
    (hHist.ordered r l C Cl hOrigin ⟨i, hiCut, y, hG.1, hG.2, hCl⟩ hrl)
  have hS : Block.Preceq B (S_at p c E rho (timeIdx rho b₀) y) :=
    block_preceq_trans hBCl (block_preceq_trans hClS
      ((hState _ le_rfl).sExtends y _ _ (Nat.succ_le_of_lt hiCut) le_rfl))
  rcases le_or_gt t b₀ with htb | htb
  · have hiT := Nat.succ_le_of_lt (arming_lt_of_tick hs hG.1 hlt)
    exact block_preceq_trans hBCl (block_preceq_trans hClS
      ((hState _ (arming_timeIdx_mono rho htb)).sExtends y _ _ hiT le_rfl))
  · have hSD := arming_S_cut hs hc.cut_lt_pending
      (fun i y hi _ => (hState i hi).sOrigin y) hc.max_le hy
      (fun q hq => hc.f_below q y
        (hq.trans (arming_timeIdx_le_idxBefore rho hc.cut_lt_pending)) hy)
    exact (arming_S_interval_sleep hs hc.gate_le_cut y
      (fun k hk => hc.f_below k y hk hy) ⟨hS, hSD⟩
      (arming_timeIdx_mono rho htb.le) (arming_timeIdx_le_idxBefore rho htd)).1

/-- The sleep history certificate keeps the gate and the exact pre-pending consumer scopes. -/
structure ArmingSleepHistoryCert (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ : Time)
    (B : Block) (l : Slot) (D : Block) (Dh : FGBlock (Fin p.n)) : Prop where
  gate : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh
  pending_cover : ∀ y t, y ∈ coveredNodes p E rho fast b₀ →
    confirmedReader p c E rho y t → SA.gateTime p.toParams l ≤ t →
    t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
    Block.Preceq B (S_at p c E rho (timeIdx rho t) y)
  pending_duties : ∀ y o t, y ∈ rho.honest → SA.gateTime p.toParams l ≤ t →
    t < SA.gateTime p.toParams (l + 1) → V2.D.Run.emits E rho y o t →
    (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)
  pending_compat : ∀ y t, y ∈ rho.honest → 0 ≤ t →
    t < SA.gateTime p.toParams (l + 1) → t ≤ rho.horizon →
    Block.Compatible B (F_at p c E rho (timeIdx rho t) y)
  inflight_heads : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest →
    V2.D.Run.emits E rho y o t → o.auth = .seat (.base (.head (l + 2))) q →
    HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H

/-- Assemble the history consumers from the general certificate and actual Clean suppliers. -/
theorem arming_sleep_history_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hne : B ≠ .genesis) :
    ArmingSleepHistoryCert p c E rho fast T b₀ B l D Dh :=
  ⟨hc, arming_cover_sleep h hState hHist hOutput hc,
    arming_pending_duties_sleep h hf hsrc hState hprov hc hne,
    arming_compat hc.max_read hc.f_below,
    arming_inflight_heads_sleep h hf hsrc hState hprov hc hne⟩

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPending
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingBatch
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Statements.CleanInvariant
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingReceipt

public section

/-! P-Ar sleep kernel. Each window and epoch belongs to one protected receiver.
The slow window starts at t(q0). The fast window starts at t(j).
Receipt services are local inputs until the Clean joint induction supplies them. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- The approved fast guard gives awake on the whole receiver window. -/
theorem arming_fast_awake {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {x : V} {j : Slot} (hG : fastCoveredSchedule p E rho x j) :
    AwakeClosed E x (slotStartZ p (j : Int)) (SA.gateTime p.toParams j) := by
  classical
  intro t ht hstart hgate
  by_contra hn
  have hfalse : E.awake x t = false := Bool.eq_false_iff.mpr hn
  obtain ⟨w, htw, hwg, hw⟩ := V2.D.Engine.wake_between hgate hfalse hG.1
  have hbound := hG.2.1 w (lt_of_le_of_lt ht htw) hwg hw
  have heq : slotStartZ p (((j + 1 : Nat) : Int) - 1) = slotStartZ p (j : Int) := by
    congr 1
    dsimp [Time] at *
    omega
  rw [heq] at hbound
  exact (not_lt.mpr hbound) (hstart.trans_lt htw)

omit [DecidableEq V] in
/-- The approved fast guard also excludes every restart after t(j), through g(j). -/
theorem arming_fast_restart_free {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {x : V} {j : Slot} (hG : fastCoveredSchedule p E rho x j) :
    RestartFreeTime rho x (slotStartZ p (j : Int)) (SA.gateTime p.toParams j) := by
  classical
  intro w hstart hgate he
  have h0 : 0 ≤ slotStartZ p (j : Int) := by
    unfold slotStartZ
    have hd := p.deltaPos
    positivity
  have hw := hG.2.2 w (h0.trans hstart.le) hgate he
  have heq : slotStartZ p (((j + 1 : Nat) : Int) - 1) = slotStartZ p (j : Int) := by
    congr 1
    dsimp [Time] at *
    omega
  rw [heq] at hw
  exact (not_lt.mpr hw) hstart

omit [DecidableEq V] in
/-- Exact awake and restart-free windows at each protected receiver. -/
theorem arming_receiver_window {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    x ∈ rho.honest ∧
    AwakeClosed E x (slotStartZ p (q : Int)) (SA.gateTime p.toParams (coverLabel p b₀)) ∧
    RestartFreeTime rho x (slotStartZ p (q : Int))
      (SA.gateTime p.toParams (coverLabel p b₀)) := by
  classical
  classical
  change x ∈ rho.honest.filter _ at hx
  obtain ⟨hxH, hG⟩ := Finset.mem_filter.mp hx
  cases fast with
  | true =>
    change fastCoveredSchedule p E rho x (coverLabel p b₀) at hG
    change q = coverLabel p b₀ at hq
    subst q
    exact ⟨hxH, arming_fast_awake hG, arming_fast_restart_free hG⟩
  | false =>
    change slowCoveredSchedule p E rho x (coverLabel p b₀) at hG
    change _ ∧ _ at hq
    have hstart : slotStartZ p ((coverLabel p b₀ : Int) - (p.k : Int) + 1) ≤
        slotStartZ p (q : Int) := by
      unfold slotStartZ
      exact mul_le_mul_of_nonneg_left hq.1 (by have hd := p.deltaPos; positivity)
    exact ⟨hxH, fun t ht ha hb => hG.2.1 t ht (hstart.trans ha) hb,
      fun w ha hb he => hG.2.2 w (hstart.trans_lt ha) hb he⟩

omit [DecidableEq V] in
/-- A protected receiver is awake at both the early read and gate of each scoped label. -/
theorem arming_receiver_times {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    E.awake x (SA.earlyTime p.toParams q) = true ∧
    E.awake x (SA.gateTime p.toParams q) = true := by
  classical
  obtain ⟨_, hA, _⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by
    cases fast <;> simp_all
  have hd := p.deltaPos
  have ht0 : 0 ≤ slotStartZ p (q : Int) := by unfold slotStartZ; positivity
  have hte : slotStartZ p (q : Int) ≤ SA.earlyTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 2 * p.Δ
    dsimp [Time] at *
    omega
  have htg : slotStartZ p (q : Int) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    dsimp [Time] at *
    omega
  have heg : SA.earlyTime p.toParams q ≤ SA.gateTime p.toParams q := by
    rw [arming_early_eq, arming_gate_eq]
    dsimp [Time] at *
    omega
  have hgj := (arming_gate_le_iff p q _).mpr hqj
  exact ⟨hA _ (ht0.trans hte) hte (heg.trans hgj), hA _ (ht0.trans htg) htg hgj⟩

omit [DecidableEq V] in
/-- Saved rows use the receiver epoch from t(q0), after phase-zero restarts. -/
theorem arming_receiver_start_epoch {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho)
    {fast : Bool} {b₀ : Time} {x : V} (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (slotStartZ p (q : Int)))
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (coverLabel p b₀))) := by
  classical
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hd := p.deltaPos
  have hstart : slotStartZ p (q : Int) < SA.gateTime p.toParams q := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (q : Int) + 6 * p.Δ
    dsimp [Time] at *
    omega
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hs
    (hstart.trans_le ((arming_gate_le_iff p q _).mpr hqj))
  intro k w he hw hg
  exact hR w hw hg.le (List.mem_of_getElem? he)

omit [DecidableEq V] in
/-- The time window gives the exact event-index epoch for a fresh batch. -/
theorem arming_receiver_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams q))
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (coverLabel p b₀))) := by
  classical
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hd := p.deltaPos
  have htv : slotStartZ p (q : Int) < SA.voteTime p.toParams q := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (q : Int) + p.Δ
    dsimp [Time] at *
    omega
  have hvg : SA.voteTime p.toParams q < SA.gateTime p.toParams q := by
    rw [arming_vote_eq, arming_gate_eq]
    dsimp [Time] at *
    omega
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hs
    (hvg.trans_le ((arming_gate_le_iff p q _).mpr hqj))
  intro k w he hv hg
  exact hR w (htv.trans hv) hg.le (List.mem_of_getElem? he)

/-- Each protected gate is enabled, including a wake exactly at t(q0). -/
theorem arming_receiver_enabled {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) {i : Nat}
    (hi : IsGateTick p c rho i x q) : enabledGateAt p c E rho i x q := by
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hbound := fgsa_restartTime_bound E rho i x (slotStartZ p (q : Int)) (by
    intro k w hki he
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hk := List.pairwise_iff_getElem.mp hs.sorted k i hkl hil hki
    rw [hke, hie] at hk
    have htime : w ≤ SA.gateTime p.toParams q := V2.D.Engine.time_le_of_key_le _ _ hk
    by_contra hn
    exact hR w (lt_of_not_ge hn)
      (htime.trans ((arming_gate_le_iff p q _).mpr hqj)) (List.mem_of_getElem? he))
  refine ⟨hi, ?_⟩
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some w => exact hbound w hr

omit [DecidableEq V] in
/-- The actual gate tick remains in this receiver's epoch, including equal-time phases. -/
theorem arming_receiver_gate_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀))
    {i : Nat} (hi : IsGateTick p c rho i x q) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (slotStartZ p (q : Int))) i := by
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  intro k w hak hki he
  have hnot := (V2.D.Engine.index_lt_actionCut_iff hs he (slotStartZ p (q : Int))).not.mp
    (Nat.not_lt.mpr hak)
  have hw : slotStartZ p (q : Int) < w := by
    apply lt_of_not_ge
    intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hnot (Or.inl hlt)
    · exact hnot (Or.inr ⟨heq, rfl⟩)
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk := List.pairwise_iff_getElem.mp hs.sorted k i hkl hil hki
  rw [hke, hie] at hk
  have htime : w ≤ SA.gateTime p.toParams q := V2.D.Engine.time_le_of_key_le _ _ hk
  exact hR w hw (htime.trans ((arming_gate_le_iff p q _).mpr hqj))
    (List.mem_of_getElem? he)

/-- The strict read equals the actual tick store when its equal-time receiver epoch survives. -/
theorem arming_tick_store_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {t : Time}
    (hi : rho.events[i]? = some (.tick x t))
    (hEpoch : V2.D.restartFree rho x (V2.D.Run.idxBefore rho t) i) :
    storeAt p c E rho i x = storeAt p c E rho (V2.D.Run.idxBefore rho t) x := by
  have hidx : V2.D.Run.idxBefore rho t ≤ i := by
    by_contra hn
    exact (lt_irrefl t) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi t).mp
      (Nat.lt_of_not_ge hn))
  apply congrArg Node.st
  apply V2.D.Run.stateBefore_eq_of_node_ne E rho hidx
  intro k e hstart hki he hnode
  have hnot := (Gen.V2.Duty.index_lt_idxBefore_iff hs he t).not.mp
    (Nat.not_lt.mpr hstart)
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk := List.pairwise_iff_getElem.mp hs.sorted k i hkl hil hki
  rw [hke, hie] at hk
  have ht : e.time = t := le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk)
    (le_of_not_gt hnot)
  cases e with
  | restart y w =>
    change y = x at hnode
    subst y
    exact hEpoch k w hstart hki he
  | tick y u =>
    change y = x at hnode
    change u = t at ht
    subst y
    subst u
    have hEq : k = i := fgsa_tick_unique E rho hs he hi
    omega
  | deliver y o u =>
    change u = t at ht
    subst u
    simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.toLex_le_toLex] at hk

/-- Healthy-prefix supplier for arming_nonrow_delivery. -/
theorem arming_nonrow_delivery_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF) :
    Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun a => a + p.Δ) b₀ := by
  have hd := Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀
    hp.healthy (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  rwa [hp.base.delta] at hd

/-- The healthy non-row law is the sleep prefix's a + Δ service law. -/
theorem arming_nonrow_delivery [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF) :
    Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun a => a + p.Δ) b₀ := by
  exact arming_nonrow_delivery_of_prefix h.pre

/-- A protected receiver supplies readiness for an honest emitted fresh HEAD. -/
theorem arming_head_ready {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {b₀ : Time} {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀)
    {s : Slot} (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    {o : Obj p} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y o (SA.voteTime p.toParams s)) :
    Gen.V2.Duty.ReadyTrigger E rho o (SA.voteTime p.toParams s) x
      (SA.voteTime p.toParams s) (SA.voteTime p.toParams s + p.Δ) := by
  obtain ⟨_, hA, _⟩ := arming_receiver_window hx hs
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hd := p.deltaPos
  refine ⟨y, hy, Or.inl he, ?_⟩
  intro t hv ht
  apply hA t
  · rw [arming_vote_eq] at hv
    have hn : (0 : Time) ≤ 4 * p.Δ * (s : Int) := by positivity
    dsimp [Time] at *
    omega
  · change 4 * p.Δ * (s : Int) ≤ t
    rw [arming_vote_eq] at hv
    dsimp [Time] at *
    omega
  · have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
      rw [arming_early_eq, arming_gate_eq]
      dsimp [Time] at *
      omega
    rw [arming_vote_add] at ht
    exact ht.le.trans (heg.trans ((arming_gate_le_iff p s _).mpr hsj))

/-- Healthy-prefix supplier for arming_fresh_head_service. -/
theorem arming_fresh_head_service_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
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
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams (coverLabel p b₀) := by
    apply le_trans _ ((arming_gate_le_iff p s _).mpr hsj)
    rw [arming_early_eq, arming_gate_eq]
    have hd := p.deltaPos
    dsimp [Time] at *
    omega
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := b₀
    within := arming_nonrow_delivery_of_prefix hp
    ready := arming_head_ready hx hs hy he
    later := lt_add_of_pos_right _ p.deltaPos
    cut_le := by rw [arming_vote_add]; exact hcut
    horizon := by rw [arming_vote_add]; exact hcut.trans hp.cut.2
    freeze_le := (arming_vote_add p s).le
    epoch := (arming_receiver_epoch hp.base.valid.toScheduleWellFormed hx hs).mono
      le_rfl (fgsa_idxBefore_mono rho heg)
    handlers := by simpa only [arming_vote_add] using hhandlers
    not_excluded := by simpa only [arming_vote_add] using hnx }⟩

/-- Transport, readiness and epoch come from the regime and protected receiver.
Handler acceptance and exclusion remain local proof obligations. -/
theorem arming_fresh_head_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
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
  exact arming_fresh_head_service_of_prefix h.pre hx hs hcut hy he hhandlers hnx

/-- Healthy-prefix supplier for arming_proposal_service_trigger. -/
theorem arming_proposal_service_trigger_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
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
  obtain ⟨_, hA, hR⟩ := arming_receiver_window hx hs
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hdeadline : a + p.Δ ≤ SA.earlyTime p.toParams s := by
    rw [← arming_vote_add]
    exact add_le_add hav le_rfl
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams (coverLabel p b₀) := by
    apply le_trans _ ((arming_gate_le_iff p s _).mpr hsj)
    rw [arming_early_eq, arming_gate_eq]
    have hd := p.deltaPos
    dsimp [Time] at *
    omega
  have ha : 0 ≤ a := le_trans (by unfold slotStartZ; have hd := p.deltaPos; positivity) hstart
  have hready : Gen.V2.Duty.ReadyTrigger E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send x a (a + p.Δ) := by
    refine ⟨y, hy, he, ?_⟩
    intro t hat htd
    exact hA t (ha.trans hat) (hstart.trans hat) (htd.le.trans (hdeadline.trans heg))
  have hepoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) := by
    apply Gen.V2.Duty.restartFree_actionCut_idxBefore hp.base.valid.toScheduleWellFormed
      (hav.trans_lt (arming_vote_lt_early p s).1)
    intro k w hw haw hwe
    exact hR w (hstart.trans_lt haw) (hwe.le.trans heg) (List.mem_of_getElem? hw)
  exact ⟨{
    dl := fun t => t + p.Δ
    cut := b₀
    anchor := a
    within := arming_nonrow_delivery_of_prefix hp
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

/-- A proposal service uses the healthy prefix and this receiver's current epoch.
Safe replay history, dependencies, timely handling and exclusion need local proofs. -/
theorem arming_proposal_service_trigger [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
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
  exact arming_proposal_service_trigger_of_prefix h.pre hx hs hcut hy he hsa hstart hav
    hhistory hhandlers hnx

/-- A proposal service uses the healthy prefix and this receiver's current epoch.
Safe replay history, dependencies, timely handling and exclusion need local proofs. -/
theorem arming_proposal_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Slot} {N : NamedProposal p.n}
    {send a : Time} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send)
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
  exact arming_proposal_service_trigger h hx hs hcut hy (Or.inl he) hsa hstart hav
    hhistory hhandlers hnx

/-- Current cut rows pass to the actual pending gate in the same epoch. -/
theorem arming_pending_rows_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time} {l : Slot} {B D : Block}
    (hl : SA.gateTime p.toParams l ≤ b₀) (hcut : b₀ < SA.gateTime p.toParams (l + 1))
    {x : V} {i : Nat} (hi : IsGateTick p c rho i x (l + 1))
    (hCutEpoch : V2.D.restartFree rho x (timeIdx rho b₀)
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))))
    (hTickEpoch : V2.D.restartFree rho x
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))) i)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k x) D)
    (hrows : ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base
        (l + 1 - (a + 1)) = some (some Ca) ∧ Block.Preceq B Ca ∧ Block.Preceq Ca D) :
    ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
      Block.Preceq B Ca := by
  rw [arming_tick_store_on hs hi hTickEpoch]
  exact arming_slow_saved_on hs hl (arming_timeIdx_le_idxBefore rho hcut)
    le_rfl hCutEpoch hF hrows

/-- Consume the exact current-row producer through the Clean assembly input. -/
theorem arming_cut_saved_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {b₀ : Time} (hState : CleanState p c E rho (timeIdx rho b₀))
    (hSaved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} {q l : Slot} {B D : Block} (hx : x ∈ rho.honest) (hql : q ≤ l)
    (hcut : SA.gateTime p.toParams q ≤ b₀)
    (hAw : AwakeClosed E x (slotStartZ p (q : Int)) b₀)
    (hEpoch : RestartFreeTime rho x (slotStartZ p (q : Int)) b₀)
    (hOrigin : B = .genesis ∨ ∃ r C, r < q ∧
      (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C)
    (hmax : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) →
      r ≤ l → Block.Preceq C D) :
    Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
      ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
        some (some C) ∧ Block.Preceq B C ∧ Block.Preceq C D := by
  rcases hSaved hx hcut hAw hEpoch hOrigin with hF | ⟨C, hC, hBC⟩
  · exact Or.inl hF
  obtain ⟨j, hji, _, hG, hRes⟩ := hState.savedOnly x q C hC
  have hmem : (q, C) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
    ⟨j, hji, x, hG.1, hG.2, hRes⟩
  exact Or.inr ⟨C, hC, hBC, hmax q C hmem hql⟩

/-- A proposal handler is direct; carried handlers contain only HEADs and rows. -/
private theorem arming_proposal_direct (st : State p.n) (parent o : Obj p)
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

/-- Healthy-prefix supplier for arming_proposal_anchor_service. -/
theorem arming_proposal_anchor_service_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Slot} {N : NamedProposal p.n}
    {send : Time} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (ht : send ≤ SA.voteTime p.toParams s)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send (SA.earlyTime p.toParams s) x) := by
  have hV := hp.base.valid
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
          fgsa_admissionTime_public p E hp.base.delta obj) y k _ send hacc
      rw [fgsaTimelyClock_actTime] at hbound
      exact hbound.trans (Gen.V2.Duty.pubFloor_le E send)
  have hStart : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    exact le_add_of_nonneg_right p.deltaPos.le
  apply arming_proposal_service_trigger_of_prefix hp hx hs hcut hy he ht hStart le_rfl
    (fgsa_historySafeAt_of_proposal x _ _ rfl)
  · intro j u hvu hue hh
    obtain ⟨parent, hj, hhandle⟩ := hh
    have hEq := arming_proposal_direct _ parent _ rfl hhandle
    subst parent
    refine ⟨hV.wire j x _ u hj, hV.deps j x _ u hj, ?_⟩
    have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
      refine ⟨4 * s + 1, ?_⟩
      rw [hp.base.delta]
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

/-- The public vote anchor supplies proposal history and timely checked handlers. -/
theorem arming_proposal_anchor_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Slot} {N : NamedProposal p.n}
    {send : Time} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (ht : send ≤ SA.voteTime p.toParams s)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send (SA.earlyTime p.toParams s) x) := by
  exact arming_proposal_anchor_service_of_prefix h.pre hx hs hcut hy he ht hNX

private theorem arming_source_decode {o : Obj p} {K : Block}
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

/-- Healthy-prefix supplier for arming_target_service. -/
theorem arming_target_service_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
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
  obtain ⟨q, N, rfl, hNK⟩ := arming_source_decode ho
  have hsend : send ≤ SA.voteTime p.toParams s := by
    obtain ⟨parent, hj, _⟩ := hacc.1
    by_contra hn
    have hij := V2.D.Engine.tick_index_lt_delivery E rho
      hp.base.valid.toScheduleWellFormed hi hj (le_of_not_ge hn)
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
    (arming_proposal_anchor_service_of_prefix hp hx hs hcut hy (Or.inr ⟨j, hacc⟩) hsend hNX)

/-- Retained targets use their original source acceptance, including across restart. -/
theorem arming_target_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {K : Block} {i : Nat}
    (hy : y ∈ rho.honest) (hi : rho.events[i]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho i y).base.blocks)
    (hCompat : Block.Compatible K
      (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.fg.F)) :
    TargetReceiptService E rho K (SA.earlyTime p.toParams s) x := by
  exact arming_target_service_of_prefix h.pre hx hs hcut hy hi hK hCompat

/-- Healthy-prefix supplier for arming_head_not_excluded. -/
theorem arming_head_not_excluded_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF)
    {x y : V} (_hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (_hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (_hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Fin p.n} {b : BlockId}
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  have hV := hp.base.valid
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

/-- An honest fresh HEAD cannot be excluded by an old label or by equivocation. -/
theorem arming_head_not_excluded [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (_hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (_hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (_hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Fin p.n} {b : BlockId}
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  exact arming_head_not_excluded_of_prefix h.pre _hx _hs _hcut hy he

/-- HEAD handlers have checked dependencies and a clock past their public label start. -/
theorem arming_head_handlers {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (q : Fin p.n) (b : BlockId) (x : V) :
    ∀ j u, SA.voteTime p.toParams s ≤ u → u < SA.earlyTime p.toParams s →
      V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) u →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (rho.stateBefore E j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (rho.stateBefore E j x) (ofHead p ⟨.seat (.head s) q, b⟩) := by
  intro j u hvu hue hh
  have hcall := hh
  obtain ⟨parent, hj, _⟩ := hh
  have deps := fgsa_hReady_of_not_block
    (dl := fun _ => SA.earlyTime p.toParams s) (t := SA.voteTime p.toParams s)
    (o := ofHead p ⟨.seat (.head s) q, b⟩) (by intro r N h; cases h)
    (fgsa_hWF_of_delivery hV.wire) j u
    ((Gen.V2.Duty.index_lt_idxBefore_iff hV.toScheduleWellFormed hj _).mpr hue) hcall
  refine ⟨deps.1, deps.2, ?_⟩
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  have h0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hpu : SA.proposalTime p.toParams s ≤ u :=
    (show SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s from by
      change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
      exact le_add_of_nonneg_right p.deltaPos.le).trans hvu
  have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hV hj hpub h0 hpu
  change 4 * p.Δ * (s : Int) ≤ (rho.stateBefore E j x).st.base.now
  rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
  exact hn

/-- Healthy-prefix supplier for arming_batch_service. -/
theorem arming_batch_service_of_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF)
    {x : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) :
    ArmingBatchReceiptService E rho x s (SA.earlyTime p.toParams s) := by
  classical
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
    by_cases hbad : ¬ Block.Compatible K
        (eraseFG (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.fg.F)
    · exact Or.inl hbad
    · right
      have hHead := arming_fresh_head_service_of_prefix hp hx hs hcut hy ⟨k, hk, hem⟩
        (arming_head_handlers hp.base.valid hp.base.delta s q b x)
        (arming_head_not_excluded_of_prefix hp hx hs hcut hy ⟨k, hk, hem⟩)
      have hK : K ∈ (storeAt p c E rho k y).base.blocks := by
        have hm := headVote_stored p _
          (storeBundle_postClock E rho k y (SA.voteTime p.toParams s)).cstore s
        change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
        rwa [clock_base_blocks] at hm
      exact ⟨hHead, arming_target_service_of_prefix hp hx hs hcut hy hk hK (not_not.mp hbad)⟩
  · intro y o m q N hy he htime hNX hd
    have ho : o = ofWire p ⟨.proposer q, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    subst o
    exact arming_proposal_anchor_service_of_prefix hp hx hs hcut hy (Or.inl he) htime hNX

/-- The regime supplies all batch service inputs for each in-cut protected label. -/
theorem arming_batch_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) :
    ArmingBatchReceiptService E rho x s (SA.earlyTime p.toParams s) := by
  exact arming_batch_service_of_prefix h.pre hx hs hcut

/-- In-cut prefix receipts need only the healthy prefix and protected receiver windows. -/
theorem arming_prefix_receipt_of_healthy_prefix [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ ΔF : Time}
    (hp : HealthyPrefix₂ p c E rho b₀ ΔF) :
    OutagePrefixReceipt p c E rho fast T b₀ := by
  apply arming_prefix_batch_receipt_on hp.base.valid hp.base.receiptIdealization
  intro x hx q hq _hT hCut
  exact arming_batch_service_of_prefix hp hx hq hCut

/-- Continuation-prefix producer for outage_continuation_receipt_of_prefix. -/
theorem arming_continuation_prefix_receipt [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutagePrefixReceipt p c E rho fast T b₀ := by
  exact arming_prefix_receipt_of_healthy_prefix h.pre

/-- Corrected P15-CUT prefix receipt, with all services derived from the regime. -/
theorem arming_prefix_batch_receipt (p : Params) : OutagePrefixReceiptDerivedClaim p := by
  intro In V inst instF c E rho fast T b₀ b₁ ΔF h
  exact arming_prefix_receipt_of_healthy_prefix h.pre

/-- A durable stable read has an actual positive-label Clean origin before the read. -/
theorem arming_protected_origin_on {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho) {T b₀ : Time}
    (hT : T ≤ b₀) (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀)) {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ r C, 1 ≤ r ∧ (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
      SA.gateTime p.toParams r ≤ T ∧ Block.Preceq B C := by
  rw [arming_stable_read hs] at hread
  have hi := arming_timeIdx_mono rho hT
  have hLift {i : Nat} (hit : i ≤ timeIdx rho T) {r : Slot} {C : Block}
      (hc : (r, C) ∈ cleanResults p c E rho i) :
      (r, C) ∈ cleanResults p c E rho (timeIdx rho T) := by
    obtain ⟨j, hj, y, ht, hJ, hC⟩ := hc
    exact ⟨j, hj.trans_le hit, y, ht, hJ, hC⟩
  have hCandidate : ∃ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho T) ∧
      Block.Preceq B C := by
    rcases (hState _ hi).sOrigin x with hg | ⟨j, hj, r, hgt, hres⟩ | ⟨j, hj, hSF⟩
    · rw [hg] at hread
      exact (hne (Gen.Pure.block_preceq_antisymm hread (Gen.Pure.block_genesis_preceq B))).elim
    · exact ⟨r, S_at p c E rho (timeIdx rho T) x,
        ⟨j, hj, x, hgt, (arming_enabled_of_result hs hgt hres).2, hres⟩, hread⟩
    · rw [hSF] at hread
      rcases (hState j (hj.trans hi)).fOrigin x |>.1 with hg | ⟨r, C, hC, _, hFC⟩
      · rw [hg] at hread
        exact (hne (Gen.Pure.block_preceq_antisymm hread
          (Gen.Pure.block_genesis_preceq B))).elim
      · exact ⟨r, C, hLift hj hC, Gen.Pure.block_preceq_trans hread hFC⟩
  obtain ⟨r, C, hC, hBC⟩ := hCandidate
  obtain ⟨j, hj, y, ht, hJ, hres⟩ := hC
  have hcut : (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) :=
    ⟨j, hj.trans_le hi, y, ht, hJ, hres⟩
  have hr : 1 ≤ r := by
    by_contra hn
    have hr0 : r = 0 := by
      dsimp only [Slot] at hn ⊢
      omega
    obtain ⟨C', hC', hgen⟩ := hHist.nonempty j y r (hj.trans_le hi) ⟨ht, hJ⟩
    have hCC : C = C' := Option.some.inj (Option.some.inj (hres.symm.trans hC'))
    have hCg : C = .genesis := hCC.trans (hgen hr0)
    rw [hCg] at hBC
    exact hne (Gen.Pure.block_preceq_antisymm hBC (Gen.Pure.block_genesis_preceq B))
  exact ⟨r, C, hr, hcut, arming_tick_le hs ht hj, hBC⟩

/-- Slow protected receivers rebuild each needed row in their current epoch at the cut. -/
theorem arming_slow_current_rows_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hState : CleanState p c E rho (timeIdx rho b₀))
    (hSaved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} (hx : x ∈ coveredNodes p E rho false b₀) {B D : Block} {r : Slot} {C : Block}
    (hr : 1 ≤ r) (hOrigin : (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀))
    (hTime : SA.gateTime p.toParams r ≤ T) (hBC : Block.Preceq B C)
    (hmax : ∀ q A, (q, A) ∈ cleanResults p c E rho (timeIdx rho b₀) →
      q ≤ ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat → Block.Preceq A D) :
    Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
      ∀ a < p.k - 1, ∃ Ca,
        GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base
          (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1 - (a + 1)) = some (some Ca) ∧
        Block.Preceq B Ca ∧ Block.Preceq Ca D := by
  classical
  by_cases hF : Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x)
  · exact Or.inl hF
  right
  intro a ha
  let l := ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat
  have hgap : r + p.k ≤ l + 1 := arming_slow_gap p r T b₀ hTime h.lag
  have hq := arming_slow_window_label p r l a hr hgap ha
  have hScope : (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤
      (l + 1 - (a + 1) : Nat) ∧ l + 1 - (a + 1) ≤ coverLabel p b₀ := by
    change ((l + 1 : Nat) : Int) - (p.k : Int) + 1 ≤
      (l + 1 - (a + 1) : Nat) ∧ l + 1 - (a + 1) ≤ l + 1
    have hk := p.kLarge
    dsimp only [Slot] at *
    omega
  obtain ⟨hxH, hAw, hEpoch⟩ := arming_receiver_window hx hScope
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hg0 := (arming_gate_le_iff p 0 r).mpr (Nat.zero_le r)
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using
      hg0.trans (hTime.trans h.order.2.1)
  have hlabel := arming_label p b₀ h6
  have hcut : SA.gateTime p.toParams (l + 1 - (a + 1)) ≤ b₀ :=
    ((arming_gate_le_iff p _ l).mpr hq.2.1).trans hlabel.1
  have hUpper : b₀ ≤ SA.gateTime p.toParams (coverLabel p b₀) := hlabel.2.le
  have hrow := arming_cut_saved_on hState hSaved hxH hq.2.1 hcut
    (fun t ht hs hc => hAw t ht hs (hc.trans hUpper))
    (fun t hs hc he => hEpoch t hs (hc.trans hUpper) he)
    (Or.inr ⟨r, C, lt_of_lt_of_le (Nat.lt_succ_self r) hq.1, hOrigin, hBC⟩) hmax
  exact hrow.resolve_left hF

omit [DecidableEq V] in
/-- Equal-time phases at an early tick stay in the protected receiver's epoch. -/
theorem arming_receiver_read_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hS : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    {i : Nat} (hi : rho.events[i]? = some (.tick x (SA.earlyTime p.toParams s))) :
    V2.D.restartFree rho x (rho.idxBefore (SA.earlyTime p.toParams s)) i := by
  classical
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hs
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  intro k w hstart hki he
  have hw : SA.earlyTime p.toParams s ≤ w := by
    by_contra hn
    have hk := (Gen.V2.Duty.index_lt_idxBefore_iff hS he _).mpr (lt_of_not_ge hn)
    omega
  have hwe : w ≤ SA.earlyTime p.toParams s := by
    by_contra hn
    have hik := V2.D.Engine.eventIndex_lt_of_time_lt hS hi he (lt_of_not_ge hn)
    omega
  have hse : slotStartZ p (s : Int) < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]
    linarith [p.deltaPos]
  exact hR w (hse.trans_le hw)
    (hwe.trans (heg.trans ((arming_gate_le_iff p s _).mpr hsj))) (List.mem_of_getElem? he)

/-- T25: the joined batch at a protected receiver uses regime-derived receipt services. -/
theorem arming_healthy_batch_protected [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hD : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    {x : V} (hx : x ∈ coveredNodes p E rho fast b₀)
    (hLabel : coverLabel p b₀ = l + 1)
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
  have hScope : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hLabel]
    cases fast with
    | true => exact rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk : (1 : Int) ≤ (p.k : Int) := by
        exact_mod_cast (show 1 ≤ p.k by have := p.kLarge; omega)
      exact ⟨by omega, le_rfl⟩
  obtain ⟨hxH, _, _⟩ := arming_receiver_window hx hScope
  have hcut := (arming_early_next p l).trans_le hl
  apply arming_healthy_batch hV h.pre.base.delta h.pre.cut htransfer hl hD x hxH
    (arming_receiver_times hx hScope).1
    (fun k hk => arming_receiver_read_epoch hS hx hScope hk)
  · intro q K hq hTarget
    obtain ⟨k, hk, hem⟩ : V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) := by
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
      exact ⟨k, hk, hem⟩
    have hJoin := fgsa_joinedAt_of_emitted_head E rho hV hk hem
    have hK := headTargetAtEmission_at_tick E rho hS hTarget hk rfl
    have hDK := arming_head_ge_on hS htransfer hD hq hJoin hk
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
    exact ⟨arming_fresh_head_service h hx hScope hcut hq ⟨k, hk, hem⟩
        (arming_head_handlers hV h.pre.base.delta (l + 1) q K.root x)
        (arming_head_not_excluded h hx hScope hcut hq ⟨k, hk, hem⟩),
      arming_target_service h hx hScope hcut hq hk hKm
        (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K)
          (Gen.Pure.block_preceq_trans hFloor hDK))⟩
  · exact h.pre.base.receiptIdealization

end AvailableChain.FGSA.Run
end

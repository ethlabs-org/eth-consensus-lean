module
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun -- shake: keep (source declarations)
public import AvailableChainFGSAClaims.Statements.Join
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (source declarations)
public import AvailableChainFGSARun.Proofs.Join
public import AvailableChainFGSARun.Proofs.HeadHistory
public import AvailableChainFGSARun.Proofs.ReadFacts

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A trigger uses a scheduled event inside the nonnegative run horizon. -/
theorem fgsa_trigger_nonneg (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {o : Obj p} {t : Time}
    (hT : Gen.V2.Duty.Trigger E rho o t) : 0 ≤ t := by
  rcases hT with ⟨v, _, i, he, _⟩ | ⟨v, _, i, ⟨parent, he, _⟩, _, _⟩ <;>
    exact (hS.in_horizon _ (List.mem_of_getElem? he)).1

/-- A valid receiver tick supplies the earlier awake interval on a NoRestart run. -/
theorem fgsa_awakeOn_before_tick_noRestart (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) {i : Nat} {x : V} {t : Time}
    (hi : rho.events[i]? = some (.tick x t)) (hx : x ∈ rho.honest)
    {a d : Time} (ha : 0 ≤ a) (hd : d ≤ t) : V2.D.AwakeOn E x a d := by
  intro u hau hud
  exact fgsa_awake_before_noRestart E rho hV hN x hx t
    (hV.in_horizon _ (List.mem_of_getElem? hi)).2
    (hV.tick_awake x t (List.mem_of_getElem? hi)) u (ha.trans hau) (hud.le.trans hd)

/-- The legacy NoRestart premise supplies the exact join guard at an existing tick. -/
theorem fgsa_joinedNow_noRestart (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {t : Time} (hi : rho.events[i]? = some (.tick x t)) :
    joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) t).st = true := by
  apply fgsa_joinedNow_of_joinedEnv E rho hS hi
  intro w _ _ he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  exact (hN j x w hj).elim

/-- N4: ready service gives processing strictly before the deadline, and it
persists to the freeze in the same receiver epoch. Retained history must be safe. -/
theorem fgsa_catchUp_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (dl : Time → Time) (cut : Time) (o : Obj p) (send a freeze : Time) (x : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hQ : ¬ isRowObject o)
    (hT : Gen.V2.Duty.ReadyTrigger E rho o send x a (dl a))
    (hx : x ∈ rho.honest) (hsa : send ≤ a) (ha : 0 ≤ a) (had : a < dl a)
    (hc : dl a ≤ cut) (hh : dl a ≤ rho.horizon) (hfreeze : dl a ≤ freeze)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho x o a)
    (hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho freeze))
    (hReady : ∀ j t', a ≤ t' → t' < dl a → V2.D.Run.handlesAt E rho j x o t' →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) o)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x) o = false) :
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho (dl a) x) o = true ∧
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho freeze x) o = true := by
  have hidx := fgsa_idxBefore_mono rho hfreeze
  have hService := Gen.V2.Duty.service_of_readyTrigger hD hQ hT hx hsa ha had hc hh hNX
  have hp := Gen.V2.Duty.processed_by_deadline_of_service E rho (fgsaTimely p)
    (fgsaAcceptanceInv p) x o a (dl a) hS had hService hHistory
    (hRF.mono le_rfl hidx) (fgsaHooks p c) (fgsaAcceptance p c)
    (fun j t' hat htd hj =>
      ⟨cstoreInv_stateBefore E rho j x, hReady j t' hat htd hj⟩) hNX
  refine ⟨hp, ?_⟩
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho freeze hS]
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl a) hS] at hp
  exact (fgsaHooks p c).processed_stable E rho hS x o _ _ hidx
    (hRF.mono (Gen.V2.Duty.actionCut_le_idxBefore hS had) le_rfl) hp

/-- A fresh honest HEAD has no historical processing at its emission action cut.
The scope is the exact emitted object, sender tick and receiver. -/
theorem fgsa_historySafeAt_of_emitted_head (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t))
    (s : Slot) (q : Fin p.n) (b : BlockId)
    (ho : ofHead p ⟨.seat (.head s) q, b⟩ ∈ V2.D.Run.emitsAt E rho i) (x : V) :
    Gen.V2.Duty.HistorySafeAt E rho x (ofHead p ⟨.seat (.head s) q, b⟩) t := by
  apply Gen.V2.Duty.historySafeAt_of_fresh
  rintro ⟨k, hk, hp⟩
  have hcut : V2.D.Run.actionCut rho t ≤ i := by
    by_contra hn
    have h := (V2.D.Engine.index_lt_actionCut_iff hV.toScheduleWellFormed hi t).mp
      (Nat.lt_of_not_ge hn)
    simp [V2.Event.time, V2.Event.phase] at h
  have hf := fgsa_emitted_head_no_prior_processed E rho hV hi s q b ho k
    (hk.trans hcut) x
  rw [hp] at hf
  cases hf

/-- N4 HEAD receipt with an exact ready anchor, safe history and a local receiver epoch.
The handler premises are at the service window, not at every earlier event. -/
theorem fgsa_head_receipt_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (dl : Time → Time) (cut : Time) (s : Slot) (q : Fin p.n) (b : BlockId)
    (send a freeze : Time) (x : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.ReadyTrigger E rho (ofHead p ⟨.seat (.head s) q, b⟩)
      send x a (dl a))
    (hx : x ∈ rho.honest) (hsa : send ≤ a) (ha : 0 ≤ a) (had : a < dl a)
    (hc : dl a ≤ cut) (hh : dl a ≤ rho.horizon) (hfreeze : dl a ≤ freeze)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho x (ofHead p ⟨.seat (.head s) q, b⟩) a)
    (hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho freeze))
    (hReady : ∀ j t', a ≤ t' → t' < dl a →
      V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) t' →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofHead p ⟨.seat (.head s) q, b⟩))
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (dl a) x).st.base.votes ∧
    baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho freeze x).st.base.votes := by
  have hp := fgsa_catchUp_before_freeze E rho hS dl cut
    (ofHead p ⟨.seat (.head s) q, b⟩) send a freeze x hD
    (by change ¬ False; exact not_false) hT hx hsa ha had hc hh hfreeze hHistory hRF hReady hNX
  exact ⟨of_decide_eq_true hp.1, of_decide_eq_true hp.2⟩

/-- N7 supplier: a joined reader at a gate gives the exact store guard.
The caller supplies the approved environment restart bound at this same tick. -/
theorem fgsa_gate_joined_of_joinedEnv (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hJ : ∀ w, 0 ≤ w → w ≤ SA.gateTime p.toParams s →
      V2.Event.restart x w ∈ rho.events → w ≤ 4 * p.Δ * (s : Int)) :
    joinedAtTime p (V2.D.Run.stateBefore E rho i x).st.restartTime
      (SA.gateTime p.toParams s) = true := by
  have hj := fgsa_joinedNow_of_joinedEnv E rho hS hi (by
    intro w hw ht he
    have hs := fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i x) s
    have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
      exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans hs
    rw [hslot]
    have hbound := hJ w hw ht he
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hbound)
  change joinedNow p (FGSA.clock p _ _) = true at hj
  unfold joinedNow at hj
  rw [fgsa_clock_restartTime, (clock_vn _ _).2] at hj
  exact hj

/-- A NoRestart run enables each existing gate tick. -/
theorem fgsa_enabledGate_noRestart (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot} (hi : IsGateTick p c rho i x s) :
    enabledGateAt p c E rho i x s := by
  refine ⟨hi, ?_⟩
  have hb := fgsa_restartTime_bound E rho i x (4 * p.Δ * (s : Int)) (by
    intro j w _ hj
    exact (hN j x w hj).elim)
  change (match (V2.D.Run.stateBefore E rho i x).st.restartTime with
    | none => True
    | some w => w ≤ 4 * p.Δ * (s : Int))
  cases hr : (V2.D.Run.stateBefore E rho i x).st.restartTime with
  | none => trivial
  | some w => exact hb w hr

/-- The enabled gate supplies the exact join test used by the gate law. -/
theorem fgsa_gate_joined_of_enabled (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {i : Nat} {x : V} {s : Slot}
    (hEnabled : enabledGateAt p c E rho i x s) :
    joinedAtTime p (V2.D.Run.stateBefore E rho i x).st.restartTime
      (SA.gateTime p.toParams s) = true := by
  have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i x) s)
  have hg := hEnabled.2
  change (match (V2.D.Run.stateBefore E rho i x).st.restartTime with
    | none => True
    | some w => w ≤ 4 * p.Δ * (s : Int)) at hg
  cases hr : (V2.D.Run.stateBefore E rho i x).st.restartTime with
  | none => rfl
  | some w =>
    rw [hr] at hg
    change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) = true
    simpa only [hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      decide_eq_true_eq] using hg

/-- P11: a scheduled gate saves the executed result in both join branches. -/
theorem fgsa_gate_saved_guarded (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s))) :
    let st := (V2.D.Run.stateBefore E rho i x).st
    GridCO.savedGenuine (FGSA.clock p st (SA.gateTime p.toParams s)).base s =
      some (if joinedAtTime p st.restartTime (SA.gateTime p.toParams s) then
          SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
            (actView (clockPre p st (SA.gateTime p.toParams s))) s
        else none) := by
  intro st
  cases hj : joinedAtTime p st.restartTime (SA.gateTime p.toParams s) with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact fgsa_gate_saved_unjoined E rho hS hi hj
  | true =>
    simp only [ite_true]
    exact fgsa_gate_saved_result E rho hS hi hj

/-- A stored HEAD at a strict time cut has a strict stamp, including local replay. -/
theorem fgsa_head_stamp_before_read (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (D : Time) (s : Slot) (q : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBeforeTime E rho D x).st.base.votes) :
    GridCO.stampVote (V2.D.Run.stateBeforeTime E rho D x).st.base
      ⟨.seat s q, .head b⟩ < D := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hm ⊢
  have hk := hm
  rw [← fgsa_vote_stamp_keys E rho _ x] at hk
  obtain ⟨⟨v, stamp⟩, hv, he⟩ := List.mem_map.mp hk
  dsimp only at he
  subst v
  unfold GridCO.stampVote
  cases hf : (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) x).st.base.voteStamp.find?
      (fun row => row.1 == (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root)) with
  | none =>
    have hn := List.find?_eq_none.mp hf (_, stamp) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row =>
    have heq : row.1 = (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) :=
      by simpa only [beq_iff_eq] using List.find?_some hf
    have hr := List.mem_of_find?_eq_some hf
    have hr' : ((⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root), row.2) ∈
        (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) x).st.base.voteStamp := by
      simpa only [← heq, Prod.mk.eta] using hr
    change row.2 < D
    rcases fgsa_vote_stamp_source_or_restart E rho _ x s q b row.2 hr' with
      ⟨j, hj, t, ha, hs⟩ | ⟨j, hj, w, he, hs, _⟩
    · obtain ⟨o, he, _⟩ := ha.1
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mp hj
      have hc := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hS he x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hc
      rw [hs]
      exact hc.trans_lt ht
    · rw [hs]
      exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mp hj

/-- N4 processing of a named proposal gives its exact body under P23-A.
The retained branch must supply HistorySafeAt at its own ready anchor. -/
theorem fgsa_proposal_receipt_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (dl : Time → Time) (cut : Time) (s : Slot) (N : NamedProposal p.n)
    (send a freeze : Time) (x : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.ReadyTrigger E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      send x a (dl a))
    (hx : x ∈ rho.honest) (hsa : send ≤ a) (ha : 0 ≤ a) (had : a < dl a)
    (hc : dl a ≤ cut) (hh : dl a ≤ rho.horizon) (hfreeze : dl a ≤ freeze)
    (hHistory : Gen.V2.Duty.HistorySafeAt E rho x (ofWire p ⟨.proposer s, .proposal N⟩) a)
    (hRF : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho freeze))
    (hReady : ∀ j t', a ≤ t' → t' < dl a →
      V2.D.Run.handlesAt E rho j x (ofWire p ⟨.proposer s, .proposal N⟩) t' →
      (fgsa p c).wellFormed (ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofWire p ⟨.proposer s, .proposal N⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofWire p ⟨.proposer s, .proposal N⟩))
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl a) x)
      (ofWire p ⟨.proposer s, .proposal N⟩) = false) :
    ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho freeze x).st.fg.TF,
      eraseFG Y = N.erase := by
  let o := ofWire p (⟨.proposer s, .proposal N⟩ : Wire p.n)
  have hp := (fgsa_catchUp_before_freeze E rho hS dl cut o send a freeze x hD
    (by change ¬ False; exact not_false) hT hx hsa ha had hc hh hfreeze hHistory hRF
    hReady hNX).2
  have hd : (toWire p o).decode = some (.block s N) := by rw [toWire_ofWire]; rfl
  have hReceiptScope : NamedProposalReceiptScope p c E rho N := by
    obtain ⟨v, hv, ht, _⟩ := hT
    exact proposal_trigger_in_receipt_scope E rho s N send (by
      rcases ht with hem | ⟨i, hi⟩
      · exact Or.inl ⟨v, hv, hem⟩
      · exact Or.inr ⟨v, hv, i, hi⟩)
  have hpidx := hp
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho freeze hS] at hpidx
  have hScope := proposal_processed_in_scope E rho hRoots hx _ s N hReceiptScope hpidx
  change processedS p (V2.D.Run.stateBeforeTime E rho freeze x).st o = true at hp
  dsimp only [processedS] at hp
  rw [hd] at hp
  obtain ⟨Y, hY, hroot⟩ := of_decide_eq_true hp
  have hYscope : RootBlockInRun p c E rho (eraseFG Y) := by
    have hm := (storeBundle_stateBeforeTime E rho freeze x).cstore.baseTree
      (eraseFG Y) |>.mpr ⟨Y, hY, rfl⟩
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho freeze hS] at hm
    exact rootBlockInRun_held E rho hx _ hm
  exact ⟨Y, hY, rootBlockInRun_eq E rho (hRoots.toNamedRootCollisionFree E rho)
    hYscope ⟨N, hScope, rfl⟩ (by simpa using (eraseFG_root Y).trans hroot)⟩

/-- Exact N4 inputs for one receiver and one object. Earlier local epochs are allowed.
For a retained object, the caller must supply safe history at `anchor`. -/
structure ReceiverService (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (send freeze : Time) (x : V) where
  dl : Time → Time
  cut : Time
  anchor : Time
  within : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut
  ready : Gen.V2.Duty.ReadyTrigger E rho o send x anchor (dl anchor)
  send_le : send ≤ anchor
  nonneg : 0 ≤ anchor
  later : anchor < dl anchor
  cut_le : dl anchor ≤ cut
  horizon : dl anchor ≤ rho.horizon
  freeze_le : dl anchor ≤ freeze
  history : Gen.V2.Duty.HistorySafeAt E rho x o anchor
  epoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho anchor)
    (V2.D.Run.idxBefore rho freeze)
  handlers : ∀ j t, anchor ≤ t → t < dl anchor → V2.D.Run.handlesAt E rho j x o t →
    (fgsa p c).wellFormed o = true ∧
    (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
    fgsaTimely p (V2.D.Run.stateBefore E rho j x) o
  not_excluded : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl anchor) x) o = false

/-- A ready receiver processes the exact service object before the freeze. -/
theorem ReceiverService.processed {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {o : Obj p} {send freeze : Time} {x : V}
    (h : ReceiverService E rho o send freeze x)
    (hS : V2.D.ScheduleWellFormed E rho) (hx : x ∈ rho.honest) (hQ : ¬ isRowObject o) :
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho freeze x) o = true :=
  (fgsa_catchUp_before_freeze E rho hS h.dl h.cut o send h.anchor freeze x h.within hQ
    h.ready hx h.send_le h.nonneg h.later h.cut_le h.horizon h.freeze_le h.history h.epoch
    h.handlers h.not_excluded).2

/-- Ready named-proposal service returns the exact body at its freeze. -/
theorem ReceiverService.proposal {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {s : Slot} {N : NamedProposal p.n} {send freeze : Time} {x : V}
    (h : ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send freeze x)
    (hS : V2.D.ScheduleWellFormed E rho) (hx : x ∈ rho.honest)
    (hRoots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho freeze x).st.fg.TF, eraseFG Y = N.erase :=
  fgsa_proposal_receipt_on E rho hS hRoots h.dl h.cut s N send h.anchor freeze x h.within
    h.ready hx h.send_le h.nonneg h.later h.cut_le h.horizon h.freeze_le h.history h.epoch
    h.handlers h.not_excluded

/-- Exact fresh HEAD service. History safety follows from the named emission tick. -/
structure FreshHeadService (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (q : Fin p.n) (b : BlockId) (freeze : Time) (x : V) where
  dl : Time → Time
  cut : Time
  within : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut
  ready : Gen.V2.Duty.ReadyTrigger E rho (ofHead p ⟨.seat (.head s) q, b⟩)
    (SA.voteTime p.toParams s) x (SA.voteTime p.toParams s) (dl (SA.voteTime p.toParams s))
  later : SA.voteTime p.toParams s < dl (SA.voteTime p.toParams s)
  cut_le : dl (SA.voteTime p.toParams s) ≤ cut
  horizon : dl (SA.voteTime p.toParams s) ≤ rho.horizon
  freeze_le : dl (SA.voteTime p.toParams s) ≤ freeze
  epoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
    (V2.D.Run.idxBefore rho freeze)
  handlers : ∀ j t, SA.voteTime p.toParams s ≤ t → t < dl (SA.voteTime p.toParams s) →
    V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) t →
    (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
    (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
    fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofHead p ⟨.seat (.head s) q, b⟩)
  not_excluded : (fgsa p c).excludes
    (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams s)) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false

/-- Fresh HEAD service gives membership and a strict freeze stamp. -/
theorem FreshHeadService.receipt {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {s : Slot} {q : Fin p.n} {b : BlockId} {freeze : Time} {x v : V} {i : Nat}
    (h : FreshHeadService E rho s q b freeze x) (hV : V2.D.ExecutionValid E rho)
    (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (SA.voteTime p.toParams s)))
    (ho : ofHead p ⟨.seat (.head s) q, b⟩ ∈ V2.D.Run.emitsAt E rho i) :
    baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho freeze x).st.base.votes ∧
    GridCO.stampVote (V2.D.Run.stateBeforeTime E rho freeze x).st.base
      (baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n)) < freeze := by
  have hp := (fgsa_head_receipt_on E rho hV.toScheduleWellFormed h.dl h.cut s q b
    (SA.voteTime p.toParams s) (SA.voteTime p.toParams s) freeze x h.within h.ready hx
    le_rfl (by
      change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
      have hd := p.deltaPos
      positivity) h.later h.cut_le h.horizon
    h.freeze_le (fgsa_historySafeAt_of_emitted_head E rho hV hi s q b ho x) h.epoch
    h.handlers h.not_excluded).2
  exact ⟨hp, fgsa_head_stamp_before_read E rho hV.toScheduleWellFormed x freeze s q b hp⟩

/-- Environment joinedness at the exact vote tick supplies the executed duty guard. -/
theorem fgsa_head_joined_of_joinedAt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hJ : joinedAt p E rho x s (SA.voteTime p.toParams s)) :
    joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (SA.voteTime p.toParams s)).st = true := by
  apply fgsa_joinedNow_of_joinedEnv E rho hS hi
  have hd := p.deltaPos
  have hs : p.slotOf (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ hd.le (by dsimp [Time] at *; omega)
  intro w hw ht he
  rw [hs]
  exact hJ.2.2 w hw ht he

/-- A block target has a ready named proposal service, or is genesis.
Retained targets use an explicit receiver service, including safe replay history. -/
def TargetReceiptService (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (K : Block) (freeze : Time) (x : V) : Prop :=
  K = .genesis ∨ ∃ s N send, N.erase = K ∧
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩) send freeze x)

/-- Genesis needs no proposal receipt. -/
theorem fgsa_target_service_genesis
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (D : Time) (x : V) :
    TargetReceiptService E rho .genesis D x := Or.inl rfl

/-- A ready named proposal is a service for its exact erased target. -/
theorem fgsa_target_service_of_proposal
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (N : NamedProposal p.n) (send freeze : Time) (x : V)
    (h : Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      send freeze x)) : TargetReceiptService E rho N.erase freeze x :=
  Or.inr ⟨s, N, send, rfl, h⟩

/-- Target service gives exact base membership without a global epoch assumption. -/
theorem fgsa_target_receipt_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hRoots : NamedReceiptRootCollisionFree p c E rho)
    (K : Block) (freeze : Time) (x : V) (hx : x ∈ rho.honest)
    (h : TargetReceiptService E rho K freeze x) :
    K ∈ (V2.D.Run.stateBeforeTime E rho freeze x).st.base.blocks := by
  rcases h with rfl | ⟨s, N, send, rfl, ⟨h⟩⟩
  · exact ((storeBundle_stateBeforeTime E rho freeze x).cstore.baseTree _).mpr
      ⟨.genesis, (storeBundle_stateBeforeTime E rho freeze x).cstore.fg.gen, rfl⟩
  · obtain ⟨Y, hY, he⟩ := h.proposal hS hx hRoots
    exact ((storeBundle_stateBeforeTime E rho freeze x).cstore.baseTree _).mpr ⟨Y, hY, he⟩

/-- A base block at a strict time read has a strict stamp, also after restart. -/
theorem fgsa_block_stamp_before_read (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (D : Time) (hD : 0 < D) (K : Block)
    (hm : K ∈ (V2.D.Run.stateBeforeTime E rho D x).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBeforeTime E rho D x).st.base K < D := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hS] at hm ⊢
  have hk : K ∈ (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) x).st.base.blockStamp.map
      Prod.fst := by
    rw [(storeBundle_stateBefore E rho _ x).«meta».stampKeys]
    exact hm
  obtain ⟨⟨b, stamp⟩, hv, he⟩ := List.mem_map.mp hk
  dsimp only at he
  subst b
  unfold GridCO.stampBlock
  cases hf : (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) x).st.base.blockStamp.find?
      (fun row => row.1 == K) with
  | none =>
    have hn := List.find?_eq_none.mp hf (K, stamp) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row =>
    have heq : row.1 = K := by simpa only [beq_iff_eq] using List.find?_some hf
    have hr : (K, row.2) ∈
        (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) x).st.base.blockStamp := by
      simpa only [← heq, Prod.mk.eta] using List.mem_of_find?_eq_some hf
    change row.2 < D
    rcases fgsa_block_stamp_source_or_restart E rho _ x K row.2 hr with
      ⟨_, hs⟩ | ⟨j, hj, t, o, _, ha, hs⟩ | ⟨j, hj, w, he, _, _, hs⟩
    · rw [hs]
      exact hD
    · obtain ⟨o', he, _⟩ := ha.1
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mp hj
      have hc := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hS he x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hc
      rw [hs]
      exact hc.trans_lt ht
    · rw [hs]
      exact (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mp hj

omit [DecidableEq V] in
/-- Joinedness supplies awake at an earlier read after the join cutoff. -/
theorem fgsa_awake_of_joinedAt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) (t u : Time) (hJ : joinedAt p E rho x s t)
    (hu : 0 ≤ u) (hcut : slotStartZ p ((s : Int) - 1) ≤ u) (hut : u ≤ t) : E.awake x u = true := by
  classical
  by_contra hn
  obtain ⟨w, huw, hwt, hw⟩ := V2.D.Engine.wake_between hut (Bool.eq_false_iff.mpr hn) hJ.1
  have hwpos : 0 < w := hu.trans_lt huw
  exact (not_lt.mpr (hJ.2.1 w hwpos hwt hw)) (hcut.trans_lt huw)

/-- Each prior restart is at most the current local restart marker. -/
theorem fgsa_restartTime_ge (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {j i : Nat} {x : V} {w : Time}
    (hj : rho.events[j]? = some (.restart x w)) (hji : j < i) :
    ∃ u, (V2.D.Run.stateBefore E rho i x).st.restartTime = some u ∧ w ≤ u := by
  let Q : Node p → Prop := fun nd => ∃ u, nd.st.restartTime = some u ∧ w ≤ u
  apply V2.D.Engine.stateBefore_step_induction E rho Q (Nat.succ_le_of_lt hji) x
  · intro k e hjk hki he hn hQ
    obtain ⟨u, hu, hwu⟩ := hQ
    cases e with
    | restart y t =>
      change y = x at hn
      subst y
      have hwt : w ≤ t := by
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
        have hk := List.pairwise_iff_getElem.mp hS.sorted j k hjl hkl (by omega)
        rw [hje, hke] at hk
        exact V2.D.Engine.time_le_of_key_le _ _ hk
      refine ⟨t, ?_, hwt⟩
      simp only [V2.D.World.step, Function.update_self]
      exact acRestart_restartTime p _ t
    | tick y t =>
      change y = x at hn
      subst y
      refine ⟨u, ?_, hwu⟩
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t,
        fgsa_clock_restartTime]
      exact hu
    | deliver y o t =>
      change y = x at hn
      subst y
      refine ⟨u, ?_, hwu⟩
      simp only [V2.D.World.step, Function.update_self]
      change (FGSA.process p _ (toWire p o)).restartTime = some u
      rw [fgsa_process_restartTime]
      exact hu
  · rw [V2.D.Run.stateBefore_succ E rho hj]
    refine ⟨w, ?_, le_rfl⟩
    simp only [V2.D.World.step, Function.update_self]
    exact acRestart_restartTime p _ w

/-- An executed honest HEAD supplies the environment joined guard at its vote tick. -/
theorem fgsa_joinedAt_of_emitted_head (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {s : Slot} {q : Fin p.n} {b : BlockId}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (ho : ofHead p ⟨.seat (.head s) q, b⟩ ∈ V2.D.Run.emitsAt E rho i) :
    joinedAt p E rho x s (SA.voteTime p.toParams s) := by
  have hem := ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have he := (fgsa_emits_head E rho _ x _ s q b).mp hem
  have hs : p.slotOf (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le (by have hd := p.deltaPos; dsimp [Time] at *; omega)
  have bound (w : Time) (_hw : 0 ≤ w) (hwt : w ≤ SA.voteTime p.toParams s)
      (hr : V2.Event.restart x w ∈ rho.events) : w ≤ slotStartZ p ((s : Int) - 1) := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hj hi hwt
      (by change 0 < (1 : Nat); decide)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hV.toScheduleWellFormed hj hji
    have hg := he.2.2.2.1
    change joinedNow p (clock p (V2.D.Run.stateBefore E rho i x).st _ ) = true at hg
    unfold joinedNow at hg
    rw [fgsa_clock_restartTime, hu, (clock_vn _ _).2] at hg
    have hub : u ≤ slotStartZ p ((s : Int) - 1) := by
      change decide (u ≤ 4 * p.Δ * ((p.slotOf (SA.voteTime p.toParams s) : Int) - 1)) = true at hg
      rw [hs] at hg
      exact of_decide_eq_true hg
    exact hwu.trans hub
  refine ⟨he.1, ?_, bound⟩
  intro w hw hwt hwake
  exact bound w hw.le hwt (hV.wake_restart x
    (hV.honest_only _ (List.mem_of_getElem? hi)) w hw
    (hwt.trans (hV.in_horizon _ (List.mem_of_getElem? hi)).2) hwake)

end AvailableChain.FGSA.Run
end

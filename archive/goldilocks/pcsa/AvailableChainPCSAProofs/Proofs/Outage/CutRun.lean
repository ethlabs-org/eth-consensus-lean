module
public import AvailableChainPCSAProofs.Proofs.Outage.CutStore
public import AvailableChainPCSAProofs.Proofs.Outage.CleanBridge

public section

/-! Run facts for the clean side of the cut (pcsa34-r4.3 §5.5 steps 1–2), stage
1: the record `S` of an honest node is genesis or one of its own gate results,
every stored lock row is live, a gate result stays saved, and the state
before a tick is the read state of the previous time. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-! ### Ticks of one node -/

/-- The clock at a gate time runs the gate of its label. -/
theorem pcsa_clock_at_gate (st : State p.n) (i : Slot) :
    clock p st (SA.gateTime p.toParams i) =
      gateStep p (clockPre p st (SA.gateTime p.toParams i)) i := by
  rcases pcsa_clock_cases p st (SA.gateTime p.toParams i) with ⟨-, hng⟩ | ⟨-, -, hg⟩
  · exfalso
    apply hng
    rw [pcsa_gate_slot]
    refine ⟨?_, rfl⟩
    have hΔ : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * (i : Int) + 6 * p.Δ - 6 * p.Δ
    have : (0 : Int) ≤ (i : Int) := Int.natCast_nonneg _
    nlinarith
  · rw [hg, pcsa_gate_slot]

/-- [stage 1] The gate result of a label is the walk on the pre-gate clock of
the node's tick at the gate time. -/
theorem pcsa_gate_tick_result (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hfr : StageOneFrame p c E rho) {x : V}
    (hx : x ∈ rho.honest) {k : Nat} {i : Slot}
    (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams i))) :
    gateResultAt p c E rho x i = some (SA.Root.confirmationFrom p.toParams .genesis
      (actView (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams i))) i) := by
  have hF : (V2.D.Run.stateBefore E rho k x).st.fg.F = .genesis :=
    ((FrameVacuous_def p _).mp (hfr x hx k)).1
  rw [pcsa_gateResultAt_def, pcsa_gateInAt_def, pcsa_preTick_def,
    pcsa_tickIdx_of_event E rho hs hk]
  change some (SA.Root.confirmationFrom p.toParams
    (eraseFG (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams i)).fg.F)
    (actView (clockPre p (V2.D.Run.stateBefore E rho k x).st (SA.gateTime p.toParams i))) i) = _
  rw [(pcsa_clockPre_frame p _ _).2.2.2.1, hF]
  rfl

omit [DecidableEq V] in
/-- Every earlier event of a node is before the time of its tick. -/
theorem pcsa_node_events_before_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho) {k : Nat} {x : V}
    {t : Time} (hk : rho.events[k]? = some (.tick x t)) :
    ∀ k' < k, ∀ e, rho.events[k']? = some e → e.node = x → e.time < t := by
  intro k' hk' e he hn
  obtain ⟨hkl', hke'⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  have hkey := (List.pairwise_iff_getElem.mp hs.sorted) k' k hkl' hkl hk'
  rw [hke', hke] at hkey
  rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨heq, hph⟩
  · exact hlt
  · exfalso
    cases e with
    | restart u t' => exact hnr k' u t' he
    | deliver u o t' =>
      change (2 : Nat) ≤ 1 at hph
      omega
    | tick u t' =>
      change u = x at hn
      change t' = t at heq
      subst hn heq
      have := (List.Nodup.getElem?_inj hkl' hs.nodup).mp (he.trans hk.symm)
      omega

/-! ### The record -/

/-- The state of a node after a tick. -/
theorem pcsa_step_tick_st (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat)
    (x : V) (t : Time) :
    (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.tick x t) x).st =
      clock p (V2.D.Run.stateBefore E rho k x).st t := by
  change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
  rw [Function.update_self]
  exact pcsa_tick_st E rho _ x t

/-- The state of a node after a delivery. -/
theorem pcsa_step_deliver_st (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat)
    (x : V) (o : (pcsaWith m p c).Object) (t : Time) :
    (V2.D.World.step E rho (V2.D.Run.stateBefore E rho k) (.deliver x o t) x).st =
      process p (V2.D.Run.stateBefore E rho k x).st (toWire p o) := by
  change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st = _
  rw [Function.update_self]
  rfl

/-- [stage 1] The frame of a node stays vacuous across a delivery. -/
theorem pcsa_deliver_frame (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hfr : StageOneFrame p c E rho) {x : V} (hx : x ∈ rho.honest) {k : Nat}
    {o : (pcsaWith m p c).Object}
    {t : Time} (he : rho.events[k]? = some (.deliver x o t)) :
    (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).fg.F = .genesis := by
  have hv := hfr x hx (k + 1)
  rw [V2.D.Run.stateBefore_succ E rho he, pcsa_step_deliver_st] at hv
  exact ((FrameVacuous_def p _).mp hv).1

/-- [stage 1; pcsa34-r4.3 §5.2.2 (v)] The record of an honest node is genesis
or the result of one of its earlier gate ticks. -/
theorem pcsa_record_origin (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (K : Nat) :
    (V2.D.Run.stateBefore E rho K x).st.base.stableRecord = .genesis ∨
      ∃ i k, k < K ∧ rho.events[k]? = some (.tick x (SA.gateTime p.toParams i)) ∧
        gateResultAt p c E rho x i =
          some (some (V2.D.Run.stateBefore E rho K x).st.base.stableRecord) := by
  have hs := h.valid.toScheduleWellFormed
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => nd.st.base.stableRecord = .genesis ∨ ∃ i k, k < K ∧
      rho.events[k]? = some (.tick x (SA.gateTime p.toParams i)) ∧
      gateResultAt p c E rho x i = some (some nd.st.base.stableRecord))
    (Nat.zero_le K) x ?_ (Or.inl rfl)
  intro k e _ hkK he hn hQ
  beta_reduce at hQ ⊢
  cases e with
  | restart u t => exact absurd he (h.noRestart k u t)
  | tick u t =>
    change u = x at hn
    subst u
    rw [pcsa_step_tick_st]
    have hF : (V2.D.Run.stateBefore E rho k x).st.fg.F = .genesis :=
      ((FrameVacuous_def p _).mp (hfr x hx k)).1
    have hF' : (clockPre p (V2.D.Run.stateBefore E rho k x).st t).fg.F = .genesis := by
      rw [(pcsa_clockPre_frame p _ t).2.2.2.1]
      exact hF
    have hpre := (pcsa_clockPre_slow p (V2.D.Run.stateBefore E rho k x).st t).1
    rcases pcsa_clock_cases p (V2.D.Run.stateBefore E rho k x).st t with ⟨hc, -⟩ | ⟨-, hts, hc⟩
    · rw [hc, hpre]
      exact hQ
    · rw [hc, pcsa_gateStep_genesis p _ _ hF']
      split
      · rw [hpre]
        exact hQ
      · rcases pcsa_gateFrom_record p .genesis _ _
          (clockPre p (V2.D.Run.stateBefore E rho k x).st t)
          ((t - 6 * p.Δ) / (4 * p.Δ)).toNat with he' | he'
        · rw [he', hpre]
          exact hQ
        · right
          have hk' : rho.events[k]? = some (.tick x (SA.gateTime p.toParams
              ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)) := by
            rw [he, ← hts]
          refine ⟨_, k, hkK, hk', ?_⟩
          rw [pcsa_gate_tick_result E rho hs hfr hx hk', ← hts, he']
  | deliver u o t =>
    change u = x at hn
    subst u
    rw [pcsa_step_deliver_st, (pcsa_process_slow p _ (toWire p o)
      ((FrameVacuous_def p _).mp (hfr x hx k)).1 (pcsa_deliver_frame E rho hfr hx he)).1.stable]
    exact hQ

/-! ### Live rows -/

/-- [stage 1] Every lock row of an honest node is live at its store time. -/
theorem pcsa_rows_live (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (hL : (1 : Time) ≤ SA.lifetime p.toParams) (K : Nat) :
    ∀ row ∈ (V2.D.Run.stateBefore E rho K x).st.base.obligations,
      (V2.D.Run.stateBefore E rho K x).st.base.now < row.2.2 := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => ∀ row ∈ nd.st.base.obligations, nd.st.base.now < row.2.2)
    (Nat.zero_le K) x ?_ (fun row hr => absurd hr List.not_mem_nil)
  intro k e _ _ he hn hQ
  beta_reduce at hQ ⊢
  cases e with
  | restart u t => exact absurd he (h.noRestart k u t)
  | tick u t =>
    change u = x at hn
    subst u
    rw [pcsa_step_tick_st, pcsa_clock_now]
    exact pcsa_clock_live p _ t ((FrameVacuous_def p _).mp (hfr x hx k)).1 hL
  | deliver u o t =>
    change u = x at hn
    subst u
    rw [pcsa_step_deliver_st]
    obtain ⟨hb, hloss, -⟩ := pcsa_process_slow p _ (toWire p o)
      ((FrameVacuous_def p _).mp (hfr x hx k)).1 (pcsa_deliver_frame E rho hfr hx he)
    rw [LockLoss_def] at hloss
    intro row hr
    rw [hb.now]
    exact hQ row (hloss.1 hr)

/-! ### Saved results -/

/-- [stage 1] After the gate tick of a label, the node's saved result of the
label is its gate result. -/
theorem pcsa_saved_of_gate (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (h : Base₂ p c E rho) (hfr : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    {i : Slot} {k K : Nat} (hk : rho.events[k]? = some (.tick x (SA.gateTime p.toParams i)))
    (hkK : k < K) :
    GridCO.savedGenuine (V2.D.Run.stateBefore E rho K x).st.base i =
      gateResultAt p c E rho x i := by
  have hs := h.valid.toScheduleWellFormed
  have hun := pcsa_unsaved_before E rho h.noRestart hfr x hx i k
    (pcsa_node_events_before_tick E rho hs h.noRestart hk)
  have hF : (V2.D.Run.stateBefore E rho k x).st.fg.F = .genesis :=
    ((FrameVacuous_def p _).mp (hfr x hx k)).1
  have hF' : (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams i)).fg.F = .genesis := by
    rw [(pcsa_clockPre_frame p _ _).2.2.2.1]
    exact hF
  have hun' : GridCO.savedGenuine (clockPre p (V2.D.Run.stateBefore E rho k x).st
      (SA.gateTime p.toParams i)).base i = none := by
    change ((clockPre p _ _).base.genuine.find? (fun row => row.1 == i)).map Prod.snd = none
    rw [(pcsa_clockPre_slow p _ _).2.1]
    exact hun
  have hk1 : GridCO.savedGenuine (V2.D.Run.stateBefore E rho (k + 1) x).st.base i =
      gateResultAt p c E rho x i := by
    rw [V2.D.Run.stateBefore_succ E rho hk, pcsa_step_tick_st, pcsa_clock_at_gate,
      pcsa_gateStep_genesis p _ _ hF', hun', pcsa_gate_tick_result E rho hs hfr hx hk]
    exact pcsa_gateFrom_saved_self p _ _ _ _ _ hun'
  rw [← hk1]
  obtain ⟨r, hr⟩ : ∃ r, GridCO.savedGenuine (V2.D.Run.stateBefore E rho (k + 1) x).st.base i =
      some r := by
    rw [hk1, pcsa_gate_tick_result E rho hs hfr hx hk]
    exact ⟨_, rfl⟩
  rw [hr]
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => GridCO.savedGenuine nd.st.base i = some r) hkK x ?_ hr
  intro k' e _ _ he hn hQ
  beta_reduce at hQ ⊢
  cases e with
  | restart u t => exact absurd he (h.noRestart k' u t)
  | tick u t =>
    change u = x at hn
    subst u
    rw [pcsa_step_tick_st]
    exact pcsa_clock_saved_keep p _ t i r ((FrameVacuous_def p _).mp (hfr x hx k')).1 hQ
  | deliver u o t =>
    change u = x at hn
    subst u
    rw [pcsa_step_deliver_st]
    have hg := (pcsa_process_slow p _ (toWire p o)
      ((FrameVacuous_def p _).mp (hfr x hx k')).1 (pcsa_deliver_frame E rho hfr hx he)).1.genuine
    change ((process p _ (toWire p o)).base.genuine.find? (fun row => row.1 == i)).map
      Prod.snd = _
    rw [hg]
    exact hQ

/-! ### The state before a tick -/

/-- The state of a node before its tick at `t` is its read state at `t − 1`. -/
theorem pcsa_preTick_read (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho) {k : Nat} {x : V}
    {t : Time} (hk : rho.events[k]? = some (.tick x t)) :
    storeAt p c E rho x (t - 1) = (V2.D.Run.stateBefore E rho k x).st := by
  rw [pcsa_storeAt_index E rho hs]
  have hle : (rho.events.filter (fun e => decide (e.time ≤ t - 1))).length ≤ k := by
    by_contra hn
    have := (V2.D.Engine.index_lt_read_length_iff hs (t - 1) hk).mp (Nat.lt_of_not_le hn)
    change t ≤ t - 1 at this
    linarith
  have hb := pcsa_node_events_before_tick E rho hs hnr hk
  congr 1
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => V2.D.Run.stateBefore E rho
      (rho.events.filter (fun e => decide (e.time ≤ t - 1))).length x = nd) hle x ?_ rfl
  intro k' e hk1 hk2 he hn _
  exfalso
  have h1 := hb k' hk2 e he hn
  have h2 : ¬ k' < (rho.events.filter (fun e => decide (e.time ≤ t - 1))).length := by omega
  rw [V2.D.Engine.index_lt_read_length_iff hs (t - 1) he] at h2
  exact h2 (Int.le_sub_one_of_lt h1)

end AvailableChain.PCSA.Run
end

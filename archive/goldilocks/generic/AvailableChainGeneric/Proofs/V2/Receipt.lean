module
public import AvailableChainGeneric.Proofs.V2.Sleep
public import AvailableChainGeneric.Statements.V2.Receipt
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainGeneric.Proofs.V2.Reads
public import AvailableChainKitV2.EngineClock

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

-- GLY:1166–1167; Delivery.lean:25–38 supplies the same two fields.
theorem deliveryWithin_of_partialSynchrony (h : PartialSynchrony E rho) :
    DeliveryWithin E rho (fun t => max t E.t_GST + E.Δ) rho.horizon :=
  ⟨h.broadcast, h.relay⟩

-- GLY:1168–1169; Delivery.lean:43–56 supplies the same two fields.
theorem deliveryWithin_of_healthyPrefix (b₀ : Time) (h : HealthyPrefixDelivery E rho b₀) :
    DeliveryWithin E rho (fun t => t + E.Δ) b₀ :=
  ⟨h.broadcast, h.relay⟩

-- S3-02; Statements/V2/Receipt.lean:77–91; KitV2/Stable.lean:49.
theorem timely_of_clock_statement : TimelyOfClockStatement := by
  intro V _ In P E rho Timely C hS w o T j i hact hj hji hrf
  apply (C.timely_iff _ o).2
  rw [C.clockOf_eq]
  apply le_trans hact
  have hbase : T ≤ C.clock.now (Run.stateBefore E rho (j + 1) w) := by
    rw [(Run.step_tick_eq E rho hj).1, C.clock.now_tick]
  refine stateBefore_step_induction E rho (fun st => T ≤ C.clock.now st)
    (Nat.succ_le_of_lt hji) w ?_ hbase
  intro k e hjk hki he hv hk
  cases e with
  | restart u t =>
      dsimp only [Event.node] at hv
      subst u
      exact absurd he (hrf k t (Nat.le_trans (Nat.le_succ j) hjk) hki)
  | tick u t =>
      dsimp only [Event.node] at hv
      subst u
      dsimp only [World.step]
      rw [Function.update_self, C.clock.now_tick]
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
      have hkey := (List.pairwise_iff_getElem.mp hS.sorted) j k hjl hkl
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hjk)
      rw [hje, hke] at hkey
      exact time_le_of_key_le _ _ hkey
  | deliver u o' t =>
      dsimp only [Event.node] at hv
      subst u
      dsimp only [World.step]
      rw [Function.update_self, C.clock.process]
      exact hk

-- S3-02; Statements/V2/Receipt.lean:95–105; Proofs/V2/Reads.lean:40.
theorem timely_of_emit_statement : TimelyOfEmitStatement := by
  intro V _ In P E rho Timely C o t ht hpub hth
  exact publicTime_le_pubFloor E hpub hth

-- S3-02; Statements/V2/Receipt.lean:109–122; KitV2/EngineClock.lean:104.
theorem timely_of_relay_statement : TimelyOfRelayStatement := by
  intro V _ In P E rho Timely C hAS hS hrestore hwake v i o t hacc
  have hzero : 0 ≤ (0 : Time) ∧ PublicTime E 0 := by
    refine ⟨le_rfl, ?_⟩
    unfold PublicTime
    exact ⟨0, (Int.zero_mul E.Δ).symm⟩
  have hclock : 0 ≤ C.clock.now (Run.stateBefore E rho i v) ∧
      PublicTime E (C.clock.now (Run.stateBefore E rho i v)) := by
    refine stateBefore_step_induction E rho
      (fun st => 0 ≤ C.clock.now st ∧ PublicTime E (C.clock.now st))
      (Nat.zero_le i) v ?_ ?_
    · intro k e h0k hki he hv hk
      cases e with
      | restart u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [World.step]
          rw [Function.update_self, hrestore]
          exact ⟨(hS.in_horizon _ (List.mem_of_getElem? he)).1,
            hwake v t' (List.mem_of_getElem? he)⟩
      | tick u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [World.step]
          rw [Function.update_self, C.clock.now_tick]
          have hmem := List.mem_of_getElem? he
          exact ⟨(hS.in_horizon _ hmem).1, hS.tick_public v t' hmem⟩
      | deliver u o' t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [World.step]
          rw [Function.update_self, C.clock.process]
          exact hk
    · unfold Run.stateBefore World.init
      simp only [List.take_zero, List.foldl_nil, C.clock.init]
      exact hzero
  unfold Run.acceptsAt Run.handlesAt at hacc
  rcases hacc with ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩
  rw [Run.stateBefore_succ E rho hi] at htrue
  dsimp only [World.step] at htrue
  rw [Function.update_self] at htrue
  have htimely := hAS.timely _ o' o
    (by rw [C.clockOf_eq]; exact hclock.1) hfalse htrue hhandles
  have hact := (C.timely_iff _ o).1 htimely
  rw [C.clockOf_eq] at hact
  exact hact.trans (publicTime_le_pubFloor E hclock.2
    (stateBefore_now_le_event_atRestart C.clock ⟨hrestore⟩ E rho hS hi v))

/-- Public action times give relay timeliness with arbitrary wake times. -/
theorem timely_of_relay_public_actTime
    (E : Generic.Env V) (rho : Run V P) {Timely : P.State → P.Object → Prop}
    (C : TimelyClock P Timely) (hAS : AdmitSound P C)
    (hS : ScheduleWellFormed E rho) (R : RestoreTimeLaw C.clock)
    (hpubAct : ∀ o, V2.PublicTime E (C.actTime o))
    (v : V) (i : Nat) (o : P.Object) (t : Time)
    (hacc : Run.acceptsAt E rho i v o t) : C.actTime o ≤ pubFloor E t := by
  have hn : 0 ≤ C.clock.now (Run.stateBefore E rho i v) := by
    rcases stateBefore_now_source_atRestart C.clock R E rho i v with hz | ⟨j, _, he⟩
    · rw [hz]
    · rcases he with he | he <;>
        exact (hS.in_horizon _ (List.mem_of_getElem? he)).1
  obtain ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩ := hacc
  rw [Run.stateBefore_succ E rho hi] at htrue
  dsimp only [World.step] at htrue
  rw [Function.update_self] at htrue
  have ht := hAS.timely _ o' o (by rwa [C.clockOf_eq]) hfalse htrue hhandles
  have ha := (C.timely_iff _ o).1 ht
  rw [C.clockOf_eq] at ha
  exact publicTime_le_pubFloor E (hpubAct o)
    (ha.trans (stateBefore_now_le_event_atRestart C.clock R E rho hS hi v))

-- S3-03; Statements/V2/Receipt.lean:162–179; KitV2/Stable.lean:49.
theorem firstAccept_of_processed_statement : FirstAcceptOfProcessedStatement := by
  intro V _ In P E rho w o i₀ k hik hrf h₀ hk htick hdeliv
  by_contra hno
  have hfalse : P.processed (Run.stateBefore E rho k w) o = false := by
    refine stateBefore_step_induction E rho (fun st => P.processed st o = false)
      hik w ?_ h₀
    intro i e hi hik' he hv hprev
    cases e with
    | restart u t =>
        dsimp only [Event.node] at hv
        subst u
        exact absurd he (hrf i t hi hik')
    | tick u t =>
        dsimp only [Event.node] at hv
        subst u
        rw [← Run.stateBefore_succ E rho he]
        exact htick i t hi hik' he hprev
    | deliver u o' t' =>
        dsimp only [Event.node] at hv
        subst u
        dsimp only [World.step]
        rw [Function.update_self]
        cases hprocessed : P.processed (P.process (Run.stateBefore E rho i w) o') o with
        | false => rfl
        | true =>
            have hnext : P.processed (Run.stateBefore E rho (i + 1) w) o = true := by
              rw [Run.stateBefore_succ E rho he]
              dsimp only [World.step]
              rw [Function.update_self]
              exact hprocessed
            apply False.elim
            apply hno
            refine ⟨i, t', hi, hik', ?_⟩
            unfold Run.acceptsAt Run.handlesAt
            exact ⟨⟨o', he, hdeliv i o' t' hi hik' he hprev hprocessed⟩, hprev, hnext⟩
  rw [hk] at hfalse
  exact Bool.noConfusion hfalse

-- S3-02 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
theorem timely_of_clock :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (w : V), ∀ (o : P.Object), ∀ (T : Time), ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : restartFree rho w j i),
    Timely (Run.stateBefore E rho i w) o :=
  @timely_of_clock_statement

-- S3-02 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
set_option linter.unusedDecidableInType false in
theorem timely_of_emit :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object), ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_emit_statement

-- S3-02 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
theorem timely_of_relay :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d t, C.clock.now (P.restore d t) = t),
  ∀ (hwake : ∀ u t, .restart u t ∈ rho.events → V2.PublicTime E t),
  ∀ (v : V), ∀ (i : Nat), ∀ (o : P.Object), ∀ (t : Time),
  ∀ (hacc : Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_relay_statement

-- S3-03 LINK; the binder names are the Statement names, for named arguments.
set_option linter.unusedVariables false in
theorem firstAccept_of_processed :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ (w : V), ∀ (o : P.Object), ∀ (i₀ k : Nat),
  ∀ (hik : i₀ ≤ k),
  ∀ (hrf : restartFree rho w i₀ k),
  ∀ (h₀ : P.processed (Run.stateBefore E rho i₀ w) o = false),
  ∀ (hk : P.processed (Run.stateBefore E rho k w) o = true),
  ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (P.process (Run.stateBefore E rho i w) o') o = true →
      P.handles (Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ Run.acceptsAt E rho i w o t' :=
  @firstAccept_of_processed_statement

-- S3-04; Statements/V2/Receipt.lean:126–158; KitV2/Execution.lean:128.
/-- Fresh objects cannot use the historical processing exemption. -/
theorem historySafeAt_of_fresh {w : V} {o : P.Object} {a : Time}
    (h : ¬ V2.ProcessedByActionCut E rho w o a) : HistorySafeAt E rho w o a :=
  fun hh => False.elim (h hh)

/-- Processing that persists to the action cut gives safe history. -/
theorem historySafeAt_of_processed_mono {w : V} {o : P.Object} {a : Time}
    (h : ∀ i j, i ≤ j → j ≤ V2.Run.actionCut rho a →
      P.processed (V2.Run.stateBefore E rho i w) o = true →
      P.processed (V2.Run.stateBefore E rho j w) o = true) :
    HistorySafeAt E rho w o a := by
  rintro ⟨i, hi, hp⟩
  exact h i _ hi le_rfl hp

/-- A service witness gives processing only with explicit acceptance and history laws. -/
theorem processed_by_deadline_of_service : ProcessedByDeadlineOfServiceStatement := by
  intro V In _ P E rho Timely Inv w o a d hS had hService hHistory hRF hHooks
    hAccept hReady hNX
  rw [← stateBefore_idxBefore E rho d hS] at hNX ⊢
  rcases hService with hh | ⟨t', hat, htd, j, hj⟩
  · exact hHooks.processed_stable E rho hS w o _ _ (actionCut_le_idxBefore hS had)
      hRF (hHistory hh)
  · obtain ⟨hInv, hWF, hDeps, hTimely⟩ := hReady j t' hat htd hj
    obtain ⟨o', he, hhandles⟩ := hj
    have hjn := (index_lt_idxBefore_iff hS he d).mpr htd
    have haj : V2.Run.actionCut rho a ≤ j := by
      by_contra hn
      have h := (index_lt_actionCut_iff hS he a).mp (Nat.lt_of_not_ge hn)
      simp only [Event.time, Event.phase] at h
      dsimp [Time] at *; omega
    have hpost : V2.Run.stateBefore E rho (j + 1) w =
        P.process (V2.Run.stateBefore E rho j w) o' := by
      rw [V2.Run.stateBefore_succ E rho he]
      simp only [V2.World.step, Function.update_self]
    have hrf := hRF.mono (haj.trans (Nat.le_succ j)) le_rfl
    rcases hAccept.accepts _ o' o hInv hhandles hWF hDeps hTimely with hp | hx
    · exact hHooks.processed_stable E rho hS w o _ _ (Nat.succ_le_of_lt hjn) hrf
        (by rwa [hpost])
    · have hn := hHooks.excludes_stable E rho hS w o _ _ (Nat.succ_le_of_lt hjn) hrf
        (by rwa [hpost])
      rw [hNX] at hn
      cases hn

variable {dl : Time → Time} {cut send a t : Time}
  {v w : V} {o : P.Object} {i : Nat}

/-- A ready trigger supplies every transport guard at the chosen anchor. -/
theorem service_of_readyTrigger
    (hD : DeliveryWithin E rho dl cut)
    (hT : ReadyTrigger E rho o send w a (dl a)) (hw : w ∈ rho.honest)
    (hta : send ≤ a) (ha : 0 ≤ a) (had : a < dl a)
    (hc : dl a ≤ cut) (hh : dl a ≤ rho.horizon)
    (hx : P.excludes (V2.Run.stateBeforeTime E rho (dl a) w) o = false) :
    V2.DeliveryService E rho w o a (dl a) := by
  obtain ⟨v, hv, he | ⟨i, he⟩, hr⟩ := hT
  · exact hD.broadcast v hv o send he w hw a hta ha had hc hh hr hx
  · exact hD.relay v hv i o send he w hw a hta ha had hc hh hr hx

/-- A fresh emission has a handler strictly before its deadline. -/
theorem ready_broadcast (hD : DeliveryWithin E rho dl cut)
    (hv : v ∈ rho.honest) (he : V2.Run.emits E rho v o t)
    (hw : w ∈ rho.honest) (ht : 0 ≤ t) (hd : t < dl t)
    (hc : dl t ≤ cut) (hh : dl t ≤ rho.horizon)
    (hR : V2.LinkReadyOn E rho v w t (dl t))
    (hFresh : ¬ V2.ProcessedByActionCut E rho w o t)
    (hx : P.excludes (V2.Run.stateBeforeTime E rho (dl t) w) o = false) :
    V2.HandledBetween E rho w o t (dl t) :=
  (hD.broadcast v hv o t he w hw t le_rfl ht hd hc hh hR hx).resolve_left hFresh

/-- A fresh relay has a handler strictly before its deadline. -/
theorem ready_relay (hD : DeliveryWithin E rho dl cut)
    (hv : v ∈ rho.honest) (he : V2.Run.acceptsAt E rho i v o t)
    (hw : w ∈ rho.honest) (ht : 0 ≤ t) (hd : t < dl t)
    (hc : dl t ≤ cut) (hh : dl t ≤ rho.horizon)
    (hR : V2.LinkReadyOn E rho v w t (dl t))
    (hFresh : ¬ V2.ProcessedByActionCut E rho w o t)
    (hx : P.excludes (V2.Run.stateBeforeTime E rho (dl t) w) o = false) :
    V2.HandledBetween E rho w o t (dl t) :=
  (hD.relay v hv i o t he w hw t le_rfl ht hd hc hh hR hx).resolve_left hFresh

theorem accepted_by_deadline_statement : AcceptedByDeadlineStatement := by
  intro V _ In P E rho Timely Inv dl cut o send a w hD hT hw hta ha had hc hh
    hHistory hS hRF hHooks hAccept hReady hNX
  exact processed_by_deadline_of_service E rho Timely Inv w o a (dl a) hS had
    (service_of_readyTrigger hD hT hw hta ha had hc hh hNX)
    hHistory hRF hHooks hAccept hReady hNX

set_option linter.unusedVariables false in
theorem accepted_by_deadline :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : V2.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    DeliveryWithin E rho dl cut →
    ReadyTrigger E rho o send w a (dl a) →
    w ∈ rho.honest → send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    HistorySafeAt E rho w o a →
    V2.ScheduleWellFormed E rho →
    V2.restartFree rho w (V2.Run.actionCut rho a) (V2.Run.idxBefore rho (dl a)) →
    V2.HooksSound P → AcceptanceLaw P Timely Inv →
    (∀ j t', a ≤ t' → t' < dl a → V2.Run.handlesAt E rho j w o t' →
      Inv (V2.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧ P.depsPresent (V2.Run.stateBefore E rho j w) o = true ∧
      Timely (V2.Run.stateBefore E rho j w) o) →
    P.excludes (V2.Run.stateBeforeTime E rho (dl a) w) o = false →
    P.processed (V2.Run.stateBeforeTime E rho (dl a) w) o = true :=
  @accepted_by_deadline_statement

end AvailableChain.Gen.V2

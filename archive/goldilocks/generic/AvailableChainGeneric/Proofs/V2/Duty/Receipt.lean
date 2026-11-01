module
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy
public import AvailableChainGeneric.Proofs.V2.Duty.Sleep
public import AvailableChainGeneric.Statements.V2.Duty.Receipt -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Delivery -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainKitV2.DutyEngineClock

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
  {E : Generic.Env V} {rho : D.Run V P}

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:17.
theorem deliveryWithin_of_partialSynchrony (h : D.PartialSynchrony E rho) :
    DeliveryWithin E rho (fun t => max t E.t_GST + E.Δ) rho.horizon :=
  ⟨h.broadcast_emitted, h.relay_accepted⟩

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:22.
theorem deliveryWithin_of_healthyPrefix (b₀ : Time) (h : D.HealthyPrefixDelivery E rho b₀) :
    DeliveryWithin E rho (fun t => t + E.Δ) b₀ :=
  ⟨h.broadcast_emitted, h.relay_accepted⟩

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:27.
theorem timely_of_clock_statement : TimelyOfClockStatement := by
  intro V _ In P E rho Timely C hS w o T j i hact hj hji hrf
  apply (C.timely_iff _ o).2
  rw [C.clockOf_eq]
  apply le_trans hact
  have hbase : T ≤ C.clock.now (D.Run.stateBefore E rho (j + 1) w) := by
    rw [(D.Run.step_tick_eq E rho hj).1, C.clock.now_tick]
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
      dsimp only [D.World.step]
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
      dsimp only [D.World.step]
      rw [Function.update_self, C.clock.process]
      exact hk

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:61.
theorem timely_of_emit_statement : TimelyOfEmitStatement := by
  intro V _ In P E rho Timely C o t ht hpub hth
  exact publicTime_le_pubFloor E hpub hth

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:66.
theorem timely_of_relay_statement : TimelyOfRelayStatement := by
  intro V _ In P E rho Timely C hAS hS hrestore hwake v i o t hacc
  have hzero : 0 ≤ (0 : Time) ∧ V2.PublicTime E 0 := by
    refine ⟨le_rfl, ?_⟩
    unfold V2.PublicTime
    exact ⟨0, (Int.zero_mul E.Δ).symm⟩
  have hclock : 0 ≤ C.clock.now (D.Run.stateBefore E rho i v) ∧
      V2.PublicTime E (C.clock.now (D.Run.stateBefore E rho i v)) := by
    refine stateBefore_step_induction E rho
      (fun st => 0 ≤ C.clock.now st ∧ V2.PublicTime E (C.clock.now st))
      (Nat.zero_le i) v ?_ ?_
    · intro k e h0k hki he hv hk
      cases e with
      | restart u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [D.World.step]
          rw [Function.update_self, hrestore]
          exact ⟨(hS.in_horizon _ (List.mem_of_getElem? he)).1,
            hwake v t' (List.mem_of_getElem? he)⟩
      | tick u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [D.World.step]
          rw [Function.update_self, C.clock.now_tick]
          have hmem := List.mem_of_getElem? he
          exact ⟨(hS.in_horizon _ hmem).1, hS.tick_public v t' hmem⟩
      | deliver u o' t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [D.World.step]
          rw [Function.update_self, C.clock.process]
          exact hk
    · unfold D.Run.stateBefore D.World.init
      simp only [List.take_zero, List.foldl_nil, C.clock.init]
      exact hzero
  unfold D.Run.acceptsAt D.Run.handlesAt at hacc
  rcases hacc with ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩
  rw [D.Run.stateBefore_succ E rho hi] at htrue
  dsimp only [D.World.step] at htrue
  rw [Function.update_self] at htrue
  have htimely := hAS.timely _ o' o
    (by rw [C.clockOf_eq]; exact hclock.1) hfalse htrue hhandles
  have hact := (C.timely_iff _ o).1 htimely
  rw [C.clockOf_eq] at hact
  exact hact.trans (publicTime_le_pubFloor E hclock.2
    (stateBefore_now_le_event_atRestart C.clock ⟨hrestore⟩ E rho hS hi v))

/-- Public action times give relay timeliness with arbitrary wake times. -/
theorem timely_of_relay_public_actTime
    (E : Generic.Env V) (rho : D.Run V P) {Timely : P.State → P.Object → Prop}
    (C : TimelyClock P Timely) (hAS : AdmitSound P C)
    (hS : D.ScheduleWellFormed E rho) (R : RestoreTimeLaw C.clock)
    (hpubAct : ∀ o, V2.PublicTime E (C.actTime o))
    (v : V) (i : Nat) (o : P.Object) (t : Time)
    (hacc : D.Run.acceptsAt E rho i v o t) : C.actTime o ≤ pubFloor E t := by
  have hn : 0 ≤ C.clock.now (D.Run.stateBefore E rho i v) := by
    rcases stateBefore_now_source_atRestart C.clock R E rho i v with hz | ⟨j, _, he⟩
    · rw [hz]
    · rcases he with he | he <;>
        exact (hS.in_horizon _ (List.mem_of_getElem? he)).1
  obtain ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩ := hacc
  rw [D.Run.stateBefore_succ E rho hi] at htrue
  dsimp only [D.World.step] at htrue
  rw [Function.update_self] at htrue
  have ht := hAS.timely _ o' o (by rwa [C.clockOf_eq]) hfalse htrue hhandles
  have ha := (C.timely_iff _ o).1 ht
  rw [C.clockOf_eq] at ha
  exact publicTime_le_pubFloor E (hpubAct o)
    (ha.trans (stateBefore_now_le_event_atRestart C.clock R E rho hS hi v))

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:114.
theorem firstAccept_of_processed_statement : FirstAcceptOfProcessedStatement := by
  intro V _ In P E rho w o i₀ k hik hrf h₀ hk htick hdeliv
  by_contra hno
  have hfalse : P.processed (D.Run.stateBefore E rho k w) o = false := by
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
        rw [← D.Run.stateBefore_succ E rho he]
        exact htick i t hi hik' he hprev
    | deliver u o' t' =>
        dsimp only [Event.node] at hv
        subst u
        dsimp only [D.World.step]
        rw [Function.update_self]
        cases hprocessed : P.processed (P.process (D.Run.stateBefore E rho i w) o') o with
        | false => rfl
        | true =>
            have hnext : P.processed (D.Run.stateBefore E rho (i + 1) w) o = true := by
              rw [D.Run.stateBefore_succ E rho he]
              dsimp only [D.World.step]
              rw [Function.update_self]
              exact hprocessed
            apply False.elim
            apply hno
            refine ⟨i, t', hi, hik', ?_⟩
            unfold D.Run.acceptsAt D.Run.handlesAt
            exact ⟨⟨o', he, hdeliv i o' t' hi hik' he hprev hprocessed⟩, hprev, hnext⟩
  rw [hk] at hfalse
  exact Bool.noConfusion hfalse

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:154.
theorem timely_of_clock :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (w : V), ∀ (o : P.Object), ∀ (T : Time), ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : D.restartFree rho w j i),
    Timely (D.Run.stateBefore E rho i w) o :=
  @timely_of_clock_statement

set_option linter.unusedVariables false in
set_option linter.unusedDecidableInType false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:171.
theorem timely_of_emit :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object), ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : V2.PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_emit_statement

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:185.
theorem timely_of_relay :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d t, C.clock.now (P.restore d t) = t),
  ∀ (hwake : ∀ u t, .restart u t ∈ rho.events → V2.PublicTime E t),
  ∀ (v : V), ∀ (i : Nat), ∀ (o : P.Object), ∀ (t : Time),
  ∀ (hacc : D.Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_relay_statement

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:200.
theorem firstAccept_of_processed :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (w : V), ∀ (o : P.Object), ∀ (i₀ k : Nat),
  ∀ (hik : i₀ ≤ k),
  ∀ (hrf : D.restartFree rho w i₀ k),
  ∀ (h₀ : P.processed (D.Run.stateBefore E rho i₀ w) o = false),
  ∀ (hk : P.processed (D.Run.stateBefore E rho k w) o = true),
  ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (D.Run.stateBefore E rho i w) o = false →
      P.processed (D.Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (D.Run.stateBefore E rho i w) o = false →
      P.processed (P.process (D.Run.stateBefore E rho i w) o') o = true →
      P.handles (D.Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ D.Run.acceptsAt E rho i w o t' :=
  @firstAccept_of_processed_statement

/-- Acceptance under the pending-set rule. Protocol owners supply the invariant
and timeliness at each relevant handler. Missing dependency refusals remain
pending; DeliveryDemand supplies a retry in each ready window. -/
theorem AcceptanceLaw.processed_of_not_excluded
    {Timely : P.State → P.Object → Prop} {Inv : P.State → Prop}
    (h : AcceptanceLaw P Timely Inv) (st : P.State) (o' o : P.Object)
    (hInv : Inv st) (hhandles : P.handles st o' o) (hWF : P.wellFormed o = true)
    (hDeps : P.depsPresent st o = true) (hTimely : Timely st o)
    (hNX : P.excludes (P.process st o') o = false) :
    P.processed (P.process st o') o = true := by
  rcases h.accepts st o' o hInv hhandles hWF hDeps hTimely with hp | hx
  · exact hp
  · rw [hNX] at hx
    cases hx

/-- Safe history or a retry is the pending-set form of a service witness. -/
theorem processed_or_retried_of_service {w : V} {o : P.Object} {a d : Time}
    (h : D.DeliveryService E rho w o a d) (hHistory : HistorySafeAt E rho w o a) :
    P.processed (D.Run.stateAfterRestartsAt E rho a w) o = true ∨
      D.HandledBetween E rho w o a d :=
  h.imp hHistory id

/-- Fresh objects cannot use the historical processing exemption. -/
theorem historySafeAt_of_fresh {w : V} {o : P.Object} {a : Time}
    (h : ¬ D.ProcessedByActionCut E rho w o a) : HistorySafeAt E rho w o a :=
  fun hh => False.elim (h hh)

/-- Processing that persists to the action cut gives safe history. -/
theorem historySafeAt_of_processed_mono {w : V} {o : P.Object} {a : Time}
    (h : ∀ i j, i ≤ j → j ≤ D.Run.actionCut rho a →
      P.processed (D.Run.stateBefore E rho i w) o = true →
      P.processed (D.Run.stateBefore E rho j w) o = true) :
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
    have haj : D.Run.actionCut rho a ≤ j := by
      by_contra hn
      have h := (index_lt_actionCut_iff hS he a).mp (Nat.lt_of_not_ge hn)
      simp only [Event.time, Event.phase] at h
      dsimp [Time] at *; omega
    have hpost : D.Run.stateBefore E rho (j + 1) w =
        P.process (D.Run.stateBefore E rho j w) o' := by
      rw [D.Run.stateBefore_succ E rho he]
      simp only [D.World.step, Function.update_self]
    have hrf := hRF.mono (haj.trans (Nat.le_succ j)) le_rfl
    rcases hAccept.accepts _ o' o hInv hhandles hWF hDeps hTimely with hp | hx
    · exact hHooks.processed_stable E rho hS w o _ _ (Nat.succ_le_of_lt hjn) hrf
        (by rwa [hpost])
    · have hn := hHooks.excludes_stable E rho hS w o _ _ (Nat.succ_le_of_lt hjn) hrf
        (by rwa [hpost])
      rw [hNX] at hn
      cases hn

variable {Q : P.Object → Prop} {dl : Time → Time} {cut send a t : Time}
  {v w : V} {o : P.Object} {i : Nat}

/-- A ready trigger supplies every transport guard at the chosen anchor. -/
theorem service_of_readyTrigger
    (hD : DeliveryWithinOn E rho Q dl cut) (hQ : Q o)
    (hT : ReadyTrigger E rho o send w a (dl a)) (hw : w ∈ rho.honest)
    (hta : send ≤ a) (ha : 0 ≤ a) (had : a < dl a)
    (hc : dl a ≤ cut) (hh : dl a ≤ rho.horizon)
    (hx : P.excludes (D.Run.stateBeforeTime E rho (dl a) w) o = false) :
    D.DeliveryService E rho w o a (dl a) := by
  obtain ⟨v, hv, he | ⟨i, he⟩, hr⟩ := hT
  · exact hD.broadcast v hv o hQ send he w hw a hta ha had hc hh hr hx
  · exact hD.relay v hv i o hQ send he w hw a hta ha had hc hh hr hx

/-- A fresh emission has a handler strictly before its deadline. -/
theorem ready_broadcast (hD : DeliveryWithinOn E rho Q dl cut)
    (hv : v ∈ rho.honest) (ho : Q o) (he : D.Run.emits E rho v o t)
    (hw : w ∈ rho.honest) (ht : 0 ≤ t) (hd : t < dl t)
    (hc : dl t ≤ cut) (hh : dl t ≤ rho.horizon)
    (hR : D.LinkReadyOn E rho v w t (dl t))
    (hFresh : ¬ D.ProcessedByActionCut E rho w o t)
    (hx : P.excludes (D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    D.HandledBetween E rho w o t (dl t) :=
  (hD.broadcast v hv o ho t he w hw t le_rfl ht hd hc hh hR hx).resolve_left hFresh

/-- A fresh relay has a handler strictly before its deadline. -/
theorem ready_relay (hD : DeliveryWithinOn E rho Q dl cut)
    (hv : v ∈ rho.honest) (ho : Q o) (he : D.Run.acceptsAt E rho i v o t)
    (hw : w ∈ rho.honest) (ht : 0 ≤ t) (hd : t < dl t)
    (hc : dl t ≤ cut) (hh : dl t ≤ rho.horizon)
    (hR : D.LinkReadyOn E rho v w t (dl t))
    (hFresh : ¬ D.ProcessedByActionCut E rho w o t)
    (hx : P.excludes (D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    D.HandledBetween E rho w o t (dl t) :=
  (hD.relay v hv i o ho t he w hw t le_rfl ht hd hc hh hR hx).resolve_left hFresh

theorem accepted_by_deadline_statement : AcceptedByDeadlineStatement := by
  intro V _ In P E rho Timely Inv dl cut o send a w hD hT hw hta ha had hc hh
    hHistory hS hRF hHooks hAccept hReady hNX
  have hOn : DeliveryWithinOn E rho (fun _ => True) dl cut :=
    ⟨fun v hv o _ t => hD.broadcast v hv o t,
      fun v hv i o _ t => hD.relay v hv i o t⟩
  exact processed_by_deadline_of_service E rho Timely Inv w o a (dl a) hS had
    (service_of_readyTrigger hOn trivial hT hw hta ha had hc hh hNX)
    hHistory hRF hHooks hAccept hReady hNX

set_option linter.unusedVariables false in
theorem accepted_by_deadline :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    DeliveryWithin E rho dl cut →
    ReadyTrigger E rho o send w a (dl a) →
    w ∈ rho.honest → send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    HistorySafeAt E rho w o a →
    D.ScheduleWellFormed E rho →
    D.restartFree rho w (D.Run.actionCut rho a) (D.Run.idxBefore rho (dl a)) →
    D.HooksSound P → AcceptanceLaw P Timely Inv →
    (∀ j t', a ≤ t' → t' < dl a → D.Run.handlesAt E rho j w o t' →
      Inv (D.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧ P.depsPresent (D.Run.stateBefore E rho j w) o = true ∧
      Timely (D.Run.stateBefore E rho j w) o) →
    P.excludes (D.Run.stateBeforeTime E rho (dl a) w) o = false →
    P.processed (D.Run.stateBeforeTime E rho (dl a) w) o = true :=
  @accepted_by_deadline_statement

end AvailableChain.Gen.V2.Duty

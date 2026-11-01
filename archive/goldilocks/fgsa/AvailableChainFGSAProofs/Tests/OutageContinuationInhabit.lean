module
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean -- shake: keep (fixture root lemmas)
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming

/-! OUTPUT-DIRECT non-vacuity in the kernel. One honest node sleeps at time 15,
restarts at 16, and runs only awake ticks. The covering gate is at 14; restored
votes start at 21, after join. The outage endpoints are 12 and 18; the old budget
fails. Every emission has a same-time delivery. The horizon is 37. -/

-- Test fixtures and examples stay private.
set_option linter.privateModule false

set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.OutageContinuationInhabit.Sleep
private abbrev p : FGSA.Params :=
  ⟨⟨1, 1, 3, 2, by decide, by decide, by decide, by decide⟩, 2, 0, by decide, 2, by decide, fun
      d => ⟨d.slot + 1⟩⟩
private abbrev E : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, le_rfl, fun _ t => decide (t < 15 ∨ 16 ≤ t)⟩
private abbrev mkRun (es : List (V2.Event (Fin 1) (fgsa p unitCodec).Object)) :
    V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 37
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()
private abbrev events : List (V2.Event (Fin 1) (fgsa p unitCodec).Object) :=
  (List.range 38).foldl (fun es n =>
    if n = 15 then es else
    let es := if n = 16 then es ++ [.restart 0 n] else es
    let r := mkRun (es ++ [.tick 0 n])
    es ++ [.tick 0 n] ++ (V2.D.Run.emitsAt E r es.length).map (fun o => .deliver 0 o n)) []
private abbrev rho := mkRun events

-- Concrete data shared by the schedule and execution certificates.
private abbrev head (s b : Nat) : HeadWire p.n := ⟨.seat (.head s) 0, ⟨b⟩⟩
private abbrev row1 : RowWire p.n :=
  ⟨.seat .fg 0, .vote ⟨.vote 1 ⟨0⟩ false, none⟩⟩
private abbrev row2 : RowWire p.n :=
  ⟨.seat .fg 0, .vote ⟨.vote 2 ⟨6⟩ false, some ⟨1, ⟨0⟩⟩⟩⟩
private abbrev body1 : NamedProposal p.n :=
  .node .genesis 1 ⟨2⟩ 2 [head 0 0] [head 0 0] []
private abbrev body2 : NamedProposal p.n :=
  .node body1 2 ⟨3⟩ 2 [head 1 2] [head 1 2] []
private abbrev body3 : NamedProposal p.n :=
  .node body2 3 ⟨4⟩ 2 [head 2 3] [head 2 3] []
private abbrev body5 : NamedProposal p.n :=
  .node body2 5 ⟨6⟩ 474839418492892347327 [] [] [row1]
private abbrev body6 : NamedProposal p.n :=
  .node body5 6 ⟨7⟩ 2 [head 5 6] [head 5 6] []
private abbrev body7 : NamedProposal p.n :=
  .node body6 7 ⟨8⟩ 2 [head 6 7] [head 6 7] []
private abbrev body8 : NamedProposal p.n :=
  .node body7 8 ⟨9⟩ 34202398735908265492430813541546585471 [head 7 8] [head 7 8] [row2]
private abbrev body9 : NamedProposal p.n :=
  .node body8 9 ⟨10⟩ 2 [head 8 9] [head 8 9] []

private abbrev eventTable : List (V2.Event (Fin 1) (fgsa p unitCodec).Object) :=
  [.tick 0 0, .tick 0 1, .deliver 0 (ofHead p (head 0 0)) 1,
    .tick 0 2, .tick 0 3, .tick 0 4,
    .deliver 0 (ofWire p ⟨.proposer 1, .proposal body1⟩) 4,
    .tick 0 5, .deliver 0 (ofHead p (head 1 2)) 5,
    .tick 0 6, .tick 0 7, .tick 0 8,
    .deliver 0 (ofWire p ⟨.proposer 2, .proposal body2⟩) 8,
    .tick 0 9, .deliver 0 (ofHead p (head 2 3)) 9,
    .tick 0 10, .tick 0 11, .tick 0 12,
    .deliver 0 (ofWire p ⟨.proposer 3, .proposal body3⟩) 12,
    .tick 0 13, .deliver 0 (ofHead p (head 3 4)) 13,
    .tick 0 14, .deliver 0 (ofRow p row1) 14, .restart 0 16,
    .tick 0 16, .tick 0 17, .tick 0 18, .tick 0 19, .tick 0 20,
    .deliver 0 (ofWire p ⟨.proposer 5, .proposal body5⟩) 20,
    .tick 0 21, .deliver 0 (ofHead p (head 5 6)) 21,
    .tick 0 22, .tick 0 23, .tick 0 24,
    .deliver 0 (ofWire p ⟨.proposer 6, .proposal body6⟩) 24,
    .tick 0 25, .deliver 0 (ofHead p (head 6 7)) 25,
    .tick 0 26, .tick 0 27, .tick 0 28,
    .deliver 0 (ofWire p ⟨.proposer 7, .proposal body7⟩) 28,
    .tick 0 29, .deliver 0 (ofHead p (head 7 8)) 29,
    .tick 0 30, .deliver 0 (ofRow p row2) 30, .tick 0 31, .tick 0 32,
    .deliver 0 (ofWire p ⟨.proposer 8, .proposal body8⟩) 32,
    .tick 0 33, .deliver 0 (ofHead p (head 8 9)) 33,
    .tick 0 34, .tick 0 35, .tick 0 36,
    .deliver 0 (ofWire p ⟨.proposer 9, .proposal body9⟩) 36,
    .tick 0 37, .deliver 0 (ofHead p (head 9 10)) 37]

private theorem events_eq : events = eventTable := by decide +kernel

private theorem run_eq : rho = mkRun eventTable := congrArg mkRun events_eq

-- Every emission is the object delivered immediately after its tick.
private def emissionTable (i : Nat) : List (fgsa p unitCodec).Object :=
  match eventTable[i + 1]? with
  | some (.deliver _ o _) => [o]
  | _ => []

private theorem emits_eq (i : Nat) :
    V2.D.Run.emitsAt E (mkRun eventTable) i = emissionTable i := by
  have cert : ∀ j : Fin eventTable.length,
      V2.D.Run.emitsAt E (mkRun eventTable) j = emissionTable j := by decide +kernel
  by_cases hi : i < eventTable.length
  · exact cert ⟨i, hi⟩
  · have h0 : eventTable[i]? = none := List.getElem?_eq_none (by omega)
    have h1 : eventTable[i + 1]? = none := List.getElem?_eq_none (by omega)
    simp only [V2.D.Run.emitsAt, h0, emissionTable, h1]

private abbrev children (o : (fgsa p unitCodec).Object) : List (fgsa p unitCodec).Object :=
  match o.payload with
  | .proposal N => N.raw.map (ofHead p) ++ N.support.map (ofHead p) ++ N.rows.map (ofRow p)
  | _ => []
private theorem carries_children (o o' : (fgsa p unitCodec).Object) :
    (fgsa p unitCodec).carries o o' ↔ o' ∈ children o := by
  change carriesS p o o' ↔ _
  cases o with
  | mk a m =>
    cases m with
    | head => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | row => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | proposal N =>
      change _ ↔ o' ∈ (N.raw.map (ofHead p) ++ N.support.map (ofHead p)) ++
        N.rows.map (ofRow p)
      constructor
      · rintro (h | h | h)
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h
      · intro h
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

private def EventOK (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop :=
  match e with
    | .deliver v o t =>
      (fgsa p unitCodec).wellFormed o = true ∧
      (fgsa p unitCodec).depsPresent (V2.D.Run.stateBefore E rho i v) o = true ∧
      (fgsa p unitCodec).processed (V2.D.Run.stateBefore E rho i v) o = false ∧
      (∃ j : Fin rho.events.length, rho.events[j.val].time ≤ t ∧
        rho.events[j.val] = .tick v rho.events[j.val].time ∧ o ∈ V2.D.Run.emitsAt E rho j) ∧
      (∀ o' ∈ children o, ∃ j : Fin rho.events.length,
        rho.events[j.val].time ≤ t ∧ rho.events[j.val] = .tick 0 rho.events[j.val].time ∧
          o' ∈ V2.D.Run.emitsAt E rho j)
    | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) :
    Decidable (EventOK i e) := by
  cases e <;> unfold EventOK <;> infer_instance

private theorem checks : ∀ i : Fin rho.events.length, EventOK i rho.events[i.val] := by
  simp only [EventOK, events_eq, run_eq, emits_eq]
  apply @of_decide_eq_true _ (by
    refine @Fintype.decidableForallFintype _ _ (fun i => ?_) inferInstance
    split <;> infer_instance)
  decide +kernel

private theorem lsync_schedule : V2.D.ScheduleWellFormed E rho where
  horizon_nonneg := by decide
  sorted := by
    rw [run_eq]
    decide +kernel
  nodup := by
    rw [run_eq]
    decide +kernel
  in_horizon := by
    rw [run_eq]
    decide +kernel
  honest_only := by
    rw [run_eq]
    decide +kernel
  tick_public := by
    intro v t ht
    have hall : ∀ e ∈ rho.events, 0 ≤ e.time := by
      rw [run_eq]
      decide +kernel
    have hn : 0 ≤ t := hall _ ht
    exact ⟨t.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  tick_total := by
    intro v _ t _ ht hh hawake
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 37 at hh
    have ht15 : t ≠ 15 := by
      intro he
      subst t
      exact Bool.noConfusion hawake
    have cert : ∀ n ∈ List.range 38, n ≠ 15 →
        V2.Event.tick 0 (n : Int) ∈ rho.events := by rw [run_eq]; decide +kernel
    have he : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
    rw [← he]
    exact cert t.toNat (List.mem_range.mpr (by simp only [Time] at *; omega))
      (by simp only [Time] at *; omega)

private theorem wake_eq {v : Fin 1} {t : Time} (h : V2.D.Wakes E v t) :
    t = 16 := by
  change decide (t < 15 ∨ 16 ≤ t) = true ∧
    decide (t - 1 < 15 ∨ 16 ≤ t - 1) = false at h
  have ha : t < 15 ∨ 16 ≤ t := of_decide_eq_true h.1
  have hb : ¬ (t - 1 < 15 ∨ 16 ≤ t - 1) := of_decide_eq_false h.2
  simp only [Time] at *; omega

private def RestartOK (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Bool :=
  match e with | .restart _ u => decide (u = 16) | _ => true

private theorem restart_time {v : Fin 1} {t : Time}
    (ht : V2.Event.restart v t ∈ rho.events) : t = 16 := by
  have cert : ∀ e ∈ rho.events, RestartOK e = true := by
    rw [run_eq]
    decide +kernel
  exact of_decide_eq_true (cert _ ht)

private theorem event_awake : ∀ e ∈ rho.events, E.awake e.node e.time = true := by
  rw [run_eq]
  decide +kernel

private theorem fgp_sleep_valid : V2.D.SleepWellFormed E rho where
  tick_awake := fun _ _ he => event_awake _ he
  deliver_awake := fun _ _ _ he => event_awake _ he
  restart_awake := fun _ _ he => event_awake _ he
  wake_restart := by
    intro v _ t _ _ hw
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    rw [wake_eq hw, run_eq]
    decide +kernel

private theorem restarts : V2.D.RestartsAtWakes E rho := by
  intro v t ht
  rw [restart_time ht]
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  exact ⟨by decide, ⟨by decide, by decide⟩⟩

private theorem lsync_execution : V2.D.ExecutionValid E rho where
  toSleepWellFormed := fgp_sleep_valid
  toScheduleWellFormed := lsync_schedule
  wire := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.1
  deps := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.2.1
  fresh := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.2.2.1
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    obtain ⟨j, ht, hj, hem⟩ := hc.2.2.2.1
    have huv : v = u := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hh := checks ⟨i, hil⟩
    simp only [EventOK, he] at hh
    obtain ⟨j, ht, hj, hem⟩ := hh.2.2.2.2 o' ((carries_children o o').mp hc)
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩

private def Delivered (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop :=
  match e with
      | .tick v t => ∀ o ∈ V2.D.Run.emitsAt E rho i, t + fgsaDelay E.Δ 3 o ≤ 37 →
        ∃ j : Fin rho.events.length, t ≤ rho.events[j.val].time ∧
          rho.events[j.val].time < t + fgsaDelay E.Δ 3 o ∧
          rho.events[j.val] = .deliver v o rho.events[j.val].time
      | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) :
    Decidable (Delivered i e) := by
  cases e <;> unfold Delivered <;> infer_instance

private theorem lsync_delivered : ∀ i : Fin rho.events.length, Delivered i rho.events[i.val] := by
  simp only [Delivered, events_eq, run_eq, emits_eq]
  apply @of_decide_eq_true _ (by
    refine @Fintype.decidableForallFintype _ _ (fun i => ?_) inferInstance
    split <;> infer_instance)
  decide +kernel

private def ProcessedDelivery (j : Nat) : Prop :=
  match rho.events[j]? with
  | some (.deliver v o _) => (fgsa p unitCodec).processed
      (V2.D.Run.stateBefore E rho (j + 1) v) o = true
  | _ => True

private instance (j : Nat) : Decidable (ProcessedDelivery j) := by
  unfold ProcessedDelivery
  split <;> infer_instance

private theorem delivery_processed : ∀ j : Fin rho.events.length, ProcessedDelivery j := by
  simp only [ProcessedDelivery, events_eq, run_eq]
  apply @of_decide_eq_true _ (by
    refine @Fintype.decidableForallFintype _ _ (fun i => ?_) inferInstance
    split <;> infer_instance)
  decide +kernel

private theorem deliveryPrefix :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ 3) 37 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, hem⟩ w _ a hta ha had hcut _ _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := lsync_delivered ⟨i, hil⟩
    simp only [Delivered, he] at hc
    have hd : t + fgsaDelay E.Δ 3 o ≤ 37 := by
      change a + fgsaDelay E.Δ 3 o ≤ 37 at hcut
      linarith
    obtain ⟨j, ht, hd, hj⟩ := hc o hem hd
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    have hevent := List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩
    by_cases hja : a ≤ rho.events[j.val].time
    · exact Or.inr ⟨_, hja, by
        change rho.events[j.val].time < a + fgsaDelay E.Δ 3 o
        linarith,
        j, o, hevent, Or.inl rfl⟩
    · refine Or.inl ⟨j.val + 1, ?_, ?_⟩
      · exact Nat.succ_le_of_lt ((V2.D.Engine.index_lt_actionCut_iff
          lsync_schedule hevent a).mpr (Or.inl (lt_of_not_ge hja)))
      · have hp := delivery_processed j
        change ProcessedDelivery j.val at hp
        simpa only [ProcessedDelivery, hevent] using hp
  relay_accepted := by
    intro v _ i o t ha w _ a hta _ had _ _ _ _
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    obtain ⟨obj, hi, hhandles⟩ := ha.1
    by_cases hlt : t < a
    · refine Or.inl ⟨i + 1, ?_, ha.2.2⟩
      exact Nat.succ_le_of_lt ((V2.D.Engine.index_lt_actionCut_iff
        lsync_schedule hi a).mpr (Or.inl hlt))
    · have heq : t = a := le_antisymm hta (le_of_not_gt hlt)
      subst a
      exact Or.inr ⟨t, le_rfl, had, i, obj, hi, hhandles⟩

/-- ROOT-DIGEST W3b. The existing event certificate gives actual emission origin. -/
private theorem delay_rootEmission {x : Fin 1} {o : Obj p} {t : Time}
    (hd : V2.Event.deliver x o t ∈ rho.events) : ∃ i u,
    rho.events[i]? = some (.tick 0 u) ∧ o ∈ rho.emitsAt E i := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨hjl, he⟩ := List.getElem?_eq_some_iff.mp hj
  have hc := checks ⟨j, hjl⟩
  change EventOK j rho.events[j] at hc
  have hc' : EventOK j (.deliver x o t) := he ▸ hc
  dsimp only [EventOK] at hc'
  obtain ⟨i, _, hi, hem⟩ := hc'.2.2.2.1
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  exact ⟨i, _, List.getElem?_eq_some_iff.mpr ⟨i.isLt, hi⟩, hem⟩

/-- ROOT-DIGEST W3b. Decode a delivered proposal without any root assumption. -/
private theorem delay_rootProposal {x : Fin 1} {o : Obj p} {t : Time} {B : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events) (hp : o.payload = .proposal B) :
    ∃ s, o = ofWire p ⟨.proposer s, .proposal B⟩ := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
  have hw := lsync_execution.wire j x o t hj
  cases hm : (toWire p o).decode with
  | none =>
    change FGSA.wellFormed p (toWire p o) = true at hw
    simp only [FGSA.wellFormed, hm, Bool.false_eq_true] at hw
  | some m =>
    have he (w : Wire p.n) (h : toWire p o = w) : o = ofWire p w := by
      apply (toWireEquiv p).injective
      exact h.trans ((toWireEquiv p).right_inv w).symm
    cases m with
    | vote s j b => rw [he _ (decode_eq_vote.mp hm)] at hp; cases hp
    | row j body => rw [he _ (decode_eq_row.mp hm)] at hp; cases hp
    | block s b =>
      have ho := he _ (decode_eq_block.mp hm)
      rw [ho] at hp
      cases Msg.proposal.inj hp
      exact ⟨s, ho⟩

/-- ROOT-DIGEST W3b. Each scoped non-genesis body has a delivered origin. -/
private theorem delay_rootParents : ∀ x o t b,
    V2.Event.deliver x o t ∈ rho.events → o.payload = .proposal b →
    ∃ i y, b.parent ∈ (V2.D.Run.stateBefore E rho i y).st.namedBodies := by
  intro x o t b hd hp
  obtain ⟨i, u, hi, hem⟩ := delay_rootEmission hd
  obtain ⟨j, hj⟩ := emitted_payload_parent_stored E rho ⟨i, hi, hem⟩ hp
  exact ⟨j, 0, hj⟩

/-- ROOT-DIGEST W3b. Equal delivered slot roots identify the same single-seat action. -/
private theorem delay_rootDeliveredEq {x y : Fin 1} {o o' : Obj p} {t u : Time}
    {B C : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events) (hp : o.payload = .proposal B)
    (hd' : V2.Event.deliver y o' u ∈ rho.events) (hp' : o'.payload = .proposal C)
    (he : B.root = C.root) : B = C := by
  obtain ⟨s, rfl⟩ := delay_rootProposal hd hp
  obtain ⟨s', rfl⟩ := delay_rootProposal hd' hp'
  obtain ⟨i, ti, hi, hem⟩ := delay_rootEmission hd
  obtain ⟨j, tj, hj, hem'⟩ := delay_rootEmission hd'
  have hbr := emitted_proposal_slot_root E rho (fun _ => rfl) i 0 ti s B hi hem
  have hcr := emitted_proposal_slot_root E rho (fun _ => rfl) j 0 tj s' C hj hem'
  have hslots : B.slot = C.slot := Nat.add_right_cancel
    (congrArg BlockId.value (hbr.symm.trans (he.trans hcr)))
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem'
  have ha := (fgsa_emits_proposal E rho _ 0 ti s _).mp hem
  have ha' := (fgsa_emits_proposal E rho _ 0 tj s' _).mp hem'
  obtain ⟨H, raw0, sup0, rows0, hb, _, _⟩ := rowsOk_withApp _ _ _ ha.2.2.2.2
  obtain ⟨H', raw1, sup1, rows1, hc, _, _⟩ := rowsOk_withApp _ _ _ ha'.2.2.2.2
  have hBs : B.slot = s := by
    have hh := congrArg (fun m : Msg p.n => match m with
      | .proposal b => b.slot | _ => 0) hb
    exact hh
  have hCs : C.slot = s' := by
    have hh := congrArg (fun m : Msg p.n => match m with
      | .proposal b => b.slot | _ => 0) hc
    exact hh
  have hss : s = s' := hBs.symm.trans (hslots.trans hCs)
  rw [← hss] at ha'
  have htt : ti = tj := ha.2.1.symm.trans ha'.2.1
  subst tj
  have hij : i = j := by
    obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hj
    exact (lsync_execution.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)
  subst j
  exact (Msg.proposal.inj (Option.some.inj (ha.2.2.2.2.symm.trans ha'.2.2.2.2)))

/-- ROOT-DIGEST W3b. Origin closes the body scope; no fixture premise is assumed. -/
private theorem delay_rootPremise : NamedRootCollisionFree p unitCodec E rho where
  root_injective := by
    intro B C hB hC A D hA hD he
    have scopeX {X : NamedProposal p.n} (hX : NamedProposal.Preceq X B ∨ NamedProposal.Preceq X C) :
        NamedProposalInRun p unitCodec E rho X := by
      rcases hX with hX | hX
      · exact namedScope_ancestor E rho hB hX
      · exact namedScope_ancestor E rho hC hX
    have deliveredRoot {x : Fin 1} {o : Obj p} {t : Time} {X : NamedProposal p.n}
            (hd : V2.Event.deliver x o t ∈ rho.events) (hp : o.payload = .proposal X) :
        X.root = ⟨X.slot + 1⟩ := by
      obtain ⟨s, rfl⟩ := delay_rootProposal hd hp
      obtain ⟨i, u, hi, hem⟩ := delay_rootEmission hd
      exact emitted_proposal_slot_root E rho (fun _ => rfl) i 0 u s X hi hem
    rcases namedProposalInRun_genesis_or_delivered E rho delay_rootParents (scopeX hA) with
      rfl | hdA
    · rcases namedProposalInRun_genesis_or_delivered E rho delay_rootParents (scopeX hD) with
        rfl | hdD
      · rfl
      · obtain ⟨x, o, t, hd, hp⟩ := hdD
        exact (Nat.succ_ne_zero D.slot
          (congrArg BlockId.value (he.trans (deliveredRoot hd hp))).symm).elim
    · obtain ⟨x, o, t, hd, hp⟩ := hdA
      rcases namedProposalInRun_genesis_or_delivered E rho delay_rootParents (scopeX hD) with
        rfl | hdD
      · exact (Nat.succ_ne_zero A.slot
          (congrArg BlockId.value ((deliveredRoot hd hp).symm.trans he))).elim
      · obtain ⟨y, o', u, hd', hp'⟩ := hdD
        exact delay_rootDeliveredEq hd hp hd' hp' he

private theorem delay_receiptRoots : NamedReceiptRootCollisionFree p unitCodec E rho := by
  have emittedScope {v : Fin 1} {o : (fgsa p unitCodec).Object} {t : Time} {N : NamedProposal p.n}
      (hem : V2.D.Run.emits E rho v o t) (hp : o.payload = .proposal N) :
      NamedProposalInRun p unitCodec E rho N := by
    obtain ⟨i, hi, ho⟩ := hem
    have cert : ∀ j : Fin rho.events.length, ∀ o ∈ V2.D.Run.emitsAt E rho j,
        (match o.payload with
          | .proposal _ => decide (V2.Event.deliver 0 o rho.events[j.val].time ∈ rho.events)
          | _ => true) = true := by
      simp only [events_eq, run_eq, emits_eq]
      decide +kernel
    have hc := cert ⟨i, (List.getElem?_eq_some_iff.mp hi).1⟩ o ho
    have hd : V2.Event.deliver 0 o t ∈ rho.events := by
      simp only [hp, (List.getElem?_eq_some_iff.mp hi).2,
        decide_eq_true_eq, V2.Event.time] at hc
      exact hc
    exact namedScope_delivered E rho hd hp
  have scope {A : NamedProposal p.n} (hA : NamedProposalReceiptScope p unitCodec E rho A) :
      NamedProposalInRun p unitCodec E rho A := by
    rcases hA with hA | ⟨v, _, o, t, N, hem, hp, hAN⟩
    · exact hA
    · exact namedScope_ancestor E rho (emittedScope hem hp) hAN
  intro A B hA hB he
  exact namedProposal_eq E rho delay_rootPremise (scope hA) (scope hB) he

private theorem base : Base₂ p unitCodec E rho where
  valid := lsync_execution
  receiptIdealization := delay_receiptRoots
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    rcases l with (_ | _) | _
    · exact hl.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hl.elim
  cstar := by
    intro l hl
    rcases l with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hl.elim
    · exact hl.elim
  restartsAtWakes := restarts
  delta := rfl

private theorem awake_card {t : Time} (ht : t < 15 ∨ 16 ≤ t) :
    (Gen.V2.Duty.awakeHonest E rho t).card = 1 := by
  rw [Gen.V2.Duty.awakeHonest_def, Finset.filter_true_of_mem (fun _ _ => decide_eq_true ht)]
  rfl

private theorem faulty_card : (Gen.V2.Duty.faulty rho).card = 0 := by decide

/-- No event occurs during full honest sleep at time 15. -/
theorem all_asleep (t : Time) (h15 : 15 ≤ t) (h16 : t < 16) :
    Gen.V2.Duty.awakeHonest E rho t = ∅ := by
  rw [Gen.V2.Duty.awakeHonest_def]
  exact Finset.filter_false_of_mem (fun _ _ h => by
    rcases (of_decide_eq_true h : t < 15 ∨ 16 ≤ t) with h' | h'
    · exact (not_lt.mpr h15) h'
    · exact (not_le.mpr h16) h')

private theorem healthy_cut {b : Time} (hb : b ≤ 37) :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ 3) b where
  broadcast_emitted := by
    intro v hv o t he w hw a hta ha had hcut hhor hlink hx
    exact deliveryPrefix.broadcast_emitted v hv o t he w hw a hta ha had
      (hcut.trans hb) hhor hlink hx
  relay_accepted := by
    intro v hv i o t he w hw a hta ha had hcut hhor hlink hx
    exact deliveryPrefix.relay_accepted v hv i o t he w hw a hta ha had
      (hcut.trans hb) hhor hlink hx

private theorem sync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ 3) where
  broadcast_emitted := by
    intro v hv o t he w hw a hta ha had hcut hhor hawake hx
    have hm : max a E.t_GST = a := max_eq_left ha
    dsimp only at had hcut hhor hawake hx ⊢
    rw [hm] at had hcut hhor hawake hx ⊢
    exact deliveryPrefix.broadcast_emitted v hv o t he w hw a hta ha had hcut hhor hawake hx
  relay_accepted := by
    intro v hv i o t he w hw a hta ha had hcut hhor hawake hx
    have hm : max a E.t_GST = a := max_eq_left ha
    dsimp only at had hcut hhor hawake hx ⊢
    rw [hm] at had hcut hhor hawake hx ⊢
    exact deliveryPrefix.relay_accepted v hv i o t he w hw a hta ha had hcut hhor hawake hx

private theorem joined (v : Fin 1) (t : Time) (ht : t < 15 ∨ 20 ≤ t) :
    joinedAt p E rho v (slotAt p t) t := by
  have hbound (h16 : 16 ≤ t) : 16 ≤ slotStartZ p ((slotAt p t : Int) - 1) := by
    have h20 : 20 ≤ t := by simp only [Time] at *; omega
    have hd : 5 ≤ t / 4 := by simp only [Time] at *; omega
    change 16 ≤ 4 * (((t / 4).toNat : Int) - 1)
    simp only [Time] at *; omega
  refine ⟨?_, ?_, ?_⟩
  · exact decide_eq_true (by simp only [Time] at *; omega)
  · intro u _ hut hw
    rw [wake_eq hw] at hut ⊢
    exact hbound hut
  · intro u _ hut he
    rw [restart_time he] at hut ⊢
    exact hbound hut

private theorem joined_card (t : Time) (ht : t < 15 ∨ 20 ≤ t) :
    (joinedHonest p E rho t).card = 1 := by
  classical
  rw [joinedHonest, Finset.filter_true_of_mem (fun v _ => joined v t ht)]
  rfl

private theorem covered (fast : Bool) (v : Fin 1) :
    v ∈ coveredNodes p E rho fast 12 := by
  have hslow : slowCoveredSchedule p E rho v (coverLabel p 12) := by
    refine ⟨by decide, ?_, ?_⟩
    · intro t _ _ hh
      exact decide_eq_true (Or.inl (by change t ≤ 14 at hh; simp only [Time] at *; omega))
    · intro u _ hu he
      rw [restart_time he] at hu
      change (16 : Int) ≤ 14 at hu
      simp only [Time] at *; omega
  have hfast : fastCoveredSchedule p E rho v (coverLabel p 12) := by
    exact joined v 14 (Or.inl (by decide))
  classical
  cases fast
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslow⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfast⟩

private theorem bad_empty (fast : Bool) : outageW p E rho fast 12 5 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact (Finset.mem_filter.mp hv).2.1 (covered fast v)

private theorem sleepy_bad_card (t : Time) :
    (sleepyBad p E rho t).card ≤ 1 := Finset.card_le_univ _

/-- Every field of the continuation premise holds, in both modes, with
a sleep and wake within [b₀,b₁) = [12,18). -/
private theorem continuation_legacy (fast : Bool) :
    OutageContinuationPrem p unitCodec fast E rho 4 12 18 3 where
  pre := ⟨base, ⟨by decide, by decide⟩, healthy_cut (by decide), by decide, by
    intro t _ ht
    rw [awake_card (t := t) (Or.inl (by simp only [Time] at *; omega)), faulty_card]
    decide⟩
  sleepy := by
    intro t _ ht
    have h1 := Finset.card_le_univ (awakeHonestIn E rho (t - p.η) t ∪ Gen.V2.Duty.faulty rho)
    rw [Fintype.card_fin] at h1
    rw [awake_card (t := t) (Or.inl (by simp only [Time] at *; omega))]
    simp only [Time] at *; omega
  order := by decide
  lag := by cases fast <;> decide
  -- The restored vote at 21 follows the restart at 16 and the join cutoff at 16.
  lengthV := (outageV_iff_vote_bound p 12 18 (by decide)).mpr (by decide)
  fastPart := by
    intro _ t _ ht
    rw [awake_card (t := t) (Or.inl (by simp only [Time] at *; omega))]
    decide
  sync := sync
  gst := by decide
  partAfter := by
    intro t ht _
    rw [awake_card (t := t) (Or.inr (by simp only [Time] at *; omega)), faulty_card]
    decide

/-- The same public continuation claim has a valid sleep premise in both modes. -/
theorem outageContinuation_inhabited_sleep (fast : Bool) :
    OutageContinuationSleepPrem p unitCodec fast E rho 4 12 18 3 where
  toOutageContinuationPrem := continuation_legacy fast
  sleepPre := ⟨(continuation_legacy fast).pre, by
    intro t _ ht
    rw [joined_card t (Or.inl (by simp only [Time] at *; omega)), faulty_card]
    decide⟩
  joinedSleepy := by
    intro t _ ht
    have hc := sleepy_bad_card t
    rw [joined_card t (Or.inl (by simp only [Time] at *; omega))]
    simp only [Time] at *; omega
  joinedFastPart := by
    intro _ t _ ht
    rw [joined_card t (Or.inl (by simp only [Time] at *; omega))]
    decide
  protection := by
    refine ⟨5, ?_, ?_⟩
    · intro s
      change (18 : Int) ≤ 4 * (s : Int) + 1 ↔ 5 ≤ s
      simp only [Slot] at *
      omega
    · intro s hs _
      change 5 ≤ s at hs
      have hv : 20 ≤ SA.voteTime p.toParams s := by
        change 20 ≤ 4 * (s : Int) + 1
        simp only [Slot] at *
        omega
      rw [bad_empty fast, Finset.union_empty, Finset.sdiff_empty]
      change (Gen.V2.Duty.faulty rho).card <
        (joinedHonest p E rho (SA.voteTime p.toParams s)).card
      rw [faulty_card, joined_card _ (Or.inr hv)]
      decide
  joinedPartAfter := by
    intro t ht _
    have hEnd : OutageEnd p (restoredLabel p 18) = 37 := by decide
    have ht33 : 33 ≤ t := by rw [hEnd] at ht; simp only [Time] at *; omega
    rw [faulty_card, joined_card t (Or.inr (by simp only [Time] at *; omega))]
    decide
  sleepyAfter := by
    intro t ht _
    have hEnd : OutageEnd p (restoredLabel p 18) = 37 := by decide
    have ht33 : 33 ≤ t := by rw [hEnd] at ht; simp only [Time] at *; omega
    have hc := sleepy_bad_card t
    rw [joined_card t (Or.inr (by simp only [Time] at *; omega))]
    simp only [Time] at *; omega

/-- The old Outage₂ budget fails for these endpoints, so only the continuation
claim covers this run. -/
theorem old_budget_fails : ¬ ((18 : Time) - 12 ≤ min p.η (L p)) := by decide

theorem not_outage₂ (fast : Bool) : ¬ Outage₂ p unitCodec fast E rho 4 12 18 3 :=
  fun h => old_budget_fails h.budget

#print axioms outageContinuation_inhabited_sleep
#print axioms fgp_sleep_valid
#print axioms restarts
#print axioms joined
#print axioms delay_receiptRoots
#print axioms all_asleep
#print axioms not_outage₂

end AvailableChain.FGSA.Run.Tests.OutageContinuationInhabit.Sleep

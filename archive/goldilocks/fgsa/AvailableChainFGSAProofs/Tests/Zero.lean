module
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean
-- shake: keep (test examples use the Export names)

-- Test fixtures and examples stay private.
set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.Zero

private abbrev p4 : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private abbrev rho0 : V2.D.Run (Fin 4) (fgsa p4 unitCodec) where
  honest := {0}
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

private abbrev env0 : Generic.Env (Fin 4) :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

private theorem schedule0 : V2.D.ScheduleWellFormed env0 rho0 where
  horizon_nonneg := le_rfl
  sorted := List.pairwise_singleton _ _
  nodup := List.nodup_singleton _
  in_horizon := by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨le_rfl, le_rfl⟩
  honest_only := by
    intro e he
    have heq := List.mem_singleton.mp he
    subst e
    exact Finset.mem_singleton_self _
  tick_public := by
    intro v t ht
    have he : V2.Event.tick v t = .tick 0 0 := List.mem_singleton.mp ht
    cases he
    exact ⟨0, rfl⟩
  tick_total := by
    intro v hv t _ ht hh _
    have he : t = 0 := le_antisymm hh ht
    subst t
    have hv : v = 0 := Finset.mem_singleton.mp hv
    subst v
    exact List.mem_singleton_self _

private theorem noDelivery0 (i : Nat) (v : Fin 4) (o : (fgsa p4 unitCodec).Object)
    (t : Time) : rho0.events[i]? ≠ some (.deliver v o t) := by
  cases i <;> simp

private theorem namedRoots0 : NamedRootCollisionFree p4 unitCodec env0 rho0 := by
  have hnone : ∀ x o t, V2.Event.deliver x o t ∉ rho0.events := by
    intro x o t hd
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    exact noDelivery0 i x o t hi
  have hg {A : NamedProposal p4.n} (hA : NamedProposalInRun p4 unitCodec env0 rho0 A) :
      A = .genesis := by
    rcases namedProposalInRun_genesis_or_delivered env0 rho0
      (by intro x o t b hd; exact (hnone x o t hd).elim) hA with h | hd
    · exact h
    · obtain ⟨x, o, t, hd, _⟩ := hd
      exact (hnone x o t hd).elim
  refine ⟨?_⟩
  intro B C hB hC A D hA hD _
  have scopeX {X : NamedProposal p4.n} (hX : NamedProposal.Preceq X B ∨
      NamedProposal.Preceq X C) :
      NamedProposalInRun p4 unitCodec env0 rho0 X := by
    rcases hX with hX | hX
    · exact namedScope_ancestor env0 rho0 hB hX
    · exact namedScope_ancestor env0 rho0 hC hX
  exact (hg (scopeX hA)).trans (hg (scopeX hD)).symm

private theorem receiptRoots0 : NamedReceiptRootCollisionFree p4 unitCodec env0 rho0 := by
  have scope {A : NamedProposal p4.n}
      (hA : NamedProposalReceiptScope p4 unitCodec env0 rho0 A) :
      NamedProposalInRun p4 unitCodec env0 rho0 A := by
    rcases hA with hA | ⟨v, _, o, t, N, ⟨i, hi, hem⟩, hp, _⟩
    · exact hA
    · cases i with
      | zero =>
        have he := Option.some.inj hi
        cases he
        have hn : ∀ o ∈ V2.D.Run.emitsAt env0 rho0 0,
            (match o.payload with | .proposal _ => false | _ => true) = true := by
          decide +kernel
        simpa only [hp, Bool.false_eq_true] using hn o hem
      | succ i => simp at hi
  intro A B hA hB he
  exact namedProposal_eq env0 rho0 namedRoots0 (scope hA) (scope hB) he

-- Horizon zero with three faulty validators; no receipt is scheduled.
private theorem base0 : Base₂ p4 unitCodec env0 rho0 where
  valid := {
    toSleepWellFormed := {
      tick_awake := by intros; rfl
      deliver_awake := by intros; rfl
      restart_awake := by intros; rfl
      wake_restart := by intro v hv t ht hh hw; exact Bool.noConfusion hw.2 }
    toScheduleWellFormed := schedule0
    wire := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    deps := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    fresh := by intro i v o t h; exact (noDelivery0 i v o t h).elim
    unforgeable := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim
    carried := by rintro v o t ⟨i, hi⟩; exact (noDelivery0 i v o t hi).elim }
  receiptIdealization := receiptRoots0
  linked := by
    refine ⟨4, Equiv.refl _, ?_⟩
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · exact hℓ.elim
    · exact ⟨rfl, fun _ => rfl⟩
    · exact hℓ.elim
  cstar := by
    intro ℓ hℓ
    rcases ℓ with (_ | _) | _
    · change Function.Bijective (fun i : Fin 4 => i)
      exact Function.bijective_id
    · exact hℓ.elim
    · exact hℓ.elim
  restartsAtWakes := by intro v t he; simp at he
  delta := rfl

private theorem healthy0 : V2.D.HealthyPrefixDelivery env0 rho0 0 where
  broadcast_emitted := by
    intro v hv o t hem w hw a hta ha had hcut
    change a + 1 ≤ 0 at hcut
    dsimp [Time] at ha hcut
    omega
  relay_accepted := by
    intro v hv i o t ha
    obtain ⟨obj, hi, _⟩ := ha.1
    exact (noDelivery0 i v obj t hi).elim

private theorem prefix0 : CleanCutSet p4 unitCodec env0 rho0 0 :=
  ⟨HealthyPrefix₂.of_legacy base0 ⟨le_rfl, le_rfl⟩ healthy0
    (fun _ ht hb => (not_lt_of_ge ht hb).elim),
    fun _ ht hb => (not_lt_of_ge ht hb).elim⟩

-- The equal-delay regime recovers the old all-object law.
example : V2.D.HealthyPrefixDelivery env0 rho0 0 := prefix0.legacy_delivery

-- Three faulty nodes and a required tick of the one honest node.
example : (Gen.V2.Duty.faulty rho0).card = 3 := by decide +kernel
example : ¬ Gen.Pure.FaultQ p4.n (Gen.V2.Duty.faulty rho0).card := by
  intro h
  have hn : ¬ (Gen.V2.Duty.faulty rho0).card < Gen.Pure.qF p4.n := by decide +kernel
  exact hn h.lt
example : timeIdx rho0 0 = 1 := by decide +kernel
example : timeIdx rho0 (-1) = 0 ∧ timeIdx rho0 (rho0.horizon + 1) = 1 := by decide +kernel

-- A complete, nonempty healthy-prefix witness with false FaultQ.
example : CleanHistoryAt p4 unitCodec env0 rho0 0 ∧
    CleanTruncAt p4 unitCodec env0 rho0 0 :=
  ⟨cleanHistoryAt_zero prefix0.toHealthyPrefix₂, cleanTruncAt_zero prefix0.toHealthyPrefix₂⟩

private theorem zero_S (i : Nat) (hi : i ≤ 1) (x : Fin 4) :
    S_at p4 unitCodec env0 rho0 i x = .genesis := by
  interval_cases i <;> fin_cases x <;> rfl

example : CleanSafetyAt p4 unitCodec env0 rho0 :=
  cleanSafetyAt_of_trunc p4 unitCodec env0 rho0 schedule0 (by
    constructor
    · intro i j x y hi hj hx hy
      rw [zero_S i hi x, zero_S j hj y]
      rfl
    · intro i j x hi hj hij hx
      rw [zero_S i hi x, zero_S j hj x]
      exact Gen.Pure.block_preceq_refl .genesis)

-- Both theorem applications keep exactly the requested premises.
example (E : Generic.Env (Fin 4)) (h : CleanCutSet p4 unitCodec E rho0 0) :
    CleanHistoryAt p4 unitCodec E rho0 0 ∧ CleanTruncAt p4 unitCodec E rho0 0 :=
  ⟨cleanHistoryAt_zero h.toHealthyPrefix₂, cleanTruncAt_zero h.toHealthyPrefix₂⟩

example (E : Generic.Env (Fin 4)) (hs : V2.D.ScheduleWellFormed E rho0)
    (ht : Gen.Pure.CompatOn (· ∈ rho0.honest) (S_at p4 unitCodec E rho0)
        (· ≤ timeIdx rho0 rho0.horizon) ∧
      Gen.Pure.MonoOn (· ∈ rho0.honest) (S_at p4 unitCodec E rho0)
        (· ≤ timeIdx rho0 rho0.horizon)) :
    CleanSafetyAt p4 unitCodec E rho0 := cleanSafetyAt_of_trunc p4 unitCodec E rho0 hs ht

#print axioms namedRoots0
#print axioms receiptRoots0
#print axioms base0
#print axioms prefix0
#print axioms zero_S

end AvailableChain.FGSA.Run.Tests.Zero
end

-- Non-vacuity: Δ = 1; row emitted at 14, delivered at 16; ΔF = 3.
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.Delay
private abbrev p : FGSA.Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 2, 0, by decide, 2, by decide, fun
      d => ⟨d.slot + 1⟩⟩
private abbrev E : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
private abbrev mkRun (es : List (V2.Event (Fin 1) (fgsa p unitCodec).Object)) :
    V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 17
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()
private abbrev events : List (V2.Event (Fin 1) (fgsa p unitCodec).Object) :=
  (List.range 18).foldl (fun es n =>
    let r := mkRun (es ++ [.tick 0 n])
    es ++ [.tick 0 n] ++ ((V2.D.Run.emitsAt E r es.length).filter
      (fun o => match o.payload with | .row _ => false | _ => true)).map
        (fun o => .deliver 0 o n) ++
      (if n = 16 then (V2.D.Run.emitsAt E r 21).map (fun o => .deliver 0 o n) else [])) []
private abbrev rho := mkRun events
-- Concrete data shared by the schedule, execution and delayed-row certificates.
private abbrev head (s b : Nat) : HeadWire p.n := ⟨.seat (.head s) 0, ⟨b⟩⟩
private abbrev row1 : RowWire p.n :=
  ⟨.seat .fg 0, .vote ⟨.vote 1 ⟨0⟩ false, none⟩⟩
private abbrev body1 : NamedProposal p.n :=
  .node .genesis 1 ⟨2⟩ 2 [head 0 0] [head 0 0] []
private abbrev body2 : NamedProposal p.n :=
  .node body1 2 ⟨3⟩ 2 [head 1 2] [head 1 2] []
private abbrev body3 : NamedProposal p.n :=
  .node body2 3 ⟨4⟩ 2 [head 2 3] [head 2 3] []
private abbrev body4 : NamedProposal p.n :=
  .node body3 4 ⟨5⟩ 2 [head 3 4] [head 3 4] []

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
    .tick 0 14, .tick 0 15, .tick 0 16,
    .deliver 0 (ofWire p ⟨.proposer 4, .proposal body4⟩) 16,
    .deliver 0 (ofRow p row1) 16,
    .tick 0 17, .deliver 0 (ofHead p (head 4 5)) 17]

private theorem events_eq : events = eventTable := by decide +kernel

private theorem run_eq : rho = mkRun eventTable := congrArg mkRun events_eq

-- The row emitted at 14 is delivered at 16; other emissions follow their tick.
private def emissionTable (i : Nat) : List (fgsa p unitCodec).Object :=
  match eventTable[i]? with
  | some (.tick _ t) =>
    if t = 14 then [ofRow p row1] else
      match eventTable[i + 1]? with
      | some (.deliver _ o _) => [o]
      | _ => []
  | _ => []

private theorem emits_eq (i : Nat) :
    V2.D.Run.emitsAt E (mkRun eventTable) i = emissionTable i := by
  have cert : ∀ j : Fin eventTable.length,
      V2.D.Run.emitsAt E (mkRun eventTable) j = emissionTable j := by decide +kernel
  by_cases hi : i < eventTable.length
  · exact cert ⟨i, hi⟩
  · have hn : eventTable[i]? = none := List.getElem?_eq_none (by omega)
    simp only [V2.D.Run.emitsAt, emissionTable, hn]

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
    rw [run_eq]
    intro v _ t _ ht hh _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 17 at hh
    interval_cases t <;> decide +kernel

private theorem lsync_execution : V2.D.ExecutionValid E rho where
  toSleepWellFormed := {
    tick_awake := by intros; rfl
    deliver_awake := by intros; rfl
    restart_awake := by intros; rfl
    wake_restart := by intro v hv t ht hh hw; exact Bool.noConfusion hw.2 }
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
      | .tick v t => ∀ o ∈ V2.D.Run.emitsAt E rho i, t + fgsaDelay E.Δ 3 o ≤ 17 →
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

private theorem slowPrefix : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ 3) 17 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, hem⟩ w _ a hta ha had hcut _ _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := lsync_delivered ⟨i, hil⟩
    simp only [Delivered, he] at hc
    have hd : t + fgsaDelay E.Δ 3 o ≤ 17 := by
      change a + fgsaDelay E.Δ 3 o ≤ 17 at hcut
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

private abbrev row : (fgsa p unitCodec).Object := (V2.D.Run.emitsAt E rho 21)[0]'(by decide +kernel)
private theorem row_eq : row = ofRow p row1 := by
  simp only [row, run_eq, emits_eq]
  rfl

private theorem row_emits : V2.D.Run.emits E rho 0 row 14 := by
  refine ⟨21, ?_, ?_⟩
  · rw [run_eq]
    decide +kernel
  · exact List.getElem_mem _

private def NoEarlyRow (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop := match e with
  | .deliver _ o t => 15 ≤ t ∨ row ∉ o :: children o
  | _ => True
private instance (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Decidable (NoEarlyRow e) := by
  cases e <;> unfold NoEarlyRow <;> infer_instance

private theorem no_early_row : ∀ j : Fin rho.events.length, NoEarlyRow rho.events[j.val] := by
  change ∀ j : Fin events.length, NoEarlyRow (events[j.val]'j.isLt)
  rw [events_eq]
  decide +kernel

private theorem old_fails : ¬ V2.D.HealthyPrefixDelivery E rho 17 := by
  intro h
  have hx : (fgsa p unitCodec).excludes (V2.D.Run.stateBeforeTime E rho 15 0) row = false := by
    rw [run_eq, row_eq]
    decide +kernel
  have hs := h.broadcast_emitted 0 (Finset.mem_univ _) row 14 row_emits
    0 (Finset.mem_univ _) 14 le_rfl (by decide) (by decide) (by decide)
    (by decide) (by intro u hu hh; rfl) hx
  rcases hs with ⟨k, hk, hp⟩ | ⟨t, _, htd, j, o, hj, hh⟩
  · have cert : ∀ k : Fin (V2.D.Run.actionCut rho 14 + 1),
        (fgsa p unitCodec).processed (V2.D.Run.stateBefore E rho k 0) row = false := by
      rw [run_eq, row_eq]
      decide +kernel
    exact Bool.noConfusion ((cert ⟨k, by omega⟩).symm.trans hp)
  · obtain ⟨hjl, he⟩ := List.getElem?_eq_some_iff.mp hj
    have hc := no_early_row ⟨j, hjl⟩
    simp only [NoEarlyRow, he] at hc
    rcases hc with hc | hc
    · exact (not_lt_of_ge hc) htd
    · apply hc
      rcases (fgsaHooks p unitCodec).handles_carries _ o row hh with rfl | hcarry
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((carries_children o row).mp hcarry)
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
  restartsAtWakes := by
    intro v t hi
    have cert : ∀ e ∈ rho.events,
        (match e with | .restart _ _ => true | _ => false) = false := by
      rw [run_eq]
      decide +kernel
    exact Bool.noConfusion (cert _ hi)
  delta := rfl

private theorem slow_clean_legacy : Clean₂ p unitCodec E rho 3 := by
  refine ⟨⟨⟨base, ⟨by decide, le_rfl⟩, slowPrefix, by decide, ?_⟩, ?_⟩, rfl⟩
  · intro t _ _
    change 0 < 1
    decide
  · change 0 < 1
    decide

private theorem old_clean_fails : ¬ Clean₂ p unitCodec E rho := by
  intro h
  apply old_fails
  have hd := h.pre.healthy
  rw [fgsaDelay_self] at hd
  exact ⟨hd.broadcast_emitted, hd.relay_accepted⟩

private theorem lsync_delay_gap : E.Δ < (3 : Time) := by decide

private theorem delay_joined (t : Time) : (joinedHonest p E rho t).card = 1 := by
  classical
  have hj : ∀ v : Fin 1, joinedAt p E rho v (slotAt p t) t := by
    intro v
    refine ⟨rfl, ?_, ?_⟩
    · intro u hu hut hw
      exact Bool.noConfusion hw.2
    · intro u hu hut he
      have cert : ∀ e ∈ rho.events,
          (match e with | .restart _ _ => true | _ => false) = false := by
          rw [run_eq]
          decide +kernel
      exact Bool.noConfusion (cert _ he)
  simp only [joinedHonest, Finset.filter_true_of_mem (fun v _ => hj v)]
  decide

private theorem slow_clean : CleanSet p unitCodec E rho 3 :=
  ⟨slow_clean_legacy, ⟨slow_clean_legacy.pre,
    ⟨slow_clean_legacy.pre.toHealthyPrefix₂, by
      intro t ht hh
      rw [delay_joined]
      decide⟩, by rw [delay_joined]; decide⟩⟩

-- The exported safety claim applies to this slower-row run.
private theorem slow_safety : CleanSafetyAt p unitCodec E rho :=
  fgsa_cleanSafetyClaim p unitCodec E rho () ⟨slow_clean⟩

#print axioms lsync_execution
#print axioms delivery_processed
#print axioms delay_receiptRoots
#print axioms delay_joined
#print axioms slow_clean
#print axioms old_clean_fails
#print axioms slow_safety

end AvailableChain.FGSA.Run.Tests.Delay

module
public import AvailableChainSAPC.Proofs.RunCleanPath
public import AvailableChainKit.Roots
public meta import AvailableChainSAPC.Model.Protocol

/-!
Counterexample to the round-9 universal clean-path extension obligation.
With Δ = 1, n = 4, and one fault, the faulty slot-1 proposer sends two
genesis children at time 4. All three honest nodes receive both. They
choose x at time 5 (its root is larger) and receive all three x HEADs.
At event prefix 42, before the first time-6 tick, the joint invariant
still permits the path {genesis, y}. The time-6 save of N(1,x) then
prevents any extension of that path. This is a failure of the proof
obligation, not of an AvailableChain claim.

The finite checks use kernel reduction. The witness includes the complete
public schedule, self-delivery, signature provenance, accepted relay,
root injectivity, and the cap. It starts at the actual engine init.
-/

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/
namespace AvailableChain.SAPC.Tests.CleanInvariantCounterexample
open AvailableChain.Generic AvailableChain.Statements.Generic

abbrev p : Params := ⟨1, 4, 2, 0, by decide, by decide, by decide, by decide⟩
local instance : DecidableEq (sapc p).Object := inferInstanceAs (DecidableEq (Wire 4))

def x : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 1) 1
def y : Block := .node .genesis 1 (nodeRoot Block.genesis.root 1 0) 0

/-- `x` and `y` are siblings at slot 1 with different bodies. The time-5
HEAD choice is a score tie between them, so the larger root, `x`, wins it. -/
theorem y_root_lt_x_root : y.root < x.root := by decide

def proposal (b : Block) : Wire 4 := ⟨.proposer 1, .proposal b [] [] none⟩
def head (r : Slot) (v : Fin 4) (b : Block) : Wire 4 :=
  ⟨.seat r v, .head ⟨b, none⟩⟩
def readers : List (Fin 4) := [0, 1, 2]
def ticks (t : Time) : List (Event (Fin 4) (Wire 4)) :=
  readers.map (fun v => .tick v t)
def deliverAll (o : Wire 4) (t : Time) : List (Event (Fin 4) (Wire 4)) :=
  readers.map (fun v => .deliver v o t)
def heads (r : Slot) (b : Block) (t : Time) : List (Event (Fin 4) (Wire 4)) :=
  readers.flatMap (fun v => deliverAll (head r v b) t)

def env : Env (Fin 4) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

def run : Run (Fin 4) (sapc p) where
  honest := {0, 1, 2}
  horizon := 6
  events := show List (Event (Fin 4) (Wire 4)) from
    ticks 0 ++ ticks 1 ++ heads 0 .genesis 1 ++ ticks 2 ++ ticks 3 ++
    ticks 4 ++ deliverAll (proposal x) 4 ++ deliverAll (proposal y) 4 ++
    ticks 5 ++ heads 1 x 5 ++ ticks 6
  seatOf := fun _ => show Fin 4 ≃ Fin 4 from Equiv.refl (Fin 4)
  proposerOf := fun _ => 3

set_option maxRecDepth 100000

theorem next_save :
    run.events[42]? = some (.tick 0 (earlyTime p 1)) ∧
    savedTimely (Run.stateBefore (sapc p) run 43 0) 1 = some (some x) := by
  change (run.events[42]? = some (.tick 0 6)) ∧ _
  decide


private theorem sapc_counterexample_schedule : ScheduleWellFormed env run := by
  refine { horizon_nonneg := by decide
           sorted := by decide
           nodup := by decide
           in_horizon := by decide
           honest_only := by decide
           tick_public := ?_
           tick_total := ?_ }
  · intro v t ht
    have hn := (show ∀ e ∈ run.events, 0 ≤ e.time ∧ e.time ≤ 6 from by decide)
      _ ht
    exact ⟨t.toNat, by simpa only [env, mul_one] using! (Int.toNat_of_nonneg hn.1).symm⟩
  · intro v hv t _ ht hb
    change t ≤ 6 at hb
    have hc : ∀ v ∈ run.honest, ∀ k : Fin 7,
        Event.tick v (k.val : Time) ∈ run.events := by decide
    have htn : t.toNat < 7 := (Int.toNat_lt ht).mpr (lt_of_le_of_lt hb (by decide))
    simpa only [Int.toNat_of_nonneg ht] using hc v hv ⟨t.toNat, htn⟩

private theorem delivery_checks : ∀ i : Fin run.events.length,
    (match run.events[i.val] with
    | .tick _ _ => true
    | .deliver v o _ =>
      wellFormed p o && depsPresent (Run.stateBefore (sapc p) run i v) o &&
      !processed p (Run.stateBefore (sapc p) run i v) o) = true := by decide

private theorem delivery : DeliveryWellFormed (sapc p) run := by
  have hc (i : Nat) (v : Fin 4) (o : Wire 4) (t : Time)
      (he : run.events[i]? = some (.deliver v o t)) :
      wellFormed p o = true ∧ depsPresent (Run.stateBefore (sapc p) run i v) o = true ∧
        processed p (Run.stateBefore (sapc p) run i v) o = false := by
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp he
    have h := delivery_checks ⟨i, hi⟩
    rw [he] at h
    simpa only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, and_assoc] using h
  exact ⟨fun i v o t he => (hc i v o t he).1,
    fun i v o t he => (hc i v o t he).2.1,
    fun i v o t he => (hc i v o t he).2.2⟩

private def plain (o : Wire 4) : Bool :=
  match o.payload with
  | .head _ => true
  | .proposal _ [] [] none => true
  | _ => false

private theorem deliveries_plain : ∀ e ∈ run.events, ∀ o ∈ e.object?.toList,
    plain o = true := by set_option backward.isDefEq.respectTransparency false in decide

private theorem plain_handles {st : State 4} {o child : Wire 4}
    (hp : plain o = true) (hh : handles p st o child) : o = child := by
  rcases o with ⟨auth, msg⟩
  cases msg with
  | head h => simpa [handles] using hh
  | pc c => simp [plain] at hp
  | proposal b raw support cert =>
    cases raw <;> cases support <;> cases cert <;> simp [plain] at hp
    cases auth <;> simpa [handles, pcMembers] using hh

private theorem plain_no_carried {o child : Wire 4}
    (hp : plain o = true) : ¬ carries o child := by
  rcases o with ⟨auth, msg⟩
  cases msg with
  | head h => simp [carries]
  | pc c => simp [plain] at hp
  | proposal b raw support cert =>
    cases raw <;> cases support <;> cases cert <;> simp [plain] at hp
    simp [carries, pcMembers]


private theorem signature_checks : ∀ i : Fin run.events.length,
    (match run.events[i.val] with
    | .tick _ _ => true
    | .deliver _ o t => decide (∀ u ∈ run.honest,
        Run.holder (sapc p) run o.auth = some u →
        ∃ j : Fin run.events.length, run.events[j.val] = .tick u t ∧
          o ∈ Run.emittedAt (sapc p) env run j u t)) = true := by decide

private theorem signatures : UnforgeableSignatures (sapc p) env run := by
  constructor
  · intro v o t hp u hu hh
    obtain ⟨i, he⟩ := hp
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp he
    have hc := signature_checks ⟨i, hi⟩
    rw [he] at hc
    obtain ⟨j, hj, hm⟩ := of_decide_eq_true hc u hu hh
    exact ⟨t, le_refl _, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hm⟩
  · intro v o t hp child hc u _ _
    obtain ⟨i, he⟩ := hp
    have hp := deliveries_plain _ (List.mem_iff_getElem?.mpr ⟨i, he⟩) o (by simp [Event.object?])
    exact (plain_no_carried hp hc).elim

theorem execution : ExecutionValid (sapc p) env run :=
  { sapc_counterexample_schedule, delivery, signatures with }

private theorem broadcasts : ∀ i : Fin run.events.length,
    (match run.events[i.val] with
    | .deliver _ _ _ => true
    | .tick v t => decide (∀ o ∈ Run.emittedAt (sapc p) env run i v t,
        ∀ w ∈ run.honest, ∃ j : Fin run.events.length,
          run.events[j.val] = .deliver w o t)) = true := by decide

private theorem receipts : ∀ e ∈ run.events,
    (match e with
    | .tick _ _ => true
    | .deliver _ o t => decide (∀ w ∈ run.honest, ∃ j : Fin run.events.length,
        run.events[j.val] = .deliver w o t ∧
        processed p (Run.stateBefore (sapc p) run j w) o = false ∧
        processed p (Run.stateBefore (sapc p) run (j + 1) w) o = true)) = true := by decide

private theorem relay : AcceptedObjectRelay (sapc p) env run := by
  intro v _ i o t ha w hw _ _
  obtain ⟨parent, he, hh⟩ := ha.1
  have hm := List.mem_iff_getElem?.mpr ⟨i, he⟩
  have hp := deliveries_plain _ hm parent (by simp [Event.object?])
  have ho := plain_handles hp hh
  subst parent
  obtain ⟨j, hj, hf, ht⟩ := of_decide_eq_true (receipts _ hm) w hw
  refine ⟨t, le_refl _, ?_, j, ⟨o, ?_, Or.inl rfl⟩, hf, ht⟩
  · have := (sapc_counterexample_schedule.in_horizon _ hm).1
    change t < max t 0 + 1
    exact lt_of_le_of_lt (le_max_left t 0) (lt_add_one _)
  · exact List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩

private theorem synchrony : PartialSynchrony (sapc p) env run := by
  constructor
  · intro v _ o t hem w hw _ _
    obtain ⟨i, he, ho⟩ := hem
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp he
    have hc := broadcasts ⟨i, hi⟩
    rw [he] at hc
    obtain ⟨j, hj⟩ := of_decide_eq_true hc o ho w hw
    refine ⟨t, le_refl _, ?_, j, o, ?_, Or.inl rfl⟩
    · change t < max t 0 + 1
      exact lt_of_le_of_lt (le_max_left t 0) (lt_add_one _)
    · exact List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩
  · intro v hv i o t ha w hw hp hd _
    obtain ⟨t', hlo, hhi, j, hj⟩ := relay v hv i o t ha w hw hp hd
    exact ⟨t', hlo, hhi, j, hj.1⟩

/-- ROOT-DIGEST W3: the finite trace names only genesis and the two siblings. -/
private def namedOnly (o : Wire 4) : Bool :=
  match (sapcInterface p).block o.payload with
  | none => true
  | some B => decide (B ∈ ([.genesis, x, y] : List Block))

private theorem delivered_named : ∀ e ∈ run.events,
    e.object?.all namedOnly = true := by decide +kernel

private theorem emitted_named : ∀ i : Fin run.events.length,
    (match run.events[i.val] with
    | .deliver _ _ _ => true
    | .tick v t => (Run.emittedAt (sapc p) env run i v t).all namedOnly) = true := by
  decide +kernel

private theorem named_tip (o : Wire 4) (tip : Block) (h : namedOnly o = true)
    (hb : (sapcInterface p).block o.payload = some tip) :
    tip ∈ ([.genesis, x, y] : List Block) := by
  unfold namedOnly at h
  rw [hb] at h
  exact of_decide_eq_true h

private theorem finite_root_scope :
    RootInjective env (sapcInterface p).toInterface run := by
  have closed : ∀ tip ∈ ([.genesis, x, y] : List Block),
      ∀ B, Block.Preceq B tip → B ∈ ([.genesis, x, y] : List Block) := by
    intro tip ht B hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · have he : B = .genesis := of_decide_eq_true hp
      rw [he]; exact List.mem_cons_self
    · have hB : B = x ∨ B = .genesis := by
        simpa [x, Block.Preceq, Block.preceq] using hp
      rcases hB with rfl | rfl <;> simp
    · have hB : B = y ∨ B = .genesis := by
        simpa [y, Block.Preceq, Block.preceq] using hp
      rcases hB with rfl | rfl <;> simp
  have scope (B : Block) (h : BlockInRun env (sapcInterface p).toInterface run B) :
      B ∈ ([.genesis, x, y] : List Block) := by
    rcases h with rfl | ⟨v, o, t, tip, ho, hb, hp⟩
    · exact List.mem_cons_self
    · apply closed tip _ B hp
      apply named_tip o tip _ hb
      rcases ho with ⟨i, hi⟩ | ⟨i, hi, hm⟩
      · have h := delivered_named _ (List.mem_of_getElem? hi)
        change (some o).all namedOnly = true at h
        exact h
      · obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
        have h := emitted_named ⟨i, hlt⟩
        rw [he] at h
        exact List.all_eq_true.mp h o hm
  have hinj : ∀ B ∈ ([.genesis, x, y] : List Block),
      ∀ C ∈ ([.genesis, x, y] : List Block), B.root = C.root → B = C := by
    decide +kernel
  intro B C hB hC hr
  exact hinj B (scope B hB) C (scope C hC) hr

#print axioms finite_root_scope

/-- A full Sleepy execution with the fault cap and full honest participation. -/
theorem sleepy : SleepyRegime (sapc p) env (sapcInterface p).toInterface run 0 := by
  refine { rootInjective := finite_root_scope
           execution := execution
           partialSynchrony := synchrony
           gst_zero := rfl
           start_zero := rfl
           participation := ?_ }
  intro t _ _
  change (faulty run).card < (awakeAt env run.honest t).card
  have he : awakeAt env run.honest t = run.honest := by simp [awakeAt, env]
  rw [he]
  decide

theorem cap : FaultBound (sapc p) (pcFaultCap p) run := by
  unfold FaultBound
  decide

def rejectedPath (b : Block) : Prop := b = .genesis ∨ b = y

private theorem rejectedPath_clean : CleanPath rejectedPath := by
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · intro a b hp hb
    rcases hb with rfl | rfl
    · exact Or.inl (by simpa [Block.Preceq, Block.preceq] using hp)
    · simpa [rejectedPath, y, Block.Preceq, Block.preceq, or_comm] using hp
  · intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      change Block.compatible _ _ = true <;> decide

private theorem prefix_states : ∀ i : Fin 43, ∀ v : Fin 4,
    let st := Run.stateBefore (sapc p) run i v
    st.base.stableRecord = .genesis ∧ st.base.goldfishRecord = .genesis ∧
    st.base.obligations = [] ∧ st.base.genuine = [] ∧
    (st.timely = [] ∨ st.timely = [(0, none)]) ∧
    st.bestPC = none ∧
    ∀ o ∈ st.receivedHeads, o.payload.ack = none := by decide

private theorem no_valid_pc (i : Nat) (hi : i ≤ 42) (v : Fin 4) (c : PC 4) :
    pcValid p (Run.stateBefore (sapc p) run i v) c ≠ true := by
  intro hc
  have hwf := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  have hmem := (Bool.and_eq_true_iff.mp hc).2
  have hn : c.witnesses ≠ [] := by
    intro hn
    simp [pcWellFormed, hn, pcQuorum] at hwf
  obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hn
  have ha := (prefix_states ⟨i, by omega⟩ v).2.2.2.2.2.2 o
    (of_decide_eq_true (List.all_eq_true.mp hmem o ho))
  have hw := (pcWellFormed_witness p c hwf o ho).2.1
  rw [ha] at hw
  contradiction

private theorem prefix_times : ∀ i : Fin 42,
    ((run.events[i.val]?).map Event.time).getD 0 < 6 := by decide

private theorem no_gate_before (i : Nat) (hi : i < 42) (v : Fin 4) (r : Slot)
    (he : run.events[i]? = some (.tick v (gateTime p r))) : False := by
  have ht := prefix_times ⟨i, hi⟩
  simp only [he, Option.map_some, Option.getD_some, Event.time] at ht
  change (4 * (r : Time) + 6) < 6 at ht
  have hr : (0 : Time) ≤ r := Int.natCast_nonneg r
  linarith

private theorem head_pc_absent : ∀ i : Fin 42,
    (match run.events[i.val]? with
    | some (.tick v t) => decide (∀ r : Fin 2,
        selectedPC p (clock p (Run.stateBefore (sapc p) run i v) t) r = none)
    | _ => true) = true := by decide

/-- The round-9 invariant permits the stored branch that loses the HEAD choice. -/
theorem before_cutoff : CleanPathFacts p env run 42 rejectedPath := by
  set_option backward.isDefEq.respectTransparency false in
  refine ⟨rejectedPath_clean, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi v _
    have hs := prefix_states ⟨i, by omega⟩ v
    exact ⟨Or.inl hs.1, Or.inl hs.2.1,
      fun b g d hm => by simp only [hs.2.2.1, List.not_mem_nil] at hm,
      fun r b hm => by simp only [hs.2.2.2.1, List.not_mem_nil] at hm⟩
  · intro b hb
    rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨0, by decide, 30, by decide, by decide⟩
  · intro v _ b g d hm
    simp only [(prefix_states ⟨42, by decide⟩ v).2.2.1, List.not_mem_nil] at hm
  · intro j hj v _ r _ he
    exact (no_gate_before j hj v r he).elim
  · intro j hj v _ r _ he
    exact (no_gate_before j hj v r he).elim
  · intro i hi v _ c hc
    exact (no_valid_pc i hi v c hc).elim
  · intro i hi v _ r b ht
    rcases (prefix_states ⟨i, by omega⟩ v).2.2.2.2.1 with hn | hn
    · simp [savedTimely, hn] at ht
    · simp [savedTimely, hn] at ht
  · intro _ i _ v _
    exact capBroken_false_before p env run execution cap v i
  · intro i _ v _
    exact archive_authenticated_before p env run execution.toUnforgeableSignatures i v
  · intro i hi v _ r _ he
    exact (no_gate_before i hi v r he).elim
  · intro i hi v _ r c he _ hc
    have ht := (sapc_counterexample_schedule.in_horizon _ (List.mem_iff_getElem?.mpr ⟨i, he⟩)).2
    have hr : r < 2 := by
      change 4 * (r : Time) + 1 ≤ 6 at ht
      have hr : (r : Time) < 2 := by linarith
      exact_mod_cast hr
    have hn := head_pc_absent ⟨i, hi⟩
    rw [he] at hn
    have hn := of_decide_eq_true hn ⟨r, hr⟩
    rw [hn] at hc
    contradiction
  · intro i hi v _ r c _ _ hc
    rw [clock_bestPC, (prefix_states ⟨i, by omega⟩ v).2.2.2.2.2.1] at hc
    contradiction

/-- No larger clean path can contain both the rejected branch and the new N. -/
theorem no_extension : ¬ ∃ nextPath, (∀ b, rejectedPath b → nextPath b) ∧
    CleanPathFacts p env run 43 nextPath := by
  rintro ⟨nextPath, hext, hinv⟩
  have hx := (hinv.timely 43 (le_refl _) 0 (by decide) 1 x next_save.2).2 cap
  have hy := hext y (Or.inr rfl)
  have hxy := hinv.chain.comparable x y hx hy
  have hconflict : Block.compatible x y = false := by decide
  change Block.compatible x y = true at hxy
  rw [hconflict] at hxy
  contradiction

/-- The losing stored sibling is absent from the new run-determined path.
At this prefix there is no genuine gate, successful timely save, or PC
use. This checks the cause of the round-10 failure against the new definition. -/
theorem canonical_before : cleanRunPath p run 42 = (fun b => b = .genesis) := by
  set_option backward.isDefEq.respectTransparency false in
  have noSource (b : Block) (hb : CleanRunSource p run 42 b) : False := by
    cases hb with
    | genuine j hj v hv r b ht hc => exact no_gate_before j hj v r ht
    | timely r b cap source =>
      obtain ⟨v, hv, j, hj, ht, hs⟩ := source
      rcases (prefix_states ⟨j + 1, by omega⟩ v).2.2.2.2.1 with hn | hn
      · simp [savedTimely, hn] at hs
      · simp [savedTimely, hn] at hs
    | gate j hj v hv r c ht ha hc => exact no_gate_before j hj v r ht
    | head j hj v hv r c ht ha hc =>
      have ht' := (sapc_counterexample_schedule.in_horizon _ (List.mem_iff_getElem?.mpr ⟨j, ht⟩)).2
      have hr : r < 2 := by
        change 4 * (r : Time) + 1 ≤ 6 at ht'
        have hr : (r : Time) < 2 := by linarith
        exact_mod_cast hr
      have hn := head_pc_absent ⟨j, hj⟩
      rw [ht] at hn
      have hn := of_decide_eq_true hn ⟨r, hr⟩
      rw [hn] at hc
      contradiction
    | proposal j hj v hv r c ht ha hc =>
      rw [clock_bestPC, (prefix_states ⟨j, by omega⟩ v).2.2.2.2.2.1] at hc
      contradiction
  funext b
  apply propext
  constructor
  · rintro (hg | ⟨c, hc, hp⟩)
    · exact hg
    · exact (noSource c hc).elim
  · exact Or.inl

theorem canonical_excludes_losing_branch : ¬ cleanRunPath p run 42 y := by
  rw [canonical_before]
  intro h
  cases h

/-- The actual save adds the selected branch. It need not extend any
arbitrarily chosen stored sibling. -/
theorem canonical_next_contains_winner : cleanRunPath p run 43 x :=
  Or.inr ⟨x, .timely 1 x cap ⟨0, by decide, 42, by decide, next_save.1, next_save.2⟩,
    GridCO.block_preceq_self x⟩

end AvailableChain.SAPC.Tests.CleanInvariantCounterexample
end

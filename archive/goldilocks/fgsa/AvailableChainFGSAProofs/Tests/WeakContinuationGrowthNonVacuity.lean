module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts
-- shake: keep (own-library route)
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable

set_option maxRecDepth 4096

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.GrowthGenerator

variable {count : Nat} [NeZero count] {p : Params}
open AvailableChain.SimplexFG

/-- An emitted HEAD has passed the join test. -/
theorem nvGen_head_action {p : Params} {In : Type} {c : AppCodec In}
    {nd : Node p} {s : Slot} {x : In} {m : Msg p.n}
    (ha : act p c nd (.headAction s) x = some m) :
    some (.head (headVote p nd.st s).root) = some m := by
  change (if joinedNow p nd.st then some (.head (headVote p nd.st s).root) else none) =
    some m at ha
  split at ha
  · exact ha
  · cases ha

/-- An emitted proposal has passed the join test. -/
theorem nvGen_proposal_action {p : Params} {In : Type} {c : AppCodec In}
    {nd : Node p} {s : Slot} {x : In} {m : Msg p.n}
    (ha : act p c nd (.propAction s) x = some m) :
    (propose p nd.st s).map (withApp p (c.app x)) = some m := by
  change (if joinedNow p nd.st then
    (propose p nd.st s).map (withApp p (c.app x)) else none) = some m at ha
  split at ha
  · exact ha
  · cases ha

def params : Params where
  Δ := 1
  n := count
  k := 2
  η := 0
  deltaPos := by decide
  nPos := Nat.pos_of_ne_zero (NeZero.ne count)
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

abbrev Validator := Fin count

abbrev Event := V2.Event (Validator (count := count)) (fgsa (params (count := count))
  unitCodec).Object

abbrev World := V2.D.World (Validator (count := count)) (fgsa (params (count := count)) unitCodec)

def strongEnv : Generic.Env (Validator (count := count)) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

def weakEnv : Generic.Env (Validator (count := count)) := (strongEnv (count := count))

def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats (params (count := count)) ℓ) → (Validator
  (count := count))
  | .base _, i => i
  | .prop _, _ => 0

def runData (horizon : Time) (events : List (Event (count := count))) :
    V2.D.Run (Validator (count := count)) (fgsa (params (count := count)) unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := events
  seatOf := (seatOf (count := count))
  input _ _ := ()

def nodes : List (Validator (count := count)) := List.finRange count

omit [NeZero count] in
theorem nvGen_nodes_nodup : (nodes (count := count)).Nodup := List.nodup_finRange count

def tickBatch (t : Time) (w : (World (count := count))) : (World (count := count)) × List (Obj
  (params (count := count))) :=
  (nodes (count := count)).foldl (fun acc v =>
    let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
      (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ (show List (Obj (params (count := count))) from
      result.2))) (w, [])

def deliverOne (t : Time) (acc : (World (count := count)) × List (Event (count := count))) (vo :
  (Validator (count := count)) × Obj (params (count := count))) :
    (World (count := count)) × List (Event (count := count)) :=
  if (fgsa (params (count := count)) unitCodec).processed (acc.1 vo.1) vo.2 then acc else
    (V2.D.World.step (weakEnv (count := count)) ((runData (count := count)) 263 []) acc.1
      (.deliver vo.1 vo.2 t),
      acc.2 ++ [.deliver vo.1 vo.2 t])

def timeBatch (t : Time) (w : (World (count := count))) : (World (count := count)) × List (Event
  (count := count)) :=
  let ticks := (tickBatch (count := count)) t w
  let deliveries := ticks.2.flatMap (fun o => (nodes (count := count)).map (fun v => (v, o)))
  deliveries.foldl ((deliverOne (count := count)) t) (ticks.1, (nodes (count := count)).map (fun
    v => .tick v t))

def buildPrefix : Nat → (World (count := count)) × List (Event (count := count))
  | 0 => (V2.D.World.init, [])
  | steps + 1 =>
      let previous := buildPrefix steps
      let batch := (timeBatch (count := count)) (steps : Time) previous.1
      (batch.1, previous.2 ++ batch.2)

theorem nvGen_linked (h : Time) (es : List (Event (count := count))) :
    V2.D.Linked (fgsaFamilies (params (count := count)) unitCodec).linked ((runData (count :=
      count)) h es) := by
  refine ⟨count, Equiv.refl _, ?_⟩
  intro label hf
  cases label with
  | prop s => exact hf.elim
  | base label =>
      cases label with
      | head s => exact hf.elim
      | fg => exact ⟨rfl, fun _ => rfl⟩

theorem nvGen_delivery_fold_mem (t : Time) (xs : List ((Validator (count := count)) × Obj (params
  (count := count))))
    (acc : (World (count := count)) × List (Event (count := count))) (e : (Event (count :=
      count))) :
    e ∈ (xs.foldl ((deliverOne (count := count)) t) acc).2 ↔
      e ∈ acc.2 ∨ e ∈ (xs.foldl ((deliverOne (count := count)) t) acc).2 ∧
        ∃ v o, e = .deliver v o t := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil]; tauto
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      by_cases hp : (fgsa (params (count := count)) unitCodec).processed (acc.1 x.1) x.2 = true
      · simp only [deliverOne, hp, ↓reduceIte]
        tauto
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ((he | he) | he)
          · exact Or.inl he
          · exact Or.inr ⟨Or.inl (Or.inr he), x.1, x.2, he⟩
          · exact Or.inr ⟨Or.inr he, he.2⟩
        · rintro (he | ⟨he, hd⟩)
          · exact Or.inl (Or.inl he)
          · exact he

theorem nvGen_timeBatch_shape (t : Time) (w : (World (count := count))) (e : (Event (count :=
  count)))
    (he : e ∈ ((timeBatch (count := count)) t w).2) :
    e.time = t ∧ (∃ v, e = .tick v t) ∨ e.time = t ∧ ∃ v o, e = .deliver v o t := by
  rw [timeBatch, nvGen_delivery_fold_mem] at he
  rcases he with ht | ⟨_, v, o, rfl⟩
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    exact Or.inl ⟨rfl, v, rfl⟩
  · exact Or.inr ⟨rfl, v, o, rfl⟩

theorem nvGen_timeBatch_time (t : Time) (w : (World (count := count))) (e : (Event (count :=
  count)))
    (he : e ∈ ((timeBatch (count := count)) t w).2) : e.time = t :=
  ((nvGen_timeBatch_shape (count := count)) t w e he).elim And.left And.left

theorem nvGen_timeBatch_no_restart (t : Time) (w : (World (count := count))) (v : (Validator
  (count :=
  count))) (s : Time) :
    V2.Event.restart v s ∉ ((timeBatch (count := count)) t w).2 := by
  intro he
  rcases (nvGen_timeBatch_shape (count := count)) t w _ he with ⟨_, u, hu⟩ | ⟨_, u, o, hu⟩ <;>
    cases hu

omit [NeZero count] in
theorem nvGen_nodes_complete (v : (Validator (count := count))) : v ∈ (nodes (count := count)) := by
  exact List.mem_finRange v

theorem nvGen_timeBatch_tick (t : Time) (w : (World (count := count))) (v : (Validator (count :=
  count))) :
    V2.Event.tick v t ∈ ((timeBatch (count := count)) t w).2 := by
  rw [timeBatch, nvGen_delivery_fold_mem]
  exact Or.inl (List.mem_map.mpr ⟨v, (nvGen_nodes_complete (count := count)) v, rfl⟩)

theorem nvGen_witness_prefix_times (steps : Nat) (e : (Event (count := count))) (he : e ∈
  ((buildPrefix (count := count)) steps).2) :
    0 ≤ e.time ∧ e.time < steps := by
  induction steps with
  | zero => simp [buildPrefix] at he
  | succ steps ih =>
      change e ∈ ((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
        ((buildPrefix (count := count)) steps).1).2 at he
      rcases List.mem_append.mp he with he | he
      · have := ih he
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [Time] at *
        omega
      · rw [nvGen_timeBatch_time (count := count) _ _ _ he]
        exact ⟨Int.natCast_nonneg _, by simp⟩

theorem nvGen_prefix_no_restart (steps : Nat) (v : (Validator (count := count))) (t : Time) :
    V2.Event.restart v t ∉ ((buildPrefix (count := count)) steps).2 := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      change V2.Event.restart v t ∉ ((buildPrefix (count := count)) steps).2 ++
        ((timeBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2
      simp only [List.mem_append, not_or]
      exact ⟨ih, (nvGen_timeBatch_no_restart (count := count)) _ _ v t⟩

theorem nvGen_prefix_tick (steps t : Nat) (ht : t < steps) (v : (Validator (count := count))) :
    V2.Event.tick v (t : Time) ∈ ((buildPrefix (count := count)) steps).2 := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      change V2.Event.tick v (t : Time) ∈ ((buildPrefix (count := count)) steps).2 ++
        ((timeBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2
      by_cases he : t = steps
      · subst t
        exact List.mem_append_right _ ((nvGen_timeBatch_tick (count := count)) _ _ v)
      · exact List.mem_append_left _ (ih (by omega))

theorem nvGen_phase_le_two (e : (Event (count := count))) : e.phase ≤ 2 := by cases e <;> simp
  [V2.Event.phase]

theorem nvGen_key_le_delivery (e : (Event (count := count))) (v : (Validator (count := count))) (o :
  Obj (params (count := count))) (t : Time)
    (ht : e.time ≤ t) : e.key ≤ (V2.Event.deliver v o t).key := by
  exact Prod.Lex.toLex_le_toLex'.mpr ⟨ht, fun _ => (nvGen_phase_le_two (count := count)) e⟩

theorem nvGen_delivery_fold_sorted (t : Time) (xs : List ((Validator (count := count)) × Obj (params
  (count := count))))
    (acc : (World (count := count)) × List (Event (count := count))) (hs : acc.2.Pairwise (fun e
      f => e.key ≤ f.key))
    (ht : ∀ e ∈ acc.2, e.time ≤ t) :
    (xs.foldl ((deliverOne (count := count)) t) acc).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa (params (count := count)) unitCodec).processed (acc.1 x.1) x.2 = true
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hs ht
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte]
        apply ih
        · rw [List.pairwise_append]
          refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
          intro e he f hf
          obtain rfl := List.mem_singleton.mp hf
          exact (nvGen_key_le_delivery (count := count)) e _ _ _ (ht e he)
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact ht e he
          · obtain rfl := List.mem_singleton.mp he
            exact le_rfl

theorem nvGen_timeBatch_sorted (t : Time) (w : (World (count := count))) :
    ((timeBatch (count := count)) t w).2.Pairwise (fun e f => e.key ≤ f.key) := by
  apply (nvGen_delivery_fold_sorted (count := count))
  · simp only [List.pairwise_map, V2.Event.key, V2.Event.time, V2.Event.phase]
    exact List.pairwise_of_forall (fun _ _ => le_rfl)
  · intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact le_rfl

theorem nvGen_prefix_sorted (steps : Nat) :
    ((buildPrefix (count := count)) steps).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction steps with
  | zero => exact List.Pairwise.nil
  | succ steps ih =>
      change (((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
        ((buildPrefix (count := count)) steps).1).2).Pairwise _
      rw [List.pairwise_append]
      refine ⟨ih, (nvGen_timeBatch_sorted (count := count)) _ _, ?_⟩
      intro e he f hf
      have he' := ((nvGen_witness_prefix_times (count := count)) steps e he).2
      have hf' := (nvGen_timeBatch_time (count := count)) _ _ f hf
      apply Prod.Lex.toLex_le_toLex'.mpr
      dsimp only
      rw [hf']
      exact ⟨le_of_lt he', fun h => False.elim (ne_of_lt he' h)⟩

def genFold (w : (World (count := count))) (es : List (Event (count := count))) : (World (count
  := count)) :=
  es.foldl (V2.D.World.step (weakEnv (count := count)) ((runData (count := count)) 263 [])) w

def GenFresh : (World (count := count)) → List (Event (count := count)) → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => (fgsa (params (count := count)) unitCodec).processed (w v) o = false
        | _ => True) ∧
      GenFresh (V2.D.World.step (weakEnv (count := count)) ((runData (count := count)) 263 []) w
        e) es

theorem nvGen_genFold_append (w : (World (count := count))) (es ds : List (Event (count :=
  count))) :
    (genFold (count := count)) w (es ++ ds) = (genFold (count := count)) ((genFold (count :=
      count)) w es) ds :=
  List.foldl_append

theorem nvGen_genFresh_append (w : (World (count := count))) (es ds : List (Event (count :=
  count))) :
    (GenFresh (count := count)) w (es ++ ds) ↔ (GenFresh (count := count)) w es ∧ (GenFresh
      (count := count)) ((genFold (count := count)) w es) ds := by
  induction es generalizing w with
  | nil => simp [GenFresh, genFold]
  | cons e es ih =>
      simp only [List.cons_append, GenFresh, ih, genFold, List.foldl_cons]
      tauto

theorem nvGen_tick_fold_replay (t : Time) (vs : List (Validator (count := count)))
    (w : (World (count := count))) (os : List (Obj (params (count := count)))) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).1 =
      (genFold (count := count)) w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w os with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.foldl_cons, List.map_cons, genFold, V2.D.World.step] at *
      exact ih _ _

theorem nvGen_tickBatch_replay (t : Time) (w : (World (count := count))) :
    ((tickBatch (count := count)) t w).1 = (genFold (count := count)) w ((nodes (count :=
      count)).map (fun v => .tick v t)) :=
  (nvGen_tick_fold_replay (count := count)) t (nodes (count := count)) w []

theorem nvGen_tick_list_fresh (t : Time) (vs : List (Validator (count := count))) (w : (World (count
  := count))) :
    (GenFresh (count := count)) w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

theorem nvGen_delivery_fold_replay_fresh (t : Time) (xs : List ((Validator (count := count)) × Obj
  (params (count := count))))
    (w : (World (count := count))) (acc : (World (count := count)) × List (Event (count := count)))
    (hr : acc.1 = (genFold (count := count)) w acc.2) (hf : (GenFresh (count := count)) w acc.2) :
    (xs.foldl ((deliverOne (count := count)) t) acc).1 = (genFold (count := count)) w (xs.foldl
      ((deliverOne (count := count)) t) acc).2 ∧
      (GenFresh (count := count)) w (xs.foldl ((deliverOne (count := count)) t) acc).2 := by
  induction xs generalizing acc with
  | nil => exact ⟨hr, hf⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa (params (count := count)) unitCodec).processed (acc.1 x.1) x.2 = true
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hr hf
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte]
        apply ih
        · rw [nvGen_genFold_append, ← hr]
          rfl
        · rw [nvGen_genFresh_append, ← hr]
          exact ⟨hf, Bool.eq_false_iff.mpr hp, trivial⟩

theorem nvGen_timeBatch_replay_fresh (t : Time) (w : (World (count := count))) :
    ((timeBatch (count := count)) t w).1 = (genFold (count := count)) w ((timeBatch (count :=
      count)) t w).2 ∧
      (GenFresh (count := count)) w ((timeBatch (count := count)) t w).2 :=
  (nvGen_delivery_fold_replay_fresh (count := count)) t _ w _ ((nvGen_tickBatch_replay (count :=
    count)) t
    w) ((nvGen_tick_list_fresh (count := count)) t (nodes (count := count)) w)

theorem nvGen_prefix_replay_fresh (steps : Nat) :
    ((buildPrefix (count := count)) steps).1 = (genFold (count := count)) V2.D.World.init
      ((buildPrefix (count := count)) steps).2 ∧
      (GenFresh (count := count)) V2.D.World.init ((buildPrefix (count := count)) steps).2 := by
  induction steps with
  | zero => exact ⟨rfl, trivial⟩
  | succ steps ih =>
      have hb := (nvGen_timeBatch_replay_fresh (count := count)) (steps : Time) ((buildPrefix (count
        := count)) steps).1
      constructor
      · change ((timeBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).1 =
          (genFold (count := count)) V2.D.World.init
            (((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
              ((buildPrefix (count := count)) steps).1).2)
        rw [nvGen_genFold_append, ← ih.1]
        exact hb.1
      · change (GenFresh (count := count)) V2.D.World.init
          (((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
            ((buildPrefix (count := count)) steps).1).2)
        rw [nvGen_genFresh_append, ← ih.1]
        exact ⟨ih.2, hb.2⟩

theorem nvGen_genFresh_get (w : (World (count := count))) (es : List (Event (count := count))) (hf :
  (GenFresh (count := count)) w es)
    (i : Nat) (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    (fgsa (params (count := count)) unitCodec).processed ((genFold (count := count)) w (es.take
      i) v) o = false := by
  induction es generalizing w i with
  | nil => simp at he
  | cons e es ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst e
          exact hf.1
      | succ i =>
          exact ih _ hf.2 i (by simpa using he)

theorem nvGen_runData_fresh (h : Time) (es : List (Event (count := count)))
    (hf : (GenFresh (count := count)) V2.D.World.init es)
    (i : Nat) (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    (fgsa (params (count := count)) unitCodec).processed
      (V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count := count)) h es) i v) o
        = false := by
  exact (nvGen_genFresh_get (count := count)) V2.D.World.init es hf i v o t he

def GenEmits (w : (World (count := count))) (es : List (Event (count := count))) (v : (Validator
  (count := count))) (o : Obj (params (count := count))) (t : Time) : Prop :=
  ∃ pre post, es = pre ++ .tick v t :: post ∧
    o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) ((genFold
      (count := count)) w pre v) v t).2

def GenOrigin (w : (World (count := count))) (es : List (Event (count := count))) : Prop :=
  ∀ v o t, V2.Event.deliver v o t ∈ es → ∃ u, (GenEmits (count := count)) w es u o t

theorem nvGen_genEmits_cons (w : (World (count := count))) (e : (Event (count := count))) (es : List
  (Event (count := count)))
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (h : (GenEmits (count := count)) (V2.D.World.step (weakEnv (count := count)) ((runData
      (count := count)) 263 []) w e) es v o t) :
    (GenEmits (count := count)) w (e :: es) v o t := by
  obtain ⟨pre, post, he, ho⟩ := h
  exact ⟨e :: pre, post, congrArg (e :: ·) he, ho⟩

theorem nvGen_genEmits_append_left (w : (World (count := count))) (es ds : List (Event (count :=
  count)))
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time) (h :
      (GenEmits (count := count)) w es v o t) :
    (GenEmits (count := count)) w (es ++ ds) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := h
  exact ⟨pre, post ++ ds, by simp only [List.append_assoc, List.cons_append], ho⟩

theorem nvGen_genEmits_append_right (w : (World (count := count))) (es ds : List (Event (count
  := count)))
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time) (h :
      (GenEmits (count := count)) ((genFold (count := count)) w es) ds v o t) :
    (GenEmits (count := count)) w (es ++ ds) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := h
  refine ⟨es ++ pre, post, (List.append_assoc ..).symm, ?_⟩
  rwa [(nvGen_genFold_append (count := count))]

theorem nvGen_genOrigin_append (w w' : (World (count := count))) (es ds : List (Event (count :=
  count)))
    (hr : w' = (genFold (count := count)) w es) (he : (GenOrigin (count := count)) w es) (hd :
      (GenOrigin (count := count)) w' ds) :
    (GenOrigin (count := count)) w (es ++ ds) := by
  intro v o t hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨u, hu⟩ := he v o t hm
    exact ⟨u, (nvGen_genEmits_append_left (count := count)) w es ds u o t hu⟩
  · obtain ⟨u, hu⟩ := hd v o t hm
    rw [hr] at hu
    exact ⟨u, (nvGen_genEmits_append_right (count := count)) w es ds u o t hu⟩

theorem nvGen_tick_fold_origin (t : Time) (vs : List (Validator (count := count)))
    (w : (World (count := count))) (os : List (Obj (params (count := count)))) (o : Obj (params
      (count := count)))
    (ho : o ∈ (vs.foldl (fun acc v =>
      let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2) :
    o ∈ os ∨ ∃ v, (GenEmits (count := count)) w (vs.map (fun v => .tick v t)) v o t := by
  induction vs generalizing w os with
  | nil => exact Or.inl ho
  | cons v vs ih =>
      rcases ih _ _ ho with hm | ⟨u, hu⟩
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨v, [], vs.map (fun u => .tick u t), rfl, hm⟩
      · exact Or.inr ⟨u, (nvGen_genEmits_cons (count := count)) w (.tick v t) _ u o t hu⟩

theorem nvGen_tickBatch_origin (t : Time) (w : (World (count := count))) (o : Obj (params (count :=
  count)))
    (ho : o ∈ ((tickBatch (count := count)) t w).2) :
    ∃ v, (GenEmits (count := count)) w ((nodes (count := count)).map (fun v => .tick v t)) v o t
      := by
  rcases (nvGen_tick_fold_origin (count := count)) t (nodes (count := count)) w [] o ho with h | h
  · exact (List.not_mem_nil h).elim
  · exact h

theorem nvGen_delivery_fold_sublist (t : Time) (xs : List ((Validator (count := count)) × Obj
  (params
  (count := count))))
    (acc : (World (count := count)) × List (Event (count := count))) :
    ∃ ds, (xs.foldl ((deliverOne (count := count)) t) acc).2 = acc.2 ++ ds ∧
      ds.Sublist (xs.map (fun vo => .deliver vo.1 vo.2 t)) := by
  induction xs generalizing acc with
  | nil => exact ⟨[], (List.append_nil _).symm, .slnil⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      obtain ⟨ds, he, hs⟩ := ih ((deliverOne (count := count)) t acc x)
      by_cases hp : (fgsa (params (count := count)) unitCodec).processed (acc.1 x.1) x.2 = true
      · simp only [deliverOne, hp, ↓reduceIte] at he ⊢
        exact ⟨ds, he, hs.cons _⟩
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte] at he ⊢
        refine ⟨.deliver x.1 x.2 t :: ds, ?_, hs.cons_cons _⟩
        simpa only [List.append_assoc, List.singleton_append] using he

theorem nvGen_timeBatch_block (t : Time) (w : (World (count := count))) :
    ∃ ds, ((timeBatch (count := count)) t w).2 = (nodes (count := count)).map (fun v => .tick v
      t) ++ ds ∧
      ds.Sublist (((tickBatch (count := count)) t w).2.flatMap
        (fun o => (nodes (count := count)).map (fun v => .deliver v o t))) := by
  obtain ⟨ds, he, hs⟩ := (nvGen_delivery_fold_sublist (count := count)) t
    (((tickBatch (count := count)) t w).2.flatMap (fun o => (nodes (count := count)).map (fun v
      => (v, o))))
    (((tickBatch (count := count)) t w).1, (nodes (count := count)).map (fun v => .tick v t))
  refine ⟨ds, he, ?_⟩
  simp only [List.map_flatMap, List.map_map, Function.comp_def] at hs
  exact hs

theorem nvGen_prefix_blocks (steps : Nat) :
    ((buildPrefix (count := count)) steps).2 = (List.range steps).flatMap
      (fun (s : Nat) => ((timeBatch (count := count)) (s : Time) ((buildPrefix (count := count))
        s).1).2) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      change ((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
        ((buildPrefix (count := count)) steps).1).2 = _
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]

theorem nvGen_timeBatch_origin (t : Time) (w : (World (count := count))) : (GenOrigin (count :=
  count)) w ((timeBatch (count := count)) t w).2 := by
  obtain ⟨ds, he, hs⟩ := (nvGen_timeBatch_block (count := count)) t w
  intro v o s hm
  rw [he] at hm ⊢
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    cases hu
  · obtain ⟨o', ho', hv⟩ := List.mem_flatMap.mp (hs.subset hm)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
    cases hu
    obtain ⟨u, hu⟩ := (nvGen_tickBatch_origin (count := count)) t w o ho'
    exact ⟨u, (nvGen_genEmits_append_left (count := count)) w _ ds u o t hu⟩

theorem nvGen_prefix_origin (steps : Nat) : (GenOrigin (count := count)) V2.D.World.init
  ((buildPrefix
  (count := count)) steps).2 := by
  induction steps with
  | zero => intro v o t hm; exact (List.not_mem_nil hm).elim
  | succ steps ih =>
      exact (nvGen_genOrigin_append (count := count)) _ _ _ _ ((nvGen_prefix_replay_fresh (count
        := count))
        steps).1 ih ((nvGen_timeBatch_origin (count := count)) _ _)

theorem nvGen_genEmits_runData (h : Time) (es : List (Event (count := count))) (v : (Validator
  (count
  := count))) (o : Obj (params (count := count))) (t : Time)
    (he : (GenEmits (count := count)) V2.D.World.init es v o t) : V2.D.Run.emits (weakEnv (count
      := count)) ((runData (count := count)) h es) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := he
  have hi : ((runData (count := count)) h (pre ++ .tick v t :: post)).events[pre.length]? =
      some (.tick v t) := by simp [runData]
  refine ⟨pre.length, hi, ?_⟩
  rw [V2.D.Run.emitsAt, hi]
  simp only [V2.D.Run.stateBefore, runData, List.take_left']
  exact ho

theorem nvGen_gen_tick_holder (st : Node (params (count := count))) (v : (Validator (count :=
  count)))
  (t : Time) (o : Obj (params (count := count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2) :
    V2.D.Run.holder ((runData (count := count)) 263 []) o.auth = some v := by
  change o ∈ (if (weakEnv (count := count)).awake v t then
    (duties (params (count := count)) t).flatMap (fun l =>
      (((runData (count := count)) 263 []).ownSeats (RunDuty.signLabel l) v).filterMap (fun i =>
        ((fgsa (params (count := count)) unitCodec).act ((fgsa (params (count := count))
          unitCodec).clock st t) l ()).map
          (fun m => ⟨.seat (RunDuty.signLabel l) i, m⟩))) ++ [] else []) at ho
  split at ho
  · rw [List.append_nil] at ho
    obtain ⟨l, _, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨i, hi, hm⟩ := List.mem_filterMap.mp ho
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.mp hm
    have hseat : (seatOf (count := count)) (RunDuty.signLabel l) i = v
      := (List.mem_filter.mp hi).2 |> of_decide_eq_true
    exact congrArg some hseat
  · exact (List.not_mem_nil ho).elim

theorem nvGen_genOrigin_unforgeable (h : Time) (es : List (Event (count := count))) (horigin :
  (GenOrigin (count := count)) V2.D.World.init es)
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (hp : V2.D.Run.processes ((runData (count := count)) h es) v o t) (u : (Validator (count :=
      count)))
    (hu : V2.D.Run.holder ((runData (count := count)) h es) o.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits (weakEnv (count := count)) ((runData (count := count)) h es) u
      o t' := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨x, hx⟩ := horigin v o t (List.mem_of_getElem? hi)
  have hemit := (nvGen_genEmits_runData (count := count)) h es x o t hx
  obtain ⟨pre, post, _, ho⟩ := hx
  have hholder := (nvGen_gen_tick_holder (count := count)) ((genFold (count := count))
    V2.D.World.init
    pre x) x t o ho
  have hux : u = x := Option.some.inj (hu.symm.trans hholder)
  exact ⟨t, le_rfl, hux.symm ▸ hemit⟩

theorem nvGen_tick_nodup_without_gossip {In V : Type} [DecidableEq V]
    (P : V2.ProtocolSpecD In) (E : Generic.Env V) (rho : V2.D.Run V P)
    (st : P.State) (v : V) (t : Time) (hg : P.gossip (P.clock st t) t = [])
    (hD : V2.D.DutiesInjectiveAt P t) :
    (V2.D.tick E rho st v t).2.Nodup := by
  change (if E.awake v t then
    (P.duties t).flatMap (fun l =>
      (rho.ownSeats (P.signLabel l) v).filterMap (fun i =>
        (P.act (P.clock st t) l (rho.input v t)).map
          (fun m => (⟨.seat (P.signLabel l) i, m⟩ : P.Object)))) ++
        (P.gossip (P.clock st t) t).map (fun m => ⟨.none, m⟩) else []).Nodup
  rw [hg, List.map_nil]
  split
  · rw [List.append_nil, List.nodup_flatMap]
    constructor
    · intro l _
      apply List.Nodup.filterMap
      · intro i j o hi hj
        obtain ⟨m, _, hm⟩ := Option.map_eq_some_iff.mp hi
        obtain ⟨m', _, hm'⟩ := Option.map_eq_some_iff.mp hj
        have he := congrArg V2.Signed.auth (hm.trans hm'.symm)
        cases he
        rfl
      · exact (List.nodup_finRange _).filter _
    · apply List.Pairwise.imp_of_mem _ (P.duties_nodup t)
      intro l l' hl hl' hne o ho ho'
      obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp ho
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp ho'
      obtain ⟨m, _, hm⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨m', _, hm'⟩ := Option.map_eq_some_iff.mp hj
      have he := congrArg V2.Signed.auth (hm.trans hm'.symm)
      exact hne (hD l l' ((P.duties_spec l t).mp hl)
        ((P.duties_spec l' t).mp hl') (V2.Auth.seat.inj he).1)
  · exact List.nodup_nil

theorem nvGen_gen_tick_nodup (st : Node (params (count := count))) (v : (Validator (count :=
  count)))
  (t : Time) :
    (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2.Nodup :=
  nvGen_tick_nodup_without_gossip (fgsa (params (count := count)) unitCodec) (weakEnv (count :=
    count)) ((runData (count := count)) 263 []) st v t rfl
    (fgsa_dutiesInjectiveAt t)

theorem nvGen_tick_fold_nodup (t : Time) (vs : List (Validator (count := count))) (hn : vs.Nodup)
    (w : (World (count := count))) (os : List (Obj (params (count := count)))) (ho : os.Nodup)
    (hh : ∀ o ∈ os, ∀ v ∈ vs, V2.D.Run.holder ((runData (count := count)) 263 []) o.auth ≠ some v) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2.Nodup := by
  induction vs generalizing w os with
  | nil => exact ho
  | cons v vs ih =>
      rw [List.nodup_cons] at hn
      rw [List.foldl_cons]
      apply ih hn.2
      · apply ho.append ((nvGen_gen_tick_nodup (count := count)) (w v) v t)
        intro o hos hot
        exact hh o hos v (List.mem_cons_self ..) ((nvGen_gen_tick_holder (count := count)) (w v)
          v t o
          hot)
      · intro o hom u hum
        rcases List.mem_append.mp hom with hom | hom
        · exact hh o hom u (List.mem_cons_of_mem _ hum)
        · rw [nvGen_gen_tick_holder (w v) v t o hom]
          intro he
          exact hn.1 (Option.some.inj he ▸ hum)

theorem nvGen_tickBatch_nodup (t : Time) (w : (World (count := count))) : ((tickBatch (count :=
  count)) t w).2.Nodup :=
  (nvGen_tick_fold_nodup (count := count)) t (nodes (count := count)) (nvGen_nodes_nodup (count
    := count)) w
    [] List.nodup_nil (by simp)

theorem nvGen_timeBatch_nodup (t : Time) (w : (World (count := count))) : ((timeBatch (count :=
  count)) t w).2.Nodup := by
  obtain ⟨ds, he, hs⟩ := (nvGen_timeBatch_block (count := count)) t w
  rw [he]
  apply List.Nodup.append
  · exact (show (nodes (count := count)).Nodup from (nvGen_nodes_nodup (count := count))).map (by
    intro v u h; cases h; rfl)
  · apply List.Nodup.sublist hs
    change (((tickBatch (count := count)) t w).2.flatMap (fun (o : Obj (params (count := count))) =>
      (nodes (count := count)).map (fun v => (V2.Event.deliver v o t : V2.Event (Validator
        (count := count)) (Obj (params (count := count))))))).Nodup
    rw [List.nodup_flatMap]
    constructor
    · intro o _
      exact (show (nodes (count := count)).Nodup from (nvGen_nodes_nodup (count := count))).map (by
        intro v u h; cases h; rfl)
    · apply ((nvGen_tickBatch_nodup (count := count)) t w).imp
      intro o o' hne e he he'
      obtain ⟨v, _, hv⟩ := List.mem_map.mp he
      obtain ⟨u, _, hu⟩ := List.mem_map.mp he'
      exact hne (V2.Event.deliver.inj (hv.trans hu.symm)).2.1
  · intro e he hd
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp (hs.subset hd)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp ho
    cases hu

theorem nvGen_prefix_nodup (steps : Nat) : ((buildPrefix (count := count)) steps).2.Nodup := by
  induction steps with
  | zero => exact List.nodup_nil
  | succ steps ih =>
      apply ih.append ((nvGen_timeBatch_nodup (count := count)) _ _)
      intro e he hb
      have hlt := ((nvGen_witness_prefix_times (count := count)) steps e he).2
      rw [nvGen_timeBatch_time _ _ _ hb] at hlt
      exact (lt_irrefl _ hlt)

theorem nvGen_runData_stateBefore (h : Time) (es : List (Event (count := count))) (i : Nat) :
    V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count := count)) h es) i =
      (genFold (count := count)) V2.D.World.init (es.take i) := rfl

theorem nvGen_gen_derive_positive (B : FGBlock (Fin (params (count := count)).n)) :
    1 ≤ (heightView (params (count := count)) B).h :=
  (Window.windowHeightLaws (params (count := count)) (params (count := count)).K_W (params
    (count := count)).kWLarge).one_le_h B

theorem nvGen_gen_attest_valid (st : State (params (count := count)).n) (record : RecordOnce)
    (i : Fin (params (count := count)).n) (body : RowPayload)
    (hbody : (attest (params (count := count)) st record i).1 = some body) : body.valid = true := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨h, T, timeout, hh, he, _, _, _⟩ :=
    KitFG.createRowOnce_released (params (count := count)).E (params (count := count)).cfg record i
      (fgInputs (params (count := count)) st).1 (fgInputs (params (count := count)) st).2 ha
  have hf := KitFG.height_pair_vote_fields hh
  obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
  have heh : (heightView (params (count := count)) C).h = h := by
    rw [heightView_bridge]
    exact congrArg Prod.fst hc
  have hpos : 1 ≤ h := heh ▸ (nvGen_gen_derive_positive (count := count)) C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair record.toRecord (fgInputs (params (count := count)) st).2).filter
      (fun fp => decide (fp.height < h)) |>.map (fun fp => decide (fp.height < h))).getD true)
        = true
  cases hfp : finality_pair record.toRecord (fgInputs (params (count := count)) st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

theorem nvGen_gen_tick_seat (st : Node (params (count := count))) (v : (Validator (count := count)))
  (t : Time) (o : Obj (params (count := count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2) :
    ∃ l i m, o = ⟨.seat (RunDuty.signLabel l) i, m⟩ ∧ l ∈ duties (params (count := count)) t ∧
      (fgsa (params (count := count)) unitCodec).act ((fgsa (params (count := count))
        unitCodec).clock st t) l () = some m := by
  change o ∈ (if (weakEnv (count := count)).awake v t then
    (duties (params (count := count)) t).flatMap (fun l =>
      (((runData (count := count)) 263 []).ownSeats (RunDuty.signLabel l) v).filterMap (fun i =>
        ((fgsa (params (count := count)) unitCodec).act ((fgsa (params (count := count))
          unitCodec).clock st t) l ()).map
          (fun m => ⟨.seat (RunDuty.signLabel l) i, m⟩))) ++ [] else []) at ho
  split at ho
  · rw [List.append_nil] at ho
    obtain ⟨l, hl, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp ho
    obtain ⟨m, ha, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨l, i, m, rfl, hl, ha⟩
  · exact (List.not_mem_nil ho).elim

theorem nvGen_gen_tick_nonproposal_wire (st : Node (params (count := count))) (v : (Validator (count
  := count))) (t : Time) (o : Obj (params (count := count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2)
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa (params (count := count)) unitCodec).wellFormed o = true := by
  obtain ⟨l, i, m, rfl, _, ha⟩ := (nvGen_gen_tick_seat (count := count)) st v t o ho
  cases l with
  | headAction s =>
      have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
      have he : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
        st.st t) s).root = m := Option.some.inj ha
      subst m
      rfl
  | fgAction r =>
      change (attest (params (count := count)) (FGSA.clock (params (count := count)) st.st t)
        st.record
        ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact (nvGen_gen_attest_valid (count := count)) _ _ _ _ hb
  | propAction s =>
      have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
      change (propose (params (count := count)) (FGSA.clock (params (count := count)) st.st t)
        s).map
        (withApp (params (count := count)) 0) = some m at ha
      unfold propose at ha
      split at ha
      · cases ha
      · simp only [Option.map_map] at ha
        obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
        exact (hn _ rfl).elim

theorem nvGen_i7_admitRow_duplicate (st : State (params (count := count)).n) (i : Fin (params (count
  := count)).n)
    (body : RowPayload)
    (h : (⟨.seat .fg i, body⟩ : RowWire (params (count := count)).n) ∈ st.rowPool) :
    admitRow (params (count := count)) st ⟨.seat .fg i, body⟩ = st := by
  simp [admitRow, RowWire.decode?, h]

theorem nvGen_i7_clock_fields (st : State (params (count := count)).n) (t : Time) :
    (FGSA.clock (params (count := count)) st t).proposals = st.proposals ∧
      (FGSA.clock (params (count := count)) st t).rowPool = st.rowPool := by
  have hn (st : State (params (count := count)).n) : (normalizeS st).proposals = st.proposals ∧
      (normalizeS st).rowPool = st.rowPool := by
    unfold normalizeS
    split <;> exact ⟨rfl, rfl⟩
  have hg (st : State (params (count := count)).n) (s : Slot) :
      (gateStep (params (count := count)) st s).proposals = st.proposals ∧
        (gateStep (params (count := count)) st s).rowPool = st.rowPool := by
    unfold gateStep
    rw [(hn _).1, (hn _).2]
    split <;> (try split) <;> exact ⟨rfl, rfl⟩
  have hc : (clockPre (params (count := count)) st t).proposals = st.proposals ∧
      (clockPre (params (count := count)) st t).rowPool = st.rowPool := by
    unfold clockPre
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl⟩
  unfold FGSA.clock
  dsimp only
  split
  · rw [(hg _ _).1, (hg _ _).2]
    exact hc
  · exact hc

theorem nvGen_i7_clock_proposals (st : State (params (count := count)).n) (t : Time) :
    (FGSA.clock (params (count := count)) st t).proposals = st.proposals := ((nvGen_i7_clock_fields
      (count := count)) st t).1

theorem nvGen_i7_clock_rowPool (st : State (params (count := count)).n) (t : Time) :
    (FGSA.clock (params (count := count)) st t).rowPool = st.rowPool := ((nvGen_i7_clock_fields
      (count
      := count)) st t).2

theorem nvGen_i7_reconcile_fields (st : State (params (count := count)).n) :
    (reconcile st).proposals = st.proposals ∧ (reconcile st).rowPool = st.rowPool := by
  unfold reconcile normalizeS
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem nvGen_i7_admitRow_eq (st : State (params (count := count)).n) (a : RowWire (params (count :=
  count)).n) :
    admitRow (params (count := count)) st a = st ∨
      admitRow (params (count := count)) st a = { st with rowPool := st.rowPool ++ [a] } := by
  unfold admitRow
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem nvGen_i7_tick_st (st : Node (params (count := count))) (v : (Validator (count :=
  count))) (t :
  Time) :
    (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).1.st =
      FGSA.clock (params (count := count)) st.st t := by
  have hf (os : List (Obj (params (count := count)))) (nd : Node (params (count := count))) :
      (os.foldl (fgsa (params (count := count)) unitCodec).recordOwn nd).st = nd.st := by
    induction os generalizing nd with
    | nil => rfl
    | cons o os ih => exact ih _
  exact hf _ _

def GenStoredRows (P : RowWire (params (count := count)).n → Prop) (st : State (params (count :=
  count)).n) : Prop :=
  ∀ w ∈ st.proposals, ∀ s b,
    w.decode = some (.block s b) → ∀ a ∈ b.rows, P a

theorem nvGen_gen_proposalRows_origin (P : RowWire (params (count := count)).n → Prop) (st : State
  (params (count := count)).n)
    (H : Block) (hp : ∀ a ∈ st.rowPool, P a) (hs : (GenStoredRows (count := count)) P st) :
    ∀ a ∈ proposalRows (params (count := count)) st H, P a := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin (params (count := count)) st (st.slot (params (count := count)))
    H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hp a hm
  · exact hs o ho s b hd a hm

theorem nvGen_gen_tick_proposal_rows (st : Node (params (count := count))) (v : (Validator (count :=
  count))) (t : Time)
    (o : Obj (params (count := count))) (ho : o ∈ (V2.D.tick (weakEnv (count := count))
      ((runData (count := count)) 263 []) st v t).2)
    (b : NamedProposal (params (count := count)).n)
    (he : o.payload = .proposal b) :
    v = 0 ∧ ∃ H, b.rows = proposalRows (params (count := count)) (FGSA.clock (params (count :=
      count)) st.st t) H := by
  have hh := (nvGen_gen_tick_holder (count := count)) st v t o ho
  obtain ⟨l, i, m, rfl, _, ha⟩ := (nvGen_gen_tick_seat (count := count)) st v t o ho
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have hm : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
      st.st t) s).root = m := Option.some.inj ha
    subst m
    cases he
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count)) st.st t)
      st.record
      ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases he
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    have hv : v = 0 := (Option.some.inj hh).symm
    change (propose (params (count := count)) (FGSA.clock (params (count := count)) st.st t) s).map
        (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      cases he
      exact ⟨hv, _, rfl⟩

theorem nvGen_i7_clock_votes (st : State (params (count := count)).n) (t : Time) :
    (FGSA.clock (params (count := count)) st t).base.votes = st.base.votes := by
  have hw (st : GridCO.State (params (count := count)).n .root) (b : Block) (g : Nat) (d : Time) :
      (GridCO.writeObligation st b g d).votes = st.votes := by
    rfl
  have hfold (xs : List Block) (levels : Block → List Nat) (d : Time)
      (st : GridCO.State (params (count := count)).n .root) :
      (xs.foldl (fun acc b => (levels b).foldl
        (fun acc g => GridCO.writeObligation acc b g d) acc) st).votes = st.votes := by
    have inner (gs : List Nat) (b : Block) (st : GridCO.State (params (count := count)).n .root) :
        (gs.foldl (fun acc g => GridCO.writeObligation acc b g d) st).votes = st.votes := by
      induction gs generalizing st with
      | nil => rfl
      | cons g gs ih => exact (ih _).trans (hw st b g d)
    induction xs generalizing st with
    | nil => rfl
    | cons b xs ih => exact (ih _).trans (inner _ b st)
  have hg (st : GridCO.State (params (count := count)).n .root) (a : Block) (s : Slot) :
      (SA.Root.gateFrom (params (count := count)).toParams a st s).votes = st.votes := by
    unfold SA.Root.gateFrom GridCO.gateFrom
    split
    · rfl
    · dsimp only
      split
      · rfl
      · exact hfold _ _ _ _
  have hn (st : State (params (count := count)).n) : (normalizeS st).base.votes = st.base.votes
    := by
    unfold normalizeS
    split <;> rfl
  have hgate (st : State (params (count := count)).n) (s : Slot) :
      (gateStep (params (count := count)) st s).base.votes = st.base.votes := by
    unfold gateStep
    rw [hn]
    split
    · rfl
    · split
      · rfl
      · exact hg _ _ _
  have hc : (clockPre (params (count := count)) st t).base.votes = st.base.votes := by
    unfold clockPre
    dsimp only
    split_ifs <;> rfl
  unfold FGSA.clock
  dsimp only
  split
  · rw [hgate]; exact hc
  · exact hc

def GenKnown (P : Obj (params (count := count)) → Prop) (st : State (params (count := count)).n)
  : Prop :=
  (∀ a ∈ st.rowPool, P (ofRow (params (count := count)) a)) ∧
    (GenStoredRows (count := count)) (fun a => P (ofRow (params (count := count)) a)) st ∧
    ∀ h ∈ st.base.votes.filterMap liftHead?, P (ofHead (params (count := count)) h)

theorem nvGen_gen_known_mono (P Q : Obj (params (count := count)) → Prop) (st : State (params (count
  := count)).n)
    (h : (GenKnown (count := count)) P st) (hp : ∀ o, P o → Q o) : (GenKnown (count := count)) Q
      st :=
  ⟨fun a ha => hp _ (h.1 a ha),
    fun w hw s b hd a ha => hp _ (h.2.1 w hw s b hd a ha),
    fun a ha => hp _ (h.2.2 a ha)⟩

theorem nvGen_gen_known_clock (P : Obj (params (count := count)) → Prop) (st : State (params
  (count :=
  count)).n) (t : Time)
    (h : (GenKnown (count := count)) P st) : (GenKnown (count := count)) P (FGSA.clock (params
      (count := count)) st t) := by
  simpa only [GenKnown, GenStoredRows, nvGen_i7_clock_proposals, nvGen_i7_clock_rowPool,
    nvGen_i7_clock_votes] using h

theorem nvGen_gen_known_row (P : Obj (params (count := count)) → Prop) (st : State (params (count :=
  count)).n)
    (a : RowWire (params (count := count)).n) (h : (GenKnown (count := count)) P st) (ha : P
      (ofRow (params (count := count)) a)) :
    (GenKnown (count := count)) P (admitRow (params (count := count)) st a) := by
  rcases (nvGen_i7_admitRow_eq (count := count)) st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

theorem nvGen_gen_known_rows (P : Obj (params (count := count)) → Prop) (rows : List (RowWire
  (params
  (count := count)).n))
    (st : State (params (count := count)).n) (h : (GenKnown (count := count)) P st) (hr : ∀ a ∈
      rows, P (ofRow (params (count := count)) a)) :
    (GenKnown (count := count)) P (rows.foldl (admitRow (params (count := count))) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ ((nvGen_gen_known_row (count := count)) P st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem nvGen_gen_known_vote (P : Obj (params (count := count)) → Prop) (st : GridCO.State (params
  (count := count)).n .root)
    (o : GridCO.Wire (params (count := count)).n .root)
    (h : ∀ a ∈ st.votes.filterMap liftHead?, P (ofHead (params (count := count)) a))
    (ho : ∀ a, liftHead? o = some a → P (ofHead (params (count := count)) a)) :
    ∀ a ∈ (GridCO.admitVote (params (count := count)).toParams.engine st o).votes.filterMap
      liftHead?,
      P (ofHead (params (count := count)) a) := by
  unfold GridCO.admitVote
  split
  · dsimp only
    split
    · exact h
    · intro a ha
      obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
      rcases List.mem_append.mp hw with hw | hw
      · exact h a (List.mem_filterMap.mpr ⟨w, hw, he⟩)
      · exact ho a (List.mem_singleton.mp hw ▸ he)
  · exact h

theorem nvGen_i7_lift_baseVote (a h : HeadWire (params (count := count)).n) (he : liftHead?
  (baseVote
  a) = some h) :
    a = h := by
  obtain ⟨auth, b⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    simp [baseVote, baseHead, HeadWire.decode?, GridCO.fromHead, liftHead?,
      GridCO.headLabel?, GridCO.headSeat?, GridCO.headTarget?] at he
  exact he

theorem nvGen_gen_known_base_proposal (P : Obj (params (count := count)) → Prop) (st : GridCO.State
  (params (count := count)).n .root)
    (s : Slot) (b : Block) (raw sup : List (HeadWire (params (count := count)).n))
    (h : ∀ a ∈ st.votes.filterMap liftHead?, P (ofHead (params (count := count)) a))
    (hr : ∀ a ∈ raw, P (ofHead (params (count := count)) a)) :
    ∀ a ∈ (GridCO.admitProposal (params (count := count)).toParams.engine st (baseProposal s b
      raw sup)
      b (raw.map baseHead)).votes.filterMap liftHead?, P (ofHead (params (count := count)) a) := by
  have hf (xs : List (HeadWire (params (count := count)).n)) (st : GridCO.State (params (count
    := count)).n .root)
      (hs : ∀ a ∈ st.votes.filterMap liftHead?, P (ofHead (params (count := count)) a))
      (hx : ∀ a ∈ xs, P (ofHead (params (count := count)) a)) :
      ∀ a ∈ ((xs.map baseHead).foldl (fun acc row =>
        GridCO.admitVote (params (count := count)).toParams.engine acc (GridCO.fromHead row))
          st).votes.filterMap
          liftHead?, P (ofHead (params (count := count)) a) := by
    induction xs generalizing st with
    | nil => exact hs
    | cons a xs ih =>
      apply ih _ ((nvGen_gen_known_vote (count := count)) P st (baseVote a) hs ?_)
      · exact fun a ha => hx a (List.mem_cons_of_mem _ ha)
      · intro h he
        exact (nvGen_i7_lift_baseVote (count := count)) a h he ▸ hx a (List.mem_cons_self ..)
  unfold GridCO.admitProposal baseProposal
  dsimp only
  split
  · exact h
  · exact hf raw _ h hr

theorem nvGen_i7_decode_vote (o : Obj (params (count := count))) (s : Slot) (i : Fin (params
  (count :=
  count)).n) (b : BlockId)
    (h : (toWire (params (count := count)) o).decode = some (.vote s i b)) :
    o = ⟨.seat (.base (.head s)) i, .head b⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | prop r => cases payload <;> cases h
    | base l => cases l <;> cases payload <;> cases h; rfl

theorem nvGen_i7_decode_row (o : Obj (params (count := count))) (i : Fin (params (count :=
  count)).n)
  (body : RowPayload)
    (h : (toWire (params (count := count)) o).decode = some (.row i body)) :
    o = ⟨.seat (.base .fg) i, .row body⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | prop s => cases payload <;> cases h
    | base l => cases l <;> cases payload <;> cases h; rfl

theorem nvGen_i7_decode_proposal (o : Obj (params (count := count))) (s : Slot) (b : NamedProposal
  (params (count := count)).n)
    (h : (toWire (params (count := count)) o).decode = some (.block s b)) :
    o.payload = .proposal b := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | base l => cases l <;> cases payload <;> cases h
    | prop r => cases payload <;> cases h; rfl

theorem nvGen_gen_known_reconcile (P : Obj (params (count := count)) → Prop) (st : State (params
  (count := count)).n)
    (h : (GenKnown (count := count)) P st) : (GenKnown (count := count)) P (reconcile st) := by
  unfold reconcile normalizeS
  dsimp only
  split <;> exact h

theorem nvGen_gen_known_process (P : Obj (params (count := count)) → Prop) (st : State (params
  (count
  := count)).n) (o : Obj (params (count := count)))
    (h : (GenKnown (count := count)) P st) (ho : P o)
    (hc : ∀ o', carriesS (params (count := count)) o o' → P o') :
    (GenKnown (count := count)) P (FGSA.process (params (count := count)) st (toWire (params
      (count := count)) o)) := by
  unfold FGSA.process
  cases hd : (toWire (params (count := count)) o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b =>
      dsimp only
      obtain rfl := (nvGen_i7_decode_vote (count := count)) o s i b hd
      refine ⟨h.1, h.2.1, ?_⟩
      apply (nvGen_gen_known_vote (count := count)) P st.base _ h.2.2
      intro a he
      have he' : (⟨.seat (.head s) i, b⟩ : HeadWire (params (count := count)).n) = a :=
        Option.some.inj he
      exact he' ▸ ho
    | row i body =>
      dsimp only
      obtain rfl := (nvGen_i7_decode_row (count := count)) o i body hd
      exact (nvGen_gen_known_row (count := count)) P st _ h ho
    | block s b =>
      dsimp only
      have he := (nvGen_i7_decode_proposal (count := count)) o s b hd
      have hr : ∀ a ∈ b.rows, P (ofRow (params (count := count)) a) := by
        intro a ha
        apply hc
        simp only [carriesS, he]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
      have hv : ∀ a ∈ b.raw, P (ofHead (params (count := count)) a) := by
        intro a ha
        apply hc
        simp only [carriesS, he]
        exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)
      unfold admitBlock
      split
      · exact h
      · split
        · exact h
        · rename_i parent hparent
          split
          · apply (nvGen_gen_known_rows (count := count)) _ _ _ _ hr
            have hs : (GenKnown (count := count)) P
                { st with
                  base := GridCO.admitProposal (params (count := count)).toParams.engine st.base
                    (baseProposal s b.erase b.raw b.support) b.erase (b.raw.map baseHead)
                  fg := Window.on_block (params (count := count)) (params (count := count)).K_W
                    st.fg (fgBlock parent b.erase b.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal b⟩] } := by
              refine ⟨h.1, ?_, (nvGen_gen_known_base_proposal (count := count)) P st.base s b.erase
                b.raw b.support h.2.2 hv⟩
              intro w hw s' b' hd' a ha
              rcases List.mem_append.mp hw with hw | hw
              · exact h.2.1 w hw s' b' hd' a ha
              · have he := List.mem_singleton.mp hw
                subst w
                cases hd'
                exact hr a ha
            split
            · exact hs
            · exact (nvGen_gen_known_reconcile (count := count)) P _ hs
          · exact h

theorem nvGen_gen_tick_children_known (P : Obj (params (count := count)) → Prop) (st : Node (params
  (count := count)))
    (v : (Validator (count := count))) (t : Time) (o : Obj (params (count := count))) (h :
      (GenKnown (count := count)) P st.st)
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2) :
    ∀ o', carriesS (params (count := count)) o o' → P o' := by
  have hs := (nvGen_gen_known_clock (count := count)) P st.st t h
  obtain ⟨l, i, m, rfl, _, ha⟩ := (nvGen_gen_tick_seat (count := count)) st v t o ho
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have hm : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
      st.st t) s).root = m := Option.some.inj ha
    subst m
    exact fun _ h => h.elim
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count)) st.st t)
      st.record
      ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact fun _ h => h.elim
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    change (propose (params (count := count)) (FGSA.clock (params (count := count)) st.st t) s).map
        (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      have hv (a : HeadWire (params (count := count)).n)
          (hm : a ∈ (proposerVotes (FGSA.clock (params (count := count)) st.st t) s).filterMap
            liftHead?) :
          P (ofHead (params (count := count)) a) := by
        obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp hm
        exact hs.2.2 a (List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩)
      intro o' hc
      rcases hc with hm | hm | hm
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact hv a ha
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
        exact hv a (List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact (nvGen_gen_proposalRows_origin (count := count)) _ _ _ hs.1 hs.2.1 a ha

theorem nvGen_gen_tick_fold_known (P : Obj (params (count := count)) → Prop) (t : Time) (vs : List
  (Validator (count := count)))
    (w : (World (count := count))) (os : List (Obj (params (count := count)))) (hw : ∀ v,
      (GenKnown (count := count)) P (w v).st)
    (ho : ∀ o ∈ os, ∀ o', carriesS (params (count := count)) o o' → P o') :
    let result := vs.foldl (fun acc v =>
      let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)
    (∀ v, (GenKnown (count := count)) P (result.1 v).st) ∧
      ∀ o ∈ result.2, ∀ o', carriesS (params (count := count)) o o' → P o' := by
  induction vs generalizing w os with
  | nil => exact ⟨hw, ho⟩
  | cons v vs ih =>
    apply ih
    · intro u
      by_cases he : u = v
      · subst u
        rw [Function.update_self]
        exact ((nvGen_i7_tick_st (count := count)) (w v) v t).symm ▸ (nvGen_gen_known_clock
          (count :=
          count)) P (w v).st t (hw v)
      · rw [Function.update_of_ne he]
        exact hw u
    · intro o hm o' hc
      rcases List.mem_append.mp hm with hm | hm
      · exact ho o hm o' hc
      · exact (nvGen_gen_tick_children_known (count := count)) P (w v) v t o (hw v) hm o' hc

theorem nvGen_gen_delivery_fold_known (P : Obj (params (count := count)) → Prop) (t : Time)
    (xs : List ((Validator (count := count)) × Obj (params (count := count)))) (acc : (World
      (count := count)) × List (Event (count := count)))
    (hw : ∀ v, (GenKnown (count := count)) P (acc.1 v).st)
    (ho : ∀ vo ∈ xs, P vo.2 ∧ ∀ o', carriesS (params (count := count)) vo.2 o' → P o') :
    ∀ v, (GenKnown (count := count)) P ((xs.foldl ((deliverOne (count := count)) t) acc).1 v).st
      := by
  induction xs generalizing acc with
  | nil => exact hw
  | cons vo xs ih =>
    apply ih
    · unfold deliverOne
      split
      · exact hw
      · intro v
        dsimp only
        by_cases hv : v = vo.1
        · subst v
          simp only [V2.D.World.step, Function.update_self]
          exact (nvGen_gen_known_process (count := count)) P _ vo.2 (hw vo.1)
            (ho vo (List.mem_cons_self ..)).1 (ho vo (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hv] using hw v
    · exact fun vo hv => ho vo (List.mem_cons_of_mem _ hv)

theorem nvGen_gen_timeBatch_known (P : Obj (params (count := count)) → Prop) (t : Time) (w : (World
  (count := count)))
    (hw : ∀ v, (GenKnown (count := count)) P (w v).st) (ho : ∀ o ∈ ((tickBatch (count := count))
      t w).2, P o) :
    ∀ v, (GenKnown (count := count)) P (((timeBatch (count := count)) t w).1 v).st := by
  obtain ⟨ht, hc⟩ := (nvGen_gen_tick_fold_known (count := count)) P t (nodes (count := count)) w
    [] hw
    (by simp)
  apply (nvGen_gen_delivery_fold_known (count := count)) P t _ _ ht
  intro vo hv
  obtain ⟨o, hm, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
  subst vo
  exact ⟨ho o hm, hc o hm⟩

theorem nvGen_gen_timeBatch_delivered (t : Time) (w : (World (count := count))) (v : (Validator
  (count
  := count)))
    (o : Obj (params (count := count))) (s : Time) (hm : V2.Event.deliver v o s ∈ ((timeBatch
      (count := count)) t w).2) :
    s = t ∧ o ∈ ((tickBatch (count := count)) t w).2 := by
  obtain ⟨ds, he, hs⟩ := (nvGen_timeBatch_block (count := count)) t w
  rw [he] at hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    cases hu
  · obtain ⟨o', ho, hv⟩ := List.mem_flatMap.mp (hs.subset hm)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
    cases hu
    exact ⟨rfl, ho⟩

def GenPast (es : List (Event (count := count))) (t : Time) (o : Obj (params (count := count)))
  : Prop :=
  ∃ v s, s ≤ t ∧ (GenEmits (count := count)) V2.D.World.init es v o s

def GenCarried (es : List (Event (count := count))) : Prop :=
  ∀ v o t, V2.Event.deliver v o t ∈ es →
    ∀ o', carriesS (params (count := count)) o o' → (GenPast (count := count)) es t o'

theorem nvGen_gen_past_append (es ds : List (Event (count := count))) (t : Time) (o : Obj (params
  (count := count)))
    (h : (GenPast (count := count)) es t o) : (GenPast (count := count)) (es ++ ds) t o := by
  obtain ⟨v, s, ht, he⟩ := h
  exact ⟨v, s, ht, (nvGen_genEmits_append_left (count := count)) _ es ds v o s he⟩

theorem nvGen_gen_past_bound (es : List (Event (count := count))) (t u : Time) (o : Obj (params
  (count
  := count)))
    (h : (GenPast (count := count)) es t o) (htu : t ≤ u) : (GenPast (count := count)) es u o := by
  obtain ⟨v, s, ht, he⟩ := h
  exact ⟨v, s, ht.trans htu, he⟩

theorem nvGen_gen_batch_carried (es : List (Event (count := count))) (t : Time) (w : (World
  (count :=
  count)))
    (he : w = (genFold (count := count)) V2.D.World.init es)
    (hw : ∀ v, (GenKnown (count := count)) ((GenPast (count := count)) es t) (w v).st) (hc :
      (GenCarried (count := count)) es) :
    (∀ v, (GenKnown (count := count)) ((GenPast (count := count)) (es ++ ((timeBatch (count :=
      count)) t w).2) (t + 1))
      (((timeBatch (count := count)) t w).1 v).st) ∧ (GenCarried (count := count)) (es ++
        ((timeBatch (count := count)) t w).2) := by
  have hp (o : Obj (params (count := count))) (ho : (GenPast (count := count)) es t o) :
      (GenPast (count := count)) (es ++ ((timeBatch (count := count)) t w).2) (t + 1) o :=
    (nvGen_gen_past_bound (count := count)) _ t (t + 1) o ((nvGen_gen_past_append (count :=
      count)) es _ t o
      ho) (le_add_of_nonneg_right (by decide))
  constructor
  · apply (nvGen_gen_timeBatch_known (count := count)) ((GenPast (count := count)) (es ++
      ((timeBatch
    (count := count)) t w).2) (t + 1)) t w
    · exact fun v => (nvGen_gen_known_mono (count := count)) _ _ _ (hw v) hp
    · intro o ho
      obtain ⟨u, hu⟩ := (nvGen_tickBatch_origin (count := count)) t w o ho
      obtain ⟨ds, hd, _⟩ := (nvGen_timeBatch_block (count := count)) t w
      have hu' : (GenEmits (count := count)) w ((timeBatch (count := count)) t w).2 u o t := by
        rw [hd]
        exact (nvGen_genEmits_append_left (count := count)) w _ ds u o t hu
      refine ⟨u, t, le_add_of_nonneg_right (by decide), ?_⟩
      apply (nvGen_genEmits_append_right (count := count)) V2.D.World.init es _ u o t
      rw [← he]
      exact hu'
  · intro v o s hm o' hcarry
    rcases List.mem_append.mp hm with hm | hm
    · exact (nvGen_gen_past_append (count := count)) es _ s o' (hc v o s hm o' hcarry)
    · obtain ⟨hs, ho⟩ := (nvGen_gen_timeBatch_delivered (count := count)) t w v o s hm
      subst s
      have hk := ((nvGen_gen_tick_fold_known (count := count)) ((GenPast (count := count)) es t) t
        (nodes (count := count)) w [] hw (by simp)).2
      exact (nvGen_gen_past_append (count := count)) es _ t o' (hk o ho o' hcarry)

theorem nvGen_gen_prefix_carried (steps : Nat) :
    (∀ v, (GenKnown (count := count)) ((GenPast (count := count)) ((buildPrefix (count :=
      count)) steps).2 steps) (((buildPrefix (count := count)) steps).1 v).st) ∧
      (GenCarried (count := count)) ((buildPrefix (count := count)) steps).2 := by
  induction steps with
  | zero =>
    constructor
    · intro v
      exact ⟨by simp [buildPrefix, V2.D.World.init, fgsa, initial],
        by intro w hw; exact (List.not_mem_nil hw).elim,
        by simp [buildPrefix, V2.D.World.init, fgsa, initial, GridCO.initial]⟩
    · intro v o t hm; exact (List.not_mem_nil hm).elim
  | succ steps ih =>
    simpa only [buildPrefix, Nat.cast_add, Nat.cast_one] using
      (nvGen_gen_batch_carried (count := count)) ((buildPrefix (count := count)) steps).2 steps
        ((buildPrefix (count := count)) steps).1
        ((nvGen_prefix_replay_fresh (count := count)) steps).1 ih.1 ih.2

theorem nvGen_genCarried_runData (h : Time) (es : List (Event (count := count))) (hc : (GenCarried
  (count := count)) es)
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (hp : V2.D.Run.processes ((runData (count := count)) h es) v o t)
    (o' : Obj (params (count := count))) (hcarry : (fgsa (params (count := count))
      unitCodec).carries o o') (u : (Validator (count := count)))
    (hh : V2.D.Run.holder ((runData (count := count)) h es) o'.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits (weakEnv (count := count)) ((runData (count := count)) h es) u
      o' t' := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨x, s, ht, he⟩ := hc v o t (List.mem_of_getElem? hi) o' hcarry
  have hem := (nvGen_genEmits_runData (count := count)) h es x o' s he
  obtain ⟨pre, post, _, ho⟩ := he
  have hh' := (nvGen_gen_tick_holder (count := count)) ((genFold (count := count))
    V2.D.World.init pre
    x) x s o' ho
  have hu : u = x := Option.some.inj (hh.symm.trans hh')
  exact ⟨s, ht, hu.symm ▸ hem⟩

theorem nvGen_gen_past_row_valid (es : List (Event (count := count))) (t : Time) (a : RowWire
  (params
  (count := count)).n)
    (h : (GenPast (count := count)) es t (ofRow (params (count := count)) a)) : a.valid = true := by
  obtain ⟨v, s, _, pre, post, _, ho⟩ := h
  have hw := (nvGen_gen_tick_nonproposal_wire (count := count)) ((genFold (count := count))
    V2.D.World.init pre v) v s (ofRow (params (count := count)) a) ho
    (by intro b; cases a with | mk auth body => cases auth <;> simp [ofRow,
      ofWire])
  obtain ⟨auth, body⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    simp [fgsa, FGSA.wellFormed, toWire, toAuth, ofRow, ofWire, ofAuth, Wire.decode,
      RowWire.valid, RowWire.decode?] at hw ⊢
  exact hw

theorem nvGen_w1_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s b hd a hm

theorem nvGen_w1_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩

theorem nvGen_w1_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp p a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  let raw := (proposerVotes st s).filterMap liftHead?
  let sup := (proposerSupport st s).filterMap liftHead?
  unfold propose at hm
  rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
  simp only [Option.map_map] at hm
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm
  have heP : P.erase = H := (namedByErase?_sound st H P hP).2
  change FGSA.wellFormed p ⟨.proposer s, .proposal (namedProposal p P s a raw sup rows)⟩ = true
  simp only [FGSA.wellFormed, Wire.decode]
  rw [namedProposal_erase, heP]
  simp only [namedProposal, NamedProposal.raw, NamedProposal.support, NamedProposal.rows]
  change (true && (s == s) && decide (H.slot < s) &&
    raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    sup.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
    contentOk p (proposalBlock p H s a raw sup rows) raw sup rows) = true
  obtain ⟨hraw, hsup⟩ := nvGen_w1_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (nvGen_w1_proposal_rows st H hv)
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc := contentOk_proposalBlock p H s a raw sup rows
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

theorem nvGen_w1_known_fold (P : Obj (params (count := count)) → Prop) (w : (World (count :=
  count)))
  (es : List (Event (count := count)))
    (hnr : ∀ v t, V2.Event.restart v t ∉ es)
    (hw : ∀ v, (GenKnown (count := count)) P (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P o ∧ ∀ o', carriesS (params (count := count)) o o' → P o') :
    ∀ v, (GenKnown (count := count)) P ((genFold (count := count)) w es v).st := by
  induction es generalizing w with
  | nil => exact hw
  | cons e es ih =>
    apply ih
    · exact fun v t hm => hnr v t (List.mem_cons_of_mem _ hm)
    · intro u
      cases e with
      | restart v t => exact (hnr v t (List.mem_cons_self ..)).elim
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact ((nvGen_i7_tick_st (count := count)) (w v) v t).symm ▸ (nvGen_gen_known_clock
            (count :=
            count)) P _ t (hw v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (nvGen_gen_known_process (count := count)) P _ o (hw v)
            (he v o t (List.mem_cons_self ..)).1
            (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

theorem nvGen_w1_rows_at_index (h : Time) (es : List (Event (count := count)))
    (ho : (GenOrigin (count := count)) V2.D.World.init es) (hc : (GenCarried (count := count))
      es) (hnr : ∀ v t, V2.Event.restart v t ∉ es) (i : Nat) (v : (Validator (count := count))) :
    EmissionRowsValid (V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count :=
      count)) h es) i v).st := by
  let P := fun o => ∃ t, (GenPast (count := count)) es t o
  have hk : (GenKnown (count := count)) P ((genFold (count := count)) V2.D.World.init (es.take
    i) v).st := by
    apply (nvGen_w1_known_fold (count := count))
    · exact fun v t hm => hnr v t (List.mem_of_mem_take hm)
    · intro u
      exact ⟨by simp [V2.D.World.init, fgsa, initial],
        by simp [GenStoredRows, V2.D.World.init, fgsa, initial],
        by simp [V2.D.World.init, fgsa, initial, GridCO.initial]⟩
    · intro u o t hm
      have hm' := List.mem_of_mem_take hm
      obtain ⟨x, hx⟩ := ho u o t hm'
      exact ⟨⟨t, x, t, le_rfl, hx⟩, fun o' hcarry => ⟨t, hc u o t hm' o' hcarry⟩⟩
  rw [nvGen_runData_stateBefore]
  exact ⟨fun a ha => by
      obtain ⟨t, ht⟩ := hk.1 a ha
      exact (nvGen_gen_past_row_valid (count := count)) es t a ht,
    fun w hw s b hd a ha => by
      obtain ⟨t, ht⟩ := hk.2.1 w hw s b hd a ha
      exact (nvGen_gen_past_row_valid (count := count)) es t a ht⟩

theorem nvGen_w1_emit_wire (h : Time) (es : List (Event (count := count)))
    (hs : V2.D.ScheduleWellFormed (weakEnv (count := count)) ((runData (count := count)) h es))
    (horigin : (GenOrigin (count := count)) V2.D.World.init es) (hcarried : (GenCarried (count
      := count)) es)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es)
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (hem : V2.D.Run.emits (weakEnv (count := count)) ((runData (count := count)) h es) v o t) :
    (fgsa (params (count := count)) unitCodec).wellFormed o = true := by
  obtain ⟨i, hi, ho⟩ := hem
  rw [(V2.D.Run.step_tick_eq weakEnv (runData h es) hi).2] at ho
  obtain ⟨l, j, m, rfl, hl, ha⟩ := (nvGen_gen_tick_seat (count := count))
    (V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count := count)) h es) i v) v t o ho
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have he : .head (headVote (params (count := count))
        (FGSA.clock (params (count := count)) (V2.D.Run.stateBefore (weakEnv (count := count))
          ((runData (count := count)) h es) i v).st t) s).root = m :=
      Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count))
      (V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count := count)) h es) i v).st t)
      (V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count := count)) h es) i
        v).record ⟨0, (params (count := count)).nPos⟩).1.map Msg.row
        = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact (nvGen_gen_attest_valid (count := count)) _ _ _ _ hb
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    have ht : SA.proposalTime (params (count := count)).toParams s = t :=
      ((fgsa (params (count := count)) unitCodec).duties_spec (.propAction s) t).1 hl
    subst t
    have hm : (propose (params (count := count))
        (FGSA.clock (params (count := count)) (V2.D.Run.stateBefore (weakEnv (count := count))
          ((runData (count := count)) h es) i v).st
          (SA.proposalTime (params (count := count)).toParams s)) s).map (withApp (params (count
            := count)) 0) = some m := ha
    have hs0 : 0 < s := by
      by_contra hn
      have he : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      change none = some m at hm
      cases hm
    have hv := (nvGen_w1_rows_at_index (count := count)) h es horigin hcarried hnr i v
    have hv' : EmissionRowsValid
        (FGSA.clock (params (count := count)) (V2.D.Run.stateBefore (weakEnv (count := count))
          ((runData (count := count)) h es) i v).st
          (SA.proposalTime (params (count := count)).toParams s)) := by
      simpa only [EmissionRowsValid, nvGen_i7_clock_rowPool, nvGen_i7_clock_proposals] using hv
    exact nvGen_w1_proposal_wf _ s 0 hv'
      (fgsa_propose_parent_lt (weakEnv (count := count)) ((runData (count := count)) h es) hs hi
        hs0) hm

theorem nvGen_w1_process_inert (st : State (params (count := count)).n) (o : Obj (params (count :=
  count)))
    (hp : processedS (params (count := count)) st o = true) :
    FGSA.process (params (count := count)) st (toWire (params (count := count)) o) = st := by
  unfold processedS at hp
  unfold FGSA.process
  cases hd : (toWire (params (count := count)) o).decode with
  | none => rw [hd] at hp
  | some m =>
    rw [hd] at hp
    cases m with
    | vote s i b =>
      have hm := of_decide_eq_true hp
      change (⟨.seat s i, .head b⟩ : GridCO.Wire (params (count := count)).n .root) ∈
        st.base.votes at hm
      simp [admitHead, GridCO.admitVote, hm]
    | row i body =>
      have hm := of_decide_eq_true hp
      obtain rfl := (nvGen_i7_decode_row (count := count)) o i body hd
      exact (nvGen_i7_admitRow_duplicate (count := count)) st i body hm
    | block s b =>
      have hm := of_decide_eq_true hp
      apply admitBlock_refused
      cases hP : parentFG st b.erase with
      | none => exact Or.inr (Or.inl rfl)
      | some P => exact Or.inr (Or.inr ⟨P, rfl, by simp [blockAccepted, hm]⟩)

theorem nvGen_w1_deliver_st (t : Time) (acc : (World (count := count)) × List (Event (count :=
  count)))
    (vo : (Validator (count := count)) × Obj (params (count := count))) (u : (Validator (count
      := count))) :
    (((deliverOne (count := count)) t acc vo).1 u).st =
      if u = vo.1 then FGSA.process (params (count := count)) (acc.1 u).st (toWire (params
        (count := count)) vo.2)
      else (acc.1 u).st := by
  unfold deliverOne
  split
  · rename_i hp
    by_cases hu : u = vo.1
    · subst u
      rw [ite_eq_left rfl, nvGen_w1_process_inert _ _ hp]
    · rw [ite_eq_right hu]
  · dsimp only
    by_cases hu : u = vo.1
    · subst u
      simp only [V2.D.World.step, Function.update_self]
      rfl
    · simp only [V2.D.World.step, Function.update_of_ne hu, ite_eq_right hu]

theorem nvGen_w1_offer_st (t : Time) (acc : (World (count := count)) × List (Event (count :=
  count)))
  (o : Obj (params (count := count)))
    (vs : List (Validator (count := count))) (hn : vs.Nodup) (u : (Validator (count := count))) :
    (((vs.map (fun v => (v, o))).foldl ((deliverOne (count := count)) t) acc).1 u).st =
      if u ∈ vs then FGSA.process (params (count := count)) (acc.1 u).st (toWire (params (count
        := count)) o)
      else (acc.1 u).st := by
  induction vs generalizing acc with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.foldl_cons, ih _ hn.of_cons, nvGen_w1_deliver_st]
    by_cases huv : u = v
    · subst u
      simp only [List.mem_cons, true_or, ↓reduceIte, hn.notMem]
    · by_cases hu : u ∈ vs <;> simp [huv, hu]

theorem nvGen_tick_fold_node (t : Time) (vs : List (Validator (count := count))) (hn : vs.Nodup)
    (w : (World (count := count))) (os : List (fgsa (params (count := count)) unitCodec).Object)
      (u : (Validator (count := count))) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).1 u =
      if u ∈ vs then (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (w u) u t).1 else w u := by
  induction vs generalizing w os with
  | nil => simp
  | cons v vs ih =>
      apply (ih hn.of_cons _ _).trans
      by_cases huv : u = v
      · subst u
        simp only [hn.notMem, ↓reduceIte, Function.update_self, List.mem_cons_self]
      · by_cases hu : u ∈ vs <;> simp [huv, hu]

theorem nvGen_tick_fold_emits (t : Time) (vs : List (Validator (count := count))) (hn : vs.Nodup)
    (w : (World (count := count))) (os : List (fgsa (params (count := count)) unitCodec).Object)
      (o : (fgsa (params (count := count)) unitCodec).Object) :
    o ∈ (vs.foldl (fun acc v =>
      let result := V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
        (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2 ↔
      o ∈ os ∨ ∃ v ∈ vs, o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count))
        263 []) (w v) v t).2 := by
  induction vs generalizing w os with
  | nil => simp
  | cons v vs ih =>
      have hstep := ih hn.of_cons
        (Function.update w v (V2.D.tick (weakEnv (count := count)) ((runData (count := count))
          263 []) (w v) v t).1)
        (os ++ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) (w v) v
          t).2)
      constructor
      · intro ho
        rcases hstep.mp ho with hm | ⟨u, hu, ho⟩
        · rcases List.mem_append.mp hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr ⟨v, List.mem_cons_self, hm⟩
        · have hne : u ≠ v := by intro he; exact hn.notMem (he ▸ hu)
          exact Or.inr ⟨u, List.mem_cons_of_mem _ hu,
            by simpa only [Function.update_of_ne hne] using ho⟩
      · intro ho
        apply hstep.mpr
        rcases ho with hm | ⟨u, hu, ho⟩
        · exact Or.inl (List.mem_append_left _ hm)
        · rcases List.mem_cons.mp hu with rfl | hu
          · exact Or.inl (List.mem_append_right _ ho)
          · have hne : u ≠ v := by intro he; exact hn.notMem (he ▸ hu)
            exact Or.inr ⟨u, hu, by simpa only [Function.update_of_ne hne] using ho⟩

theorem nvGen_w1_tickBatch_st (t : Time) (w : (World (count := count))) (u : (Validator (count :=
  count))) :
    (((tickBatch (count := count)) t w).1 u).st = FGSA.clock (params (count := count)) (w u).st
      t := by
  have he := (nvGen_tick_fold_node (count := count)) t (nodes (count := count))
    (nvGen_nodes_nodup (count :=
    count)) w [] u
  rw [ite_eq_left (nvGen_nodes_complete u)] at he
  exact congrArg Node.st he |>.trans ((nvGen_i7_tick_st (count := count)) (w u) u t)

def GenUniformStores (w : (World (count := count))) : Prop := ∀ u v, (w u).st = (w v).st

theorem nvGen_w1_offer_uniform (t : Time) (acc : (World (count := count)) × List (Event (count :=
  count))) (o : Obj (params (count := count)))
    (hw : (GenUniformStores (count := count)) acc.1) :
    (GenUniformStores (count := count)) (((nodes (count := count)).map (fun v => (v, o))).foldl
      ((deliverOne (count := count)) t) acc).1 := by
  intro u v
  rw [nvGen_w1_offer_st t acc o nodes nvGen_nodes_nodup, nvGen_w1_offer_st t acc o nodes
    nvGen_nodes_nodup,
    ite_eq_left (nvGen_nodes_complete u), ite_eq_left (nvGen_nodes_complete v), hw u v]

theorem nvGen_w1_objects_uniform (t : Time) (os : List (Obj (params (count := count))))
    (acc : (World (count := count)) × List (Event (count := count))) (hw : (GenUniformStores
      (count := count)) acc.1) :
    (GenUniformStores (count := count)) ((os.flatMap (fun o => (nodes (count := count)).map (fun
      v => (v, o)))).foldl
      ((deliverOne (count := count)) t) acc).1 := by
  induction os generalizing acc with
  | nil => exact hw
  | cons o os ih =>
    rw [List.flatMap_cons, List.foldl_append]
    exact ih _ ((nvGen_w1_offer_uniform (count := count)) t acc o hw)

theorem nvGen_w1_batch_uniform (t : Time) (w : (World (count := count))) (hw : (GenUniformStores
  (count := count)) w) :
    (GenUniformStores (count := count)) ((timeBatch (count := count)) t w).1 := by
  apply (nvGen_w1_objects_uniform (count := count))
  intro u v
  rw [nvGen_w1_tickBatch_st, nvGen_w1_tickBatch_st, hw u v]

theorem nvGen_w1_prefix_uniform (steps : Nat) : (GenUniformStores (count := count)) ((buildPrefix
  (count := count)) steps).1 := by
  induction steps with
  | zero => exact fun _ _ => rfl
  | succ steps ih => exact (nvGen_w1_batch_uniform (count := count)) _ _ ih

theorem nvGen_w1_tickBatch_emits (t : Time) (w : (World (count := count))) (o : Obj (params
  (count :=
  count))) :
    o ∈ ((tickBatch (count := count)) t w).2 ↔
      ∃ v, o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) (w v) v
        t).2 := by
  have he := (nvGen_tick_fold_emits (count := count)) t (nodes (count := count))
    (nvGen_nodes_nodup (count
    := count)) w [] o
  constructor
  · intro ho
    rcases he.mp ho with ho | ⟨v, _, ho⟩
    · exact (List.not_mem_nil ho).elim
    · exact ⟨v, ho⟩
  · rintro ⟨v, hv⟩
    exact he.mpr (Or.inr ⟨v, (nvGen_nodes_complete (count := count)) v, hv⟩)

theorem nvGen_w1_reachable (es : List (Event (count := count))) (u : (Validator (count := count))) :
    Reachable (params (count := count)) ((genFold (count := count)) V2.D.World.init es u).st := by
  have h := reachable_stateBefore (weakEnv (count := count)) ((runData (count := count)) 263 es)
    es.length u
  rwa [(nvGen_runData_stateBefore (count := count)), List.take_length] at h

theorem nvGen_w1_tick_deps (st : Node (params (count := count))) (v : (Validator (count :=
  count))) (t
  : Time)
    (hr : Reachable (params (count := count)) st.st) (o : Obj (params (count := count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2) :
    depsS (params (count := count)) (FGSA.clock (params (count := count)) st.st t) o = true := by
  obtain ⟨l, j, m, rfl, _, ha⟩ := (nvGen_gen_tick_seat (count := count)) st v t o ho
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have he : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
      st.st t) s).root = m := Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count)) st.st t)
      st.record ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    rfl
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    change (propose (params (count := count)) (FGSA.clock (params (count := count)) st.st t)
      s).map (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp ha
      let pre := FGSA.clock (params (count := count)) st.st t
      have hnamed := namedByErase?_sound pre _ P hP
      have hinv := (storeBundle_of_reachable (params (count := count)) _ (Reachable.tick t
        hr)).cstore
      let H := getHead (params (count := count)) pre (proposerVotes pre s) (proposerSupport pre s)
      obtain ⟨Q, hQ, he⟩ := (hinv.baseTree H).mp (getHead_stored (params (count := count)) _
        hinv _ _)
      have hlookup := (fgBlockOf_spec (params (count := count)) pre hinv H Q).mpr ⟨hQ, he⟩
      change (decide (P ∈ pre.namedBodies) && (fgBlockOf pre P.erase).isSome) = true
      rw [hnamed.2, hlookup]
      simp only [Option.isSome_some, Bool.and_true, decide_eq_true_eq]
      exact hnamed.1

theorem nvGen_w1_batch_deps_start (t : Time) (w : (World (count := count))) (hw : (GenUniformStores
  (count := count)) w)
    (hr : ∀ v, Reachable (params (count := count)) (w v).st) (o : Obj (params (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) t w).2) (u : (Validator (count := count))) :
    depsS (params (count := count)) (((tickBatch (count := count)) t w).1 u).st o = true := by
  obtain ⟨v, hv⟩ := ((nvGen_w1_tickBatch_emits (count := count)) t w o).1 ho
  rw [nvGen_w1_tickBatch_st, hw u v]
  exact (nvGen_w1_tick_deps (count := count)) _ v t (hr v) o hv

theorem nvGen_w1_deps_mono {st st' : State (params (count := count)).n} (hT : st.fg.TF ⊆ st'.fg.TF)
    (hN : st.namedBodies ⊆ st'.namedBodies) (o : Obj (params (count := count))) (h : depsS
      (params (count := count)) st o = true) :
    depsS (params (count := count)) st' o = true := by
  unfold depsS at h ⊢
  cases hd : (toWire (params (count := count)) o).decode with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => rfl
    | row i body => rfl
    | block s b =>
      rw [hd] at h
      obtain ⟨hn, hp⟩ := Bool.and_eq_true_iff.mp h
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true (hN (of_decide_eq_true hn)), ?_⟩
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hp
      exact Option.isSome_iff_exists.mpr ⟨P,
        (parentFG_spec st' b.erase P).2
          ⟨hT ((parentFG_spec st b.erase P).1 hP).1,
            ((parentFG_spec st b.erase P).1 hP).2⟩⟩

theorem nvGen_w1_deliver_deps (t : Time) (acc : (World (count := count)) × List (Event (count :=
  count)))
    (vo : (Validator (count := count)) × Obj (params (count := count))) (u : (Validator (count
      := count))) (o : Obj (params (count := count)))
    (h : depsS (params (count := count)) (acc.1 u).st o = true) :
    depsS (params (count := count)) (((deliverOne (count := count)) t acc vo).1 u).st o = true := by
  rw [nvGen_w1_deliver_st]
  split
  · exact (nvGen_w1_deps_mono (count := count)) (process_cumulative (params (count := count)) _ _).1
      (process_namedBodies_subset _ _) o h
  · exact h

def GenDeps : (World (count := count)) → List (Event (count := count)) → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => depsS (params (count := count)) (w v).st o = true
        | _ => True) ∧
      GenDeps (V2.D.World.step (weakEnv (count := count)) ((runData (count := count)) 263 []) w
        e) es

theorem nvGen_w1_deps_append (w : (World (count := count))) (es ds : List (Event (count :=
  count))) :
    (GenDeps (count := count)) w (es ++ ds) ↔ (GenDeps (count := count)) w es ∧ (GenDeps (count
      := count)) ((genFold (count := count)) w es) ds := by
  induction es generalizing w with
  | nil => simp [GenDeps, genFold]
  | cons e es ih =>
    simp only [List.cons_append, GenDeps, ih, genFold, List.foldl_cons]
    tauto

theorem nvGen_w1_delivery_fold_deps (t : Time) (xs : List ((Validator (count := count)) × Obj
  (params
  (count := count))))
    (w : (World (count := count))) (acc : (World (count := count)) × List (Event (count :=
      count))) (hr : (genFold (count := count)) w acc.2 = acc.1)
    (hd : (GenDeps (count := count)) w acc.2)
    (hx : ∀ vo ∈ xs, depsS (params (count := count)) (acc.1 vo.1).st vo.2 = true) :
    (GenDeps (count := count)) w (xs.foldl ((deliverOne (count := count)) t) acc).2 := by
  induction xs generalizing acc with
  | nil => exact hd
  | cons vo xs ih =>
    rw [List.foldl_cons]
    apply ih
    · unfold deliverOne
      split
      · exact hr
      · simp only [nvGen_genFold_append, hr]
        rfl
    · unfold deliverOne
      split
      · exact hd
      · apply ((nvGen_w1_deps_append (count := count)) w acc.2 _).2
        exact ⟨hd, by simpa only [GenDeps, hr, and_true] using hx vo (List.mem_cons_self ..)⟩
    · intro vo' hm
      exact (nvGen_w1_deliver_deps (count := count)) t acc vo vo'.1 vo'.2 (hx vo'
        (List.mem_cons_of_mem _ hm))

theorem nvGen_w1_ticks_deps (w : (World (count := count))) (t : Time) (vs : List (Validator
  (count :=
  count))) :
    (GenDeps (count := count)) w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

theorem nvGen_w1_batch_deps (t : Time) (w : (World (count := count))) (hw : (GenUniformStores (count
  := count)) w)
    (hr : ∀ v, Reachable (params (count := count)) (w v).st) : (GenDeps (count := count)) w
      ((timeBatch (count := count)) t w).2 := by
  apply (nvGen_w1_delivery_fold_deps (count := count))
  · exact ((nvGen_tickBatch_replay (count := count)) t w).symm
  · exact (nvGen_w1_ticks_deps (count := count)) w t (nodes (count := count))
  · intro vo hm
    obtain ⟨o, ho, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
    exact (nvGen_w1_batch_deps_start (count := count)) t w hw hr o ho v

theorem nvGen_w1_prefix_deps (steps : Nat) : (GenDeps (count := count)) V2.D.World.init
  ((buildPrefix
  (count := count)) steps).2 := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
    apply ((nvGen_w1_deps_append (count := count)) _ _ _).2
    refine ⟨ih, ?_⟩
    rw [← (nvGen_prefix_replay_fresh steps).1]
    exact (nvGen_w1_batch_deps (count := count)) _ _ ((nvGen_w1_prefix_uniform (count := count))
      steps) (fun
      v => by
      rw [(nvGen_prefix_replay_fresh steps).1]
      exact (nvGen_w1_reachable (count := count)) _ v)

theorem nvGen_w1_deps_get (w : (World (count := count))) (es : List (Event (count := count))) (hd :
  (GenDeps (count := count)) w es)
    (i : Nat) (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    depsS (params (count := count)) ((genFold (count := count)) w (es.take i) v).st o = true := by
  induction es generalizing w i with
  | nil => simp at he
  | cons e es ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst e
      exact hd.1
    | succ i => exact ih _ hd.2 i (by simpa using he)

theorem nvGen_w1_prefix_schedule (steps : Nat) :
    V2.D.ScheduleWellFormed (weakEnv (count := count)) ((runData (count := count)) steps
      ((buildPrefix (count := count)) (steps + 1)).2) where
  horizon_nonneg := Int.natCast_nonneg _
  sorted := (nvGen_prefix_sorted (count := count)) _
  nodup := (nvGen_prefix_nodup (count := count)) _
  in_horizon e he := by
    obtain ⟨h0, ht⟩ := (nvGen_witness_prefix_times (count := count)) (steps + 1) e he
    change 0 ≤ e.time ∧ e.time ≤ (steps : Int)
    refine ⟨h0, ?_⟩
    have ht' : e.time < (steps : Int) + 1 := by exact_mod_cast ht
    exact Int.le_of_lt_add_one ht'
  honest_only _ _ := Finset.mem_univ _
  tick_public v t he := ⟨t.toNat, by
    have ht := ((nvGen_witness_prefix_times (count := count)) (steps + 1) (.tick v t) he).1
    change 0 ≤ t at ht
    change t = (t.toNat : Int) * 1
    rw [Int.toNat_of_nonneg ht, mul_one]⟩
  tick_total v _ t _ ht hh _ := by
    change t ≤ (steps : Int) at hh
    change (0 : Int) ≤ t at ht
    have hn : t.toNat < steps + 1 := by
      have hle : t.toNat ≤ steps := Int.toNat_le.mpr hh
      omega
    change V2.Event.tick v t ∈ ((buildPrefix (count := count)) (steps + 1)).2
    simpa only [Int.toNat_of_nonneg ht] using (nvGen_prefix_tick (count := count)) (steps + 1)
      t.toNat
      hn v

def GenSingleDutyUnique (P : Obj (params (count := count)) → Prop) : Prop :=
  ∀ l j o o', Gen.V2.Duty.SingleDuty (fgsa (params (count := count)) unitCodec) l → P o → P o' →
    o.auth
    = .seat l j → o'.auth = .seat l j → o = o'

theorem nvGen_w1_emits_unique (es : List (Event (count := count))) (hn : es.Nodup) :
    (GenSingleDutyUnique (count := count)) (fun o => ∃ v t, (GenEmits (count := count))
      V2.D.World.init es v o t) := by
  rintro l j o o' hD ⟨v, t, he⟩ ⟨v', t', he'⟩ ha ha'
  have holder (x : (Validator (count := count))) (u : Time) (a : Obj (params (count := count)))
      (he : (GenEmits (count := count)) V2.D.World.init es x a u) (ha : a.auth = .seat l j) :
      x = (seatOf (count := count)) l j := by
    obtain ⟨pre, post, _, hm⟩ := he
    have hh := (nvGen_gen_tick_holder (count := count)) ((genFold (count := count)) V2.D.World.init
      pre x) x u a hm
    rw [ha] at hh
    exact (Option.some.inj hh).symm
  have hv := holder v t o he ha
  have hv' := holder v' t' o' he' ha'
  obtain ⟨i, hi, ho⟩ := (nvGen_genEmits_runData (count := count)) 263 es v o t he
  obtain ⟨i', hi', ho'⟩ := (nvGen_genEmits_runData (count := count)) 263 es v' o' t' he'
  rw [hv] at hi
  rw [hv'] at hi'
  exact (Gen.V2.Duty.emitted_unique_of_singleDuty (weakEnv (count := count)) ((runData (count :=
    count)) 263 es) hn
    l hD j ((seatOf (count := count)) l j) i i' t t' o o' hi hi' ho ho' ha ha').2

theorem nvGen_w1_head_accept (P : Obj (params (count := count)) → Prop) (hu : (GenSingleDutyUnique
  (count := count)) P)
    (st : State (params (count := count)).n) (hk : (GenKnown (count := count)) P st) (s : Slot)
      (i : Fin (params (count := count)).n) (b : BlockId)
    (ho : P (ofHead (params (count := count)) ⟨.seat (.head s) i, b⟩)) (hs : st.slot (params
      (count := count)) = s) :
    processedS (params (count := count)) (FGSA.process (params (count := count)) st
      (toWire (params (count := count)) (ofHead (params (count := count)) ⟨.seat (.head s) i, b⟩)))
      (ofHead (params (count := count)) ⟨.seat (.head s) i, b⟩) = true := by
  let a : HeadWire (params (count := count)).n := ⟨.seat (.head s) i, b⟩
  by_cases hm : baseVote a ∈ st.base.votes
  · have hp : processedS (params (count := count)) st (ofHead (params (count := count)) a) =
    true := decide_eq_true hm
    rw [nvGen_w1_process_inert st _ hp]
    exact hp
  · have hempty : GridCO.seatVotes (GridCO.votesAt st.base s) i = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw hseat
      obtain ⟨hw, hlabel⟩ := List.mem_filter.mp hw
      have hl : GridCO.headLabel? w = some s := beq_iff_eq.mp hlabel
      have hi : GridCO.headSeat? w = some i := beq_iff_eq.mp hseat
      obtain ⟨auth, msg⟩ := w
      cases auth with
      | none => cases msg <;> cases hl
      | proposer r => cases msg <;> cases hl
      | seat r j =>
        cases msg with
        | proposal q raw sup => cases hl
        | head b' =>
          cases hl
          cases hi
          have hp : P (ofHead (params (count := count)) ⟨.seat (.head s) i, b'⟩) :=
            hk.2.2 _ (List.mem_filterMap.mpr ⟨_, hw, rfl⟩)
          have he := hu (.base (.head s)) i _ _ (fgsa_head_singleDuty s) hp ho rfl rfl
          have hb : b' = b := Msg.head.inj (congrArg V2.Signed.payload he)
          subst b'
          exact hm hw
    have hx : GridCO.equivocates (GridCO.votesAt st.base s) i = false := by
      simp [GridCO.equivocates, hempty]
    have hs' : (st.base.now / (4 * (params (count := count)).toParams.engine.Δ)).toNat = s := hs
    change decide (baseVote a ∈ (admitHead (params (count := count)) st s i b).base.votes) = true
    apply decide_eq_true
    change (⟨.seat s i, .head b⟩ : GridCO.Wire (params (count := count)).n .root) ∈ _
    change (⟨.seat s i, .head b⟩ : GridCO.Wire (params (count := count)).n .root) ∉
      st.base.votes at hm
    simp [admitHead, GridCO.admitVote, hs', hm, hx, Nat.not_lt.mpr (Nat.sub_le s 1)]

theorem nvGen_w1_row_accept (st : State (params (count := count)).n) (i : Fin (params (count :=
  count)).n) (body : RowPayload) :
    processedS (params (count := count)) (FGSA.process (params (count := count)) st
      (toWire (params (count := count)) (ofRow (params (count := count)) ⟨.seat .fg i, body⟩)))
      (ofRow (params (count := count)) ⟨.seat .fg i, body⟩) = true := by
  change decide ((⟨.seat .fg i, body⟩ : RowWire (params (count := count)).n) ∈
    (admitRow (params (count := count)) st ⟨.seat .fg i, body⟩).rowPool) = true
  unfold admitRow
  dsimp only [RowWire.decode?]
  split <;> simp_all

theorem nvGen_w1_processed_mono {st st' : State (params (count := count)).n}
    (hv : st.base.votes ⊆ st'.base.votes) (hr : st.rowPool ⊆ st'.rowPool)
    (hT : st.fg.TF ⊆ st'.fg.TF) (o : Obj (params (count := count))) :
    processedS (params (count := count)) st o = true → processedS (params (count := count)) st'
      o = true := by
  dsimp only [processedS]
  cases (toWire (params (count := count)) o).decode with
  | none => exact id
  | some m =>
    cases m with
    | vote s i b => simpa only [decide_eq_true_eq] using (fun h => hv h)
    | row i body => simpa only [decide_eq_true_eq] using (fun h => hr h)
    | block s b =>
      simp only [decide_eq_true_eq]
      rintro ⟨Y, hY, he⟩
      exact ⟨Y, hT hY, he⟩

theorem nvGen_w1_process_processed (st : State (params (count := count)).n) (a o : Obj (params
  (count
  := count)))
    (h : processedS (params (count := count)) st o = true) :
    processedS (params (count := count)) (FGSA.process (params (count := count)) st (toWire
      (params (count := count)) a)) o = true := by
  have hc := process_cumulative (params (count := count)) st (toWire (params (count := count)) a)
  exact (nvGen_w1_processed_mono (count := count)) (process_votes_subset st (toWire (params
    (count :=
    count)) a))
    hc.2.2.2.2.2.subset hc.1 o h

theorem nvGen_w1_deliver_processed (t : Time) (acc : (World (count := count)) × List (Event
  (count :=
  count)))
    (vo : (Validator (count := count)) × Obj (params (count := count))) (u : (Validator (count
      := count))) (o : Obj (params (count := count)))
    (h : processedS (params (count := count)) (acc.1 u).st o = true) :
    processedS (params (count := count)) (((deliverOne (count := count)) t acc vo).1 u).st o =
      true := by
  rw [nvGen_w1_deliver_st]
  split
  · exact (nvGen_w1_process_processed (count := count)) _ _ _ h
  · exact h

theorem nvGen_w1_fold_processed (t : Time) (xs : List ((Validator (count := count)) × Obj (params
  (count := count))))
    (acc : (World (count := count)) × List (Event (count := count))) (u : (Validator (count :=
      count))) (o : Obj (params (count := count)))
    (h : processedS (params (count := count)) (acc.1 u).st o = true) :
    processedS (params (count := count)) ((xs.foldl ((deliverOne (count := count)) t) acc).1
      u).st o = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons vo xs ih => exact ih _ ((nvGen_w1_deliver_processed (count := count)) t acc vo u o h)

theorem nvGen_w1_deliver_now (t : Time) (acc : (World (count := count)) × List (Event (count :=
  count)))
    (vo : (Validator (count := count)) × Obj (params (count := count))) (u : (Validator (count
      := count))) :
    (((deliverOne (count := count)) t acc vo).1 u).st.base.now = (acc.1 u).st.base.now := by
  rw [nvGen_w1_deliver_st]
  split
  · exact process_base_now _ _
  · rfl

theorem nvGen_w1_fold_complete (P : Obj (params (count := count)) → Prop) (t : Time)
    (xs : List ((Validator (count := count)) × Obj (params (count := count)))) (acc : (World
      (count := count)) × List (Event (count := count)))
    (hk : ∀ u, (GenKnown (count := count)) P (acc.1 u).st) (hn : ∀ u, (acc.1 u).st.base.now = t)
    (hc : ∀ vo ∈ xs, P vo.2 ∧ ∀ a, carriesS (params (count := count)) vo.2 a → P a)
    (ha : ∀ vo ∈ xs, ∀ st, (GenKnown (count := count)) P st → st.base.now = t →
      processedS (params (count := count)) (FGSA.process (params (count := count)) st (toWire
        (params (count := count)) vo.2)) vo.2 = true) :
    ∀ vo ∈ xs, processedS (params (count := count)) ((xs.foldl ((deliverOne (count := count)) t)
      acc).1 vo.1).st vo.2 = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons vo xs ih =>
    have hk' : ∀ u, (GenKnown (count := count)) P (((deliverOne (count := count)) t acc vo).1
      u).st := by
      intro u
      rw [nvGen_w1_deliver_st]
      split
      · exact (nvGen_gen_known_process (count := count)) P _ vo.2 (hk u)
          (hc vo (List.mem_cons_self ..)).1 (hc vo (List.mem_cons_self ..)).2
      · exact hk u
    have hn' : ∀ u, (((deliverOne (count := count)) t acc vo).1 u).st.base.now = t :=
      fun u => ((nvGen_w1_deliver_now (count := count)) t acc vo u).trans (hn u)
    intro vo' hm
    rcases List.mem_cons.mp hm with he | hm
    · subst vo'
      apply (nvGen_w1_fold_processed (count := count)) t xs ((deliverOne (count := count)) t acc vo)
        vo.1 vo.2
      rw [nvGen_w1_deliver_st, ite_eq_left rfl]
      exact ha vo (List.mem_cons_self ..) _ (hk vo.1) (hn vo.1)
    · exact ih _ hk' hn' (fun vo hm => hc vo (List.mem_cons_of_mem _ hm))
        (fun vo hm => ha vo (List.mem_cons_of_mem _ hm)) vo' hm

theorem nvGen_w1_nonproposal_accept (P : Obj (params (count := count)) → Prop) (hu :
  (GenSingleDutyUnique (count := count)) P)
    (nd : Node (params (count := count))) (v : (Validator (count := count))) (t : Time) (o : Obj
      (params (count := count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) nd v t).2)
    (hP : P o) (hnot : ∀ b, o.payload ≠ .proposal b)
    (st : State (params (count := count)).n) (hk : (GenKnown (count := count)) P st) (hn :
      st.base.now = t) :
    processedS (params (count := count)) (FGSA.process (params (count := count)) st (toWire
      (params (count := count)) o)) o = true := by
  obtain ⟨l, j, m, rfl, hl, ha⟩ := (nvGen_gen_tick_seat (count := count)) nd v t o ho
  have ht := ((fgsa (params (count := count)) unitCodec).duties_spec l t).1 hl
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have he : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
      nd.st t) s).root = m := Option.some.inj ha
    subst m
    apply (nvGen_w1_head_accept (count := count)) P hu st hk s j _ hP
    change (params (count := count)).slotOf st.base.now = s
    rw [hn, ← ht]
    exact (fgsa_vote_slot (c := unitCodec) nd s).symm.trans
      ((fgsa_postClock_slot (c := unitCodec) nd _).2) |>.symm
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count)) nd.st t)
      nd.record
        ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact (nvGen_w1_row_accept (count := count)) st j body
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    change (propose (params (count := count)) (FGSA.clock (params (count := count)) nd.st t)
      s).map (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact (hnot _ rfl).elim

theorem nvGen_w1_batch_nonproposal_complete (P : Obj (params (count := count)) → Prop) (hu :
  (GenSingleDutyUnique (count := count)) P)
    (t : Time) (w : (World (count := count))) (hk : ∀ v, (GenKnown (count := count)) P (w v).st)
    (hp : ∀ o ∈ ((tickBatch (count := count)) t w).2, P o)
    (hnot : ∀ o ∈ ((tickBatch (count := count)) t w).2, ∀ b,
      o.payload ≠ .proposal b) (v : (Validator (count := count))) (o : Obj (params (count :=
        count)))
    (ho : o ∈ ((tickBatch (count := count)) t w).2) :
    processedS (params (count := count)) (((timeBatch (count := count)) t w).1 v).st o = true := by
  obtain ⟨hk', hc⟩ := (nvGen_gen_tick_fold_known (count := count)) P t (nodes (count := count)) w []
    hk (by simp)
  apply (nvGen_w1_fold_complete (count := count)) P t _ _ hk'
    (fun u => by rw [nvGen_w1_tickBatch_st]; exact (clock_vn (w u).st t).2)
    (fun vo hm => ?_) (fun vo hm st hst hn => ?_) (v, o)
    (List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨v, (nvGen_nodes_complete (count := count))
      v, rfl⟩⟩)
  · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨hp a ha, hc a ha⟩
  · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
    obtain ⟨x, hx⟩ := ((nvGen_w1_tickBatch_emits (count := count)) t w a).1 ha
    exact (nvGen_w1_nonproposal_accept (count := count)) P hu (w x) x t a hx (hp a ha) (hnot a
      ha) st
      hst hn

theorem nvGen_w1_proposal_only (t : Time) (w : (World (count := count))) (v : (Validator (count :=
  count))) (s : Slot)
    (j : Fin 1) (m : Msg (params (count := count)).n)
    (ho : (⟨.seat (.prop s) j, m⟩ : Obj (params (count := count))) ∈
      (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) (w v) v t).2)
    (o' : Obj (params (count := count))) (ho' : o' ∈ ((tickBatch (count := count)) t w).2) :
    o' = ⟨.seat (.prop s) j, m⟩ := by
  have hv := (nvGen_gen_tick_holder (count := count)) (w v) v t _ ho
  have hv0 : v = 0 := (Option.some.inj hv).symm
  subst v
  have ha := (Gen.V2.Duty.mem_tick_singleDuty_iff (weakEnv (count := count)) ((runData (count :=
    count)) 263 []) (w 0) 0 t
    (.prop s) (fgsa_prop_singleDuty s) (.propAction s) rfl j m).1 ho
  have ht : (4 : Int) * s = t := ha.2.1
  obtain ⟨v', hv'⟩ := ((nvGen_w1_tickBatch_emits (count := count)) t w o').1 ho'
  have holder := (nvGen_gen_tick_holder (count := count)) (w v') v' t o' hv'
  obtain ⟨l', j', m', rfl, hl', ha'⟩ := (nvGen_gen_tick_seat (count := count)) (w v') v' t o' hv'
  have ht' := ((fgsa (params (count := count)) unitCodec).duties_spec l' t).1 hl'
  cases l' with
  | headAction r =>
    change (4 : Int) * r + 1 = t at ht'
    omega
  | fgAction r =>
    change (4 : Int) * ((r * 2 : Nat) : Int) + 6 = t at ht'
    omega
  | propAction s' =>
    change (4 : Int) * s' = t at ht'
    have he : s' = s := by
      have he : (s' : Int) = s := mul_left_cancel₀ (by decide : (4 : Int) ≠ 0)
        (ht'.trans ht.symm)
      exact_mod_cast he
    subst s'
    have hv0 : v' = 0 := (Option.some.inj holder).symm
    subst v'
    have hj : j' = j := Subsingleton.elim (α := Fin 1) _ _
    subst j'
    have hm : m' = m := Option.some.inj (ha'.symm.trans ha.2.2.2)
    subst m'
    rfl

theorem nvGen_w1_proposal_singleton (t : Time) (w : (World (count := count))) (o : Obj (params
  (count
  := count)))
    (ho : o ∈ ((tickBatch (count := count)) t w).2) (b : NamedProposal (params (count :=
      count)).n) (hp : o.payload = .proposal b) :
    ((tickBatch (count := count)) t w).2 = [o] := by
  have hall : ∀ o' ∈ ((tickBatch (count := count)) t w).2, o' = o := by
    obtain ⟨v, hv⟩ := ((nvGen_w1_tickBatch_emits (count := count)) t w o).1 ho
    obtain ⟨l, j, m, rfl, _, ha⟩ := (nvGen_gen_tick_seat (count := count)) (w v) v t o hv
    cases l with
    | headAction s =>
      have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
      have he : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
        (w v).st t) s).root = m :=
        Option.some.inj ha
      subst m
      cases hp
    | fgAction r =>
      change (attest (params (count := count)) (FGSA.clock (params (count := count)) (w v).st t)
        (w v).record
          ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      cases hp
    | propAction s =>
        have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
        intro o' ho'
        exact nvGen_w1_proposal_only (count := count) t w v s j m hv o' ho'
  have hn := (nvGen_tickBatch_nodup (count := count)) t w
  generalize ((tickBatch (count := count)) t w).2 = os at ho hall hn ⊢
  cases os with
  | nil => exact (List.not_mem_nil ho).elim
  | cons a os =>
    have he := hall a (List.mem_cons_self ..)
    subst a
    have hz : os = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      have he := hall a (List.mem_cons_of_mem _ ha)
      exact hn.notMem (he ▸ ha)
    rw [hz]

private theorem nvGen_w1_proposal_admit (nd : Node (params (count := count))) (v : (Validator (count
  := count))) (t : Time) (o : Obj (params (count := count)))
    (hr : Reachable (params (count := count)) nd.st)
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) nd v t).2)
    (hw : (fgsa (params (count := count)) unitCodec).wellFormed o = true) (b : NamedProposal
      (params (count := count)).n)
    (hp : o.payload = .proposal b) :
    processedS (params (count := count))
      (FGSA.process (params (count := count)) (FGSA.clock (params (count := count)) nd.st t)
        (toWire (params (count := count)) o)) o = true ∧
      (processedS (params (count := count)) nd.st o = false →
        b ∈ (FGSA.process (params (count := count)) (FGSA.clock (params (count := count)) nd.st
          t) (toWire (params (count := count)) o)).namedBodies) := by
  obtain ⟨l, j, m, rfl, hl, ha⟩ := (nvGen_gen_tick_seat (count := count)) nd v t o ho
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have he : .head (headVote (params (count := count)) (FGSA.clock (params (count := count))
      nd.st t) s).root = m :=
      Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count)) nd.st t)
      nd.record
        ⟨0, (params (count := count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    have ht : SA.proposalTime (params (count := count)).toParams s = t :=
      ((fgsa (params (count := count)) unitCodec).duties_spec (.propAction s) t).1 hl
    change (propose (params (count := count)) (FGSA.clock (params (count := count)) nd.st t)
      s).map (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨Parent, hParent, rfl⟩ := Option.map_eq_some_iff.mp ha
      cases hp
      let st := FGSA.clock (params (count := count)) nd.st t
      let H := getHead (params (count := count)) st (proposerVotes st s) (proposerSupport st s)
      let rs := proposalRows (params (count := count)) st H
      let N := namedProposal (params (count := count)) Parent s 0
        ((proposerVotes st s).filterMap liftHead?)
        ((proposerSupport st s).filterMap liftHead?) rs
      have hnamed := namedByErase?_sound st H Parent hParent
      have hNamed : namedParentHeld st N = true := decide_eq_true hnamed.1
      have hinv := (storeBundle_of_reachable (params (count := count)) st (Reachable.tick t
        hr)).cstore
      change FGSA.wellFormed (params (count := count)) ⟨.proposer s, .proposal N⟩ = true at hw
      change processedS (params (count := count)) (FGSA.process (params (count := count)) st
        ⟨.proposer s, .proposal N⟩)
          (ofWire (params (count := count)) ⟨.proposer s, .proposal N⟩) = true ∧
        (processedS (params (count := count)) nd.st (ofWire (params (count := count)) ⟨.proposer
          s, .proposal N⟩) = false →
          N ∈ (FGSA.process (params (count := count)) st ⟨.proposer s, .proposal N⟩).namedBodies)
      by_cases hmem : ∃ Y ∈ st.fg.TF, Y.root = N.root
      · obtain ⟨Y, hY, he⟩ := hmem
        constructor
        · exact decide_eq_true ⟨Y, (process_cumulative (params (count := count)) st _).1 hY, he⟩
        · intro hf
          change decide (∃ Z ∈ nd.st.fg.TF, Z.root = N.root) = false at hf
          have hY' : Y ∈ nd.st.fg.TF := by simpa only [st, clock_fg] using hY
          exact (of_decide_eq_false hf ⟨Y, hY', he⟩).elim
      · have hslot : N.erase.slot ≤ st.slot (params (count := count)) := by
          have hs := fgsa_proposal_slot (c := unitCodec) nd s
          rw [ht] at hs
          exact le_of_eq hs.symm
        have hfresh : ∀ c ∈ st.base.blocks, c.root ≠ N.erase.root := by
          intro c hc he
          obtain ⟨Y, hY, rfl⟩ := (hinv.baseTree c).1 hc
          exact hmem ⟨Y, hY,
            (eraseFG_root Y).symm.trans (he.trans (named_erase_root N))⟩
        have hF : Block.Preceq (eraseFG st.fg.F) N.erase := by
          change (decide (eraseFG st.fg.F = N.erase) ||
            Block.preceq (eraseFG st.fg.F) Parent.erase) = true
          rw [hnamed.2]
          exact Bool.or_eq_true_iff.mpr (Or.inr
            (F_preceq_headInTree (params (count := count)) st hinv _ _ _))
        have hvalid : ∀ Q, parentFG st N.erase = some Q →
            rowsValidForParent (params (count := count)) Q N.erase.slot rs = true := by
          intro Q hQ
          have hs : st.slot (params (count := count)) = s := by
            have hs := fgsa_proposal_slot (c := unitCodec) nd s
            rw [ht] at hs
            exact hs
          change fgBlockOf st Parent.erase = some Q at hQ
          rw [hnamed.2] at hQ
          change rowsValidForParent (params (count := count)) Q s (proposalRows (params (count
            := count)) st H) = true
          rw [proposalRows_eq_proposalRowsFor, ← hs]
          exact proposalRowsFor_valid (params (count := count)) st (st.slot (params (count :=
            count))) H Q hQ
        have hpar : N.erase.parent ∈ st.base.blocks := by
          change Parent.erase ∈ st.base.blocks
          rw [hnamed.2]
          exact getHead_stored (params (count := count)) st hinv _ _
        obtain ⟨_, Q, hQ, hB⟩ := admitBlock_sufficient (params (count := count)) st hinv s N
          hNamed hw
          hpar hslot hfresh hF hvalid
        have hacc : blockAccepted (params (count := count)) st s N Q = true := by
          cases hacc : blockAccepted (params (count := count)) st s N Q with
          | true => rfl
          | false =>
            have hproc := admitBlock_refused (params (count := count)) st s N (Or.inr (Or.inr
              ⟨Q, hQ, hacc⟩))
            change fgBlock Q N.erase N.rows ∈ (admitBlock (params (count := count)) st s
              N).fg.TF at hB
            rw [hproc] at hB
            exact (hmem ⟨_, hB, (fgBlock_root Q N.erase N.rows).trans
              (named_erase_root N)⟩).elim
        obtain ⟨pool, heq, _⟩ := admitBlock_accepted_eq (params (count := count)) st s N Q
          hNamed hQ hacc
        refine ⟨decide_eq_true ⟨_, hB,
          (fgBlock_root Q N.erase N.rows).trans (named_erase_root N)⟩, fun _ => ?_⟩
        change N ∈ (admitBlock (params (count := count)) st s N).namedBodies
        rw [heq]
        dsimp only
        split
        · apply (mem_namedBodies _ N).mpr
          exact Or.inr ⟨s, List.mem_append_right _ (List.mem_singleton_self _)⟩
        · apply (mem_namedBodies _ N).mpr
          right
          refine ⟨s, ?_⟩
          rw [(nvGen_i7_reconcile_fields _).1]
          exact List.mem_append_right _ (List.mem_singleton_self _)

theorem nvGen_w1_proposal_accept (nd : Node (params (count := count))) (v : (Validator (count :=
  count))) (t : Time) (o : Obj (params (count := count)))
    (hr : Reachable (params (count := count)) nd.st)
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) nd v t).2)
    (hw : (fgsa (params (count := count)) unitCodec).wellFormed o = true)
    (b : NamedProposal (params (count := count)).n)
    (hp : o.payload = .proposal b) :
    processedS (params (count := count))
      (FGSA.process (params (count := count)) (FGSA.clock (params (count := count)) nd.st t)
        (toWire (params (count := count)) o)) o = true :=
  ((nvGen_w1_proposal_admit (count := count)) nd v t o hr ho hw b hp).1

theorem nvGen_w1_batch_proposal_complete (t : Time) (w : (World (count := count))) (hu :
  (GenUniformStores (count := count)) w)
    (hr : ∀ v, Reachable (params (count := count)) (w v).st) (o : Obj (params (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) t w).2) (hw : (fgsa (params (count := count))
      unitCodec).wellFormed o = true)
    (b : NamedProposal (params (count := count)).n)
    (hp : o.payload = .proposal b) (v : (Validator (count := count))) :
    processedS (params (count := count)) (((timeBatch (count := count)) t w).1 v).st o = true := by
  have hs := (nvGen_w1_proposal_singleton (count := count)) t w o ho b hp
  obtain ⟨u, he⟩ := ((nvGen_w1_tickBatch_emits (count := count)) t w o).1 ho
  have ha := (nvGen_w1_proposal_accept (count := count)) (w u) u t o (hr u) he hw b hp
  change processedS (params (count := count)) (((((tickBatch (count := count)) t w).2.flatMap
    (fun a => (nodes (count := count)).map (fun u => (u, a)))).foldl ((deliverOne (count :=
      count)) t)
      (((tickBatch (count := count)) t w).1, (nodes (count := count)).map (fun u => .tick u
        t))).1 v).st o = true
  rw [hs, List.flatMap_singleton, nvGen_w1_offer_st t _ o nodes nvGen_nodes_nodup,
    ite_eq_left (nvGen_nodes_complete v), nvGen_w1_tickBatch_st, hu v u]
  exact ha

theorem nvGen_w1_prefix_emits (steps : Nat) (o : Obj (params (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2) :
    ∃ v, (GenEmits (count := count)) V2.D.World.init ((buildPrefix (count := count)) (steps +
      1)).2 v o steps := by
  obtain ⟨v, hv⟩ := (nvGen_tickBatch_origin (count := count)) steps ((buildPrefix (count := count))
    steps).1 o ho
  obtain ⟨ds, he, _⟩ := (nvGen_timeBatch_block (count := count)) steps ((buildPrefix (count :=
    count))
    steps).1
  have hb : (GenEmits (count := count)) ((buildPrefix (count := count)) steps).1
      ((timeBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2 v o steps
        := by
    rw [he]
    exact (nvGen_genEmits_append_left (count := count)) _ _ ds v o steps hv
  refine ⟨v, (nvGen_genEmits_append_right (count := count)) V2.D.World.init ((buildPrefix (count :=
    count)) steps).2 _ v o steps ?_⟩
  rwa [← ((nvGen_prefix_replay_fresh (count := count)) steps).1]

theorem nvGen_w1_batch_complete (P : Obj (params (count := count)) → Prop) (hunique :
  (GenSingleDutyUnique (count := count)) P)
    (t : Time) (w : (World (count := count))) (hu : (GenUniformStores (count := count)) w)
    (hr : ∀ v, Reachable (params (count := count)) (w v).st) (hk : ∀ v, (GenKnown (count :=
      count)) P (w v).st)
    (hP : ∀ o ∈ ((tickBatch (count := count)) t w).2, P o)
    (hwf : ∀ o ∈ ((tickBatch (count := count)) t w).2, (fgsa (params (count := count))
      unitCodec).wellFormed o = true)
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (ho : o ∈ ((tickBatch
      (count := count)) t w).2) :
    processedS (params (count := count)) (((timeBatch (count := count)) t w).1 v).st o = true := by
  classical
  by_cases hp : ∃ a ∈ ((tickBatch (count := count)) t w).2, ∃ b, a.payload = .proposal b
  · obtain ⟨a, ha, b, he⟩ := hp
    have hs := (nvGen_w1_proposal_singleton (count := count)) t w a ha b he
    have hoa : o = a := List.mem_singleton.mp (hs ▸ ho)
    subst o
    exact (nvGen_w1_batch_proposal_complete (count := count)) t w hu hr a ha (hwf a ha) b he v
  · apply (nvGen_w1_batch_nonproposal_complete (count := count)) P hunique t w hk hP _ v o ho
    intro a ha b he
    exact hp ⟨a, ha, b, he⟩

theorem nvGen_w1_prefix_complete (steps : Nat) (v : (Validator (count := count))) (o : Obj (params
  (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2) :
    processedS (params (count := count)) (((buildPrefix (count := count)) (steps + 1)).1 v).st o
      = true := by
  let P := fun a => ∃ u t, (GenEmits (count := count)) V2.D.World.init ((buildPrefix (count :=
    count)) (steps + 1)).2 u a t
  have hk : ∀ u, (GenKnown (count := count)) P (((buildPrefix (count := count)) steps).1 u).st := by
    intro u
    apply (nvGen_gen_known_mono (count := count)) _ P _ (((nvGen_gen_prefix_carried (count :=
      count))
      steps).1 u)
    rintro a ⟨x, t, _, he⟩
    exact ⟨x, t, (nvGen_genEmits_append_left (count := count)) V2.D.World.init ((buildPrefix
      (count :=
      count)) steps).2 _ x a t he⟩
  have hp : ∀ a ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count))
    steps).1).2, P a := by
    intro a ha
    obtain ⟨u, hu⟩ := (nvGen_w1_prefix_emits (count := count)) steps a ha
    exact ⟨u, steps, hu⟩
  have hwf : ∀ a ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2,
      (fgsa (params (count := count)) unitCodec).wellFormed a = true := by
    intro a ha
    obtain ⟨u, hu⟩ := (nvGen_w1_prefix_emits (count := count)) steps a ha
    exact (nvGen_w1_emit_wire (count := count)) steps _ ((nvGen_w1_prefix_schedule (count :=
      count)) steps)
      ((nvGen_prefix_origin (count := count)) (steps + 1))
      ((nvGen_gen_prefix_carried (count := count)) (steps + 1)).2
      (nvGen_prefix_no_restart (steps + 1)) u a steps
        ((nvGen_genEmits_runData (count
        := count)) steps _ u a steps hu)
  exact (nvGen_w1_batch_complete (count := count)) P ((nvGen_w1_emits_unique (count := count)) _
    ((nvGen_prefix_nodup (count := count)) (steps + 1))) steps _
    ((nvGen_w1_prefix_uniform (count := count)) steps) (fun u => by
      rw [(nvGen_prefix_replay_fresh steps).1]
      exact (nvGen_w1_reachable (count := count)) _ u) hk hp hwf v o ho

theorem nvGen_w1_emission_time (es : List (Event (count := count))) (v : (Validator (count :=
  count)))
  (o : Obj (params (count := count))) (t : Time)
    (he : (GenEmits (count := count)) V2.D.World.init es v o t) (d : RunDuty)
    (hD : Gen.V2.Duty.SingleDuty (fgsa (params (count := count)) unitCodec) d.signLabel)
    (j : Fin (RunLabel.seats (params (count := count)) d.signLabel))
    (ha : o.auth = .seat d.signLabel j) : RunDuty.actTime (params (count := count)) d = t := by
  obtain ⟨pre, post, _, ho⟩ := he
  obtain ⟨auth, payload⟩ := o
  dsimp only at ha
  subst auth
  exact ((Gen.V2.Duty.mem_tick_singleDuty_iff (weakEnv (count := count)) ((runData (count :=
    count)) 263 [])
    ((genFold (count := count)) V2.D.World.init pre v) v t d.signLabel hD d rfl j payload).1 ho).2.1

theorem nvGen_w1_not_past (steps : Nat) (v : (Validator (count := count))) (o : Obj (params
  (count :=
  count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
      (((buildPrefix (count := count)) steps).1 v) v steps).2) :
    ¬ (GenPast (count := count)) ((buildPrefix (count := count)) steps).2 steps o := by
  have hh := (nvGen_gen_tick_holder (count := count)) (((buildPrefix (count := count)) steps).1 v) v
    steps o ho
  obtain ⟨d, j, m, rfl, hd, ha⟩ := (nvGen_gen_tick_seat (count := count)) (((buildPrefix (count :=
    count)) steps).1 v) v steps o ho
  have ht := ((fgsa (params (count := count)) unitCodec).duties_spec d steps).1 hd
  rintro ⟨u, t, _, he⟩
  have no_single (hD : Gen.V2.Duty.SingleDuty (fgsa (params (count := count)) unitCodec)
    d.signLabel) : False := by
    have heTime := (nvGen_w1_emission_time (count := count)) _ u _ t he d hD j rfl
    obtain ⟨pre, post, hes, _⟩ := he
    have hm : V2.Event.tick u t ∈ ((buildPrefix (count := count)) steps).2 := by rw [hes]; simp
    have hlt := ((nvGen_witness_prefix_times (count := count)) steps (.tick u t) hm).2
    change t < (steps : Int) at hlt
    exact (lt_irrefl (steps : Int)) ((ht.symm.trans heTime) ▸ hlt)
  cases d with
  | headAction s => exact no_single (fgsa_head_singleDuty s)
  | propAction s => exact no_single (fgsa_prop_singleDuty s)
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count))
      (((buildPrefix (count := count)) steps).1 v).st steps)
      (((buildPrefix (count := count)) steps).1 v).record ⟨0, (params (count :=
        count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    have hu : u = v := by
      obtain ⟨pre, post, _, hem⟩ := he
      have hhu := (nvGen_gen_tick_holder (count := count)) ((genFold (count := count))
        V2.D.World.init
        pre u) u t _ hem
      exact Option.some.inj (hhu.symm.trans hh)
    subst u
    obtain ⟨i, hi, hem⟩ := (nvGen_genEmits_runData (count := count)) 263 ((buildPrefix (count :=
      count)) steps).2 v _ t he
    have hsent := fgsa_row_sent_before (weakEnv (count := count)) ((runData (count := count))
      263 ((buildPrefix (count := count)) steps).2)
      v j body (List.getElem?_eq_some_iff.mp hi).1 t hi hem
    change (body.height_pair, body.finality_pair) ∈
      ((genFold (count := count)) V2.D.World.init (((buildPrefix (count := count)) steps).2.take
        ((buildPrefix (count := count)) steps).2.length) v).record.sent
      at hsent
    rw [List.take_length, ← (nvGen_prefix_replay_fresh steps).1] at hsent
    exact (attest_some_fresh _ _ _ _ hb) hsent

theorem nvGen_w1_clock_processed (st : State (params (count := count)).n) (t : Time) (o : Obj
  (params
  (count := count))) :
    processedS (params (count := count)) (FGSA.clock (params (count := count)) st t) o =
      processedS (params (count := count)) st o := by
  unfold processedS
  rw [nvGen_i7_clock_votes, nvGen_i7_clock_rowPool, clock_fg]

theorem nvGen_w1_known_fold_local (P : (Validator (count := count)) → Obj (params (count :=
  count)) →
  Prop) (w : (World (count := count)))
    (es : List (Event (count := count)))
    (hnr : ∀ v t, V2.Event.restart v t ∉ es) (hk : ∀ v, (GenKnown (count := count)) (P v) (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P v o ∧ ∀ a, carriesS (params (count := count)) o a → P v a) :
    ∀ v, (GenKnown (count := count)) (P v) ((genFold (count := count)) w es v).st := by
  induction es generalizing w with
  | nil => exact hk
  | cons e es ih =>
    apply ih
    · exact fun v t hm => hnr v t (List.mem_cons_of_mem _ hm)
    · intro u
      cases e with
      | restart v t => exact (hnr v t (List.mem_cons_self ..)).elim
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact ((nvGen_i7_tick_st (count := count)) (w v) v t).symm ▸ (nvGen_gen_known_clock
            (count :=
            count)) (P v) _ t (hk v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (nvGen_gen_known_process (count := count)) (P v) _ o (hk v)
            (he v o t (List.mem_cons_self ..)).1 (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

theorem nvGen_w1_batch_known_receipt (steps : Nat) (v : (Validator (count := count))) :
    (GenKnown (count := count)) (fun o => (GenPast (count := count)) ((buildPrefix (count :=
      count)) steps).2 steps o ∨
      V2.Event.deliver v o steps ∈ ((timeBatch (count := count)) steps ((buildPrefix (count :=
        count)) steps).1).2)
      (((timeBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).1 v).st := by
  rw [(nvGen_timeBatch_replay_fresh _ _).1]
  apply (nvGen_w1_known_fold_local (count := count)) (fun u o => (GenPast (count := count))
    ((buildPrefix (count := count)) steps).2 steps o ∨
    V2.Event.deliver u o steps ∈ ((timeBatch (count := count)) steps ((buildPrefix (count :=
      count)) steps).1).2)
  · exact nvGen_timeBatch_no_restart steps (buildPrefix steps).1
  · intro u
    exact (nvGen_gen_known_mono (count := count)) _ _ _ (((nvGen_gen_prefix_carried (count :=
      count))
      steps).1 u) (fun _ h => Or.inl h)
  · intro u o t hm
    obtain ⟨rfl, ho⟩ := (nvGen_gen_timeBatch_delivered (count := count)) steps ((buildPrefix
      (count :=
      count)) steps).1 u o t hm
    refine ⟨Or.inr hm, fun a hc => Or.inl ?_⟩
    exact ((nvGen_gen_tick_fold_known (count := count)) ((GenPast (count := count)) ((buildPrefix
      (count := count)) steps).2 steps) steps (nodes (count := count))
      ((buildPrefix (count := count)) steps).1 [] ((nvGen_gen_prefix_carried (count := count))
        steps).1 (by simp)).2 o ho a hc

theorem nvGen_w1_nonproposal_receipt (steps : Nat) (v : (Validator (count := count))) (o : Obj
  (params
  (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2)
    (hnot : ∀ b, o.payload ≠ .proposal b) :
    V2.Event.deliver v o steps ∈ ((timeBatch (count := count)) steps ((buildPrefix (count :=
      count)) steps).1).2 := by
  have hp := (nvGen_w1_prefix_complete (count := count)) steps v o ho
  have hk := (nvGen_w1_batch_known_receipt (count := count)) steps v
  obtain ⟨u, hu⟩ := ((nvGen_w1_tickBatch_emits (count := count)) steps ((buildPrefix (count :=
    count))
    steps).1 o).1 ho
  have hn := (nvGen_w1_not_past (count := count)) steps u o hu
  obtain ⟨l, j, m, rfl, _, ha⟩ := (nvGen_gen_tick_seat (count := count)) (((buildPrefix (count :=
    count)) steps).1 u) u steps o hu
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have he : .head (headVote (params (count := count))
        (FGSA.clock (params (count := count)) (((buildPrefix (count := count)) steps).1 u).st
          steps) s).root = m := Option.some.inj ha
    subst m
    have hm := of_decide_eq_true hp
    have hh := hk.2.2 _ (List.mem_filterMap.mpr ⟨_, hm, rfl⟩)
    exact hh.resolve_left hn
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count))
      (((buildPrefix (count := count)) steps).1 u).st steps)
        (((buildPrefix (count := count)) steps).1 u).record ⟨0, (params (count :=
          count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact (hk.1 _ (of_decide_eq_true hp)).resolve_left hn
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    change (propose (params (count := count)) (FGSA.clock (params (count := count))
      (((buildPrefix (count := count)) steps).1 u).st steps) s).map
      (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact (hnot _ rfl).elim

theorem nvGen_w1_fold_no_local (w : (World (count := count))) (es : List (Event (count :=
  count))) (v
  : (Validator (count := count))) (o : Obj (params (count := count)))
    (hd : ∀ a t, V2.Event.deliver v a t ∉ es)
    (hr : ∀ t, V2.Event.restart v t ∉ es) :
    processedS (params (count := count)) ((genFold (count := count)) w es v).st o = processedS
      (params (count := count)) (w v).st o := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    rw [show genFold w (e :: es) =
      genFold (V2.D.World.step weakEnv (runData 263 []) w e) es from rfl,
      ih _ (fun a t hm => hd a t (List.mem_cons_of_mem _ hm))
        (fun t hm => hr t (List.mem_cons_of_mem _ hm))]
    cases e with
    | restart u t =>
      have hne : v ≠ u := by intro he; subst u; exact hr t (List.mem_cons_self ..)
      simp only [V2.D.World.step, Function.update_of_ne hne]
    | deliver u a t =>
      have hne : v ≠ u := by intro he; subst u; exact hd a t (List.mem_cons_self ..)
      simp only [V2.D.World.step, Function.update_of_ne hne]
    | tick u t =>
      by_cases he : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact ((nvGen_i7_tick_st (count := count)) (w v) v t).symm ▸ (nvGen_w1_clock_processed
          (count :=
          count)) (w v).st t o
      · simp only [V2.D.World.step, Function.update_of_ne he]

theorem nvGen_w1_prefix_tick_zero (steps : Nat) :
    ((buildPrefix (count := count)) (steps + 1)).2[((buildPrefix (count := count))
      steps).2.length]? = some (.tick 0 steps) ∧
      (genFold (count := count)) V2.D.World.init
        (((buildPrefix (count := count)) (steps + 1)).2.take ((buildPrefix (count := count))
          steps).2.length) =
          ((buildPrefix (count := count)) steps).1 := by
  obtain ⟨ds, he, _⟩ := (nvGen_timeBatch_block (count := count)) steps ((buildPrefix (count :=
    count))
    steps).1
  change (((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
    ((buildPrefix (count := count)) steps).1).2)[
    ((buildPrefix (count := count)) steps).2.length]? = _ ∧ _
  constructor
  · rw [he]
    simp [nodes, List.finRange, NeZero.pos count]
  · change (genFold (count := count)) V2.D.World.init
      ((((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
        ((buildPrefix (count := count)) steps).1).2).take
        ((buildPrefix (count := count)) steps).2.length) = _
    rw [List.take_append_length]
    exact ((nvGen_prefix_replay_fresh (count := count)) steps).1.symm

private theorem nvGen_w1_stored_digest (st : State (params (count := count)).n) (hr : Reachable
  (params (count := count)) st)
    (Y : SimplexFG.FGBlock (Fin (params (count := count)).n)) (hY : Y ∈ st.fg.TF) :
    Y = .genesis ∨ Y.root = ⟨Y.slot + 1⟩ := by
  by_cases hg : Y = .genesis
  · exact Or.inl hg
  · right
    have hs := storeBundle_of_reachable (params (count := count)) st hr
    obtain ⟨s, N, hw, hErase, _⟩ := stored_wire_of_block (params (count := count)) st hs.cstore
      hs.«meta» hY hg
    obtain ⟨s', M, he, hc, _⟩ := hs.«meta».wireTree _ hw
    have hp := Msg.proposal.inj (congrArg (fun w : Wire (params (count := count)).n =>
      w.payload) he)
    cases hp
    unfold namedContentOk at hc
    rw [hErase] at hc
    have hd := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2
    dsimp only [params, proposalInput] at hd
    exact (eraseFG_root Y).symm.trans
      (hd.trans (congrArg (fun r : Nat => (⟨r + 1⟩ : BlockId)) (eraseFG_slot Y)))

theorem nvGen_w1_proposal_fresh_start (steps : Nat) (v : (Validator (count := count))) (o : Obj
  (params (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2)
      (b : NamedProposal (params (count := count)).n)
    (hp : o.payload = .proposal b) :
    processedS (params (count := count)) (((buildPrefix (count := count)) steps).1 v).st o =
      false := by
  obtain ⟨u, hu⟩ := ((nvGen_w1_tickBatch_emits (count := count)) steps ((buildPrefix (count :=
    count))
    steps).1 o).1 ho
  have hu0 := ((nvGen_gen_tick_proposal_rows (count := count)) (((buildPrefix (count := count))
    steps).1 u) u steps o hu b hp).1
  subst u
  obtain ⟨l, j, m, rfl, hl, ha⟩ := (nvGen_gen_tick_seat (count := count)) (((buildPrefix (count :=
    count)) steps).1 0) 0 steps o hu
  cases l with
  | headAction s =>
    have ha := nvGen_head_action (c := unitCodec) (x := ()) ha
    have he : .head (headVote (params (count := count))
        (FGSA.clock (params (count := count)) (((buildPrefix (count := count)) steps).1 0).st
          steps) s).root = m := Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest (params (count := count)) (FGSA.clock (params (count := count))
      (((buildPrefix (count := count)) steps).1 0).st steps)
        (((buildPrefix (count := count)) steps).1 0).record ⟨0, (params (count :=
          count)).nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s =>
    have ha := nvGen_proposal_action (c := unitCodec) (x := ()) ha
    have ht : SA.proposalTime (params (count := count)).toParams s = steps :=
      ((fgsa (params (count := count)) unitCodec).duties_spec (.propAction s) steps).1 hl
    have hs0 : 0 < s := by
      by_contra hn
      have hz : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      cases ha
    have hi := ((nvGen_w1_prefix_tick_zero (count := count)) steps).1
    rw [← ht] at hi
    have hb := (fgsa_stored_block_slots (weakEnv (count := count))
      ((runData (count := count)) steps ((buildPrefix (count := count)) (steps + 1)).2)
        ((nvGen_w1_prefix_schedule (count := count)) steps) hi hs0).2.2.1
    change ∀ B ∈ ((genFold (count := count)) V2.D.World.init
      (((buildPrefix (count := count)) (steps + 1)).2.take ((buildPrefix (count := count))
        steps).2.length) 0).st.fg.TF, B.slot < s at hb
    rw [(nvGen_w1_prefix_tick_zero steps).2] at hb
    change (propose (params (count := count)) (FGSA.clock (params (count := count))
      (((buildPrefix (count := count)) steps).1 0).st steps) s).map
      (withApp (params (count := count)) 0) = some m at ha
    unfold propose at ha
    rw [ite_eq_right (Nat.ne_of_gt hs0)] at ha
    simp only [Option.map_map] at ha
    obtain ⟨Parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
    cases hp
    change decide (∃ Y ∈ (((buildPrefix (count := count)) steps).1 v).st.fg.TF,
      Y.root = (⟨s + 1⟩ : BlockId)) = false
    apply decide_eq_false
    rintro ⟨Y, hY, he⟩
    rw [nvGen_w1_prefix_uniform steps v 0] at hY
    have hslot := hb Y hY
    have hr : Reachable (params (count := count)) (((buildPrefix (count := count)) steps).1
      0).st := by
      rw [(nvGen_prefix_replay_fresh steps).1]
      exact (nvGen_w1_reachable (count := count)) _ 0
    rcases (nvGen_w1_stored_digest (count := count)) _ hr Y hY with hg | hd
    · subst Y
      have hz := congrArg BlockId.value he
      change 0 = s + 1 at hz
      exact Nat.noConfusion hz
    · have hs := congrArg BlockId.value (hd.symm.trans he)
      change Y.slot + 1 = s + 1 at hs
      exact (Nat.lt_irrefl s) ((Nat.add_right_cancel hs) ▸ hslot)

theorem nvGen_w1_proposal_receipt (steps : Nat) (v : (Validator (count := count))) (o : Obj (params
  (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2)
      (b : NamedProposal (params (count := count)).n)
    (hp : o.payload = .proposal b) :
    V2.Event.deliver v o steps ∈ ((timeBatch (count := count)) steps ((buildPrefix (count :=
      count)) steps).1).2 := by
  by_contra hn
  have hs := (nvGen_w1_proposal_singleton (count := count)) steps ((buildPrefix (count := count))
    steps).1 o ho b hp
  have hd : ∀ a t, V2.Event.deliver v a t ∉ ((timeBatch (count := count)) steps ((buildPrefix
    (count := count)) steps).1).2 := by
    intro a t hm
    obtain ⟨rfl, ha⟩ := (nvGen_gen_timeBatch_delivered (count := count)) steps ((buildPrefix
      (count :=
      count)) steps).1 v a t hm
    have he : a = o := List.mem_singleton.mp (hs ▸ ha)
    exact hn (he ▸ hm)
  have he := (nvGen_w1_fold_no_local (count := count)) ((buildPrefix (count := count)) steps).1
    ((timeBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2 v o hd
    ((nvGen_timeBatch_no_restart (count := count)) steps ((buildPrefix (count := count)) steps).1 v)
  rw [← (nvGen_timeBatch_replay_fresh _ _).1, nvGen_w1_proposal_fresh_start steps v o ho b hp]
    at he
  have ht := (nvGen_w1_prefix_complete (count := count)) steps v o ho
  exact Bool.noConfusion (ht.symm.trans he)

theorem nvGen_w1_batch_receipt (steps : Nat) (v : (Validator (count := count))) (o : Obj (params
  (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) steps ((buildPrefix (count := count)) steps).1).2) :
    V2.Event.deliver v o steps ∈ ((timeBatch (count := count)) steps ((buildPrefix (count :=
      count)) steps).1).2 := by
  classical
  by_cases hp : ∃ b, o.payload = .proposal b
  · obtain ⟨b, hp⟩ := hp
    exact (nvGen_w1_proposal_receipt (count := count)) steps v o ho b hp
  · exact (nvGen_w1_nonproposal_receipt (count := count)) steps v o ho (fun b he => hp ⟨b, he⟩)

theorem nvGen_genFold_other (w : (World (count := count))) (es : List (Event (count := count))) (v :
  (Validator (count := count)))
    (hn : ∀ e ∈ es, e.node ≠ v) : (genFold (count := count)) w es v = w v := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
      change (genFold (count := count)) (V2.D.World.step (weakEnv (count := count)) ((runData
        (count := count)) 263 []) w e) es v = w v
      rw [ih _ (fun e he => hn e (List.mem_cons_of_mem _ he))]
      have he := hn e List.mem_cons_self
      cases e with
      | restart u t =>
          change u ≠ v at he
          exact Function.update_of_ne (Ne.symm he) _ _
      | tick u t =>
          change u ≠ v at he
          exact Function.update_of_ne (Ne.symm he) _ _
      | deliver u o t =>
          change u ≠ v at he
          exact Function.update_of_ne (Ne.symm he) _ _

theorem nvGen_w1_batch_tick_state (t : Time) (w : (World (count := count))) (i : Nat) (v :
  (Validator
  (count := count))) (u : Time)
    (he : ((timeBatch (count := count)) t w).2[i]? = some (.tick v u)) :
    u = t ∧ (genFold (count := count)) w (((timeBatch (count := count)) t w).2.take i) v = w v := by
  have hut : u = t := (nvGen_timeBatch_time (count := count)) t w (.tick v u)
    (List.mem_of_getElem? he)
  subst u
  obtain ⟨ds, hes, _⟩ := (nvGen_timeBatch_block (count := count)) t w
  have hlen : v.val < ((nodes (count := count)).map (fun v => (V2.Event.tick v t : (Event (count
    := count))))).length := by
    simpa only [List.length_map, nodes, List.length_finRange] using v.isLt
  have hv : ((timeBatch (count := count)) t w).2[v.val]? = some (.tick v t) := by
    rw [hes, List.getElem?_append_left hlen, List.getElem?_eq_getElem hlen]
    simp only [List.getElem_map, nodes, List.getElem_finRange]
    rfl
  have hi : i = v.val :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp he).1 ((nvGen_timeBatch_nodup (count :=
      count)) t w)).1
      (he.trans hv.symm)
  subst i
  refine ⟨rfl, ?_⟩
  rw [hes, List.take_append_of_le_length hlen.le]
  apply (nvGen_genFold_other (count := count))
  intro e hm hnode
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hm
  have hval := congrArg (fun e : (Event (count := count)) => e.node.val) he
  simp only [List.getElem_map, nodes, List.getElem_finRange] at hval
  change j = e.node.val at hval
  rw [hnode] at hval
  exact Nat.ne_of_lt (lt_of_lt_of_le hj (min_le_left _ _)) hval

theorem nvGen_w1_locate_emission (steps : Nat) (i : Nat) (v : (Validator (count := count))) (t :
  Time)
    (o : Obj (params (count := count))) (hi : ((buildPrefix (count := count)) steps).2[i]? =
      some (.tick v t))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
      ((genFold (count := count)) V2.D.World.init (((buildPrefix (count := count)) steps).2.take
        i) v) v t).2) :
    ∃ n < steps, t = n ∧ o ∈ ((tickBatch (count := count)) n ((buildPrefix (count := count))
      n).1).2 := by
  induction steps generalizing i with
  | zero => simp [buildPrefix] at hi
  | succ steps ih =>
    change (((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
      ((buildPrefix (count := count)) steps).1).2)[i]? = _ at hi
    change o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 [])
      ((genFold (count := count)) V2.D.World.init
      ((((buildPrefix (count := count)) steps).2 ++ ((timeBatch (count := count)) steps
        ((buildPrefix (count := count)) steps).1).2).take i) v) v t).2 at ho
    by_cases hil : i < ((buildPrefix (count := count)) steps).2.length
    · rw [List.getElem?_append_left hil] at hi
      rw [List.take_append_of_le_length (Nat.le_of_lt hil)] at ho
      obtain ⟨n, hn, ht, hm⟩ := ih i hi ho
      exact ⟨n, Nat.lt_succ_of_lt hn, ht, hm⟩
    · have hil' := Nat.le_of_not_lt hil
      rw [List.getElem?_append_right hil'] at hi
      rw [List.take_append, List.take_of_length_le hil', nvGen_genFold_append,
        ← (nvGen_prefix_replay_fresh steps).1] at ho
      obtain ⟨rfl, hs⟩ := (nvGen_w1_batch_tick_state (count := count)) steps ((buildPrefix (count :=
        count)) steps).1 _ v t hi
      rw [hs] at ho
      exact ⟨steps, Nat.lt_succ_self _, rfl, ((nvGen_w1_tickBatch_emits (count := count)) _ _
        o).2 ⟨v,
        ho⟩⟩

theorem nvGen_w1_prefix_broadcast (steps : Nat) (v : (Validator (count := count))) (o : Obj (params
  (count := count))) (t : Time)
    (he : V2.D.Run.emits (weakEnv (count := count)) ((runData (count := count)) steps
      ((buildPrefix (count := count)) (steps + 1)).2) v o t)
    (u : (Validator (count := count))) :
    V2.Event.deliver u o t ∈ ((buildPrefix (count := count)) (steps + 1)).2 := by
  obtain ⟨i, hi, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, rfl, hm⟩ := (nvGen_w1_locate_emission (count := count)) (steps + 1) i v t o hi ho
  rw [nvGen_prefix_blocks]
  exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, (nvGen_w1_batch_receipt (count :=
    count)) n u
    o hm⟩

theorem nvGen_w1_fold_stable (w : (World (count := count))) (es : List (Event (count := count)))
  (v :
  (Validator (count := count))) (o : Obj (params (count := count)))
    (hr : ∀ u t, V2.Event.restart u t ∉ es)
    (hp : processedS (params (count := count)) (w v).st o = true) :
    processedS (params (count := count)) ((genFold (count := count)) w es v).st o = true := by
  induction es generalizing w with
  | nil => exact hp
  | cons e es ih =>
    apply ih _ (fun u t hm => hr u t (List.mem_cons_of_mem _ hm))
    cases e with
    | restart u t => exact (hr u t (List.mem_cons_self ..)).elim
    | tick u t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        have he : processedS (params (count := count)) (FGSA.clock (params (count := count)) (w
          v).st t) o = true := by
          rw [nvGen_w1_clock_processed]
          exact hp
        exact ((nvGen_i7_tick_st (count := count)) (w v) v t).symm ▸ he
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hp
    | deliver u a t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact (nvGen_w1_process_processed (count := count)) _ _ _ hp
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hp

theorem nvGen_w1_prefix_prefix (m n : Nat) (h : m ≤ n) :
    ((buildPrefix (count := count)) m).2.IsPrefix ((buildPrefix (count := count)) n).2 := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact List.prefix_refl _
  | succ n ih =>
    by_cases he : m = n + 1
    · subst m; exact List.prefix_refl _
    · exact (ih (by omega)).trans ⟨((timeBatch (count := count)) n ((buildPrefix (count :=
      count)) n).1).2, rfl⟩

theorem nvGen_w1_prefix_stable (m n : Nat) (hmn : m ≤ n) (v : (Validator (count := count))) (o : Obj
  (params (count := count)))
    (hp : processedS (params (count := count)) (((buildPrefix (count := count)) m).1 v).st o =
      true) :
    processedS (params (count := count)) (((buildPrefix (count := count)) n).1 v).st o = true := by
  obtain ⟨ds, he⟩ := (nvGen_w1_prefix_prefix (count := count)) m n hmn
  rw [(nvGen_prefix_replay_fresh n).1, ← he, nvGen_genFold_append, ← (nvGen_prefix_replay_fresh
    m).1]
  apply (nvGen_w1_fold_stable (count := count)) _ ds v o _ hp
  intro u t hm
  apply (nvGen_prefix_no_restart (count := count)) n u t
  rw [← he]
  exact List.mem_append_right _ hm

theorem nvGen_w1_past_complete (steps : Nat) (o : Obj (params (count := count))) (t : Time)
    (he : (GenPast (count := count)) ((buildPrefix (count := count)) steps).2 t o) (v :
      (Validator (count := count))) :
    processedS (params (count := count)) (((buildPrefix (count := count)) steps).1 v).st o =
      true := by
  obtain ⟨u, s, _, he⟩ := he
  obtain ⟨i, hi, ho⟩ := (nvGen_genEmits_runData (count := count)) 263 _ u o s he
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, _, hm⟩ := (nvGen_w1_locate_emission (count := count)) steps i u s o hi ho
  exact (nvGen_w1_prefix_stable (count := count)) (n + 1) steps hn v o
    ((nvGen_w1_prefix_complete (count :=
    count)) n v o hm)

theorem nvGen_w1_index_after (steps m i : Nat) (hm : m ≤ steps) (e : (Event (count := count)))
    (hi : ((buildPrefix (count := count)) steps).2[i]? = some e) (ht : (m : Int) ≤ e.time) :
    ((buildPrefix (count := count)) m).2.length ≤ i := by
  obtain ⟨ds, he⟩ := (nvGen_w1_prefix_prefix (count := count)) m steps hm
  by_contra hn
  have hl : i < ((buildPrefix (count := count)) m).2.length := Nat.lt_of_not_ge hn
  rw [← he, List.getElem?_append_left hl] at hi
  exact (not_lt.mpr ht) ((nvGen_witness_prefix_times (count := count)) m e (List.mem_of_getElem?
    hi)).2

theorem nvGen_w1_index_stable (steps m i : Nat) (hm : m ≤ steps)
    (hi : ((buildPrefix (count := count)) m).2.length ≤ i) (v : (Validator (count := count))) (o
      : Obj (params (count := count)))
    (hp : processedS (params (count := count)) (((buildPrefix (count := count)) m).1 v).st o =
      true) :
    processedS (params (count := count)) ((genFold (count := count)) V2.D.World.init
      (((buildPrefix (count := count)) steps).2.take i) v).st o = true := by
  obtain ⟨ds, he⟩ := (nvGen_w1_prefix_prefix (count := count)) m steps hm
  rw [← he, List.take_append, List.take_of_length_le hi, nvGen_genFold_append,
    ← (nvGen_prefix_replay_fresh m).1]
  apply (nvGen_w1_fold_stable (count := count)) _ _ v o _ hp
  intro u t hmem
  apply (nvGen_prefix_no_restart (count := count)) steps u t
  rw [← he]
  exact List.mem_append_right _ (List.mem_of_mem_take hmem)

theorem nvGen_w1_handles_carries (st : State (params (count := count)).n) (a o : Obj (params
  (count :=
  count)))
    (hh : handlesS (params (count := count)) st a o) : a = o ∨ carriesS (params (count :=
      count)) a o := by
  rcases hh with he | hh
  · exact Or.inl he
  · generalize hd : (toWire (params (count := count)) a).decode = d at hh
    cases d with
    | none => exact hh.elim
    | some m =>
      cases m with
      | vote s i b => exact hh.elim
      | row i body => exact hh.elim
      | block s b =>
        have he := (nvGen_i7_decode_proposal (count := count)) a s b hd
        right
        simp only [carriesS, he]
        exact hh.2.elim Or.inl (fun hm => Or.inr (Or.inr hm))

theorem nvGen_w1_child_processed (steps i : Nat) (v u : (Validator (count := count))) (a o : Obj
  (params (count := count))) (t : Time)
    (hi : ((buildPrefix (count := count)) steps).2[i]? = some (.deliver v a t))
    (hc : carriesS (params (count := count)) a o) :
    processedS (params (count := count))
      ((genFold (count := count)) V2.D.World.init (((buildPrefix (count := count)) steps).2.take
        (i + 1)) u).st o = true := by
  have hm := List.mem_of_getElem? hi
  rw [nvGen_prefix_blocks] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < steps := List.mem_range.mp hn
  obtain ⟨rfl, ha⟩ := (nvGen_gen_timeBatch_delivered (count := count)) n ((buildPrefix (count :=
    count)) n).1 v a t hm
  have hp : (GenPast (count := count)) ((buildPrefix (count := count)) n).2 n o :=
    ((nvGen_gen_tick_fold_known (count := count)) ((GenPast (count := count)) ((buildPrefix
      (count :=
      count)) n).2 n) n (nodes (count := count)) ((buildPrefix (count := count)) n).1 []
      ((nvGen_gen_prefix_carried (count := count)) n).1 (by simp)).2 a ha o hc
  apply (nvGen_w1_index_stable (count := count)) steps n (i + 1) (Nat.le_of_lt hn')
  · exact ((nvGen_w1_index_after (count := count)) steps n i (Nat.le_of_lt hn') _ hi le_rfl).trans
      (Nat.le_succ i)
  · exact (nvGen_w1_past_complete (count := count)) n o n hp u

theorem nvGen_w1_prefix_relay (steps i : Nat) (v u : (Validator (count := count))) (a o : Obj
  (params
  (count := count))) (t : Time)
    (hi : ((buildPrefix (count := count)) (steps + 1)).2[i]? = some (.deliver v a t))
    (hh : a = o ∨ carriesS (params (count := count)) a o)
    (hp : processedS (params (count := count))
      ((genFold (count := count)) V2.D.World.init (((buildPrefix (count := count)) (steps +
        1)).2.take (i + 1)) u).st o = false) :
    V2.Event.deliver u o t ∈ ((buildPrefix (count := count)) (steps + 1)).2 := by
  rcases hh with rfl | hc
  · obtain ⟨x, hx⟩ := (nvGen_prefix_origin (count := count)) (steps + 1) v a t
      (List.mem_of_getElem? hi)
    exact (nvGen_w1_prefix_broadcast (count := count)) steps x a t ((nvGen_genEmits_runData
      (count :=
      count)) steps _ x a t hx) u
  · have ht := (nvGen_w1_child_processed (count := count)) (steps + 1) i v u a o t hi hc
    exact Bool.noConfusion (hp.symm.trans ht)

theorem nvGen_w1_direct_handle (E : Generic.Env (Validator (count := count))) (h : Time) (es : List
  (Event (count := count)))
    (v : (Validator (count := count))) (o : Obj (params (count := count))) (t : Time) (hm :
      V2.Event.deliver v o t ∈ es) :
    ∃ i, V2.D.Run.handlesAt E ((runData (count := count)) h es) i v o t := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨i, o, hi, Or.inl rfl⟩

/-- The generated batch supplies every later delivery anchor from its real receipt. -/
theorem nvGen_w1_service (steps : Nat) (v w : Validator (count := count))
    (o : Obj (params (count := count))) (t a d : Time)
    (he : V2.D.Run.emits weakEnv (runData steps (buildPrefix (steps + 1)).2) v o t)
    (hta : t ≤ a) (had : a < d) :
    V2.D.DeliveryService weakEnv (runData steps (buildPrefix (steps + 1)).2) w o a d := by
  obtain ⟨i, hi, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, rfl, hm⟩ := nvGen_w1_locate_emission (steps + 1) i v t o hi ho
  rcases hta.eq_or_lt with rfl | hlt
  · right
    exact ⟨n, le_rfl, had, nvGen_w1_direct_handle weakEnv _ _ w o n
      (nvGen_w1_prefix_broadcast steps v o n ⟨i, hi, by
        rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2]
        exact ho⟩ w)⟩
  · left
    refine ⟨(buildPrefix (count := count) (n + 1)).2.length, ?_, ?_⟩
    · have hp := (nvGen_w1_prefix_prefix (count := count) (n + 1) (steps + 1) hn).sublist.filter
        (fun e => decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))
      have hfilter : ((buildPrefix (count := count) (n + 1)).2.filter
          (fun e => decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))) =
          (buildPrefix (count := count) (n + 1)).2 := by
        apply List.filter_eq_self.mpr
        intro e he
        have ht := (nvGen_witness_prefix_times (n + 1) e he).2
        exact decide_eq_true (Or.inl (lt_of_le_of_lt (by
          change e.time < (n + 1 : Nat) at ht
          simp only [Time] at *
          omega) hlt))
      rw [hfilter] at hp
      exact hp.length_le
    · rw [nvGen_runData_stateBefore]
      have hp := nvGen_w1_prefix_prefix (count := count) (n + 1) (steps + 1) hn
      obtain ⟨ds, hd⟩ := hp
      rw [← hd, List.take_append_length, ← (nvGen_prefix_replay_fresh (n + 1)).1]
      exact nvGen_w1_prefix_complete n w o hm

theorem nvGen_w1_prefix_sync (steps : Nat) :
    V2.D.PartialSynchrony (weakEnv (count := count))
      (runData steps (buildPrefix (steps + 1)).2) where
  broadcast_emitted := by
    intro v _ o t he w _ a hta _ had _ _ _ _
    exact nvGen_w1_service steps v w o t a _ he hta had
  relay_accepted := by
    intro v _ i o t ha w _ a hta _ had _ _ _ _
    obtain ⟨obj, hi, hh⟩ := ha.1
    rcases nvGen_w1_handles_carries _ obj o hh with rfl | hc
    · obtain ⟨u, hu⟩ := nvGen_prefix_origin (steps + 1) v obj t (List.mem_of_getElem? hi)
      exact nvGen_w1_service steps u w obj t a _
        (nvGen_genEmits_runData steps _ u obj t hu) hta had
    · obtain ⟨u, send, hsend, hem⟩ :=
        (nvGen_gen_prefix_carried (steps + 1)).2 v obj t (List.mem_of_getElem? hi) o hc
      exact nvGen_w1_service steps u w o send a _
        (nvGen_genEmits_runData steps _ u o send hem) (hsend.trans hta) had

private theorem nvGen_w1_fold_blocks (w : (World (count := count))) (es : List (Event (count :=
  count))) (v : (Validator (count := count)))
    (hr : ∀ u t, V2.Event.restart u t ∈ es → False) (B : NamedProposal (params (count := count)).n)
    (hB : B ∈ (w v).st.namedBodies) : B ∈ ((genFold (count := count)) w es v).st.namedBodies := by
  induction es generalizing w with
  | nil => exact hB
  | cons e es ih =>
    apply ih _ (fun u t hm => hr u t (List.mem_cons_of_mem _ hm))
    cases e with
    | restart u t => exact (hr u t (List.mem_cons_self ..)).elim
    | tick u t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        have he := congrArg State.namedBodies
          ((nvGen_i7_tick_st (count := count)) (w v) v t)
        change (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) (w v) v
          t).1.st.namedBodies = _ at he
        rw [he, clock_namedBodies]
        exact hB
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hB
    | deliver u o t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact process_namedBodies_subset _ _ hB
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hB

private theorem nvGen_w1_prefix_blocks_mono (m n : Nat) (hmn : m ≤ n) (v : (Validator (count :=
  count)))
    (B : NamedProposal (params (count := count)).n) (hB : B ∈ (((buildPrefix (count := count))
      m).1 v).st.namedBodies) :
    B ∈ (((buildPrefix (count := count)) n).1 v).st.namedBodies := by
  obtain ⟨ds, he⟩ := (nvGen_w1_prefix_prefix (count := count)) m n hmn
  rw [(nvGen_prefix_replay_fresh n).1, ← he, nvGen_genFold_append, ← (nvGen_prefix_replay_fresh
    m).1]
  apply (nvGen_w1_fold_blocks (count := count)) _ ds v _ B hB
  intro u t hm
  apply (nvGen_prefix_no_restart (count := count)) n u t
  rw [← he]
  exact List.mem_append_right _ hm

private theorem nvGen_w1_prefix_body (n : Nat) (o : Obj (params (count := count)))
    (ho : o ∈ ((tickBatch (count := count)) n ((buildPrefix (count := count)) n).1).2) (B :
      NamedProposal (params (count := count)).n)
    (hp : o.payload = .proposal B) :
    B ∈ (((buildPrefix (count := count)) (n + 1)).1 0).st.namedBodies := by
  obtain ⟨u, hu⟩ := ((nvGen_w1_tickBatch_emits (count := count)) n ((buildPrefix (count := count))
    n).1 o).1 ho
  have hr : Reachable (params (count := count)) (((buildPrefix (count := count)) n).1 u).st := by
    rw [(nvGen_prefix_replay_fresh n).1]
    exact (nvGen_w1_reachable (count := count)) _ u
  obtain ⟨x, hx⟩ := (nvGen_w1_prefix_emits (count := count)) n o ho
  have hw := (nvGen_w1_emit_wire (count := count)) n _ ((nvGen_w1_prefix_schedule (count :=
    count)) n)
    ((nvGen_prefix_origin (count := count)) (n + 1))
    ((nvGen_gen_prefix_carried (count := count)) (n + 1)).2
    (nvGen_prefix_no_restart (n + 1)) x o n ((nvGen_genEmits_runData
      (count := count))
      n _ x o n hx)
  have hb := ((nvGen_w1_proposal_admit (count := count)) _ u n o hr hu hw B hp).2
    ((nvGen_w1_proposal_fresh_start (count := count)) n u o ho B hp)
  have hs := (nvGen_w1_proposal_singleton (count := count)) n ((buildPrefix (count := count)) n).1 o
    ho B hp
  change B ∈ (((((tickBatch (count := count)) n ((buildPrefix (count := count)) n).1).2.flatMap
    (fun a => (nodes (count := count)).map (fun v => (v, a)))).foldl ((deliverOne (count :=
      count)) n)
      (((tickBatch (count := count)) n ((buildPrefix (count := count)) n).1).1, (nodes (count :=
        count)).map (fun v => .tick v n))).1 0).st.namedBodies
  rw [hs, List.flatMap_singleton, nvGen_w1_offer_st n _ o nodes nvGen_nodes_nodup,
    ite_eq_left (nvGen_nodes_complete 0), nvGen_w1_tickBatch_st, nvGen_w1_prefix_uniform n 0 u]
  exact hb

private def w1_finalStore (steps : Nat) : State (params (count := count)).n := (((buildPrefix
  (count := count)) steps).1 0).st

private def w1_rootTable (steps : Nat) : List (NamedProposal (params (count := count)).n) :=
  ((w1_finalStore (count := count)) steps).namedBodies

private theorem nvGen_w1_tableInv (steps : Nat) : CStoreInv (params (count := count))
  ((w1_finalStore
  (count := count)) steps) := by
  apply (storeBundle_of_reachable (params (count := count)) _ _).cstore
  change Reachable (params (count := count)) (((buildPrefix (count := count)) steps).1 0).st
  rw [(nvGen_prefix_replay_fresh steps).1]
  exact (nvGen_w1_reachable (count := count)) _ 0

private theorem nvGen_w1_tableMeta (steps : Nat) : MetaInv (params (count := count)) ((w1_finalStore
  (count := count)) steps) := by
  apply metadataInvariant
  change Reachable (params (count := count)) (((buildPrefix (count := count)) steps).1 0).st
  rw [(nvGen_prefix_replay_fresh steps).1]
  exact (nvGen_w1_reachable (count := count)) _ 0

private theorem nvGen_w1_ancestorTable (steps : Nat) (B : NamedProposal (params (count := count)).n)
    (hB : B ∈ (w1_rootTable (count := count)) steps) (A : NamedProposal (params (count := count)).n)
    (hA : NamedProposal.Preceq A B) : A ∈ (w1_rootTable (count := count)) steps := by
  induction B with
  | genesis =>
    have he : A = .genesis := by
      simpa [NamedProposal.Preceq, NamedProposal.preceq] using hA
    exact he ▸ hB
  | node P slot root body raw sup rows ih =>
    rcases Bool.or_eq_true_iff.mp hA with he | hp
    · exact (of_decide_eq_true he) ▸ hB
    · exact ih (namedBodies_parent (params (count := count)) _ ((nvGen_w1_tableMeta (count :=
        count))
      steps) hB) hp

private theorem nvGen_w1_deliveredTable (steps : Nat) (v : (Validator (count := count))) (o : Obj
  (params (count := count))) (t : Time)
    (hd : V2.Event.deliver v o t ∈ ((buildPrefix (count := count)) steps).2) (B : NamedProposal
      (params (count := count)).n)
    (hp : o.payload = .proposal B) : B ∈ (w1_rootTable (count := count)) steps := by
  obtain ⟨u, hu⟩ := (nvGen_prefix_origin (count := count)) steps v o t hd
  obtain ⟨i, hi, ho⟩ := (nvGen_genEmits_runData (count := count)) 263 _ u o t hu
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, rfl, hm⟩ := (nvGen_w1_locate_emission (count := count)) steps i u t o hi ho
  exact (nvGen_w1_prefix_blocks_mono (count := count)) (n + 1) steps hn 0 B
    ((nvGen_w1_prefix_body (count :=
    count)) n o hm B hp)

private theorem nvGen_w1_storedTable (steps : Nat) (h : Time) (i : Nat) (v : (Validator (count
  := count)))
    (B : NamedProposal (params (count := count)).n)
    (hB : B ∈ (V2.D.Run.stateBefore (weakEnv (count := count)) ((runData (count := count)) h
      ((buildPrefix (count := count)) steps).2) i v).st.namedBodies) :
    B ∈ (w1_rootTable (count := count)) steps := by
  rw [nvGen_runData_stateBefore] at hB
  have hm := (nvGen_w1_fold_blocks (count := count)) ((genFold (count := count)) V2.D.World.init
    (((buildPrefix (count := count)) steps).2.take i))
    (((buildPrefix (count := count)) steps).2.drop i) v
    (fun u t he => (nvGen_prefix_no_restart (count := count)) steps u t (List.mem_of_mem_drop
      he)) B hB
  rw [← nvGen_genFold_append, List.take_append_drop, ← (nvGen_prefix_replay_fresh steps).1] at hm
  rwa [(nvGen_w1_prefix_uniform (count := count)) steps v 0] at hm

private theorem nvGen_w1_tableRootPremise (steps : Nat) (E : Generic.Env (Validator (count :=
  count)))
    (rho : V2.D.Run (Validator (count := count)) (fgsa (params (count := count)) unitCodec))
    (hd : ∀ v o t, V2.Event.deliver v o t ∈ rho.events → ∀ B,
      o.payload = .proposal B → B ∈ (w1_rootTable (count := count)) steps)
    (hs : ∀ i v B, B ∈ (V2.D.Run.stateBefore E rho i v).st.namedBodies → B ∈ (w1_rootTable
      (count := count)) steps) :
    NamedRootCollisionFree (params (count := count)) unitCodec E rho where
  root_injective := by
    have scope (B : NamedProposal (params (count := count)).n) (hB : NamedProposalInRun (params
      (count := count)) unitCodec E rho B) :
        B ∈ (w1_rootTable (count := count)) steps := by
      obtain ⟨C, hC, hBC⟩ := hB
      apply (nvGen_w1_ancestorTable (count := count)) steps C _ B hBC
      rcases hC with ⟨v, o, t, he, hp⟩ | ⟨v, _, i, hm⟩
      · exact hd v o t he C hp
      · exact hs i v C hm
    intro B C hB hC A D hA hD he
    have ancestor (X : NamedProposal (params (count := count)).n)
      (hX : NamedProposal.Preceq X B ∨ NamedProposal.Preceq X C) :
        X ∈ (w1_rootTable (count := count)) steps := hX.elim
      ((nvGen_w1_ancestorTable (count := count)) steps B (scope B hB) X)
        ((nvGen_w1_ancestorTable (count :=
        count)) steps C (scope C hC) X)
    exact namedBodies_root_injective (params (count := count)) _ ((nvGen_w1_tableInv (count :=
      count))
      steps) ((nvGen_w1_tableMeta (count := count)) steps)
      (ancestor A hA) (ancestor D hD) he

theorem nvGen_prefix_sleep (steps : Nat) :
    V2.D.SleepWellFormed (weakEnv (count := count))
      (runData steps (buildPrefix (steps + 1)).2) where
  tick_awake := fun _ _ _ => rfl
  deliver_awake := fun _ _ _ _ => rfl
  restart_awake := fun _ _ _ => rfl
  wake_restart := by
    intro v _ t _ _ hw
    exact Bool.noConfusion hw.2

theorem nvGen_prefix_execution (steps : Nat) :
    V2.D.ExecutionValid (weakEnv (count := count)) ((runData (count := count)) steps
      ((buildPrefix (count := count)) (steps + 1)).2) where
  toScheduleWellFormed := (nvGen_w1_prefix_schedule (count := count)) steps
  toSleepWellFormed := nvGen_prefix_sleep steps
  wire := by
    intro i v o t hi
    obtain ⟨u, hu⟩ := (nvGen_prefix_origin (count := count)) (steps + 1) v o t
      (List.mem_of_getElem? hi)
    exact (nvGen_w1_emit_wire (count := count)) steps _ ((nvGen_w1_prefix_schedule (count :=
      count)) steps)
      ((nvGen_prefix_origin (count := count)) (steps + 1))
      ((nvGen_gen_prefix_carried (count := count)) (steps + 1)).2
      (nvGen_prefix_no_restart (steps + 1)) u o t ((nvGen_genEmits_runData
        (count :=
        count)) steps _ u o t hu)
  deps := by
    intro i v o t hi
    exact (nvGen_w1_deps_get (count := count)) _ _ ((nvGen_w1_prefix_deps (count := count))
      (steps + 1)) i v
      o t hi
  fresh := (nvGen_runData_fresh (count := count)) steps _ ((nvGen_prefix_replay_fresh (count :=
    count))
    (steps + 1)).2
  unforgeable := fun v o t hp u _ hh =>
    (nvGen_genOrigin_unforgeable (count := count)) steps _ ((nvGen_prefix_origin (count :=
      count)) (steps +
      1)) v o t hp u hh
  carried := fun v o t hp o' hc u _ hh =>
    (nvGen_genCarried_runData (count := count)) steps _ ((nvGen_gen_prefix_carried (count :=
      count)) (steps
      + 1)).2 v o t hp o' hc u hh

theorem nvGen_prefix_roots (steps : Nat) :
    NamedRootCollisionFree (params (count := count)) unitCodec (weakEnv (count := count))
      ((runData (count := count)) steps ((buildPrefix (count := count)) (steps + 1)).2) := by
  apply (nvGen_w1_tableRootPremise (count := count)) (steps + 1) (weakEnv (count := count))
    ((runData
    (count := count)) steps ((buildPrefix (count := count)) (steps + 1)).2)
  · intro v o t hd B hp
    exact (nvGen_w1_deliveredTable (count := count)) (steps + 1) v o t hd B hp
  · intro i v B hB
    exact (nvGen_w1_storedTable (count := count)) (steps + 1) steps i v B hB

theorem nvGen_prefix_receiptRoots (steps : Nat) :
    NamedReceiptRootCollisionFree (params (count := count)) unitCodec weakEnv
      (runData steps (buildPrefix (steps + 1)).2) := by
  have hscope (A : NamedProposal (params (count := count)).n)
      (hA : NamedProposalReceiptScope (params (count := count)) unitCodec weakEnv
        (runData steps (buildPrefix (steps + 1)).2) A) :
      NamedProposalInRun (params (count := count)) unitCodec weakEnv
        (runData steps (buildPrefix (steps + 1)).2) A := by
    rcases hA with hA | ⟨v, _, o, t, N, hem, hp, hAN⟩
    · exact hA
    · exact ⟨N, Or.inl ⟨v, o, t, nvGen_w1_prefix_broadcast steps v o t hem v, hp⟩, hAN⟩
  have hrefl (A : NamedProposal (params (count := count)).n) : NamedProposal.Preceq A A := by
    cases A <;> simp [NamedProposal.Preceq, NamedProposal.preceq]
  intro A B hA hB he
  exact (nvGen_prefix_roots steps).root_injective A B (hscope A hA) (hscope B hB)
    A B (Or.inl (hrefl A)) (Or.inr (hrefl B)) he

theorem nvGen_prefix_sync (steps : Nat) :
    Gen.V2.Duty.PartialSynchronyBy (weakEnv (count := count)) ((runData (count := count)) steps
      ((buildPrefix (count := count)) (steps + 1)).2)
      (fgsaDelay (weakEnv (count := count)).Δ 1) := by
  have hd : fgsaDelay (p := (params (count := count))) (weakEnv (count := count)).Δ 1 = fun _ =>
    (weakEnv (count := count)).Δ := by
    funext o
    cases o with | mk a m => cases m <;> rfl
  rw [hd]
  exact ⟨((nvGen_w1_prefix_sync (count := count)) steps).broadcast_emitted,
    ((nvGen_w1_prefix_sync (count :=
    count)) steps).relay_accepted⟩

theorem nvGen_prefix_accountable (steps : Nat) :
    FinalitySlashableBound (params (count := count)) unitCodec (weakEnv (count := count))
      ((runData (count := count)) steps ((buildPrefix (count := count)) (steps + 1)).2) := by
  have hb := fgsa_slashableBound_of_valid (params (count := count)) unitCodec (weakEnv (count :=
    count))
    ((runData (count := count)) steps ((buildPrefix (count := count)) (steps + 1)).2) ((nvGen_linked
      (count := count)) _ _) ((nvGen_prefix_execution (count := count)) steps)
    (by simp [Gen.V2.Duty.faulty, runData])
  simpa only [FinalitySlashableBound_def, FGSASlashableBound_def,
    FinalityBlock_def, FinalityRunBlock_def] using hb

/-- A duty-free round releases no object, for any FG-SA state or run. -/
theorem nvGen_tick_empty {p : Params} {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (st : (fgsa p c).State) (v : V) (t : Time) (hd : duties p t = []) :
    (V2.D.tick E rho st v t).2 = [] := by
  simp [V2.D.tick, fgsa, hd]
  intro _
  rfl

/-- The generator has no delivery in a duty-free round. -/
theorem nvGen_batch_empty (t : Time) (w : World (count := count))
    (hd : duties (params (count := count)) t = []) :
    (timeBatch (count := count) t w).2 =
      (nodes (count := count)).map (fun v => .tick v t) := by
  have ht (vs : List (Validator (count := count))) (w : World (count := count))
      (os : List (fgsa (params (count := count)) unitCodec).Object) :
      (vs.foldl (fun acc v =>
        let result := V2.D.tick (weakEnv (count := count))
          (runData (count := count) 263 []) (acc.1 v) v t
        (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2 = os := by
    induction vs generalizing w os with
    | nil => rfl
    | cons v vs ih =>
        exact (ih _ _).trans (by
          rw [nvGen_tick_empty unitCodec (weakEnv (count := count)) _ _ v t hd, List.append_nil])
  have he : (tickBatch (count := count) t w).2 = [] := ht (nodes (count := count)) w []
  simp [timeBatch, he]

theorem nvGen_prefix_no_delivery (steps : Nat) (v : Validator (count := count))
    (o : Obj (params (count := count))) (t : Time)
    (hd : duties (params (count := count)) t = []) :
    V2.Event.deliver v o t ∉ (buildPrefix (count := count) steps).2 := by
  induction steps with
  | zero => exact List.not_mem_nil
  | succ steps ih =>
      intro he
      rcases List.mem_append.mp he with he | he
      · exact ih he
      · have ht : t = (steps : Time) := nvGen_timeBatch_time (count := count) _ _ _ he
        rw [← ht, nvGen_batch_empty (count := count) t _ hd] at he
        obtain ⟨u, _, hu⟩ := List.mem_map.mp he
        cases hu

#print axioms nvGen_head_action
#print axioms nvGen_proposal_action
#print axioms nvGen_prefix_execution
#print axioms nvGen_gen_tick_nonproposal_wire
#print axioms nvGen_w1_known_fold
#print axioms nvGen_w1_known_fold_local
#print axioms nvGen_prefix_sleep
#print axioms nvGen_prefix_receiptRoots
#print axioms nvGen_w1_service
#print axioms nvGen_prefix_roots
#print axioms nvGen_prefix_sync
#print axioms nvGen_prefix_accountable

end AvailableChain.FGSA.Run.Tests.GrowthGenerator
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.GrowthRestriction

open AvailableChain

/-- Keep the local events of the specified validators. -/
def restrictRun {In V : Type} [DecidableEq V] {P : V2.ProtocolSpecD In}
    (rho : V2.D.Run V P) (kept : Finset V) : V2.D.Run V P :=
  { rho with honest := kept, events := rho.events.filter (fun e : V2.Event V P.Object => decide
    (e.node ∈ kept)) }

/-- The retained index has the same earlier retained events. -/
theorem nvRestrict_filter_index {A : Type} (keep : A → Bool) (es : List A) (i : Nat) (e : A)
    (hi : es[i]? = some e) (hk : keep e = true) :
    ∃ j, (es.filter keep)[j]? = some e ∧
      (es.filter keep).take j = (es.take i).filter keep := by
  induction es generalizing i with
  | nil => simp at hi
  | cons a es ih =>
      cases i with
      | zero =>
          have he : a = e := Option.some.inj hi
          subst a
          exact ⟨0, by simp [hk], by simp⟩
      | succ i =>
          obtain ⟨j, hj, hp⟩ := ih i (by simpa using hi)
          by_cases ha : keep a = true
          · exact ⟨j + 1, by simpa [ha] using hj, by simpa [ha] using congrArg (a :: ·) hp⟩
          · have hf : keep a = false := Bool.eq_false_iff.mpr ha
            exact ⟨j, by simpa [hf] using hj, by simpa [hf] using hp⟩

/-- Every retained occurrence has a corresponding original occurrence. -/
theorem nvRestrict_index_filter {A : Type} (keep : A → Bool) (es : List A) (j : Nat) (e : A)
    (hj : (es.filter keep)[j]? = some e) :
    ∃ i, es[i]? = some e ∧ keep e = true ∧
      (es.filter keep).take j = (es.take i).filter keep := by
  induction es generalizing j with
  | nil => simp at hj
  | cons a es ih =>
      by_cases ha : keep a = true
      · cases j with
        | zero =>
            have he : a = e := by simpa [ha] using hj
            subst a
            exact ⟨0, by simp, ha, by simp⟩
        | succ j =>
            obtain ⟨i, hi, hk, hp⟩ := ih j (by simpa [ha] using hj)
            exact ⟨i + 1, by simpa using hi, hk, by simpa [ha] using congrArg (a :: ·) hp⟩
      · have hf : keep a = false := Bool.eq_false_iff.mpr ha
        obtain ⟨i, hi, hk, hp⟩ := ih j (by simpa [hf] using hj)
        exact ⟨i + 1, by simpa using hi, hk, by simpa [hf] using hp⟩

section Local
variable {In V : Type} [DecidableEq V] {P : V2.ProtocolSpecD In}
    (E : Generic.Env V) (rho : V2.D.Run V P)

private def localStep (v : V) (st : P.State) : V2.Event V P.Object → P.State
  | .restart u t => if u = v then P.restore (P.durable st) t else st
  | .tick u t => if u = v then (V2.D.tick E rho st u t).1 else st
  | .deliver u o _ => if u = v then P.process st o else st

private theorem nvRestrict_step_local (w : V2.D.World V P) (v : V) (e : V2.Event V P.Object) :
    V2.D.World.step E rho w e v = localStep E rho v (w v) e := by
  cases e with
  | restart u t =>
      by_cases he : u = v
      · subst u; simp [V2.D.World.step, localStep]
      · simp [V2.D.World.step, localStep, he, Ne.symm he]
  | tick u t =>
      by_cases he : u = v
      · subst u; simp [V2.D.World.step, localStep]
      · simp [V2.D.World.step, localStep, he, Ne.symm he]
  | deliver u o t =>
      by_cases he : u = v
      · subst u; simp [V2.D.World.step, localStep]
      · simp [V2.D.World.step, localStep, he, Ne.symm he]

private theorem nvRestrict_fold_local (es : List (V2.Event V P.Object)) (w : V2.D.World V P) (v
  : V) :
    (es.foldl (V2.D.World.step E rho) w) v = es.foldl (localStep E rho v) (w v) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih, nvRestrict_step_local]
      rfl

private theorem nvRestrict_localStep_other (v : V) (st : P.State)
    (e : V2.Event V P.Object) (hn : e.node ≠ v) : localStep E rho v st e = st := by
  cases e with
  | restart u t => change u ≠ v at hn; exact ite_eq_right hn
  | tick u t => change u ≠ v at hn; exact ite_eq_right hn
  | deliver u o t => change u ≠ v at hn; exact ite_eq_right hn

/-- Dropping other validators' events preserves a retained node's full state. -/
theorem nvRestrict_fold_restrict (es : List (V2.Event V P.Object)) (w : V2.D.World V P)
    (kept : Finset V) (v : V) (hv : v ∈ kept) :
    ((es.filter (fun e : V2.Event V P.Object => decide (e.node ∈ kept))).foldl (V2.D.World.step
      E rho) w) v =
      (es.foldl (V2.D.World.step E rho) w) v := by
  rw [nvRestrict_fold_local, nvRestrict_fold_local]
  have hs (st : P.State) :
      (es.filter (fun e : V2.Event V P.Object => decide (e.node ∈ kept))).foldl (localStep E rho
        v) st =
        es.foldl (localStep E rho v) st := by
    induction es generalizing st with
    | nil => rfl
    | cons e es ih =>
        by_cases hk : e.node ∈ kept
        · simpa only [List.filter_cons, hk, decide_true, ↓reduceIte,
            List.foldl_cons] using ih _
        · have hn : e.node ≠ v := by intro he; exact hk (he.symm ▸ hv)
          simp only [List.filter_cons, hk, decide_false, Bool.false_eq_true,
            ite_false, List.foldl_cons]
          rw [nvRestrict_localStep_other E rho v st e hn]
          exact ih st
  exact hs _

/-- Retention does not change the transition function. -/
theorem nvRestrict_step_restrict (kept : Finset V) :
    V2.D.World.step E (restrictRun rho kept) = V2.D.World.step E rho := rfl

/-- An original occurrence and its retained index read the same full node state. -/
theorem nvRestrict_state_restrict (kept : Finset V) (v : V) (hv : v ∈ kept) (i j : Nat)
    (hp : ((restrictRun rho kept).events).take j =
      (rho.events.take i).filter (fun e : V2.Event V P.Object => decide (e.node ∈ kept))) :
    V2.D.Run.stateBefore E (restrictRun rho kept) j v = V2.D.Run.stateBefore E rho i v := by
  unfold V2.D.Run.stateBefore
  rw [hp, nvRestrict_step_restrict]
  exact nvRestrict_fold_restrict E rho _ _ kept v hv

/-- Every retained prefix is the filter of an original prefix. -/
theorem nvRestrict_filter_prefix {A : Type} (keep : A → Bool) (es : List A) (j : Nat) :
    ∃ i, (es.filter keep).take j = (es.take i).filter keep := by
  by_cases hj : j < (es.filter keep).length
  · obtain ⟨i, _, _, hp⟩ := nvRestrict_index_filter keep es j (es.filter keep)[j]
      (List.getElem?_eq_getElem hj)
    exact ⟨i, hp⟩
  · exact ⟨es.length, by rw [List.take_of_length_le (Nat.le_of_not_lt hj), List.take_length]⟩

/-- A retained node's state at any retained prefix occurs in the original run. -/
theorem nvRestrict_state_restrict_any (kept : Finset V) (v : V) (hv : v ∈ kept) (j : Nat) :
    ∃ i, V2.D.Run.stateBefore E (restrictRun rho kept) j v =
      V2.D.Run.stateBefore E rho i v := by
  obtain ⟨i, hp⟩ := nvRestrict_filter_prefix (fun e : V2.Event V P.Object => decide (e.node ∈
    kept)) rho.events j
  exact ⟨i, nvRestrict_state_restrict E rho kept v hv i j hp⟩

/-- Before-time reads are unchanged at each retained node. -/
theorem nvRestrict_beforeTime_restrict (kept : Finset V) (v : V) (hv : v ∈ kept) (t : Time) :
    V2.D.Run.stateBeforeTime E (restrictRun rho kept) t v =
      V2.D.Run.stateBeforeTime E rho t v := by
  unfold V2.D.Run.stateBeforeTime
  change (((rho.events.filter (fun e : V2.Event V P.Object => decide (e.node ∈ kept))).filter
    (fun e => decide (e.time < t))).foldl (V2.D.World.step E (restrictRun rho kept))
      V2.D.World.init) v = _
  rw [nvRestrict_step_restrict, List.filter_comm]
  exact nvRestrict_fold_restrict E rho _ _ kept v hv

/-- The occurrence pairing also pairs the states after the event. -/
theorem nvRestrict_filter_prefix_succ {A : Type} (keep : A → Bool) (es : List A)
    (i j : Nat) (e : A) (hi : es[i]? = some e) (hj : (es.filter keep)[j]? = some e)
    (hk : keep e = true) (hp : (es.filter keep).take j = (es.take i).filter keep) :
    (es.filter keep).take (j + 1) = (es.take (i + 1)).filter keep := by
  rw [List.take_add_one, List.take_add_one, hi, hj, List.filter_append, hp]
  simp [hk]

/-- Both traces release the same objects at paired retained ticks. -/
theorem nvRestrict_emits_restrict (kept : Finset V) (v : V) (hv : v ∈ kept) (o : P.Object) (t :
  Time) :
    V2.D.Run.emits E (restrictRun rho kept) v o t ↔ V2.D.Run.emits E rho v o t := by
  constructor
  · rintro ⟨j, hj, ho⟩
    obtain ⟨i, hi, _, hp⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.tick v t) hj
    refine ⟨i, hi, ?_⟩
    rw [(V2.D.Run.step_tick_eq E (restrictRun rho kept) hj).2,
      nvRestrict_state_restrict E rho kept v hv i j hp] at ho
    rwa [(V2.D.Run.step_tick_eq E rho hi).2]
  · rintro ⟨i, hi, ho⟩
    obtain ⟨j, hj, hp⟩ := nvRestrict_filter_index (fun e : V2.Event V P.Object => decide (e.node
      ∈ kept)) rho.events i
      (.tick v t) hi (by change decide (v ∈ kept) = true; exact decide_eq_true hv)
    refine ⟨j, hj, ?_⟩
    rw [(V2.D.Run.step_tick_eq E (restrictRun rho kept) hj).2,
      nvRestrict_state_restrict E rho kept v hv i j hp]
    rwa [(V2.D.Run.step_tick_eq E rho hi).2] at ho

/-- A retained delivery gives the same handler calls at its paired index. -/
theorem nvRestrict_handles_restrict (kept : Finset V) (v : V) (hv : v ∈ kept) (o : P.Object) (t
  : Time) :
    (∃ j, V2.D.Run.handlesAt E (restrictRun rho kept) j v o t) ↔
      ∃ i, V2.D.Run.handlesAt E rho i v o t := by
  constructor
  · rintro ⟨j, a, hj, hh⟩
    obtain ⟨i, hi, _, hp⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.deliver v a t) hj
    exact ⟨i, a, hi, by rwa [nvRestrict_state_restrict E rho kept v hv i j hp] at hh⟩
  · rintro ⟨i, a, hi, hh⟩
    obtain ⟨j, hj, hp⟩ := nvRestrict_filter_index (fun e : V2.Event V P.Object => decide (e.node
      ∈ kept)) rho.events i
      (.deliver v a t) hi (by change decide (v ∈ kept) = true; exact decide_eq_true hv)
    exact ⟨j, a, hj, by rwa [nvRestrict_state_restrict E rho kept v hv i j hp]⟩

/-- The schedule restriction keeps the original horizon and public ticks. -/
theorem nvRestrict_schedule_restrict (kept : Finset V) (hsub : kept ⊆ rho.honest)
    (hs : V2.D.ScheduleWellFormed E rho) :
    V2.D.ScheduleWellFormed E (restrictRun rho kept) where
  horizon_nonneg := hs.horizon_nonneg
  sorted := hs.sorted.filter _
  nodup := hs.nodup.filter _
  in_horizon := fun e he => hs.in_horizon e (List.mem_filter.mp he).1
  honest_only := fun e he => of_decide_eq_true (List.mem_filter.mp he).2
  tick_public := fun v t he => hs.tick_public v t (List.mem_filter.mp he).1
  tick_total := by
    intro v hv t hp ht hh ha
    apply List.mem_filter.mpr
    exact ⟨hs.tick_total v (hsub hv) t hp ht hh ha, by
      change decide (v ∈ kept) = true
      exact decide_eq_true hv⟩

/-- Validity survives removal of other nodes' local events. -/
theorem nvRestrict_execution_restrict (kept : Finset V) (hsub : kept ⊆ rho.honest)
    (hs : V2.D.ExecutionValid E rho) : V2.D.ExecutionValid E (restrictRun rho kept) where
  toScheduleWellFormed := nvRestrict_schedule_restrict E rho kept hsub hs.toScheduleWellFormed
  toSleepWellFormed := {
    tick_awake := fun v t hm => hs.tick_awake v t (List.mem_filter.mp hm).1
    deliver_awake := fun v o t hm => hs.deliver_awake v o t (List.mem_filter.mp hm).1
    restart_awake := fun v t hm => hs.restart_awake v t (List.mem_filter.mp hm).1
    wake_restart := by
      intro v hv t ht hh hw
      exact List.mem_filter.mpr ⟨hs.wake_restart v (hsub hv) t ht hh hw,
        decide_eq_true hv⟩ }
  wire := by
    intro j v o t hj
    obtain ⟨i, hi, _, _⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.deliver v o t) hj
    exact hs.wire i v o t hi
  deps := by
    intro j v o t hj
    obtain ⟨i, hi, hk, hp⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.deliver v o t) hj
    have hv : v ∈ kept := of_decide_eq_true hk
    rw [nvRestrict_state_restrict E rho kept v hv i j hp]
    exact hs.deps i v o t hi
  fresh := by
    intro j v o t hj
    obtain ⟨i, hi, hk, hp⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.deliver v o t) hj
    have hv : v ∈ kept := of_decide_eq_true hk
    rw [nvRestrict_state_restrict E rho kept v hv i j hp]
    exact hs.fresh i v o t hi
  unforgeable := by
    rintro v o t ⟨j, hj⟩ u hu hh
    obtain ⟨i, hi, _, _⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.deliver v o t) hj
    obtain ⟨s, ht, he⟩ := hs.unforgeable v o t ⟨i, hi⟩ u (hsub hu) hh
    exact ⟨s, ht, (nvRestrict_emits_restrict E rho kept u hu o s).mpr he⟩
  carried := by
    rintro v o t ⟨j, hj⟩ a hc u hu hh
    obtain ⟨i, hi, _, _⟩ := nvRestrict_index_filter (fun e : V2.Event V P.Object => decide
      (e.node ∈ kept)) rho.events j
      (.deliver v o t) hj
    obtain ⟨s, ht, he⟩ := hs.carried v o t ⟨i, hi⟩ a hc u (hsub hu) hh
    exact ⟨s, ht, (nvRestrict_emits_restrict E rho kept u hu a s).mpr he⟩

/-- Retention preserves both alternatives of service at the same action anchor. -/
theorem nvRestrict_service_restrict (kept : Finset V) (w : V) (hw : w ∈ kept)
    (hs : V2.D.ScheduleWellFormed E rho) (o : P.Object) (a d : Time)
    (h : V2.D.DeliveryService E rho w o a d) :
    V2.D.DeliveryService E (restrictRun rho kept) w o a d := by
  rcases h with ⟨k, hk, hp⟩ | ⟨t, ht, hd, j, hj⟩
  · left
    let keep := fun e : V2.Event V P.Object => decide (e.node ∈ kept)
    let cut := fun e : V2.Event V P.Object =>
      decide (e.time < a ∨ (e.time = a ∧ e.phase = 0))
    have hc : rho.events.filter cut = rho.events.take (V2.D.Run.actionCut rho a) := by
      apply V2.D.Engine.filter_eq_take hs cut
      intro e f hef hf
      have hkey := Prod.Lex.toLex_le_toLex'.mp hef
      have hcf := of_decide_eq_true hf
      apply decide_eq_true
      rcases hcf with hlt | ⟨heq, hz⟩
      · exact Or.inl (lt_of_le_of_lt hkey.1 hlt)
      · by_cases he : e.time = f.time
        · exact Or.inr ⟨he.trans heq, Nat.eq_zero_of_le_zero (hz ▸ hkey.2 he)⟩
        · exact Or.inl (lt_of_lt_of_le (lt_of_le_of_ne hkey.1 he) heq.le)
    let j := ((rho.events.take k).filter keep).length
    refine ⟨j, ?_, ?_⟩
    · have hh := ((List.take_prefix_take_left (l := rho.events) hk).filter keep).length_le
      rw [← hc] at hh
      change j ≤ ((rho.events.filter keep).filter cut).length
      simpa only [List.filter_filter, Bool.and_comm] using hh
    · have htake := (List.prefix_iff_eq_take.mp ((List.take_prefix k rho.events).filter keep)).symm
      rw [nvRestrict_state_restrict E rho kept w hw k j htake]
      exact hp
  · right
    exact ⟨t, ht, hd, (nvRestrict_handles_restrict E rho kept w hw o t).mpr ⟨j, hj⟩⟩

/-- Family synchrony keeps the same deadline and receiver guards after retention. -/
theorem nvRestrict_sync_restrict (kept : Finset V) (hsub : kept ⊆ rho.honest) (delay : P.Object
  → Time)
    (hs : Gen.V2.Duty.PartialSynchronyBy E rho delay)
    (hsch : V2.D.ScheduleWellFormed E rho) :
    Gen.V2.Duty.PartialSynchronyBy E (restrictRun rho kept) delay where
  broadcast_emitted := by
    intro v hv o t he w hw a hta ha had hh hhor hlink hx
    have he' := (nvRestrict_emits_restrict E rho kept v hv o t).mp he
    have hx' : P.excludes (V2.D.Run.stateBeforeTime E rho (max a E.t_GST + delay o) w) o
        = false := by rwa [nvRestrict_beforeTime_restrict E rho kept w hw] at hx
    exact nvRestrict_service_restrict E rho kept w hw hsch o a _
      (hs.broadcast_emitted v (hsub hv) o t he' w (hsub hw)
        a hta ha had hh hhor hlink hx')
  relay_accepted := by
    intro v hv j o t hacc w hw a hta ha had hh hhor hlink hx
    obtain ⟨obj, hj, hhandle⟩ := hacc.1
    obtain ⟨i, hi, hk, hpre⟩ := nvRestrict_index_filter
      (fun e : V2.Event V P.Object => decide (e.node ∈ kept)) rho.events j (.deliver v obj t) hj
    have hpost := nvRestrict_filter_prefix_succ
      (fun e : V2.Event V P.Object => decide (e.node ∈ kept)) rho.events i j
      (.deliver v obj t) hi hj hk hpre
    have ha' : V2.D.Run.acceptsAt E rho i v o t := by
      refine ⟨⟨obj, hi, ?_⟩, ?_, ?_⟩
      · rwa [nvRestrict_state_restrict E rho kept v hv i j hpre] at hhandle
      · have hp0 := hacc.2.1
        rwa [nvRestrict_state_restrict E rho kept v hv i j hpre] at hp0
      · have hp' := hacc.2.2
        rwa [nvRestrict_state_restrict E rho kept v hv (i + 1) (j + 1) hpost] at hp'
    have hx' : P.excludes (V2.D.Run.stateBeforeTime E rho (max a E.t_GST + delay o) w) o
        = false := by rwa [nvRestrict_beforeTime_restrict E rho kept w hw] at hx
    exact nvRestrict_service_restrict E rho kept w hw hsch o a _
      (hs.relay_accepted v (hsub hv) i o t ha' w (hsub hw)
        a hta ha had hh hhor hlink hx')

end Local

section FGSA
variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Retained full named scope is a subset of the original full named scope. -/
theorem nvRestrict_roots_restrict (kept : Finset V) (hsub : kept ⊆ rho.honest)
    (hr : NamedRootCollisionFree p c E rho) :
    NamedRootCollisionFree p c E (restrictRun rho kept) where
  root_injective := by
    have scope (B : NamedProposal p.n)
        (hB : NamedProposalInRun p c E (restrictRun rho kept) B) :
        NamedProposalInRun p c E rho B := by
      obtain ⟨C, hC, hBC⟩ := hB
      refine ⟨C, ?_, hBC⟩
      rcases hC with ⟨x, o, t, he, hp⟩ | ⟨x, hx, j, hC⟩
      · exact Or.inl ⟨x, o, t, (List.mem_filter.mp he).1, hp⟩
      · obtain ⟨i, hi⟩ := nvRestrict_state_restrict_any E rho kept x hx j
        exact Or.inr ⟨x, hsub hx, i, by rwa [hi] at hC⟩
    intro B C hB hC A D hA hD he
    exact hr.root_injective B C (scope B hB) (scope C hC) A D hA hD he

/-- Every continuation finality observation occurs in the reference run. -/
theorem nvRestrict_finalityBlock_restrict (kept : Finset V)
    (hs : V2.D.ScheduleWellFormed E (restrictRun rho kept))
    (K : SimplexFG.FGBlock (Fin p.n))
    (hK : FinalityBlock p c E (restrictRun rho kept) K) : FinalityBlock p c E rho K := by
  obtain ⟨o, N, ho, he, hKN⟩ := hK
  refine ⟨o, N, ho, ?_, hKN⟩
  rcases he with ⟨x, t, he⟩ | ⟨x, t, he⟩
  · have hx : x ∈ kept := by
      obtain ⟨j, hj, _⟩ := he
      exact hs.honest_only _ (List.mem_of_getElem? hj)
    exact Or.inl ⟨x, t, (nvRestrict_emits_restrict E rho kept x hx o t).mp he⟩
  · exact Or.inr ⟨x, t, (List.mem_filter.mp he).1⟩

/-- Whole-run slashing weight is bounded by the reference's coherent history. -/
theorem nvRestrict_accountable_restrict (kept : Finset V)
    (hs : V2.D.ScheduleWellFormed E (restrictRun rho kept))
    (hb : FinalitySlashableBound p c E rho) :
    FinalitySlashableBound p c E (restrictRun rho kept) := by
  intro K W hK hW
  exact hb K W (nvRestrict_finalityBlock_restrict p c E rho kept hs K hK)
    (nvRestrict_finalityBlock_restrict p c E rho kept hs W hW)

end FGSA
#print axioms nvRestrict_service_restrict
#print axioms nvRestrict_execution_restrict
#print axioms nvRestrict_sync_restrict

end AvailableChain.FGSA.Run.Tests.GrowthRestriction
end

@[expose] public section

set_option maxRecDepth 1000

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthNonVacuity

/-! Closed partial witness for the corruption-growth companion.
The W1 generator supplies the model for this five-validator test.
TEST-SCOPE prevents an import of the Inhabit fixture or another Tests module.
The source ends at 253 and three honest validators continue at 254.
MissingFields states the exact fields needed to close both regime records. -/

def params : Params where
  Δ := 1
  n := 5
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

abbrev Validator := Fin 5

abbrev Event := V2.Event Validator (fgsa params unitCodec).Object

abbrev World := V2.D.World Validator (fgsa params unitCodec)

instance : DecidableEq Event := by
  change DecidableEq (V2.Event Validator (Obj params))
  infer_instance

def env : Generic.Env Validator where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats params ℓ) → Validator
  | .base _, i => i
  | .prop _, _ => 0

def runData (h : Time) (es : List Event) : V2.D.Run Validator (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := h
  events := es
  seatOf := seatOf
  input _ _ := ()

def nodes : List Validator := [0, 1, 2, 3, 4]

def retained : List Validator := [0, 1, 2]

def retainedSet : Finset Validator := {0, 1, 2}

def tickBatch (vs : List Validator) (t : Time) (w : World) : World × List (Obj params) :=
  vs.foldl (fun acc v =>
    let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ (show List (Obj params) from result.2))) (w, [])

def deliverOne (t : Time) (acc : World × List Event) (vo : Validator × Obj params) :
    World × List Event :=
  if (fgsa params unitCodec).processed (acc.1 vo.1) vo.2 = true ∨
      (V2.Event.deliver vo.1 vo.2 t : Event) ∈ acc.2 then acc else
    (V2.D.World.step env (runData 0 []) acc.1 (.deliver vo.1 vo.2 t),
      acc.2 ++ [.deliver vo.1 vo.2 t])

def timeBatch (vs : List Validator) (t : Time) (w : World) : World × List Event :=
  let ticks := tickBatch vs t w
  let offered := ticks.2.flatMap (fun o => vs.map (fun v => (v, o)))
  offered.foldl (deliverOne t) (ticks.1, vs.map (fun v => .tick v t))

def buildPrefix : Nat → World × List Event
  | 0 => (V2.D.World.init, [])
  | steps + 1 =>
      let previous := buildPrefix steps
      let batch := timeBatch nodes (steps : Time) previous.1
      (batch.1, previous.2 ++ batch.2)

def continuationData (es ds : List Event) : V2.D.Run Validator (fgsa params unitCodec) :=
  { runData 254 [] with
    honest := retainedSet
    events := es.filter (fun e => decide (e.node ∈ retainedSet)) ++ ds }

theorem nvGrowth_liveness : LivenessBoundW params 1 := ⟨by decide⟩

theorem nvGrowth_delta_ratio : params.δt = 2 * params.R := by decide

theorem nvGrowth_committees (rho : V2.D.Run Validator (fgsa params unitCodec))
    (hseat : rho.seatOf = seatOf) :
    V2.D.Linked (fgsaFamilies params unitCodec).linked rho ∧
    V2.D.CStar (fgsaFamilies params unitCodec).fresh rho := by
  constructor
  · refine ⟨5, Equiv.refl _, ?_⟩
    intro label hf
    cases label with
    | prop s => exact hf.elim
    | base label =>
        cases label with
        | head s => exact hf.elim
        | fg => exact ⟨rfl, fun i => by rw [hseat]; rfl⟩
  · intro label hf
    cases label with
    | prop s => exact hf.elim
    | base label =>
        cases label with
        | fg => exact hf.elim
        | head s =>
            rw [hseat]
            exact Function.bijective_id

theorem nvGrowth_delivery_mem (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (e : Event) :
    (e ∈ acc.2 → e ∈ (xs.foldl (deliverOne t) acc).2) ∧
    (e ∈ (xs.foldl (deliverOne t) acc).2 →
      e ∈ acc.2 ∨ ∃ vo ∈ xs, e = .deliver vo.1 vo.2 t) := by
  induction xs generalizing acc with
  | nil => exact ⟨id, Or.inl⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true ∨
          (V2.Event.deliver x.1 x.2 t : Event) ∈ acc.2
      · simp only [deliverOne, hp, ↓reduceIte]
        refine ⟨(ih acc).1, ?_⟩
        intro he
        rcases (ih acc).2 he with he | ⟨vo, hvo, he⟩
        · exact Or.inl he
        · exact Or.inr ⟨vo, List.mem_cons_of_mem _ hvo, he⟩
      · simp only [deliverOne, hp, ↓reduceIte]
        constructor
        · intro he
          exact (ih _).1 (List.mem_append_left _ he)
        · intro he
          rcases (ih _).2 he with he | ⟨vo, hvo, he⟩
          · rcases List.mem_append.mp he with he | he
            · exact Or.inl he
            · exact Or.inr ⟨x, List.mem_cons_self, List.mem_singleton.mp he⟩
          · exact Or.inr ⟨vo, List.mem_cons_of_mem _ hvo, he⟩

theorem nvGrowth_batch_shape (vs : List Validator) (t : Time) (w : World) (e : Event)
    (he : e ∈ (timeBatch vs t w).2) :
    e.time = t ∧ e.node ∈ vs ∧
      ((∃ v, e = .tick v t) ∨ ∃ v o, e = .deliver v o t) := by
  rcases (nvGrowth_delivery_mem t _ _ e).2 he with he | ⟨vo, hvo, rfl⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact ⟨rfl, hv, Or.inl ⟨v, rfl⟩⟩
  · obtain ⟨o, _, hvo⟩ := List.mem_flatMap.mp hvo
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hvo
    cases he
    exact ⟨rfl, hv, Or.inr ⟨v, o, rfl⟩⟩

theorem nvGrowth_batch_tick (vs : List Validator) (t : Time) (w : World) (v : Validator)
    (hv : v ∈ vs) : V2.Event.tick v t ∈ (timeBatch vs t w).2 :=
  (nvGrowth_delivery_mem t _ _ _).1 (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem nvGrowth_prefix_times (steps : Nat) (e : Event) (he : e ∈ (buildPrefix steps).2) :
    0 ≤ e.time ∧ e.time < steps := by
  induction steps with
  | zero => simp [buildPrefix] at he
  | succ steps ih =>
      rcases List.mem_append.mp he with he | he
      · have := ih he
        simp only [Nat.cast_add, Nat.cast_one, Time] at *
        omega
      · rw [(nvGrowth_batch_shape _ _ _ _ he).1]
        exact ⟨Int.natCast_nonneg _, by simp⟩

theorem nvGrowth_prefix_tick (steps t : Nat) (ht : t < steps) (v : Validator) :
    V2.Event.tick v (t : Time) ∈ (buildPrefix steps).2 := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      by_cases he : t = steps
      · subst t
        apply List.mem_append_right
        exact nvGrowth_batch_tick nodes (steps : Time) (buildPrefix steps).1 v
          (by fin_cases v <;> simp [nodes])
      · exact List.mem_append_left _ (ih (by omega))

theorem nvGrowth_agreement_of_suffix (es ds : List Event)
    (hds : ∀ e ∈ ds, (253 : Time) < e.time) :
    RetainedAgreesThrough₂ params unitCodec env (runData 253 es) env
      (continuationData es ds) where
  honest := fun _ _ => Finset.mem_univ _
  gst := rfl
  delta := rfl
  seats := rfl
  inputs := fun _ _ _ _ => rfl
  awake := fun _ _ _ _ => rfl
  events := by
    intro v hv
    change v ∈ retainedSet at hv
    change (es.filter (fun e => decide (e.node ∈ retainedSet)) ++ ds).filter
      (fun e => decide (e.node = v ∧ e.time ≤ (253 : Time))) =
        es.filter (fun e => decide (e.node = v ∧ e.time ≤ (253 : Time)))
    rw [List.filter_append]
    have hs : ds.filter (fun e => decide (e.node = v ∧ e.time ≤ (253 : Time))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have ht := hds e he
      simp [not_le.mpr ht]
    rw [hs, List.append_nil, List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases he : e.node = v
    · simp [he, hv]
    · simp [he]

theorem nvGrowth_prefix_no_restart (steps : Nat) (v : Validator) (t : Time) :
    V2.Event.restart v t ∉ (buildPrefix steps).2 := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      intro he
      rcases List.mem_append.mp he with he | he
      · exact ih he
      · rcases (nvGrowth_batch_shape _ _ _ _ he).2.2 with ⟨u, hu⟩ | ⟨u, o, hu⟩ <;> cases hu

theorem nvGrowth_no_restart_of (es : List Event) (w : World)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es) :
    V2.D.NoRestart (runData 253 es) ∧
    V2.D.NoRestart (continuationData es (timeBatch retained 254 w).2) := by
  constructor
  · intro i v t he
    exact hnr v t (List.mem_of_getElem? he)
  · intro i v t he
    rcases List.mem_append.mp (List.mem_of_getElem? he) with he | he
    · exact hnr v t (List.mem_filter.mp he).1
    · rcases (nvGrowth_batch_shape retained 254 w _ he).2.2 with
        ⟨u, hu⟩ | ⟨u, o, hu⟩ <;> cases hu

theorem nvGrowth_delivery_nodup (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hn : acc.2.Nodup) :
    (xs.foldl (deliverOne t) acc).2.Nodup := by
  induction xs generalizing acc with
  | nil => exact hn
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true ∨
          (V2.Event.deliver x.1 x.2 t : Event) ∈ acc.2
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hn
      · simp only [deliverOne, hp, ↓reduceIte]
        apply ih
        apply hn.append (List.nodup_singleton _)
        intro e he hf
        obtain rfl := List.mem_singleton.mp hf
        exact hp (Or.inr he)

theorem nvGrowth_batch_nodup (vs : List Validator) (hn : vs.Nodup) (t : Time) (w : World) :
    (timeBatch vs t w).2.Nodup :=
  nvGrowth_delivery_nodup _ _ _ (hn.map (by intro v u he; cases he; rfl))

theorem nvGrowth_prefix_nodup (steps : Nat) : (buildPrefix steps).2.Nodup := by
  induction steps with
  | zero => exact List.nodup_nil
  | succ steps ih =>
      apply ih.append (nvGrowth_batch_nodup nodes (by decide) _ _)
      intro e he hb
      have hlt := (nvGrowth_prefix_times steps e he).2
      rw [(nvGrowth_batch_shape _ _ _ _ hb).1] at hlt
      exact (lt_irrefl _ hlt)

theorem nvGrowth_phase_le_two (e : Event) : e.phase ≤ 2 := by cases e <;> simp [V2.Event.phase]

theorem nvGrowth_delivery_sorted (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hs : acc.2.Pairwise (fun e f => e.key ≤ f.key))
    (ht : ∀ e ∈ acc.2, e.time ≤ t) :
    (xs.foldl (deliverOne t) acc).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true ∨
          (V2.Event.deliver x.1 x.2 t : Event) ∈ acc.2
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hs ht
      · simp only [deliverOne, hp, ↓reduceIte]
        apply ih
        · rw [List.pairwise_append]
          refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
          intro e he f hf
          obtain rfl := List.mem_singleton.mp hf
          exact Prod.Lex.toLex_le_toLex'.mpr ⟨ht e he, fun _ => nvGrowth_phase_le_two e⟩
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact ht e he
          · obtain rfl := List.mem_singleton.mp he
            exact le_rfl

theorem nvGrowth_batch_sorted (vs : List Validator) (t : Time) (w : World) :
    (timeBatch vs t w).2.Pairwise (fun e f => e.key ≤ f.key) := by
  apply nvGrowth_delivery_sorted
  · simp only [List.pairwise_map, V2.Event.key, V2.Event.time, V2.Event.phase]
    exact List.pairwise_of_forall (fun _ _ => le_rfl)
  · intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact le_rfl

theorem nvGrowth_prefix_sorted (steps : Nat) :
    (buildPrefix steps).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction steps with
  | zero => exact List.Pairwise.nil
  | succ steps ih =>
      rw [buildPrefix, List.pairwise_append]
      refine ⟨ih, nvGrowth_batch_sorted _ _ _, ?_⟩
      intro e he f hf
      have he' := (nvGrowth_prefix_times steps e he).2
      apply Prod.Lex.toLex_le_toLex'.mpr
      dsimp only
      rw [(nvGrowth_batch_shape _ _ _ _ hf).1]
      exact ⟨he'.le, fun h => False.elim (ne_of_lt he' h)⟩

/-- A duty-free round releases no object, for any state or run data. -/
theorem nvGrowth_tick_empty {p : Params} {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (st : (fgsa p c).State) (v : V) (t : Time) (hd : duties p t = []) :
    (V2.D.tick E rho st v t).2 = [] := by
  simp [V2.D.tick, fgsa, hd]
  intro _
  rfl

/-- The generator has no deliveries in a duty-free round. -/
theorem nvGrowth_batch_empty (vs : List Validator) (t : Time) (w : World)
    (hd : duties params t = []) :
    (timeBatch vs t w).2 = vs.map (fun v => .tick v t) := by
  have ht (vs : List Validator) (w : World)
      (os : List (fgsa params unitCodec).Object) :
      (vs.foldl (fun acc v =>
        let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
        (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2 = os := by
    induction vs generalizing w os with
    | nil => rfl
    | cons v vs ih =>
        exact (ih _ _).trans (by
          rw [nvGrowth_tick_empty unitCodec env _ _ v t hd, List.append_nil])
  have he : (tickBatch vs t w).2 = [] := ht vs w []
  simp [timeBatch, he]

/-- This fact holds for every prefix length, without trace evaluation. -/
theorem nvGrowth_prefix_no_delivery (steps : Nat) (v : Validator) (o : Obj params)
    (t : Time) (hd : duties params t = []) :
    V2.Event.deliver v o t ∉ (buildPrefix steps).2 := by
  induction steps with
  | zero => exact List.not_mem_nil
  | succ steps ih =>
      intro he
      rcases List.mem_append.mp he with he | he
      · exact ih he
      · have ht : t = (steps : Time) := (nvGrowth_batch_shape _ _ _ _ he).1
        rw [← ht, nvGrowth_batch_empty nodes t _ hd] at he
        obtain ⟨u, _, hu⟩ := List.mem_map.mp he
        cases hu

/-- Schedule facts proved for each symbolic prefix. -/
structure PrefixFacts (steps : Nat) (es : List Event) : Prop where
  sorted : es.Pairwise (fun e f => e.key ≤ f.key)
  nodup : es.Nodup
  times : ∀ e ∈ es, 0 ≤ e.time ∧ e.time < steps
  ticks : ∀ t, t < steps → ∀ v, V2.Event.tick v (t : Time) ∈ es
  noRestart : ∀ v t, V2.Event.restart v t ∉ es
  noDelivery : ∀ v o t, duties params t = [] → V2.Event.deliver v o t ∉ es

def certifiedPrefix (steps : Nat) :
    { data : World × List Event // PrefixFacts steps data.2 } :=
  ⟨buildPrefix steps, ⟨nvGrowth_prefix_sorted steps, nvGrowth_prefix_nodup steps,
    nvGrowth_prefix_times steps, nvGrowth_prefix_tick steps, nvGrowth_prefix_no_restart steps,
    nvGrowth_prefix_no_delivery steps⟩⟩

theorem nvGrowth_generator_env : env = GrowthGenerator.weakEnv (count := 5) := rfl

theorem nvGrowth_generator_run (h : Time) (es : List Event) :
    runData h es = GrowthGenerator.runData (count := 5) h es := by
  have hs : seatOf = GrowthGenerator.seatOf (count := 5) := by
    funext label i
    cases label <;> rfl
  simp only [runData, GrowthGenerator.runData, hs]
  congr 1

/-- The opaque fixture retains validity with its symbolic schedule facts. -/
structure ValidPrefixFacts (endpoint : Nat) (data : World × List Event) : Prop
    extends PrefixFacts (endpoint + 1) data.2 where
  valid : V2.D.ExecutionValid env (runData (endpoint : Time) data.2)
  roots : NamedRootCollisionFree params unitCodec env (runData (endpoint : Time) data.2)
  receiptRoots : NamedReceiptRootCollisionFree params unitCodec env
    (runData (endpoint : Time) data.2)
  sync : Gen.V2.Duty.PartialSynchronyBy env (runData (endpoint : Time) data.2)
    (fgsaDelay env.Δ 1)
  nextAccountable : FinalitySlashableBound params unitCodec env (runData (endpoint + 1 : Nat)
    (data.2 ++ (show List Event from
      (GrowthGenerator.timeBatch (count := 5) (endpoint + 1 : Nat) data.1).2)))
  nextSync : Gen.V2.Duty.PartialSynchronyBy env (runData (endpoint + 1 : Nat)
    (data.2 ++ (show List Event from
      (GrowthGenerator.timeBatch (count := 5) (endpoint + 1 : Nat) data.1).2)))
    (fgsaDelay env.Δ 1)
  nextRoots : NamedRootCollisionFree params unitCodec env (runData (endpoint + 1 : Nat)
    (data.2 ++ (show List Event from
      (GrowthGenerator.timeBatch (count := 5) (endpoint + 1 : Nat) data.1).2)))
  nextReceiptRoots : NamedReceiptRootCollisionFree params unitCodec env
    (runData (endpoint + 1 : Nat) (data.2 ++ (show List Event from
      (GrowthGenerator.timeBatch (count := 5) (endpoint + 1 : Nat) data.1).2)))
  nextValid : V2.D.ExecutionValid env (runData (endpoint + 1 : Nat)
    (data.2 ++ (show List Event from
      (GrowthGenerator.timeBatch (count := 5) (endpoint + 1 : Nat) data.1).2)))

/-- The W1 proof is instantiated at five validators, before the trace is sealed. -/
def certifiedValidPrefix (endpoint : Nat) :
    { data : World × List Event // ValidPrefixFacts endpoint data } :=
  ⟨GrowthGenerator.buildPrefix (count := 5) (endpoint + 1), {
    sorted := (GrowthGenerator.nvGen_prefix_execution (count := 5) endpoint).sorted
    nodup := (GrowthGenerator.nvGen_prefix_execution (count := 5) endpoint).nodup
    times := GrowthGenerator.nvGen_witness_prefix_times (count := 5) (endpoint + 1)
    ticks := GrowthGenerator.nvGen_prefix_tick (count := 5) (endpoint + 1)
    noRestart := GrowthGenerator.nvGen_prefix_no_restart (count := 5) (endpoint + 1)
    noDelivery := GrowthGenerator.nvGen_prefix_no_delivery (count := 5) (endpoint + 1)
    valid := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_execution (count := 5) endpoint
    roots := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_roots (count := 5) endpoint
    receiptRoots := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_receiptRoots (count := 5) endpoint
    sync := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_sync (count := 5) endpoint
    nextValid := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_execution (count := 5) (endpoint + 1)
    nextRoots := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_roots (count := 5) (endpoint + 1)
    nextSync := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_sync (count := 5) (endpoint + 1)
    nextReceiptRoots := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_receiptRoots (count := 5) (endpoint + 1)
    nextAccountable := by
      rw [nvGrowth_generator_env, nvGrowth_generator_run]
      exact GrowthGenerator.nvGen_prefix_accountable (count := 5) (endpoint + 1) }⟩

/-- A checked opaque value keeps the long trace out of kernel conversion.
The value is the real generator paired with its symbolic schedule proofs. -/
opaque generatedPrefix : { data : World × List Event // ValidPrefixFacts 253 data } :=
  certifiedValidPrefix 253

def source : V2.D.Run Validator (fgsa params unitCodec) := runData 253 generatedPrefix.val.2

def endWorld : World := generatedPrefix.val.1

def fullSuffix : List Event := (GrowthGenerator.timeBatch (count := 5) 254 endWorld).2

def suffix : List Event := fullSuffix.filter (fun e => decide (e.node ∈ retainedSet))

def reference : V2.D.Run Validator (fgsa params unitCodec) :=
  runData 254 (source.events ++ fullSuffix)

def continuation : V2.D.Run Validator (fgsa params unitCodec) :=
  continuationData source.events suffix

theorem nvGrowth_numbers :
    source.horizon = recoveryStart params env + B_HF params 1 4 ∧
    0 < source.horizon ∧ source.horizon < continuation.horizon ∧
    (Gen.V2.Duty.faulty source).card = 0 ∧
    (Gen.V2.Duty.faulty continuation).card = 2 ∧
    params.n < 3 * (Gen.V2.Duty.faulty continuation).card ∧
    2 * (Gen.V2.Duty.faulty continuation).card < params.n := by decide

theorem nvGrowth_source_gap (t : Time) (ht : env.t_GST ≤ t) (_hh : t + 4 ≤ source.horizon) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + 4 ∧
      Gen.V2.Duty.HonestSlot source (fgsaInterface params unitCodec) s := by
  refine ⟨(t / 4).toNat + 1, ?_, ?_, ?_⟩
  · change t < 4 * (((t / 4).toNat + 1 : Nat) : Int)
    have ht0 : (0 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · change 4 * (((t / 4).toNat + 1 : Nat) : Int) ≤ t + 4
    have ht0 : (0 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · exact ⟨Nat.zero_lt_succ _, Finset.mem_univ _⟩

theorem nvGrowth_participation (t : Time) :
    (Gen.V2.Duty.faulty continuation).card <
      (Gen.V2.Duty.awakeHonest env continuation t).card := by
  change (Finset.univ \ retainedSet).card <
    (retainedSet.filter (fun v => env.awake v t = true)).card
  simp only [env, Finset.filter_true]
  decide

theorem nvGrowth_suffix_nonempty : V2.Event.tick 0 254 ∈ suffix := by
  apply List.mem_filter.mpr
  exact ⟨GrowthGenerator.nvGen_timeBatch_tick (count := 5) 254 endWorld 0, by decide⟩

theorem nvGrowth_agreement :
    RetainedAgreesThrough₂ params unitCodec env source env continuation := by
  apply nvGrowth_agreement_of_suffix source.events suffix
  intro e he
  have ht : e.time = (254 : Time) :=
    GrowthGenerator.nvGen_timeBatch_time (count := 5) 254 endWorld e
      (List.mem_filter.mp he).1
  rw [ht]
  decide

theorem nvGrowth_no_restart : V2.D.NoRestart source ∧ V2.D.NoRestart continuation := by
  constructor
  · intro i v t hi
    exact generatedPrefix.property.noRestart v t (List.mem_of_getElem? hi)
  · intro i v t hi
    rcases List.mem_append.mp (List.mem_of_getElem? hi) with he | he
    · exact generatedPrefix.property.noRestart v t (List.mem_filter.mp he).1
    · exact GrowthGenerator.nvGen_timeBatch_no_restart (count := 5) 254 endWorld v t
        (List.mem_filter.mp he).1

theorem nvGrowth_source_in_horizon (e : Event) (he : e ∈ source.events) :
    0 ≤ e.time ∧ e.time ≤ source.horizon := by
  have ht := generatedPrefix.property.times e he
  change 0 ≤ e.time ∧ e.time ≤ 253
  simp only [Time] at *
  omega

theorem nvGrowth_source_tick_total (v : Validator) (t : Time)
    (ht : 0 ≤ t) (hh : t ≤ source.horizon) :
    V2.Event.tick v t ∈ source.events := by
  rw [← Int.toNat_of_nonneg ht]
  apply generatedPrefix.property.ticks
  change t ≤ 253 at hh
  simp only [Time] at *
  omega

theorem nvGrowth_source_schedule : V2.D.ScheduleWellFormed env source where
  horizon_nonneg := by decide
  sorted := generatedPrefix.property.sorted
  nodup := generatedPrefix.property.nodup
  in_horizon := nvGrowth_source_in_horizon
  honest_only := fun _ _ => Finset.mem_univ _
  tick_public := by
    intro v t ht
    have hn : 0 ≤ t := (nvGrowth_source_in_horizon _ ht).1
    exact ⟨t.toNat, by simpa [env] using (Int.toNat_of_nonneg hn).symm⟩
  tick_total := fun v _ t _ ht hh _ => nvGrowth_source_tick_total v t ht hh

theorem nvGrowth_continuation_schedule_of (es : List Event) (w : World)
    (hs : V2.D.ScheduleWellFormed env (runData 253 es)) :
    V2.D.ScheduleWellFormed env (continuationData es (timeBatch retained 254 w).2) where
  horizon_nonneg := by change (0 : Time) ≤ 254; decide
  sorted := by
    change (es.filter _ ++ (timeBatch retained 254 w).2).Pairwise _
    rw [List.pairwise_append]
    refine ⟨hs.sorted.filter _, nvGrowth_batch_sorted _ _ _, ?_⟩
    intro e he f hf
    have ht : e.time ≤ 253 := (hs.in_horizon e (List.mem_filter.mp he).1).2
    apply Prod.Lex.toLex_le_toLex'.mpr
    dsimp only
    rw [(nvGrowth_batch_shape retained 254 w f hf).1]
    have hlt : e.time < (254 : Time) := lt_of_le_of_lt ht (by decide)
    exact ⟨hlt.le, fun h => False.elim (ne_of_lt hlt h)⟩
  nodup := by
    apply (hs.nodup.filter _).append (nvGrowth_batch_nodup retained (by decide) _ _)
    intro e he hf
    have ht : e.time ≤ 253 := (hs.in_horizon e (List.mem_filter.mp he).1).2
    rw [(nvGrowth_batch_shape retained 254 w e hf).1] at ht
    simp only [Time] at ht
    omega
  in_horizon := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · have ht := hs.in_horizon e (List.mem_filter.mp he).1
      change 0 ≤ e.time ∧ e.time ≤ 254
      change 0 ≤ e.time ∧ e.time ≤ 253 at ht
      exact ⟨ht.1, ht.2.trans (by decide)⟩
    · rw [(nvGrowth_batch_shape retained 254 w e he).1]
      exact ⟨by decide, le_rfl⟩
  honest_only := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact of_decide_eq_true (List.mem_filter.mp he).2
    · have hv := (nvGrowth_batch_shape retained 254 w e he).2.1
      simpa [retained, retainedSet, continuationData] using hv
  tick_public := by
    intro v t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hs.tick_public v t (List.mem_filter.mp ht).1
    · have heq : t = 254 := (nvGrowth_batch_shape retained 254 w _ ht).1
      subst t
      exact ⟨254, rfl⟩
  tick_total := by
    intro v hv t hp ht hh _
    change v ∈ retainedSet at hv
    change t ≤ 254 at hh
    change V2.Event.tick v t ∈ es.filter _ ++ (timeBatch retained 254 w).2
    by_cases hbefore : t ≤ 253
    · apply List.mem_append_left
      exact List.mem_filter.mpr ⟨hs.tick_total v (Finset.mem_univ _) t hp ht hbefore rfl,
        by change decide (v ∈ retainedSet) = true; exact decide_eq_true hv⟩
    · have heq : t = 254 := by simp only [Time] at *; omega
      subst t
      apply List.mem_append_right
      exact nvGrowth_batch_tick retained 254 w v (by simpa [retained, retainedSet] using hv)

theorem nvGrowth_source_valid : V2.D.ExecutionValid env source :=
  generatedPrefix.property.valid

theorem nvGrowth_source_roots : NamedRootCollisionFree params unitCodec env source :=
  generatedPrefix.property.roots

theorem nvGrowth_source_sync :
    Gen.V2.Duty.PartialSynchronyBy env source (fgsaDelay env.Δ 1) :=
  generatedPrefix.property.sync

theorem nvGrowth_reference_valid : V2.D.ExecutionValid env reference :=
  generatedPrefix.property.nextValid

theorem nvGrowth_reference_restrict :
    continuation = GrowthRestriction.restrictRun reference retainedSet := by
  simp only [continuation, continuationData, reference, suffix, GrowthRestriction.restrictRun,
    runData, List.filter_append]

theorem nvGrowth_continuation_valid : V2.D.ExecutionValid env continuation := by
  rw [nvGrowth_reference_restrict]
  exact GrowthRestriction.nvRestrict_execution_restrict env reference retainedSet
    (by intro v _; exact Finset.mem_univ v) nvGrowth_reference_valid

theorem nvGrowth_reference_roots : NamedRootCollisionFree params unitCodec env reference :=
  generatedPrefix.property.nextRoots

theorem nvGrowth_continuation_roots : NamedRootCollisionFree params unitCodec env continuation := by
  rw [nvGrowth_reference_restrict]
  exact GrowthRestriction.nvRestrict_roots_restrict params unitCodec env reference retainedSet
    (by intro v _; exact Finset.mem_univ v) nvGrowth_reference_roots

theorem nvGrowth_reference_sync :
    Gen.V2.Duty.PartialSynchronyBy env reference (fgsaDelay env.Δ 1) :=
  generatedPrefix.property.nextSync

theorem nvGrowth_continuation_sync :
    Gen.V2.Duty.PartialSynchronyBy env continuation (fgsaDelay env.Δ 1) := by
  rw [nvGrowth_reference_restrict]
  exact GrowthRestriction.nvRestrict_sync_restrict env reference retainedSet
    (by intro v _; exact Finset.mem_univ v) (fgsaDelay env.Δ 1) nvGrowth_reference_sync
    nvGrowth_reference_valid.toScheduleWellFormed

theorem nvGrowth_reference_accountable : FinalitySlashableBound params unitCodec env reference :=
  generatedPrefix.property.nextAccountable

theorem nvGrowth_continuation_accountable :
    FinalitySlashableBound params unitCodec env continuation := by
  rw [nvGrowth_reference_restrict]
  exact GrowthRestriction.nvRestrict_accountable_restrict params unitCodec env reference retainedSet
    (by rw [← nvGrowth_reference_restrict]; exact nvGrowth_continuation_valid.toScheduleWellFormed)
    nvGrowth_reference_accountable

theorem nvGrowth_source_receiptRoots :
    NamedReceiptRootCollisionFree params unitCodec env source :=
  generatedPrefix.property.receiptRoots

theorem nvGrowth_continuation_receiptRoots :
    NamedReceiptRootCollisionFree params unitCodec env continuation := by
  rw [nvGrowth_reference_restrict]
  intro A B hA hB he
  have hscope (N : NamedProposal params.n)
      (hN : NamedProposalReceiptScope params unitCodec env
        (GrowthRestriction.restrictRun reference retainedSet) N) :
      NamedProposalReceiptScope params unitCodec env reference N := by
    rcases hN with hN | ⟨v, hv, o, t, C, hem, hp, hNC⟩
    · left
      obtain ⟨C, hC, hNC⟩ := hN
      refine ⟨C, ?_, hNC⟩
      rcases hC with ⟨v, o, t, hd, hp⟩ | ⟨v, hv, j, hC⟩
      · exact Or.inl ⟨v, o, t, (List.mem_filter.mp hd).1, hp⟩
      · obtain ⟨i, hi⟩ := GrowthRestriction.nvRestrict_state_restrict_any env reference
          retainedSet v hv j
        exact Or.inr ⟨v, Finset.mem_univ v, i, by rwa [hi] at hC⟩
    · exact Or.inr ⟨v, Finset.mem_univ v, o, t, C,
        (GrowthRestriction.nvRestrict_emits_restrict env reference retainedSet v hv o t).mp hem,
        hp, hNC⟩
  exact generatedPrefix.property.nextReceiptRoots A B (hscope A hA) (hscope B hB) he

theorem nvGrowth_continuation_schedule : V2.D.ScheduleWellFormed env continuation :=
  nvGrowth_continuation_valid.toScheduleWellFormed

theorem nvGrowth_reference_state (i : Nat) (hi : i ≤ source.events.length) :
    V2.D.Run.stateBefore env reference i = V2.D.Run.stateBefore env source i := by
  unfold V2.D.Run.stateBefore
  change ((source.events ++ fullSuffix).take i).foldl _ _ = (source.events.take i).foldl _ _
  rw [List.take_append_of_le_length hi]
  rfl

theorem nvGrowth_reference_emits {v : Validator} {o : Obj params} {t : Time}
    (hem : V2.D.Run.emits env source v o t) : V2.D.Run.emits env reference v o t := by
  obtain ⟨i, hi, ho⟩ := hem
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  have hi' : reference.events[i]? = some (.tick v t) :=
    (List.getElem?_append_left hil).trans hi
  refine ⟨i, hi', ?_⟩
  rw [(V2.D.Run.step_tick_eq env reference hi').2]
  rw [(V2.D.Run.step_tick_eq env source hi).2] at ho
  rw [nvGrowth_reference_state i hil.le]
  exact ho

/-- Pending duties retain their original trigger and use the actual reference service. -/
theorem nvGrowth_pending :
    PendingSourceDelivery₂ params unitCodec env source env continuation 1 where
  sourceBroadcast := by
    intro v _ o t hem _ w hw
    unfold SourcePendingReceipt
    intro a hta ha
    dsimp only
    intro had _ hh hlink hx
    have hem' := nvGrowth_reference_emits hem
    rw [nvGrowth_reference_restrict] at hx ⊢
    have hx' := hx
    rw [GrowthRestriction.nvRestrict_beforeTime_restrict env reference retainedSet w hw] at hx'
    exact GrowthRestriction.nvRestrict_service_restrict env reference retainedSet w hw
      nvGrowth_reference_valid.toScheduleWellFormed o a _
      (nvGrowth_reference_sync.broadcast_emitted v (Finset.mem_univ _) o t hem' w
        (Finset.mem_univ _) a hta ha had hh hh hlink hx')
  sourceRelay := by
    intro v _ i o t hacc _ w hw _
    unfold SourcePendingReceipt
    intro a hta ha
    dsimp only
    intro had _ hh hlink hx
    have hacc' : V2.D.Run.acceptsAt env reference i v o t := by
      obtain ⟨obj, hi, hhandle⟩ := hacc.1
      have hil := (List.getElem?_eq_some_iff.mp hi).1
      refine ⟨⟨obj, (List.getElem?_append_left hil).trans hi, ?_⟩, ?_, ?_⟩
      · rwa [nvGrowth_reference_state i hil.le]
      · rw [nvGrowth_reference_state i hil.le]; exact hacc.2.1
      · rw [nvGrowth_reference_state (i + 1) (Nat.succ_le_of_lt hil)]; exact hacc.2.2
    rw [nvGrowth_reference_restrict] at hx ⊢
    have hx' := hx
    rw [GrowthRestriction.nvRestrict_beforeTime_restrict env reference retainedSet w hw] at hx'
    exact GrowthRestriction.nvRestrict_service_restrict env reference retainedSet w hw
      nvGrowth_reference_valid.toScheduleWellFormed o a _
      (nvGrowth_reference_sync.relay_accepted v (Finset.mem_univ _) i o t hacc' w
        (Finset.mem_univ _) a hta ha had hh hh hlink hx')

theorem nvGrowth_partialWitness :
    V2.D.ScheduleWellFormed env source ∧
    V2.D.ScheduleWellFormed env continuation ∧
    RetainedAgreesThrough₂ params unitCodec env source env continuation ∧
    source.horizon = recoveryStart params env + B_HF params 1 4 ∧
    0 < source.horizon ∧ source.horizon < continuation.horizon ∧
    V2.Event.tick 0 254 ∈ suffix ∧
    params.n < 3 * (Gen.V2.Duty.faulty continuation).card ∧
    2 * (Gen.V2.Duty.faulty continuation).card < params.n :=
  ⟨nvGrowth_source_schedule, nvGrowth_continuation_schedule, nvGrowth_agreement, nvGrowth_numbers.1,
    nvGrowth_numbers.2.1, nvGrowth_numbers.2.2.1, nvGrowth_suffix_nonempty,
    nvGrowth_numbers.2.2.2.2.2.1, nvGrowth_numbers.2.2.2.2.2.2⟩

structure MissingFields : Prop where
  sourceValid : V2.D.ExecutionValid env source
  sourceRoots : NamedRootCollisionFree params unitCodec env source
  sourceSync : Gen.V2.Duty.PartialSynchronyBy env source (fgsaDelay env.Δ 1)
  continuationValid : V2.D.ExecutionValid env continuation
  continuationRoots : NamedRootCollisionFree params unitCodec env continuation
  continuationSync : Gen.V2.Duty.PartialSynchronyBy env continuation (fgsaDelay env.Δ 1)
  pending : PendingSourceDelivery₂ params unitCodec env source env continuation 1
  accountable : FinalitySlashableBound params unitCodec env continuation

theorem nvGrowth_missing : MissingFields := {
  sourceValid := nvGrowth_source_valid
  sourceRoots := nvGrowth_source_roots
  sourceSync := nvGrowth_source_sync
  continuationValid := nvGrowth_continuation_valid
  continuationRoots := nvGrowth_continuation_roots
  continuationSync := nvGrowth_continuation_sync
  pending := nvGrowth_pending
  accountable := nvGrowth_continuation_accountable }

theorem nvGrowth_complete_of_missing (h : MissingFields) :
    StrongRecoverySearchPrefix₂ params unitCodec env source 4 1 ∧
    CleanGrowthContinuation₂ params unitCodec env source env continuation 1 := by
  constructor
  · exact {
      sync := h.sourceSync
      deltaF := le_rfl
      gap := nvGrowth_source_gap
      base := ⟨h.sourceValid, (nvGrowth_committees source rfl).1,
        (nvGrowth_committees source rfl).2,
        (by intro v t hm; exact (nvGrowth_no_restart.1 _ v t
          (List.mem_iff_getElem?.mp hm).choose_spec).elim), rfl, nvGrowth_source_receiptRoots⟩
      fault := by decide
      awake := fun _ _ _ _ _ => rfl
      gapPos := by decide
      liveness := nvGrowth_liveness
      suffixNoRestart := by
        intro v _ i t hi _ _
        exact nvGrowth_no_restart.1 i v t hi
      joinedGap := by
        intro t ht hh
        obtain ⟨s, hs, hsg, hv⟩ := nvGrowth_source_gap t (by
          have h0 : (0 : Time) ≤ recoveryStart params env := by decide
          exact h0.trans ht) hh
        refine ⟨s, hs, hsg, hv, rfl, ?_, ?_⟩
        · intro u _ _ hw; exact Bool.noConfusion hw.2
        · intro u _ _ hm
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
          exact (nvGrowth_no_restart.1 i _ u hi).elim
      endpoint := nvGrowth_numbers.1 }
  · exact {
      base := ⟨h.continuationValid, (nvGrowth_committees continuation rfl).1,
        (nvGrowth_committees continuation rfl).2, (by
          intro v t hm
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
          exact (nvGrowth_no_restart.2 i v t hi).elim),
        rfl, nvGrowth_continuation_receiptRoots⟩
      agrees := nvGrowth_agreement
      covered := nvGrowth_numbers.2.2.1.le
      sync := h.continuationSync
      pending := h.pending
      deltaF := le_rfl
      accountable := h.accountable
      participation := fun t _ _ => nvGrowth_participation t }

theorem nvGrowth_complete :
    StrongRecoverySearchPrefix₂ params unitCodec env source 4 1 ∧
    CleanGrowthContinuation₂ params unitCodec env source env continuation 1 :=
  nvGrowth_complete_of_missing nvGrowth_missing

#print axioms nvGrowth_continuation_accountable
#print axioms nvGrowth_source_receiptRoots
#print axioms nvGrowth_continuation_receiptRoots
#print axioms nvGrowth_reference_state
#print axioms nvGrowth_reference_emits
#print axioms nvGrowth_missing
#print axioms nvGrowth_complete

#print axioms nvGrowth_numbers
#print axioms nvGrowth_agreement
#print axioms nvGrowth_suffix_nonempty
#print axioms nvGrowth_no_restart
#print axioms nvGrowth_source_schedule
#print axioms nvGrowth_source_valid
#print axioms nvGrowth_source_roots
#print axioms nvGrowth_source_sync
#print axioms nvGrowth_continuation_schedule
#print axioms nvGrowth_continuation_valid
#print axioms nvGrowth_continuation_roots
#print axioms nvGrowth_continuation_sync
#print axioms nvGrowth_pending
#print axioms nvGrowth_partialWitness
#print axioms nvGrowth_complete_of_missing

end AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthNonVacuity
end

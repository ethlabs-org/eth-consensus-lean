module
public import AvailableChainRegistry.Counter
public import AvailableChainKit.Roots

@[expose] public section

namespace AvailableChain.Registry.Counter

open AvailableChain AvailableChain.Generic AvailableChain.Framework
open AvailableChain.Statements.Generic

def counterEnv (k : Nat) : Env (Fin k.succ) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := le_rfl
  awake := fun _ _ => true

def eventsAt (k t : Nat) : List (Event (Fin k.succ) counter.Object) :=
  (List.finRange k.succ).map (fun v => .tick v (t : Time)) ++
    (List.finRange k.succ).map (fun v => .deliver v ⟨.proposer t, t + 1⟩ (t : Time))

def canonical (k H : Nat) : Run (Fin k.succ) counter where
  honest := Finset.univ
  horizon := H
  events := (List.range (H + 1)).flatMap (eventsAt k)
  seatOf := fun ℓ => ℓ.elim
  proposerOf := fun _ => 0

/-! ### Generic list and step facts -/

section Lists

variable {α : Type}

/-- In a list without duplicates, an element has one index. -/
theorem index_unique {l : List α} (hl : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hj''⟩ := List.getElem?_eq_some_iff.mp hj
  exact ((hl.getElem_inj_iff).mp hj'').symm

/-- In a list without duplicates, the element at index `p` is not among the
first `p` elements. -/
theorem not_mem_take {l : List α} (hl : l.Nodup) {p : Nat} {a : α}
    (hp : l[p]? = some a) : a ∉ l.take p := by
  intro ha
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp ha
  rw [List.getElem?_take] at hq
  split_ifs at hq with hqp
  have := index_unique hl hq hp
  omega

end Lists

section Steps

variable {V : Type} [DecidableEq V]

theorem step_tick (w : World V counter) (v : V) (t : Time) :
    World.step w (.tick v t) = w :=
  Function.update_eq_self v w

theorem step_deliver_self (w : World V counter) (v : V) (o : counter.Object) (t : Time) :
    World.step w (.deliver v o t) v = counter.process (w v) o :=
  Function.update_self _ _ _

theorem step_deliver_ne (w : World V counter) {u v : V} (h : u ≠ v) (o : counter.Object)
    (t : Time) : World.step w (.deliver v o t) u = w u :=
  Function.update_of_ne h _ _

/-- A list of ticks does not change the world. -/
theorem foldl_ticks (t : Time) :
    ∀ (l : List V) (w : World V counter),
      (l.map (fun v => Event.tick v t)).foldl World.step w = w
  | [], _ => rfl
  | v :: l, w => by
    rw [List.map_cons, List.foldl_cons, step_tick]
    exact foldl_ticks t l w

/-- A list without deliveries to `u` does not change the state of `u`. -/
theorem foldl_no_deliver (u : V) :
    ∀ (l : List (Event V counter.Object)) (w : World V counter),
      (∀ x ∈ l, ∀ o t, x ≠ .deliver u o t) → (l.foldl World.step w) u = w u
  | [], _, _ => rfl
  | x :: l, w, h => by
    rw [List.foldl_cons,
      foldl_no_deliver u l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    cases x with
    | tick v t => rw [step_tick]
    | deliver v o t =>
      have hv : u ≠ v := by
        rintro rfl
        exact h _ List.mem_cons_self o t rfl
      exact step_deliver_ne w hv o t

end Steps

/-! ### The canonical run -/

/-- The proposal of slot `m`: height `m + 1`. -/
def obj (m : Nat) : counter.Object := ⟨.proposer m, m + 1⟩

theorem process_obj (m : Nat) : counter.process m (obj m) = m + 1 := by
  simp [counter, obj]

theorem mem_eventsAt {k m : Nat} {e : Event (Fin k.succ) counter.Object} :
    e ∈ eventsAt k m ↔
      (∃ v, Event.tick v (m : Time) = e) ∨ (∃ v, Event.deliver v (obj m) (m : Time) = e) := by
  simp [eventsAt, obj]

theorem time_of_mem_eventsAt {k m : Nat} {e : Event (Fin k.succ) counter.Object}
    (he : e ∈ eventsAt k m) : e.time = m := by
  rcases mem_eventsAt.mp he with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> rfl

theorem eventsAt_nodup (k m : Nat) : (eventsAt k m).Nodup := by
  rw [eventsAt, List.nodup_append]
  refine ⟨(List.nodup_finRange _).map (fun a b h => (Event.tick.inj h).1),
    (List.nodup_finRange _).map (fun a b h => (Event.deliver.inj h).1), ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨_, _, rfl⟩ := ha
  obtain ⟨_, _, rfl⟩ := hb
  cases hab

theorem length_ticks (k m : Nat) :
    ((List.finRange k.succ).map
      (fun v => (Event.tick v (m : Time) : Event (Fin k.succ) counter.Object))).length =
      k + 1 := by
  simp

/-- The events of the first `t` times. -/
def blocks (k t : Nat) : List (Event (Fin k.succ) counter.Object) :=
  (List.range t).flatMap (eventsAt k)

theorem blocks_succ (k t : Nat) : blocks k (t + 1) = blocks k t ++ eventsAt k t := by
  simp [blocks, List.range_succ, List.flatMap_append]

theorem time_of_mem_blocks {k t : Nat} {e : Event (Fin k.succ) counter.Object}
    (he : e ∈ blocks k t) : ∃ m, m < t ∧ e.time = m := by
  obtain ⟨m, hm, hem⟩ := List.mem_flatMap.mp he
  exact ⟨m, List.mem_range.mp hm, time_of_mem_eventsAt hem⟩

/-- The events of one time move every node from `m` to `m + 1`. -/
theorem foldl_eventsAt (k m : Nat) :
    (eventsAt k m).foldl World.step (fun _ => m) =
      (fun _ => m + 1 : World (Fin k.succ) counter) := by
  set_option backward.isDefEq.respectTransparency false in
  funext u
  rw [eventsAt, List.foldl_append, foldl_ticks]
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (List.mem_finRange u)
  have hnd := List.nodup_finRange k.succ
  rw [hsplit] at hnd
  obtain ⟨_, hpost, hdisj⟩ := List.nodup_append.mp hnd
  have hu_post : u ∉ post := (List.nodup_cons.mp hpost).1
  have hu_pre : u ∉ pre := fun h => hdisj u h u List.mem_cons_self rfl
  rw [hsplit, List.map_append, List.map_cons, List.foldl_append, List.foldl_cons,
    foldl_no_deliver u]
  · rw [step_deliver_self, foldl_no_deliver u]
    · exact process_obj m
    · intro x hx o t hxo
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      cases hxo
      exact hu_pre hy
  · intro x hx o t hxo
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    cases hxo
    exact hu_post hy

/-- After the events of the first `t` times, every node is at height `t`. -/
theorem foldl_blocks (k t : Nat) :
    (blocks k t).foldl World.step World.init = (fun _ => t : World (Fin k.succ) counter) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [blocks_succ, List.foldl_append, ih, foldl_eventsAt]
    rfl

theorem canonical_events (k H : Nat) : (canonical k H).events = blocks k (H + 1) := rfl

theorem events_split (k H m : Nat) (hm : m ≤ H) :
    ∃ rest, (canonical k H).events = blocks k m ++ (eventsAt k m ++ rest) := by
  have h : H + 1 = (m + 1) + (H - m) := by omega
  refine ⟨(List.map (fun x => m + 1 + x) (List.range (H - m))).flatMap (eventsAt k), ?_⟩
  rw [canonical_events]
  unfold blocks
  rw [h, List.range_add, List.flatMap_append]
  change blocks k (m + 1) ++ _ = blocks k m ++ _
  rw [blocks_succ, List.append_assoc]

theorem canonical_nodup (k H : Nat) : (canonical k H).events.Nodup := by
  rw [canonical_events, blocks, List.nodup_flatMap]
  refine ⟨fun m _ => eventsAt_nodup k m, List.pairwise_lt_range.imp ?_⟩
  intro a b hab x hxa hxb
  have ha := time_of_mem_eventsAt hxa
  have hb := time_of_mem_eventsAt hxb
  have : (a : Time) = b := ha.symm.trans hb
  have : a = b := by exact_mod_cast this
  omega

/-- The state before index `i` is the state after the first `p` events of
the time of event `i`. -/
theorem stateBefore_index {k H i : Nat} {e : Event (Fin k.succ) counter.Object}
    (hi : (canonical k H).events[i]? = some e) :
    ∃ m p, m ≤ H ∧ (eventsAt k m)[p]? = some e ∧
      Run.stateBefore counter (canonical k H) i =
        ((eventsAt k m).take p).foldl World.step (fun _ => m) := by
  have he := List.mem_of_getElem? hi
  rw [canonical_events, blocks] at he
  obtain ⟨m, hm, hem⟩ := List.mem_flatMap.mp he
  have hmH : m ≤ H := by
    have := List.mem_range.mp hm
    omega
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hem
  have hp' : p < (eventsAt k m).length := (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨rest, hsplit⟩ := events_split k H m hmH
  have hidx : (canonical k H).events[(blocks k m).length + p]? = some e := by
    rw [hsplit, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hp']
    exact hp
  have := index_unique (canonical_nodup k H) hi hidx
  subst this
  refine ⟨m, p, hmH, hp, ?_⟩
  unfold Run.stateBefore
  rw [hsplit, List.take_length_add_append, List.foldl_append, foldl_blocks,
    List.take_append_of_le_length hp'.le]

theorem stateBefore_succ {V : Type} [DecidableEq V] {rho : Run V counter} {i : Nat}
    {e : Event V counter.Object} (hi : rho.events[i]? = some e) :
    Run.stateBefore counter rho (i + 1) = World.step (Run.stateBefore counter rho i) e := by
  unfold Run.stateBefore
  rw [List.take_add_one, List.foldl_append, hi]
  rfl

/-- At a tick, every node is at the height of the tick time. -/
theorem tick_index {k H i : Nat} {v : Fin k.succ} {t : Time}
    (hi : (canonical k H).events[i]? = some (.tick v t)) :
    ∃ m : Nat, m ≤ H ∧ t = m ∧
      Run.stateBefore counter (canonical k H) i = (fun _ => m : World (Fin k.succ) counter) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨m, p, hmH, hp, hst⟩ := stateBefore_index hi
  have ht : t = m := time_of_mem_eventsAt (List.mem_of_getElem? hp)
  refine ⟨m, hmH, ht, ?_⟩
  have hpk : p ≤ k + 1 := by
    by_contra hlt
    rw [eventsAt, List.getElem?_append_right (by rw [length_ticks]; omega)] at hp
    obtain ⟨u, _, hu⟩ := List.mem_map.mp (List.mem_of_getElem? hp)
    cases hu
  rw [hst, eventsAt, List.take_append_of_le_length (by rw [length_ticks]; exact hpk),
    ← List.map_take, foldl_ticks]

/-- At a delivery to `v`, `v` accepts the next height. -/
theorem deliver_index {k H i : Nat} {v : Fin k.succ} {o : counter.Object} {t : Time}
    (hi : (canonical k H).events[i]? = some (.deliver v o t)) :
    ∃ m : Nat, m ≤ H ∧ t = m ∧ o = obj m ∧
      Run.stateBefore counter (canonical k H) i v = m ∧
      Run.stateBefore counter (canonical k H) (i + 1) v = m + 1 := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨m, p, hmH, hp, hst⟩ := stateBefore_index hi
  have hem := List.mem_of_getElem? hp
  rcases mem_eventsAt.mp hem with ⟨u, hu⟩ | ⟨u, hu⟩
  · cases hu
  · obtain ⟨rfl, rfl, rfl⟩ := Event.deliver.inj hu
    have hbefore : Run.stateBefore counter (canonical k H) i u = m := by
      rw [hst, foldl_no_deliver u]
      intro x hx o' t' hxo
      subst hxo
      rcases mem_eventsAt.mp (List.mem_of_mem_take hx) with ⟨_, h⟩ | ⟨_, h⟩
      · cases h
      · obtain ⟨rfl, rfl, rfl⟩ := Event.deliver.inj h
        exact not_mem_take (eventsAt_nodup k m) hp hx
    refine ⟨m, hmH, rfl, rfl, hbefore, ?_⟩
    rw [stateBefore_succ hi, step_deliver_self, hbefore]
    exact process_obj m

/-- The emissions of a tick at time `m` in state `m`: node 0 proposes `m + 1`. -/
theorem emittedAt_eq {k H i : Nat} {v : Fin k.succ} {m : Nat}
    (hst : Run.stateBefore counter (canonical k H) i v = m) :
    Run.emittedAt counter (counterEnv k) (canonical k H) i v (m : Time) =
      if (0 : Fin k.succ) = v then [obj m] else [] := by
  unfold Run.emittedAt
  rw [hst]
  by_cases h0 : (0 : Fin k.succ) = v
  · simp [counter, counterEnv, canonical, obj, h0]
    rfl
  · simp [counter, counterEnv, canonical, h0]
    rfl

/-! ### Blocks -/

theorem chain_depth : ∀ m : Nat, (chain m).depth = m
  | 0 => rfl
  | m + 1 => by simp [chain, Block.depth, chain_depth m]

/-- Distinct heights give distinct blocks. -/
theorem chain_injective {i j : Nat} (h : chain i = chain j) : i = j := by
  simpa [chain_depth] using congrArg Block.depth h

theorem preceq_refl (B : Block) : Block.Preceq B B := by
  cases B <;> simp [Block.Preceq, Block.preceq]

theorem preceq_node {B p : Block} (s : Slot) (r_s : BlockId) (x : Nat) (h : Block.Preceq B p) :
    Block.Preceq B (.node p s r_s x) := by
  simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  exact Or.inr h

theorem chain_preceq : ∀ {a b : Nat}, a ≤ b → Block.Preceq (chain a) (chain b)
  | a, 0, h => by
    obtain rfl : a = 0 := by omega
    exact preceq_refl _
  | a, b + 1, h => by
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact preceq_node _ _ _ (chain_preceq (by omega))
    · obtain rfl : a = b + 1 := by omega
      exact preceq_refl _

theorem preceq_chain {B : Block} : ∀ {p : Nat}, Block.Preceq B (chain p) → ∃ j, B = chain j
  | 0, h => ⟨0, by simpa [Block.Preceq, Block.preceq, chain] using h⟩
  | p + 1, h => by
    simp only [Block.Preceq, chain, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨p + 1, h⟩
    · exact preceq_chain h

theorem blockInRun_chain {V : Type} [DecidableEq V] {E : Env V}
    {rho : Run V counter} {B : Block} (hB : BlockInRun E counterIface rho B) :
    ∃ j, B = chain j := by
  rcases hB with hB | ⟨v, o, t, tip, _, htip, hpre⟩
  · exact ⟨0, hB⟩
  · have : tip = chain o.payload := (Option.some.inj htip).symm
    subst this
    exact preceq_chain hpre

/-- Roots are computed from block content, so they are injective in every run. -/
theorem counter_rootInjective {V : Type} [DecidableEq V] (E : Env V)
    (rho : Run V counter) : RootInjective E counterIface rho :=
  by
    intro A B hA hB hr
    obtain ⟨i, rfl⟩ := blockInRun_chain hA
    obtain ⟨j, rfl⟩ := blockInRun_chain hB
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => simp [chain, Block.root, nodeRoot, genesisRoot] at hr
    | succ i =>
      cases j with
      | zero => simp [chain, Block.root, nodeRoot, genesisRoot] at hr
      | succ j =>
        simp only [chain, Block.root, nodeRoot, BlockId.mk.injEq,
          Nat.add_right_cancel_iff] at hr
        have hs := (epair_inj (epair_inj hr).2).1
        exact congrArg chain (congrArg Nat.succ hs)

theorem tick_mem {k H j : Nat} (hj : j ≤ H) (v : Fin k.succ) :
    Event.tick v (j : Time) ∈ (canonical k H).events := by
  rw [canonical_events, blocks]
  exact List.mem_flatMap.mpr
    ⟨j, List.mem_range.mpr (by omega), mem_eventsAt.mpr (Or.inl ⟨v, rfl⟩)⟩

theorem deliver_mem {k H j : Nat} (hj : j ≤ H) (v : Fin k.succ) :
    Event.deliver v (obj j) (j : Time) ∈ (canonical k H).events := by
  rw [canonical_events, blocks]
  exact List.mem_flatMap.mpr
    ⟨j, List.mem_range.mpr (by omega), mem_eventsAt.mpr (Or.inr ⟨v, rfl⟩)⟩

theorem canonical_sorted (k H : Nat) :
    (canonical k H).events.Pairwise (fun e f => e.key ≤ f.key) := by
  rw [canonical_events, blocks, List.pairwise_flatMap]
  refine ⟨fun m _ => ?_, List.pairwise_lt_range.imp ?_⟩
  · rw [eventsAt, List.pairwise_append]
    refine ⟨List.pairwise_of_forall_mem_list ?_, List.pairwise_of_forall_mem_list ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      exact le_refl _
    · intro x hx y hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      exact le_refl _
    · intro x hx y hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      change toLex ((m : Time), 0) ≤ toLex ((m : Time), 1)
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, Nat.zero_le 1⟩)
  · intro a b hab x hx y hy
    unfold Event.key
    rw [time_of_mem_eventsAt hx, time_of_mem_eventsAt hy]
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (show (a : Time) < b by exact_mod_cast hab))

theorem canonical_execution (k H : Nat) :
    ExecutionValid counter (counterEnv k) (canonical k H) := by
  refine { horizon_nonneg := Int.natCast_nonneg H
           sorted := canonical_sorted k H
           nodup := canonical_nodup k H
           in_horizon := ?_
           honest_only := fun _ _ => Finset.mem_univ _
           tick_public := ?_
           tick_total := ?_
           wire := fun _ _ _ _ _ => rfl
           deps := ?_
           fresh := ?_
           unforgeable := ?_
           carried := ?_ }
  · intro e he
    rw [canonical_events] at he
    obtain ⟨m, hm, ht⟩ := time_of_mem_blocks he
    rw [ht]
    exact ⟨Int.natCast_nonneg m,
      show (m : Time) ≤ (H : Time) by exact_mod_cast (show m ≤ H by omega)⟩
  · intro v t h
    rw [canonical_events] at h
    obtain ⟨m, _, ht⟩ := time_of_mem_blocks h
    refine ⟨m, ?_⟩
    change t = (m : Time) at ht
    rw [ht]
    exact (mul_one _).symm
  · intro v _ t ⟨j, hj⟩ _ hle
    have htj : t = j := hj.trans (mul_one _)
    subst htj
    have hjH : (j : Time) ≤ (H : Time) := hle
    exact tick_mem (by exact_mod_cast hjH) v
  · intro i v o t hi
    obtain ⟨m, _, _, rfl, hst, _⟩ := deliver_index hi
    rw [hst]
    simp [counter, obj]
  · intro i v o t hi
    obtain ⟨m, _, _, rfl, hst, _⟩ := deliver_index hi
    rw [hst]
    simp [counter, obj]
  · intro v o t ⟨i, hi⟩ u _ hu
    obtain ⟨m, hmH, rfl, rfl, _, _⟩ := deliver_index hi
    have hu0 : u = 0 := by
      simp [Run.holder, obj, canonical] at hu
      exact hu.symm
    subst hu0
    obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp (tick_mem hmH 0)
    obtain ⟨m', _, hm', hst'⟩ := tick_index hi'
    have : m' = m := by exact_mod_cast hm'.symm
    subst this
    refine ⟨m', le_rfl, i', hi', ?_⟩
    rw [emittedAt_eq (congrFun hst' 0)]
    simp
  · intro v o t _ o' h
    exact h.elim

/-- A tick emits only the proposal of its time, from node 0. -/
theorem emits_obj {k H : Nat} {v : Fin k.succ} {o : counter.Object} {t : Time}
    (h : Run.emits counter (counterEnv k) (canonical k H) v o t) :
    ∃ m : Nat, m ≤ H ∧ t = m ∧ o = obj m := by
  obtain ⟨i, hi, ho⟩ := h
  obtain ⟨m, hmH, rfl, hst⟩ := tick_index hi
  rw [emittedAt_eq (congrFun hst v)] at ho
  split_ifs at ho
  · exact ⟨m, hmH, rfl, List.mem_singleton.mp ho⟩
  · simp at ho

/-- Every node accepts the proposal of time `m` at time `m`. -/
theorem acceptsAt_obj {k H m : Nat} (hm : m ≤ H) (w : Fin k.succ) :
    ∃ j, Run.acceptsAt counter (canonical k H) j w (obj m) (m : Time) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (deliver_mem (k := k) hm w)
  obtain ⟨m', _, hm', _, hb, ha⟩ := deliver_index hj
  have : m' = m := by exact_mod_cast hm'.symm
  subst this
  refine ⟨j, ⟨obj m', hj, rfl⟩, ?_, ?_⟩
  · rw [hb]
    simp [counter, obj]
  · rw [ha]
    simp [counter, obj]

theorem deadline_lt (k m : Nat) :
    (m : Time) < max (m : Time) (counterEnv k).t_GST + (counterEnv k).Δ :=
  lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)

theorem canonical_synchrony (k H : Nat) :
    PartialSynchrony counter (counterEnv k) (canonical k H) := by
  constructor
  · intro v _ o t hem w _ _ _
    obtain ⟨m, hmH, rfl, rfl⟩ := emits_obj hem
    obtain ⟨j, hj⟩ := acceptsAt_obj hmH w
    exact ⟨m, le_rfl, deadline_lt k m, j, hj.1⟩
  · intro v _ i o t ha w _ _ _ _
    obtain ⟨o', hi, ho'⟩ := ha.1
    have ho : o' = o := ho'
    subst ho
    obtain ⟨m, hmH, rfl, rfl, _, _⟩ := deliver_index hi
    obtain ⟨j, hj⟩ := acceptsAt_obj hmH w
    exact ⟨m, le_rfl, deadline_lt k m, j, hj.1⟩

theorem canonical_relay (k H : Nat) :
    AcceptedObjectRelay counter (counterEnv k) (canonical k H) := by
  intro v _ i o t ha w _ _ _
  obtain ⟨o', hi, ho'⟩ := ha.1
  have ho : o' = o := ho'
  subst ho
  obtain ⟨m, hmH, rfl, rfl, _, _⟩ := deliver_index hi
  obtain ⟨j, hj⟩ := acceptsAt_obj hmH w
  exact ⟨m, le_rfl, deadline_lt k m, j, hj⟩

/-- Every node has accepted heights `1 … t` before time `t`. -/
theorem stateBeforeTime_eq (k H t : Nat) (ht : t ≤ H + 1) (v : Fin k.succ) :
    Run.stateBeforeTime counter (canonical k H) t v = t := by
  have hf : (canonical k H).events.filter (fun e => decide (e.time < (t : Time))) =
      blocks k t := by
    have hpre : (blocks k t).filter (fun e => decide (e.time < (t : Time))) = blocks k t := by
      apply List.filter_eq_self.mpr
      intro e he
      obtain ⟨m, hm, hem⟩ := time_of_mem_blocks he
      rw [hem]
      exact decide_eq_true (by exact_mod_cast hm)
    have hpost : ((List.map (fun x => t + x) (List.range (H + 1 - t))).flatMap (eventsAt k)).filter
        (fun e => decide (e.time < (t : Time))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he hlt
      obtain ⟨a, ha, hea⟩ := List.mem_flatMap.mp he
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      rw [time_of_mem_eventsAt hea] at hlt
      have hx : t + x < t := by exact_mod_cast (of_decide_eq_true hlt)
      omega
    have h : H + 1 = t + (H + 1 - t) := by omega
    rw [canonical_events]
    unfold blocks
    rw [h, List.range_add, List.flatMap_append, List.filter_append]
    change (blocks k t).filter _ ++ _ = blocks k t
    rw [hpre, hpost, List.append_nil]
  unfold Run.stateBeforeTime
  rw [hf, foldl_blocks]

/-- Run extension from genesis for the toy spec (design §8, Phase 0):
for every horizon, the canonical synchronous run is valid, meets both
relay conditions, and is in the Sleepy regime from 0. -/
theorem canonical_sleepy (k H : Nat) :
    SleepyRegime counter (counterEnv k) counterIface (canonical k H) 0 := by
  refine { execution := canonical_execution k H
           rootInjective := counter_rootInjective _ _
           partialSynchrony := canonical_synchrony k H
           gst_zero := rfl
           start_zero := rfl
           participation := ?_ }
  intro t _ _
  simp [AwakeMajority, faulty, awakeAt, canonical, counterEnv]

open AvailableChain.Framework.Catalog

/-- Reads only grow with time, in every run: the events up to `t` are a
sublist of the events up to `t'`. -/
theorem readAt_mono {V : Type} [DecidableEq V] (rho : Run V counter) {t t' : Time}
    (h : t ≤ t') (v : V) :
    height (Run.readAt counter rho t) v ≤ height (Run.readAt counter rho t') v :=
  foldl_sublist
    (List.monotone_filter_right _ (fun _ he =>
      decide_eq_true (le_trans (of_decide_eq_true he) h)))
    _ _ (fun _ => le_refl _) v

theorem counter_safe (W : Validators) (rho : Run W.V counter) (t₀ : Time) :
    SafeFrom counter rho counterIface.confirmed t₀ := by
  constructor
  · intro u _ v _ t t' _ _ _ _
    change Block.compatible (chain (Run.readAt counter rho t u))
      (chain (Run.readAt counter rho t' v)) = true
    unfold Block.compatible
    rw [Bool.or_eq_true]
    rcases Nat.le_total (height (Run.readAt counter rho t) u)
      (height (Run.readAt counter rho t') v) with h | h
    · exact Or.inl (chain_preceq h)
    · exact Or.inr (chain_preceq h)
  · intro v _ t t' _ htt' _
    exact chain_preceq (readAt_mono rho htt' v)

/-- The Sleepy regime of Counter has runs of every horizon. -/
theorem sleepyInhabited (H : Time) :
    ∃ (W : Validators) (E : Env W.V) (rho : Run W.V counterInst.P) (t₀ : Time),
      E.Δ = counterInst.Δ ∧ H ≤ rho.horizon ∧ sleepy counterInst W E rho t₀ :=
  ⟨⟨Fin (Nat.succ 0), inferInstance, inferInstance⟩, counterEnv 0, canonical 0 H.toNat, 0, rfl,
    Int.self_le_toNat H, canonical_sleepy 0 H.toNat⟩

def certSafeConfirmed : Cert safeConfirmed counterInst where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, ⟨E, rho⟩, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W x _ t₀ _
    exact counter_safe W x.rho t₀

def certSafeStable : Cert safeStable counterInst where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    obtain ⟨W, E, rho, t₀, hΔ, hH, hs⟩ := sleepyInhabited H
    exact ⟨W, ⟨E, rho⟩, t₀, hΔ, hH, hs, trivial⟩
  proof := by
    intro W x _ t₀ _
    exact counter_safe W x.rho t₀

def certPrefix : Cert prefixOrder counterInst where
  const := ()
  valid := trivial
  inhabited := by
    intro H
    exact ⟨⟨Fin (Nat.succ 0), inferInstance, inferInstance⟩,
      ⟨counterEnv 0, canonical 0 H.toNat⟩, (), rfl, Int.self_le_toNat H, trivial, trivial⟩
  proof := by
    intro W x _ _ _
    exact ⟨fun v _ t => preceq_refl _⟩

end AvailableChain.Registry.Counter

end

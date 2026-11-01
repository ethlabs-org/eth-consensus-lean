module
import all AvailableChainFGCompose.Tests.P0d5db
import all tests.POP6bMixedFixture

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bMixed
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db

private theorem core_premises_sat : FGCoreLaws core ∧ FGTreeKeepLaws core ∧
    (∀ i j, i ≤ j → ∀ x, TFAt core env run i x ⊆ TFAt core env run j x) ∧
    FGRunOrderLaws env run core ∧
    (∀ a b : Nat, a ≤ b → FGBlock.Preceq (chain a) (chain b)) ∧
    (∀ a b : Nat, a ≤ b → stored a ⊆ stored b) := by
  have ancestry {a b : Nat} (h : a ≤ b) : FGBlock.Preceq (chain a) (chain b) := by
    induction b with
    | zero =>
      have ha : a = 0 := by omega
      subst a
      exact preceq_refl _
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | h
      · exact preceq_refl _
      · exact preceq_node_of_preceq _ _ _ _ (ih (by omega))
  have stores {a b : Nat} (h : a ≤ b) : stored a ⊆ stored b := by
    intro X hX
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hX)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨s, List.mem_range.mpr (by
        have hs' := Nat.le_of_lt_succ (List.mem_range.mp hs)
        exact Nat.lt_succ_of_le (hs'.trans (min_le_min h le_rfl))), rfl⟩)
  have laws : FGCoreLaws core := by
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_,
      fun _ _ => List.prefix_rfl, fun _ _ => List.prefix_rfl, fun _ _ => rfl, ?_, v5erase_inj⟩
    · intro st o
      change stored st ⊆ stored (match o.payload with
        | .inr X => max st X.slot | .inl _ => st)
      cases hp : o.payload with
      | inl a => exact Finset.Subset.refl _
      | inr X => exact stores (Nat.le_max_left st X.slot)
    · intro st C hC
      have hC' : chain (min (st - 1) 64) = C := Option.some.inj hC
      rw [← hC']
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨min (st - 1) 64, List.mem_range.mpr (Nat.lt_succ_of_le
          (min_le_min (Nat.sub_le st 1) le_rfl)), rfl⟩)
  have tree : FGTreeKeepLaws core := ⟨fun _ _ => Finset.Subset.refl _⟩
  refine ⟨laws, tree, fun _ _ hij x => tf_cumulative_all core env run laws tree hij x,
    ?_, fun _ _ h => ancestry h, fun _ _ h => stores h⟩
  constructor
  intro i j x _ hij
  have hi := geometry_premises_sat.2.2 (run.stateBefore env i x)
  have hj := geometry_premises_sat.2.2 (run.stateBefore env j x)
  have hkeep := tf_cumulative_all core env run laws tree hij x
  refine ⟨preceq_refl _, le_rfl, ?_⟩
  rw [hi.hmax, hj.hmax]
  exact max_le_max (Finset.sup_mono hkeep) le_rfl

#print axioms core_premises_sat

private abbrev tickIndex (t : Nat) : Nat := 2 * t + 2 * ((t - 1) / 4)

private theorem execution_premises_sat :
    V2.D.ScheduleWellFormed env run ∧ FGHonestSeats reads run = {0} ∧
    v5E.weightOf (historyFaulty reads run) < v5E.q ∧
    (∀ t : Fin 257, run.events[tickIndex t]? = some (.tick 7 (t : Time)) ∧
      run.events[tickIndex t + 1]? = some (.tick 9 (t : Time))) := by
  have table : ∀ t : Fin 257,
      eventShape[tickIndex t]? = some (true, 7, t.val) ∧
      eventShape[tickIndex t + 1]? = some (true, 9, t.val) := by decide +kernel
  have ticks : ∀ t : Fin 257, run.events[tickIndex t]? = some (.tick 7 (t : Time)) ∧
      run.events[tickIndex t + 1]? = some (.tick 9 (t : Time)) := by
    intro t
    constructor
    · change (eventShape.map eventOf)[tickIndex t]? = _
      rw [List.getElem?_map, (table t).1]
      rfl
    · change (eventShape.map eventOf)[tickIndex t + 1]? = _
      rw [List.getElem?_map, (table t).2]
      rfl
  have info : ∀ e ∈ run.events, 0 ≤ e.time ∧ e.time ≤ 256 ∧
      e.node ∈ ({7, 9} : Finset Nat) := by
    have tab : ∀ e ∈ eventShape, 0 ≤ (eventOf e).time ∧ (eventOf e).time ≤ 256 ∧
        (eventOf e).node ∈ ({7, 9} : Finset Nat) := by decide +kernel
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact tab d hd
  refine ⟨?_, ?_, by decide, ticks⟩
  · refine ⟨by decide, ?_, ?_, fun e he => ⟨(info e he).1, (info e he).2.1⟩,
      fun e he => (info e he).2.2, ?_, ?_⟩
    · have key (e : Bool × Nat × Nat) : (eventOf e).key =
          toLex ((e.2.2 : Time), if e.1 then (1 : Nat) else 2) := by
        obtain ⟨b, x, t⟩ := e
        cases b <;> rfl
      have sorted : eventShape.Pairwise (fun a b =>
          toLex ((a.2.2 : Time), if a.1 then (1 : Nat) else 2) ≤
            toLex ((b.2.2 : Time), if b.1 then (1 : Nat) else 2)) := by
        have adjacent : (eventShape.map (fun e =>
            toLex ((e.2.2 : Time), if e.1 then (1 : Nat) else 2))).IsChain
              (fun a b => a ≤ b) := by decide +kernel
        exact List.pairwise_map.mp (List.isChain_iff_pairwise.mp adjacent)
      change (eventShape.map eventOf).Pairwise _
      rw [List.pairwise_map]
      simpa only [key] using sorted
    · have recover : Function.LeftInverse
          (fun e : V2.Event Nat protocol.Object => match e with
            | .tick x t => (true, x, t.toNat)
            | .deliver x _ t => (false, x, t.toNat)
            | .restart x t => (true, x, t.toNat)) eventOf := by
        rintro ⟨b, x, t⟩
        cases b <;> simp [eventOf]
      have adjacent : (eventShape.map (fun e => 8 * e.2.2 +
          (if e.1 then 0 else 2) + (if e.2.1 = 9 then 1 else 0))).IsChain
            (fun a b => a < b) := by decide +kernel
      have nd : eventShape.Nodup := List.Nodup.of_map _
        ((List.isChain_iff_pairwise.mp adjacent).imp ne_of_lt)
      exact List.Nodup.map recover.injective nd
    · intro x t ht
      have hn : 0 ≤ t := (info _ ht).1
      refine ⟨t.toNat, ?_⟩
      change t = (t.toNat : Int) * 1
      rw [Int.toNat_of_nonneg hn, Int.mul_one]
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 257 := by change (k : Int) * 1 ≤ 256 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa [run] using hx
      rcases hx' with rfl | rfl
      · simpa [env] using List.mem_of_getElem? (ticks ⟨k, hk⟩).1
      · simpa [env] using List.mem_of_getElem? (ticks ⟨k, hk⟩).2
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide

#print axioms execution_premises_sat

private def shapeStep (w : Nat → Nat) (e : Bool × Nat × Nat) : Nat → Nat :=
  if e.1 then w else Function.update w e.2.1 (max (w e.2.1) (e.2.2 / 4))
private def shapeState (es : List (Bool × Nat × Nat)) : Nat → Nat :=
  es.foldl shapeStep (fun _ => 0)

-- This is a proved calculation of this ordinary event fold, with the actual releases.
private theorem fold_premises_sat :
    (∀ i x, run.stateBefore env i x = shapeState (eventShape.take i) x) ∧
    (∀ t x, run.stateBeforeTime env t x =
      shapeState (eventShape.filter (fun e => decide ((e.2.2 : Time) < t))) x) ∧
    (∀ j x t, run.events[j]? = some (.tick x t) →
      postClock env run x t = some (shapeState (eventShape.take j) x)) := by
  have tick (st x : Nat) (t : Time) : (V2.D.tick env run st x t).1 = st := by
    change List.foldl (fun st (_ : protocol.Object) => st) st _ = st
    exact List.foldl_fixed _
  have step (w : Nat → Nat) (e : Bool × Nat × Nat) :
      V2.D.World.step env run w (eventOf e) = shapeStep w e := by
    obtain ⟨b, x, t⟩ := e
    cases b
    · change Function.update w x (max (w x) (chain (t / 4)).slot) =
        Function.update w x (max (w x) (t / 4))
      rw [chain_slot]
    · change Function.update w x (V2.D.tick env run (w x) x (t : Time)).1 = w
      rw [tick, Function.update_eq_self]
  have fold (es : List (Bool × Nat × Nat)) (w : Nat → Nat) :
      (es.map eventOf).foldl (V2.D.World.step env run) w = es.foldl shapeStep w := by
    rw [List.foldl_map]
    simp only [step]
  have prefixCalc (i x : Nat) : run.stateBefore env i x = shapeState (eventShape.take i) x := by
    unfold V2.D.Run.stateBefore
    change (((eventShape.map eventOf).take i).foldl (V2.D.World.step env run)
      (fun _ => 0)) x = _
    rw [← List.map_take, fold]
    rfl
  have before (t : Time) (x : Nat) : run.stateBeforeTime env t x =
      shapeState (eventShape.filter (fun e => decide ((e.2.2 : Time) < t))) x := by
    have time (e : Bool × Nat × Nat) : (eventOf e).time = (e.2.2 : Time) := by
      obtain ⟨b, x, d⟩ := e
      cases b <;> rfl
    unfold V2.D.Run.stateBeforeTime
    change (((eventShape.map eventOf).filter (fun e => decide (e.time < t))).foldl
      (V2.D.World.step env run) (fun _ => 0)) x = _
    rw [List.filter_map, fold]
    simp only [Function.comp_def, time]
    rfl
  refine ⟨prefixCalc, before, ?_⟩
  intro j x t hj
  have hjl : j < run.events.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? run x t = some k := by
    rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
    refine ⟨run.events[j], List.getElem_mem hjl, ?_⟩
    rw [(List.getElem?_eq_some_iff.mp hj).2]
    simp
  have hk' := V2.D.Run.tickIdx?_spec hk
  have hkj : k = j := by
    have hkl : k < run.events.length := (List.getElem?_eq_some_iff.mp hk').1
    apply (execution_premises_sat.1.nodup.getElem_inj_iff (hi := hkl) (hj := hjl)).mp
    rw [(List.getElem?_eq_some_iff.mp hk').2, (List.getElem?_eq_some_iff.mp hj).2]
  simp only [postClock, preTick, hk, hkj, Option.map_some]
  change some (run.stateBefore env j x) = _
  rw [prefixCalc]

#print axioms fold_premises_sat

private theorem action_premises_sat : ∀ r : Fin 32, ∀ x ∈ run.honest,
    postClock env run x (v5T.action r) = some (2 * r.val + 1) ∧
    actionSourceFG core env run v5T x r = some (some (chain (2 * r.val))) := by
  have table : ∀ r : Fin 32,
      shapeState (eventShape.take (tickIndex (8 * r.val + 6))) 7 = 2 * r.val + 1 ∧
      shapeState (eventShape.take (tickIndex (8 * r.val + 6) + 1)) 9 = 2 * r.val + 1 := by
    decide +kernel
  intro r x hx
  have hx' : x = 7 ∨ x = 9 := by simpa [run] using hx
  have ht : v5T.action r = ((8 * r.val + 6 : Nat) : Time) := by
    dsimp [v5T]
  have hs := execution_premises_sat.2.2.2 ⟨8 * r.val + 6, by omega⟩
  have hp : postClock env run x (v5T.action r) = some (2 * r.val + 1) := by
    rw [ht]
    rcases hx' with rfl | rfl
    · rw [fold_premises_sat.2.2 _ _ _ hs.1, (table r).1]
    · rw [fold_premises_sat.2.2 _ _ _ hs.2, (table r).2]
  refine ⟨hp, ?_⟩
  change (postClock env run x (v5T.action r)).map core.source = _
  rw [hp]
  change some (some (chain (min (2 * r.val) 64))) = _
  rw [Nat.min_eq_left (by omega)]

#print axioms action_premises_sat

private theorem proposal_premises_sat : ∀ s : Fin 65, 1 ≤ s.val →
    V2.D.proposerOf run iface s = 7 ∧
    HonestCarrier env run iface (kernelCarrier decodeProposal v5erase FGBlock.rows)
      s (v5erase (chain s)) (chain s).rows ∧
    postClock env run 7 (v5T.proposal s) = some (s.val - 1) := by
  have table : ∀ s : Fin 65, 1 ≤ s.val →
      shapeState (eventShape.take (tickIndex (4 * s.val))) 7 = s.val - 1 := by decide +kernel
  have out : ∀ s : Fin 65, 1 ≤ s.val → output 7 (v5T.proposal s) =
      [⟨.seat (4 * (s.val : Time)) 0, .inr (chain s)⟩] := by decide +kernel
  intro s hs
  have hp : V2.D.proposerOf run iface s = 7 := by
    change (if 4 * (s.val : Int) = 6 then 9 else 7) = 7
    rw [ite_eq_right (by omega)]
  have ht : v5T.proposal s = (4 * s.val : Nat) := by dsimp [v5T]
  have hj : run.events[tickIndex (4 * s.val)]? = some (.tick 7 (v5T.proposal s)) := by
    rw [ht]
    exact (execution_premises_sat.2.2.2 ⟨4 * s.val, by omega⟩).1
  have he : (⟨.seat (4 * (s.val : Time)) 0, .inr (chain s)⟩ : protocol.Object) ∈
      V2.D.Run.emitsAt env run (tickIndex (4 * s.val)) := by
    rw [emissions_premises_sat _ _ _ hj, out s hs]
    exact List.mem_singleton_self _
  have honest : HonestProposal env run iface s (v5erase (chain s)) :=
    ⟨⟨hs, hp ▸ (by decide)⟩, ⟨.seat (4 * (s.val : Time)) 0, .inr (chain s)⟩,
      ⟨tickIndex (4 * s.val), hp ▸ hj, he⟩, rfl⟩
  exact ⟨hp, ⟨honest, ⟨.seat (4 * (s.val : Time)) 0, .inr (chain s)⟩,
    ⟨tickIndex (4 * s.val), hp ▸ hj, he⟩, chain s, by
      change some ((chain s).slot, chain s) = _
      rw [chain_slot], rfl, rfl⟩,
    (fold_premises_sat.2.2 _ _ _ hj).trans (congrArg some (table s hs))⟩

#print axioms proposal_premises_sat

private theorem classification_premises_sat :
    (∀ s B, HonestProposal env run iface s B →
      1 ≤ s ∧ s ≤ 64 ∧ B = v5erase (chain s)) ∧
    (∀ j x r a, HonestRowAt reads env run v5T j x r a →
      r < 32 ∧ x = 9 ∧ a = wireAt r) := by
  constructor
  · intro s B h
    obtain ⟨⟨hs, _⟩, o, ⟨j, hj, ho⟩, hb⟩ := h
    have hp : V2.D.proposerOf run iface s = 7 := by
      change (if 4 * (s : Int) = 6 then 9 else 7) = 7
      rw [ite_eq_right (by omega)]
    rw [hp] at hj
    have ht := (execution_premises_sat.1.in_horizon _ (List.mem_of_getElem? hj)).2
    have hs64 : s ≤ 64 := by
      change 4 * (s : Int) ≤ 256 at ht
      have hsi : (s : Int) ≤ 64 := by omega
      exact_mod_cast hsi
    rw [emissions_premises_sat j 7 _ hj] at ho
    have table : ∀ s : Fin 65, 1 ≤ s.val → output 7 (v5T.proposal s) =
        [⟨.seat (4 * (s.val : Time)) 0, .inr (chain s)⟩] := by decide +kernel
    rw [show V2.D.proposalTime iface s = v5T.proposal s from rfl,
      table ⟨s, Nat.lt_succ_of_le hs64⟩ hs, List.mem_singleton] at ho
    subst o
    exact ⟨hs, hs64, (Option.some.inj hb).symm⟩
  · intro j x r a h
    have ht := (execution_premises_sat.1.in_horizon _ (List.mem_of_getElem? h.2.1)).2
    have hr : r < 32 := by change 8 * (r : Int) + 6 ≤ 256 at ht; omega
    have table : ∀ r : Fin 32,
        output 7 (v5T.action r) = [] ∧
        output 9 (v5T.action r) =
          [reads.encode (wireAt r)] := by decide +kernel
    have hx : x = 7 ∨ x = 9 := by simpa only [run, Finset.mem_insert,
      Finset.mem_singleton] using h.1
    have hem := h.2.2
    rw [emissions_premises_sat j x _ h.2.1] at hem
    rcases hx with rfl | rfl
    · rw [(table ⟨r, hr⟩).1] at hem
      cases hem
    · rw [(table ⟨r, hr⟩).2] at hem
      have ha := congrArg V2.Signed.payload (List.mem_singleton.mp hem)
      exact ⟨hr, rfl, Sum.inl.inj ha⟩

#print axioms classification_premises_sat

private theorem chain_premises_sat :
    (∀ A s, FGBlock.Preceq A (chain s) → ∃ a, a ≤ s ∧ A = chain a) ∧
    PromotionRowOrder core env run obs iface ∧
    (∀ r s : Nat, 2 * r + 2 ≤ s → wireAt r ∈ (chain s).rows) := by
  have ancestor (A : FGBlock (Fin 1)) (s : Nat) (h : FGBlock.Preceq A (chain s)) :
      ∃ a, a ≤ s ∧ A = chain a := by
    induction s with
    | zero => exact ⟨0, le_rfl, preceq_genesis.mp h⟩
    | succ s ih =>
      change (decide (A = chain (s + 1)) || FGBlock.preceq A (chain s)) = true at h
      rw [Bool.or_eq_true] at h
      rcases h with he | he
      · exact ⟨s + 1, le_rfl, of_decide_eq_true he⟩
      · obtain ⟨a, ha, he⟩ := ih he
        exact ⟨a, ha.trans (Nat.le_succ _), he⟩
  have root (s : Nat) : (chain s).root = if s = 0 then genesisRoot else ⟨300 + s⟩ := by
    cases s <;> rfl
  have rootInj {a b : Nat} (h : (chain a).root = (chain b).root) : a = b := by
    have hv := congrArg BlockId.value h
    rw [root, root] at hv
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp only [ha, hb, ite_true, ite_false,
      genesisRoot] at hv <;> omega
  have pair (r : Nat) : (wireAt r).height_pair =
      .vote (heightAt (2 * r)) (chain (entrySlot (2 * r))).root true := by
    rw [root]
    rfl
  refine ⟨ancestor, ?_, ?_⟩
  · intro s X height U hp _ _ hU i W hW hrow
    obtain ⟨hs, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
    subst s
    obtain ⟨a, ha, rfl⟩ := ancestor U k hU
    obtain ⟨w, hw, rfl⟩ := ancestor W k hW
    obtain ⟨row, hr, names⟩ := hrow
    cases w with
    | zero => cases hr
    | succ w =>
      change row ∈ (List.range ((w + 1) / 2)).map wireAt at hr
      obtain ⟨r, hrange, heq⟩ : ∃ r ∈ List.range ((w + 1) / 2), wireAt r = row :=
        List.mem_map.mp hr
      subst row
      have hrnum := List.mem_range.mp hrange
      obtain ⟨timeout, hpair⟩ := names.2
      rw [pair] at hpair
      have hroot := congrArg (fun p : NamedHeightPair => match p with
        | .vote _ e _ => e | .empty => genesisRoot) hpair
      change (chain (entrySlot (2 * r))).root = (chain a).root at hroot
      have hae : a = entrySlot (2 * r) := (rootInj hroot).symm
      have hentry : entrySlot (2 * r) ≤ 2 * r := Nat.mul_div_le (2 * r) 4
      apply core_premises_sat.2.2.2.2.1 a w
      omega
  · intro r s hs
    cases s with
    | zero => omega
    | succ s =>
      change wireAt r ∈ (List.range ((s + 1) / 2)).map wireAt
      exact List.mem_map.mpr ⟨r, List.mem_range.mpr (by omega), rfl⟩

#print axioms chain_premises_sat

private abbrev rowIndex (r : Nat) : Nat := tickIndex (8 * r + 6) + 1

private theorem clock_premises_sat :
    (∀ t : Fin 257, run.stateBeforeTime env (t : Time) 7 = (t.val - 1) / 4 ∧
      run.stateBeforeTime env (t : Time) 9 = (t.val - 1) / 4) ∧
    run.events.length = 642 ∧
    (∀ r : Fin 32, frontierAtIdx core env run (rowIndex r) = heightAt (2 * r.val)) := by
  have table : ∀ t : Fin 257,
      shapeState (eventShape.filter (fun e => decide ((e.2.2 : Time) < (t : Time)))) 7 =
        (t.val - 1) / 4 ∧
      shapeState (eventShape.filter (fun e => decide ((e.2.2 : Time) < (t : Time)))) 9 =
        (t.val - 1) / 4 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simp only [fold_premises_sat.2.1]
    exact table t
  · change (eventShape.map eventOf).length = 642
    rw [List.length_map]
    decide +kernel
  · have rows : ∀ r : Fin 32,
        shapeState (eventShape.take (rowIndex r)) 7 = 2 * r.val + 1 ∧
        shapeState (eventShape.take (rowIndex r)) 9 = 2 * r.val + 1 := by decide +kernel
    intro r
    unfold frontierAtIdx
    change ({7, 9} : Finset Nat).sup
      (fun x => heightAt (min (run.stateBefore env (rowIndex r) x) 64)) = _
    simp only [Finset.sup_insert, Finset.sup_singleton, fold_premises_sat.1]
    rw [(rows r).1, (rows r).2, Nat.min_eq_left (by omega)]
    have hh : heightAt (2 * r.val + 1) = heightAt (2 * r.val) := by
      dsimp only [heightAt]
      omega
    rw [hh, sup_idem]

#print axioms clock_premises_sat

private theorem observed_premises_sat :
    (∀ r x K, x ∈ run.honest →
      actionSourceFG core env run v5T x r = some (some K) →
      r < 32 ∧ K = chain (2 * r)) ∧
    (∀ r : Fin 32, HonestRowAt reads env run v5T (rowIndex r) 9 r (wireAt r)) ∧
    (∀ s : Fin 64, ∀ x ∈ run.honest,
      headAtLabel core env run v5T x s = some (v5erase (chain s))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r x K hx hs
    have hm := hs
    change (postClock env run x (v5T.action r)).map core.source = _ at hm
    obtain ⟨nd, hnd, _⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨j, hj, _⟩ := postClock_tick env run hnd
    have ht := (execution_premises_sat.1.in_horizon _ (List.mem_of_getElem? hj)).2
    have hr : r < 32 := by change 8 * (r : Int) + 6 ≤ 256 at ht; omega
    rw [(action_premises_sat ⟨r, hr⟩ x hx).2] at hs
    exact ⟨hr, (Option.some.inj (Option.some.inj hs)).symm⟩
  · have out : ∀ r : Fin 32, output 9 (v5T.action r) = [reads.encode (wireAt r)] := by
      decide +kernel
    intro r
    have hj := (execution_premises_sat.2.2.2 ⟨8 * r.val + 6, by omega⟩).2
    have hj' : run.events[rowIndex r]? = some (.tick 9 (v5T.action r)) := hj
    refine ⟨by decide, hj', ?_⟩
    rw [emissions_premises_sat _ _ _ hj', out r]
    exact List.mem_singleton_self _
  · intro s x hx
    have ht : v5T.vote s = ((4 * s.val + 1 : Nat) : Time) := by dsimp [v5T]
    have hs := execution_premises_sat.2.2.2 ⟨4 * s.val + 1, by omega⟩
    have hx' : x = 7 ∨ x = 9 := by simpa [run] using hx
    change (postClock env run x (v5T.vote s)).map (fun _ => v5erase (chain s)) = _
    rw [ht]
    rcases hx' with rfl | rfl
    · rw [fold_premises_sat.2.2 _ _ _ hs.1]
      rfl
    · rw [fold_premises_sat.2.2 _ _ _ hs.2]
      rfl

#print axioms observed_premises_sat

private theorem entry_premises_sat :
    (∀ r : Fin 32, namedEntry (wire.heightPair (wireAt r)) =
      some ((obs.height (chain (2 * r.val))).h,
        (obs.height (chain (2 * r.val))).T_h.root)) ∧
    (∀ q r : Nat, q ≤ 2 * r → r < 32 →
      OpeningCoveredFG core reads env run obs.height v5T wire.heightPair
        (FGHonestSeats reads run) r (v5erase (chain q))) ∧
    (∀ {j x r a e}, HonestRowAt reads env run v5T j x r a →
      namedEntry (wire.heightPair a) = some e → ∃ C,
      actionSourceFG core env run v5T x r = some (some C) ∧
      e = ((obs.height C).h, (obs.height C).T_h.root)) := by
  have name (r : Fin 32) : namedEntry (wire.heightPair (wireAt r)) =
      some ((obs.height (chain (2 * r.val))).h,
        (obs.height (chain (2 * r.val))).T_h.root) := by
    have facts := chain_facts_premises_sat ⟨2 * r.val, by omega⟩
    rw [facts.1, facts.2.1]
    change some (heightAt (2 * r.val),
      if entrySlot (2 * r.val) = 0 then genesisRoot else ⟨300 + entrySlot (2 * r.val)⟩) = _
    have root (s : Nat) : (chain s).root = if s = 0 then genesisRoot else ⟨300 + s⟩ := by
      cases s <;> rfl
    rw [root]
  refine ⟨name, ?_, ?_⟩
  · intro q r hqr hr i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hp := action_premises_sat ⟨r, hr⟩ 9 (by decide)
    refine ⟨chain (2 * r), 2 * r + 1, rowIndex r, r, wireAt r, hp.1, hp.2, ?_,
      v5erase_mono (core_premises_sat.2.2.2.2.1 q (2 * r) hqr), le_rfl,
      observed_premises_sat.2.1 ⟨r, hr⟩, name ⟨r, hr⟩⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨2 * r, List.mem_range.mpr (by omega), rfl⟩)
  · intro j x r a e ha he
    have hx := ha.1
    obtain ⟨hr, _, rfl⟩ := classification_premises_sat.2 j x r a ha
    exact ⟨chain (2 * r), (action_premises_sat ⟨r, hr⟩ x hx).2,
      Option.some.inj (he.symm.trans (name ⟨r, hr⟩))⟩

#print axioms entry_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end

module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainKitFG.ClientOnceSafety

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem fg_seats (rho : V2.D.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ j, rho.seatOf (.base .fg) j = e j)
    (v : V) : rho.ownSeats (.base .fg) v = [e.symm v] :=
  ownSeats_bijSeat rho (ℓ := .base .fg) e he v

private theorem visible_head (s : Slot) (j : Fin p.n) (m : Msg p.n) :
    (fgsa p c).objSelfVisible ⟨.seat (.base (.head s)) j, m⟩ = false := rfl

private theorem visible_prop (s : Slot) (j : Fin 1) (m : Msg p.n) :
    (fgsa p c).objSelfVisible ⟨.seat (.prop s) j, m⟩ = false := rfl

private theorem visible_fg (j : Fin p.n) (m : Msg p.n) :
    (fgsa p c).objSelfVisible ⟨.seat (.base .fg) j, m⟩ = true := rfl

/-- The complete self-visible output: zero or one FG row at an awake action tick. -/
theorem fgsa_tick_rows_of_seats (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ j, rho.seatOf (.base .fg) j = e j)
    (nd : Node p) (v : V) (t : Time) :
    ((V2.D.tick E rho nd v t).2.filter (fgsa p c).objSelfVisible) =
      if E.awake v t = true ∧ p.actionTime ((p.slotOf t - 1) / p.R) = t then
        (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.toList.map
          (fun body => ofRow p ⟨.seat .fg (e.symm v), body⟩)
      else [] := by
  -- Unfold protocol projections in the dependent object and event types.
  set_option backward.isDefEq.respectTransparency false in
  have ht : (V2.D.tick E rho nd v t).2 =
    (if E.awake v t then
    (duties p t).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) v).filterMap (fun j =>
      (act p c ⟨FGSA.clock p nd.st t, nd.record⟩ d (rho.input v t)).map
        (fun m => (⟨.seat (RunDuty.signLabel d) j, m⟩ : Obj p)))) ++ [] else []) := rfl
  rw [ht]
  dsimp only [duties]
  clear ht
  cases hjoin : joinedNow p (FGSA.clock p nd.st t) <;>
  cases hprop : propose p (FGSA.clock p nd.st t) (p.slotOf t) <;>
  cases hrow : (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 <;>
  split_ifs <;>
    simp_all only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.nil_append, List.append_nil] <;>
    (try dsimp only [act, actS, RunDuty.signLabel]) <;>
    (try simp only [hjoin, Bool.false_eq_true, ite_false, ite_true]) <;>
    simp_all only [Option.map_none, Option.map_some, List.filterMap_none,
      List.filter_append, fg_seats rho e he, List.filter_nil] <;>
    (try dsimp only [ofRow, ofWire, ofAuth]) <;>
    simp_all [List.filter_map, Function.comp_def, visible_head (p := p) (c := c),
      visible_prop (p := p) (c := c), visible_fg (p := p) (c := c)]

private theorem released_event (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ j, rho.seatOf (.base .fg) j = e j)
    (v : V) (k : Nat) :
    ownReleasedAt E rho v k =
      ((fgClientEvent p c E rho v k).toList.flatMap (fun ev =>
        (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho k v).st ev.2.1)
          (V2.D.Run.stateBefore E rho k v).record ⟨0, p.nPos⟩).1.toList.map
          (fun body => ofRow p ⟨.seat .fg (e.symm v), body⟩))) := by
  -- Unfold protocol projections in the dependent object and event types.
  set_option backward.isDefEq.respectTransparency false in
  rw [ownReleasedAt_def]
  unfold fgClientEvent
  cases hk : rho.events[k]? with
  | none => rfl
  | some ev =>
    cases ev with
    | restart u t =>
      have hh : V2.D.Run.emitsAt E rho k = [] := by unfold V2.D.Run.emitsAt; rw [hk]
      simp only [hh, List.filter_nil, ite_self, Option.toList_none, List.flatMap_nil]
    | deliver u o t =>
      have hh : V2.D.Run.emitsAt E rho k = [] := by unfold V2.D.Run.emitsAt; rw [hk]
      simp only [hh, List.filter_nil, ite_self, Option.toList_none, List.flatMap_nil]
    | tick u t =>
      dsimp only [Option.map, V2.Event.node]
      by_cases huv : u = v
      · subst u
        have hh := (V2.D.Run.step_tick_eq E rho hk).2
        rw [ite_eq_left rfl, hh, fgsa_tick_rows_of_seats E rho e he]
        split_ifs <;> simp_all
      · simp only [Option.some.injEq, huv, false_and, ↓reduceIte,
          Option.toList_none, List.flatMap_nil]

private theorem client_append (j : Fin p.n)
    (xs ys : List (Option (FGBlock (Fin p.n)) × HeadFields)) (Λ : RecordOnce) :
    clientRunOnce p.E p.cfg j Λ (xs ++ ys) = clientRunOnce p.E p.cfg j Λ xs ++
      clientRunOnce p.E p.cfg j
        (xs.foldl (fun rec x => (createRowOnce p.E p.cfg rec j x.1 x.2).2) Λ) ys := by
  have hr : ∀ (xs : List (Option (FGBlock (Fin p.n)) × HeadFields)) Λ,
      clientRecordOnce p.E p.cfg j Λ xs =
        xs.foldl (fun rec x => (createRowOnce p.E p.cfg rec j x.1 x.2).2) Λ := by
    intro xs
    induction xs with
    | nil => intro Λ; rfl
    | cons x xs ih => intro Λ; exact ih _
  rw [KitFG.clientRunOnce_append, hr]

private theorem client_singleton (j : Fin p.n) (Λ : RecordOnce)
    (x : Option (FGBlock (Fin p.n)) × HeadFields) :
    clientRunOnce p.E p.cfg j Λ [x] = (createRowOnce p.E p.cfg Λ j x.1 x.2).1.toList := by
  rcases x with ⟨src, hd⟩
  dsimp only [clientRunOnce]
  cases (createRowOnce p.E p.cfg Λ j src hd).1 <;> rfl

private theorem client_step (st : State p.n) (Λ : RecordOnce) (j : Fin p.n) :
    let rows := (attest p st Λ ⟨0, p.nPos⟩).1.toList.map
      (fun body => ofRow p ⟨.seat .fg j, body⟩)
    rows.foldl (recordRow? p) Λ =
      (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).2 ∧
    rows.filterMap (decodeRowObject p) =
      (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1.toList := by
  dsimp only
  rw [attest_signer_irrel st Λ ⟨0, p.nPos⟩ j]
  dsimp only [attest]
  cases ha : (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1 with
  | none =>
      have hr := KitFG.createRowOnce_none p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
      simp only [hr, Option.map_none, Option.toList_none, List.map_nil,
        List.foldl_nil, List.filterMap_nil, and_self]
  | some a =>
      obtain ⟨_, _, _, _, he, _, _, hr⟩ :=
        KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
      subst a
      simp only [hr, Option.map_some, Option.toList_some, List.map_cons,
        List.map_nil, List.foldl_cons, List.foldl_nil]
      exact ⟨rfl, rfl⟩

private theorem record_succ (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (v : V) (k : Nat) :
    (V2.D.Run.stateBefore E rho (k + 1) v).record =
      (ownReleasedAt E rho v k).foldl (recordRow? p) (V2.D.Run.stateBefore E rho k v).record := by
  -- Unfold protocol projections in the dependent object and event types.
  set_option backward.isDefEq.respectTransparency false in
  rw [ownRecord_fold_run, ownReleased_succ E rho v (Nat.zero_le k), List.foldl_append,
    ← ownRecord_fold_run]

private theorem event_input (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (v : V)
    (k : Nat) (ev) (h : fgClientEvent p c E rho v k = some ev) :
    ev.2.2.2 = fgInputs p (FGSA.clock p (V2.D.Run.stateBefore E rho k v).st ev.2.1) := by
  unfold fgClientEvent at h
  cases hk : rho.events[k]? with
  | none => rw [hk] at h; cases h
  | some event =>
    rw [hk] at h
    cases event with
    | restart u t => cases h
    | deliver u o t => cases h
    | tick u t =>
      dsimp only at h
      split_ifs at h with hg
      · obtain ⟨rfl, _, _⟩ := hg
        cases h
        rfl

private theorem trace_and_record (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ j, rho.seatOf (.base .fg) j = e j)
    (v : V) (k : Nat) :
    (V2.D.Run.stateBefore E rho k v).record =
      ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)).foldl
        (fun rec x => (createRowOnce p.E p.cfg rec (e.symm v) x.1 x.2).2) RecordOnce.initial ∧
    (ownReleased E rho v 0 k).filterMap (decodeRowObject p) =
      clientRunOnce p.E p.cfg (e.symm v) RecordOnce.initial
        ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)) := by
  -- Unfold the protocol state and object types when rewriting the two folds.
  set_option backward.isDefEq.respectTransparency false in
  induction k with
  | zero =>
      rw [ownReleased_self]
      exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hxs : (fgClientEvents p c E rho v (k + 1)).map (fun ev => ev.2.2.2) =
        (fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2) ++
          (fgClientEvent p c E rho v k).toList.map (fun ev => ev.2.2.2) := by
      unfold fgClientEvents
      rw [List.range_succ, List.filterMap_append, List.map_append]
      cases hx : fgClientEvent p c E rho v k with
      | none => rw [List.filterMap_cons_none hx]; rfl
      | some ev => rw [List.filterMap_cons_some hx]; rfl
    rw [record_succ, ownReleased_succ E rho v (Nat.zero_le k),
      List.filterMap_append, released_event E rho e he, hxs,
      List.foldl_append, client_append, ← ih.1, ih.2]
    cases hx : fgClientEvent p c E rho v k with
    | none =>
      simp only [Option.toList_none, List.flatMap_nil, List.map_nil, List.foldl_nil,
        List.filterMap_nil, List.append_nil]
      have hnil : clientRunOnce p.E p.cfg (e.symm v)
          (V2.D.Run.stateBefore E rho k v).record [] = [] := rfl
      rw [hnil, List.append_nil]
      exact ⟨trivial, rfl⟩
    | some ev =>
      have hi := event_input E rho v k ev hx
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [hi, client_singleton]
      have hs := client_step (p := p) (FGSA.clock p (V2.D.Run.stateBefore E rho k v).st ev.2.1)
        (V2.D.Run.stateBefore E rho k v).record (e.symm v)
      exact ⟨hs.1, congrArg (_ ++ ·) hs.2⟩

/-- For a fixed FG seat map, the decoded emitted rows are exactly the client
run on the actual awake action inputs, across restarts. -/
theorem fgsa_client_trace_of_seats (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ j, rho.seatOf (.base .fg) j = e j)
    (v : V) (k : Nat) :
    (ownReleased E rho v 0 k).filterMap (decodeRowObject p) =
      clientRunOnce p.E p.cfg (e.symm v) RecordOnce.initial
        ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)) :=
  (trace_and_record E rho e he v k).2

omit [DecidableEq V] in
/-- Linked supplies one seat bijection for every FG round. -/
theorem fgsa_linked_seats (rho : V2.D.Run V (fgsa p c))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    ∃ e : Fin p.n ≃ V, ∀ j, rho.seatOf (.base .fg) j = e j := by
  obtain ⟨N, e, hF⟩ := hL
  obtain ⟨hn, _⟩ := hF (.base .fg) trivial
  change p.n = N at hn
  subst N
  refine ⟨e, fun j => ?_⟩
  obtain ⟨h, hr⟩ := hF (.base .fg) trivial
  exact hr j

/-- A bijective seat map gives one owned seat for any duty label. -/
theorem fgsa_ownSeats_bijSeat (rho : V2.D.Run V (fgsa p c)) (ℓ : RunLabel)
    (e : Fin (RunLabel.seats p ℓ) ≃ V) (he : ∀ j, rho.seatOf ℓ j = e j) (v : V) :
    rho.ownSeats ℓ v = [e.symm v] :=
  ownSeats_bijSeat rho (ℓ := ℓ) e he v

/-- The run adapter and row decoder recover the actual seat's client row. -/
theorem fgsa_decode_attest_object (st : State p.n) (Λ : RecordOnce) (j : Fin p.n)
    (body : RowPayload) (h : (attest p st Λ ⟨0, p.nPos⟩).1 = some body) :
    decodeRowObject p (ofRow p ⟨.seat .fg j, body⟩) =
      (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1 :=
  fgsa_attest_decode st Λ j body h

/-- The trace under Linked uses one fixed seat and includes restarts. -/
theorem fgsa_client_trace (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    ∃ e : Fin p.n ≃ V, (∀ j, rho.seatOf (.base .fg) j = e j) ∧
      ∀ v k, (ownReleased E rho v 0 k).filterMap (decodeRowObject p) =
        clientRunOnce p.E p.cfg (e.symm v) RecordOnce.initial
          ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  exact ⟨e, he, fgsa_client_trace_of_seats E rho e he⟩

private theorem emitted_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (a : RowWire p.n) (u : Row (Fin p.n)) (k n : Nat) (t : Time)
    (hk : rho.events[k]? = some (.tick x t)) (ha : ofRow p a ∈ V2.D.Run.emitsAt E rho k)
    (hn : k < n) (hd : RowWire.toRow? a = some u) :
    u ∈ (ownReleased E rho x 0 n).filterMap (decodeRowObject p) := by
  have hs : (fgsa p c).objSelfVisible (ofRow p a) = true := by
    obtain ⟨au, body⟩ := a
    rcases au with ⟨(_ | _), _⟩ | _ | _
    · cases hd
    · rfl
    · cases hd
    · cases hd
  have hd' : decodeRowObject p (ofRow p a) = some u := by
    have heq : decodeRowObject p (ofRow p a) = RowWire.toRow? a := by
      obtain ⟨au, body⟩ := a
      rcases au with ⟨(_ | _), _⟩ | _ | _ <;> rfl
    exact heq.trans hd
  apply List.mem_filterMap.mpr
  refine ⟨ofRow p a, ?_, hd'⟩
  rw [ownReleased_def]
  apply List.mem_flatMap.mpr
  refine ⟨k, ?_, ?_⟩
  · simpa using hn
  · simp only [ownReleasedAt_def, hk, Option.map_some, V2.Event.node, ite_true]
    exact List.mem_filter.mpr ⟨ha, hs⟩

/-- Under Linked, every honest node's emitted rows contain no slashable pair.
No schedule, store invariant, or restart restriction is required. -/
theorem emittedRowsNoSlash (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x := by
  obtain ⟨e, _, htrace⟩ := fgsa_client_trace E rho hL
  intro x _ a b ha hb u v hu hv
  obtain ⟨i, t, hi, ha⟩ := ha
  obtain ⟨j, t', hj, hb⟩ := hb
  have hm := emitted_mem E rho x a u i (max i j + 1) t hi ha (by omega) hu
  have hm' := emitted_mem E rho x b v j (max i j + 1) t' hj hb (by omega) hv
  rw [htrace] at hm hm'
  exact KitFG.clientRunOnce_noSlash p.E p.cfg (e.symm x) _ u hm v hm'

end AvailableChain.FGSA.Run
end

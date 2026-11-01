module
public import AvailableChainFGCompose.Statements.SafetyStore
public import AvailableChainFGCompose.Statements.SafetyClient
public import AvailableChainKitFG.ClientOnceSafety
public import AvailableChainGeneric.Proofs.V2.Duty.Fields

public section

/-! S3a: the client trace and the honest no-slash fact over the safety reads.
Ports AvailableChainFGSARun/Proofs/ClientTrace.lean (trace_and_record,
released_event, emitted_mem, emittedRowsNoSlash). The local tick calculation
is the protocol law `FGSafetyClientLaws.tick_rows`. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Wire : Type}
variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

/-- A decoded own object records its row. -/
theorem safetyRecordStep_some {rec : RecordOnce} {o : P.Object} {u : Row (Fin n)}
    (h : S.decodeObject o = some u) : safetyRecordStep S rec o = record_row_once rec u := by
  rw [safetyRecordStep_def, h]

/-- An own object that decodes to no row leaves the record unchanged. -/
theorem safetyRecordStep_none {rec : RecordOnce} {o : P.Object}
    (h : S.decodeObject o = none) : safetyRecordStep S rec o = rec := by
  rw [safetyRecordStep_def, h]

/-- The client input of a node at its own tick. -/
theorem safetyInputAt_tick {x : V} {k : Nat} {t : Time}
    (h : rho.events[k]? = some (.tick x t)) :
    safetyInputAt S E rho x k =
      if E.awake x t = true ∧ S.enabled t = true then
        some (S.inputs (P.clock (V2.D.Run.stateBefore E rho k x) t)) else none := by
  rw [safetyInputAt_def, h]
  change (if x = x ∧ E.awake x t = true ∧ S.enabled t = true then
      some (S.inputs (P.clock (V2.D.Run.stateBefore E rho k x) t)) else none) = _
  by_cases hc : E.awake x t = true ∧ S.enabled t = true
  · rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left hc]
  · rw [ite_eq_right (fun h' => hc h'.2), ite_eq_right hc]

/-- No client input at an index that is not a tick of the node. -/
theorem safetyInputAt_other {x : V} {k : Nat}
    (h : ∀ t, rho.events[k]? ≠ some (.tick x t)) : safetyInputAt S E rho x k = none := by
  rw [safetyInputAt_def]
  cases hk : rho.events[k]? with
  | none => rfl
  | some e =>
    cases e with
    | restart y t => rfl
    | deliver y o t => rfl
    | tick y t =>
      change (if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
          some (S.inputs (P.clock (V2.D.Run.stateBefore E rho k x) t)) else none) = none
      rw [ite_eq_right]
      rintro ⟨rfl, -⟩
      exact h t hk

omit [DecidableEq V] in
/-- Linked gives one bijection between FG seats and nodes. -/
theorem safety_linked_seats (linked : P.Label → Prop) (hfg : linked S.fgLabel)
    (hl : V2.D.Linked linked rho) :
    ∃ e : Fin n ≃ V, ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i := by
  obtain ⟨N, e, hF⟩ := hl
  obtain ⟨h, hs⟩ := hF S.fgLabel hfg
  refine ⟨S.fgSeats.trans ((finCongr h).trans e), fun i => ?_⟩
  rw [hs]
  rfl

/-- The own-record step folds the decoded rows into the record. -/
theorem safety_record_fold (rec : RecordOnce) (l : List P.Object) :
    l.foldl (safetyRecordStep S) rec =
      (l.filterMap S.decodeObject).foldl record_row_once rec := by
  induction l generalizing rec with
  | nil => rfl
  | cons o l ih =>
    cases h : S.decodeObject o with
    | none =>
      rw [List.foldl_cons, List.filterMap_cons_none h, safetyRecordStep_none S h, ih]
    | some u =>
      rw [List.foldl_cons, List.filterMap_cons_some h, List.foldl_cons,
        safetyRecordStep_some S h, ih]

omit [DecidableEq V] in
private theorem safety_tick_node (x : V) (t : Time) :
    Option.map V2.Event.node (some (V2.Event.tick x t : V2.Event V P.Object)) = some x := rfl

omit [DecidableEq V] in
private theorem safety_tick_node_ne {x y : V} (t : Time) (h : y ≠ x) :
    Option.map V2.Event.node (some (V2.Event.tick y t : V2.Event V P.Object)) ≠ some x :=
  fun h' => h (Option.some.inj h')

private theorem safety_emitsAt_restart {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.restart y t)) : V2.D.Run.emitsAt E rho k = [] := by
  delta V2.D.Run.emitsAt
  rw [hk]

private theorem safety_emitsAt_deliver {k : Nat} {y : V} {o : P.Object} {t : Time}
    (hk : rho.events[k]? = some (.deliver y o t)) : V2.D.Run.emitsAt E rho k = [] := by
  delta V2.D.Run.emitsAt
  rw [hk]

/-- One client input: the released row and the record write of one step. -/
private theorem safety_run_single (Λ : RecordOnce) (i : Fin n)
    (inp : Option (FGBlock (Fin n)) × HeadFields) :
    (createRowOnce Ef cfg Λ i inp.1 inp.2).1.toList =
        clientRunOnce Ef cfg i Λ (some inp).toList ∧
      (createRowOnce Ef cfg Λ i inp.1 inp.2).1.toList.foldl record_row_once Λ =
        clientRecordOnce Ef cfg i Λ (some inp).toList := by
  obtain ⟨src, hd⟩ := inp
  dsimp only [Option.toList, clientRunOnce, clientRecordOnce]
  cases ha : (createRowOnce Ef cfg Λ i src hd).1 with
  | none => exact ⟨rfl, (KitFG.createRowOnce_none Ef cfg Λ i src hd ha).symm⟩
  | some a =>
    obtain ⟨_, _, _, _, _, _, _, hr⟩ := KitFG.createRowOnce_released Ef cfg Λ i src hd ha
    exact ⟨rfl, hr.symm⟩

/-- One event of the node: the decoded releases and the record write are one
client step on the event's input. -/
private theorem safety_client_step (J : FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
    (he : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i) (x : V) (k : Nat) :
    (V2.D.Engine.ownReleasedAt E rho x k).filterMap S.decodeObject =
        clientRunOnce Ef cfg (e.symm x) (S.record (V2.D.Run.stateBefore E rho k x))
          (safetyInputAt S E rho x k).toList ∧
      ((V2.D.Engine.ownReleasedAt E rho x k).filterMap S.decodeObject).foldl record_row_once
          (S.record (V2.D.Run.stateBefore E rho k x)) =
        clientRecordOnce Ef cfg (e.symm x) (S.record (V2.D.Run.stateBefore E rho k x))
          (safetyInputAt S E rho x k).toList := by
  cases hk : rho.events[k]? with
  | none =>
    have hi := safetyInputAt_other S E rho (x := x) (k := k) (fun t h => by
      rw [hk] at h
      cases h)
    rw [V2.D.Engine.ownReleasedAt_def, hk, ite_eq_right (by simp), hi]
    exact ⟨rfl, rfl⟩
  | some ev =>
    cases ev with
    | restart y t =>
      have hi := safetyInputAt_other S E rho (x := x) (k := k) (fun t' h => by
        rw [hk] at h
        cases h)
      rw [V2.D.Engine.ownReleasedAt_def, safety_emitsAt_restart E rho hk, List.filter_nil,
        ite_self, hi]
      exact ⟨rfl, rfl⟩
    | deliver y o t =>
      have hi := safetyInputAt_other S E rho (x := x) (k := k) (fun t' h => by
        rw [hk] at h
        cases h)
      rw [V2.D.Engine.ownReleasedAt_def, safety_emitsAt_deliver E rho hk, List.filter_nil,
        ite_self, hi]
      exact ⟨rfl, rfl⟩
    | tick y t =>
      by_cases hyx : y = x
      · rw [hyx] at hk
        rw [V2.D.Engine.ownReleasedAt_def, hk, ite_eq_left (safety_tick_node x t),
          (V2.D.Run.step_tick_eq E rho hk).2, J.tick_rows E rho e he, safetyInputAt_tick S E rho hk]
        by_cases hc : E.awake x t = true ∧ S.enabled t = true
        · rw [ite_eq_left hc, ite_eq_left hc]
          exact safety_run_single Ef cfg _ _ _
        · rw [ite_eq_right hc, ite_eq_right hc]
          exact ⟨rfl, rfl⟩
      · have hi := safetyInputAt_other S E rho (x := x) (k := k) (fun t' h => by
          rw [hk] at h
          cases h
          exact hyx rfl)
        rw [V2.D.Engine.ownReleasedAt_def, hk, ite_eq_right (safety_tick_node_ne t hyx), hi]
        exact ⟨rfl, rfl⟩

/-- For a fixed FG seat map, the own record and the decoded own releases are
the client fold over the actual awake action inputs, across restarts. -/
theorem safety_client_trace (J : FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
    (he : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i) (x : V) (k : Nat) :
    S.record (V2.D.Run.stateBefore E rho k x) =
        clientRecordOnce Ef cfg (e.symm x) RecordOnce.initial
          ((List.range k).filterMap (safetyInputAt S E rho x)) ∧
      (V2.D.Engine.ownReleased E rho x 0 k).filterMap S.decodeObject =
        clientRunOnce Ef cfg (e.symm x) RecordOnce.initial
          ((List.range k).filterMap (safetyInputAt S E rho x)) := by
  induction k with
  | zero =>
    rw [V2.D.Engine.ownReleased_self]
    exact ⟨J.initial_record, rfl⟩
  | succ k ih =>
    have hxs : (List.range (k + 1)).filterMap (safetyInputAt S E rho x) =
        (List.range k).filterMap (safetyInputAt S E rho x) ++
          (safetyInputAt S E rho x k).toList := by
      rw [List.range_succ, List.filterMap_append]
      cases hx : safetyInputAt S E rho x k with
      | none => rw [List.filterMap_cons_none hx]; rfl
      | some a => rw [List.filterMap_cons_some hx]; rfl
    have hrec : S.record (V2.D.Run.stateBefore E rho (k + 1) x) =
        (V2.D.Engine.ownReleasedAt E rho x k).foldl (safetyRecordStep S)
          (S.record (V2.D.Run.stateBefore E rho k x)) := by
      have h := Gen.V2.Duty.ownRecord_fold_restart S.record (safetyRecordStep S)
        J.clock_record J.process_record J.own_record E rho (Nat.le_succ k) x
        (fun _ t _ _ _ => J.restart_record _ t)
      rw [V2.D.Engine.ownReleased_succ E rho x (le_refl k), V2.D.Engine.ownReleased_self,
        List.nil_append] at h
      exact h
    obtain ⟨hs1, hs2⟩ := safety_client_step S Ef cfg E rho J e he x k
    rw [hxs, KitFG.clientRecordOnce_append, KitFG.clientRunOnce_append, ← ih.1, hrec,
      safety_record_fold, hs2, V2.D.Engine.ownReleased_succ E rho x (Nat.zero_le k),
      List.filterMap_append, ih.2, hs1]
    exact ⟨rfl, rfl⟩

private theorem safety_emitted_mem (W : FGSafetyWireLaws S) (x : V) (a : Wire)
    (u : Row (Fin n)) (k N : Nat) (t : Time)
    (hk : rho.events[k]? = some (.tick x t)) (ha : S.encode a ∈ V2.D.Run.emitsAt E rho k)
    (hn : k < N) (hd : S.decode a = some u) :
    u ∈ (V2.D.Engine.ownReleased E rho x 0 N).filterMap S.decodeObject := by
  have hd' : S.decodeObject (S.encode a) = some u := (W.decode_encode a).trans hd
  have hs : P.objSelfVisible (S.encode a) = true := W.decoded_visible _ u hd'
  apply List.mem_filterMap.mpr
  refine ⟨S.encode a, ?_, hd'⟩
  rw [V2.D.Engine.ownReleased_def]
  apply List.mem_flatMap.mpr
  refine ⟨k, ?_, ?_⟩
  · simpa using hn
  · rw [V2.D.Engine.ownReleasedAt_def, hk, ite_eq_left (safety_tick_node x t)]
    exact List.mem_filter.mpr ⟨ha, hs⟩

/-- Under Linked, an honest node's emitted rows contain no slashable pair. No
schedule, store invariant or restart restriction is required. -/
theorem safety_emitted_noSlash (W : FGSafetyWireLaws S) (J : FGSafetyClientLaws S Ef cfg)
    (linked : P.Label → Prop) (hfg : linked S.fgLabel) (hl : V2.D.Linked linked rho)
    (x : V) : safetyNoSlash S E rho x := by
  obtain ⟨e, he⟩ := safety_linked_seats S rho linked hfg hl
  rw [safetyNoSlash_def]
  intro a b ha hb u v hu hv
  rw [safetyEmits_def] at ha hb
  obtain ⟨i, t, hi, ha⟩ := ha
  obtain ⟨j, t', hj, hb⟩ := hb
  have hm := safety_emitted_mem S E rho W x a u i (max i j + 1) t hi ha (by omega) hu
  have hm' := safety_emitted_mem S E rho W x b v j (max i j + 1) t' hj hb (by omega) hv
  rw [(safety_client_trace S Ef cfg E rho J e he x (max i j + 1)).2] at hm hm'
  exact KitFG.clientRunOnce_noSlash Ef cfg (e.symm x) _ u hm v hm'

end AvailableChain.FGCompose
end

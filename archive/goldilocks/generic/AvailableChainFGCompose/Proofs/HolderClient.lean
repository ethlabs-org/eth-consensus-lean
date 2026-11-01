module
public import AvailableChainFGCompose.Statements.HolderClient
public import AvailableChainFGCompose.Proofs.SafetyClient
public import AvailableChainFGCompose.Proofs.RowPermission

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire Body : Type}
variable (S : FGSafetyReads P n Wire) (Ef : Electorate (Fin n)) (cfg : FGConfig)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGExecutionObs V P)
variable {holder : Fin n → V}
variable (EL : FGExecutionObsLaws E rho O) (J : FGHolderClientLaws S Ef cfg E rho O holder)

include EL in
private theorem own_source_in_segment {x : V} {j k : Nat} {e : V2.Event V P.Object}
    (he : rho.events[j]? = some e) (hk : O.start x j ≤ k) (hk' : k < O.done x j)
    (hw : O.ownWrites x k ≠ []) :
    ∃ t, rho.events[j]? = some (.tick x t) ∧ O.duty x j ≤ k := by
  obtain ⟨_, m, t, hm, hdm, hkm⟩ := EL.own_source x k hw
  have horder := EL.cut_order m _ x hm
  have hjm : j = m := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have := EL.event_order j m _ _ x he hm hlt
      omega
    · have := EL.event_order m j _ _ x hm he hgt
      omega
  subst m
  exact ⟨t, hm, hdm⟩

omit [DecidableEq V] in
include J in
private theorem record_kept (x : V) (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ O.cutLength x) (hw : ∀ k, a ≤ k → k < b → O.ownWrites x k = []) :
    S.record (O.cutState x b) = S.record (O.cutState x a) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [J.record_step x b (by omega), hw b hab (by omega)]
    exact ih (by omega) (fun k hk hk' => hw k hk (by omega))

include EL J in
/-- Non-own work up to the drained duty preserves the holder's durable record. -/
theorem holder_record_at_duty {x : V} {j : Nat} {t : Time}
    (he : rho.events[j]? = some (.tick x t)) :
    S.record (obsDutyState O x j) = S.record (O.stateBefore j x) := by
  have ho := EL.cut_order j _ x he
  rw [obsDutyState_def, ← EL.start_state j _ x he]
  apply record_kept S Ef cfg E rho O J x _ _ (by omega) (by omega)
  intro k hk hk'
  by_contra hw
  obtain ⟨_, _, hd⟩ := own_source_in_segment E rho O EL he hk (by omega) hw
  omega

omit [DecidableEq V] in
include J in
private theorem record_span (x : V) (a m : Nat) (hm : a + m ≤ O.cutLength x) :
    S.record (O.cutState x (a + m)) =
      ((List.range m).flatMap (fun i => O.ownWrites x (a + i))).foldl
        (safetyRecordStep S) (S.record (O.cutState x a)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show a + (m + 1) = a + m + 1 by omega, J.record_step x (a + m) (by omega)]
    rw [ih (by omega), List.range_succ, List.flatMap_append, List.foldl_append]
    simp

include EL J in
private theorem record_event (x : V) (j : Nat) :
    S.record (O.stateBefore (j + 1) x) =
      (obsOwnReleased O x j).foldl (safetyRecordStep S) (S.record (O.stateBefore j x)) := by
  by_cases ht : ∃ t, rho.events[j]? = some (.tick x t)
  · obtain ⟨t, ht⟩ := ht
    have ho := EL.cut_order j _ x ht
    have hr := record_span S Ef cfg E rho O J x (O.duty x j)
      (O.done x j - O.duty x j) (by omega)
    rw [Nat.add_sub_of_le ho.2.2.1, EL.own_complete j x t ht,
      EL.done_state j _ x ht] at hr
    rw [hr, ← holder_record_at_duty S Ef cfg E rho O EL J ht]
    rfl
  · have hn : ∀ t, rho.events[j]? ≠ some (.tick x t) := fun t h => ht ⟨t, h⟩
    rw [obsOwnReleased_def, EL.released_other j x hn, List.filter_nil, List.foldl_nil]
    cases he : rho.events[j]? with
    | none =>
      have hj : rho.events.length ≤ j := List.getElem?_eq_none_iff.mp he
      rw [EL.tail_state (j + 1) x (by omega), EL.tail_state j x hj]
    | some e =>
      have ho := EL.cut_order j e x he
      rw [← EL.done_state j e x he, ← EL.start_state j e x he]
      apply record_kept S Ef cfg E rho O J x _ _ (by omega) ho.2.2.2
      intro k hk hk'
      by_contra hw
      obtain ⟨t, ht, _⟩ := own_source_in_segment E rho O EL he hk hk' hw
      exact hn t ht

private theorem input_other {x : V} {j : Nat}
    (hn : ∀ t, rho.events[j]? ≠ some (.tick x t)) :
    obsSafetyInputAt S E rho O x j = none := by
  rw [obsSafetyInputAt_def]
  cases he : rho.events[j]? with
  | none => rfl
  | some e =>
    cases e with
    | restart y t => rfl
    | deliver y o t => rfl
    | tick y t =>
      dsimp only
      split_ifs with h
      · exact False.elim (hn t (by simpa [h.1] using he))
      · rfl

private theorem run_single (rec : RecordOnce) (i : Fin n)
    (inp : Option (FGBlock (Fin n)) × HeadFields) :
    (createRowOnce Ef cfg rec i inp.1 inp.2).1.toList =
      clientRunOnce Ef cfg i rec (some inp).toList ∧
    (createRowOnce Ef cfg rec i inp.1 inp.2).1.toList.foldl record_row_once rec =
      clientRecordOnce Ef cfg i rec (some inp).toList := by
  obtain ⟨src, hd⟩ := inp
  dsimp only [Option.toList, clientRunOnce, clientRecordOnce]
  cases ha : (createRowOnce Ef cfg rec i src hd).1 with
  | none => exact ⟨rfl, (KitFG.createRowOnce_none Ef cfg rec i src hd ha).symm⟩
  | some a =>
    obtain ⟨_, _, _, _, _, _, _, hr⟩ := KitFG.createRowOnce_released Ef cfg rec i src hd ha
    exact ⟨rfl, hr.symm⟩

include EL J in
private theorem holder_client_step (i : Fin n) (j : Nat) :
    (obsOwnReleased O (holder i) j).filterMap S.decodeObject =
      clientRunOnce Ef cfg i (S.record (O.stateBefore j (holder i)))
        (obsSafetyInputAt S E rho O (holder i) j).toList ∧
    ((obsOwnReleased O (holder i) j).filterMap S.decodeObject).foldl record_row_once
        (S.record (O.stateBefore j (holder i))) =
      clientRecordOnce Ef cfg i (S.record (O.stateBefore j (holder i)))
        (obsSafetyInputAt S E rho O (holder i) j).toList := by
  by_cases ht : ∃ t, rho.events[j]? = some (.tick (holder i) t)
  · obtain ⟨t, ht⟩ := ht
    rw [J.holder_rows j (holder i) t i ht rfl, obsSafetyInputAt_def, ht]
    simp only [true_and]
    rw [← holder_record_at_duty S Ef cfg E rho O EL J ht]
    by_cases hc : E.awake (holder i) t = true ∧ S.enabled t = true
    · simp only [hc]
      exact run_single Ef cfg _ i _
    · simp only [hc, ite_false]
      exact ⟨rfl, rfl⟩
  · have hn : ∀ t, rho.events[j]? ≠ some (.tick (holder i) t) := fun t h => ht ⟨t, h⟩
    rw [input_other S E rho O hn, obsOwnReleased_def, EL.released_other j (holder i) hn]
    exact ⟨rfl, rfl⟩

include EL J in
/-- Holder client trace over actual inputs; the local cut laws include every restart step. -/
theorem safety_client_trace_obs : FGHolderClientTrace S Ef cfg E rho O holder := by
  intro i _ k
  induction k with
  | zero =>
    rw [EL.init_state, J.initial_record]
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hxs : (List.range (k + 1)).filterMap (obsSafetyInputAt S E rho O (holder i)) =
        (List.range k).filterMap (obsSafetyInputAt S E rho O (holder i)) ++
          (obsSafetyInputAt S E rho O (holder i) k).toList := by
      rw [List.range_succ, List.filterMap_append]
      cases hx : obsSafetyInputAt S E rho O (holder i) k with
      | none => rw [List.filterMap_cons_none hx]; rfl
      | some a => rw [List.filterMap_cons_some hx]; rfl
    obtain ⟨hs1, hs2⟩ := holder_client_step S Ef cfg E rho O EL J i k
    rw [hxs, KitFG.clientRecordOnce_append, KitFG.clientRunOnce_append, ← ih.1,
      record_event S Ef cfg E rho O EL J, safety_record_fold, hs2]
    refine ⟨rfl, ?_⟩
    rw [obsOwnReleasedBefore_def, List.range_succ, List.flatMap_append, List.filterMap_append]
    rw [← obsOwnReleasedBefore_def, ih.2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hs1]

/-- X1c driver trace at the canonical driver observations. -/
theorem safety_client_trace_driver (F : FGDependencyDriver V Body P)
    (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object) :
    SafetyClientTraceDriverStatement S Ef cfg E rho F T Op holder := by
  intro EL J
  exact safety_client_trace_obs S Ef cfg E rho _ EL J

omit [DecidableEq V] in
private theorem holder_emitted_mem (W : FGSafetyWireLaws S) {x : V} {a : Wire}
    {u : Row (Fin n)} {t : Time} {N : Nat}
    (ha : obsEmits O rho x (S.encode a) t) (hd : S.decode a = some u)
    (hN : ∀ j, rho.events[j]? = some (.tick x t) → j < N) :
    u ∈ (obsOwnReleasedBefore O x N).filterMap S.decodeObject := by
  obtain ⟨j, hj, ha⟩ := ha
  have hd' := (W.decode_encode a).trans hd
  apply List.mem_filterMap.mpr
  refine ⟨S.encode a, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (hN j hj), ?_⟩, hd'⟩
  exact List.mem_filter.mpr ⟨ha, W.decoded_visible _ _ hd'⟩

include EL J in
/-- Actual released rows of an honest FG holder contain no slashable pair. -/
theorem safety_emitted_noSlash_obs (W : FGSafetyWireLaws S) (i : Fin n)
    (hi : holder i ∈ rho.honest) : obsSafetyNoSlash S rho O (holder i) := by
  intro a b ha hb u v hu hv
  obtain ⟨t, ha⟩ := ha
  obtain ⟨t', hb⟩ := hb
  have hm := holder_emitted_mem S rho O W ha hu (N := rho.events.length)
    (fun _ h => (List.getElem?_eq_some_iff.mp h).1)
  have hm' := holder_emitted_mem S rho O W hb hv (N := rho.events.length)
    (fun _ h => (List.getElem?_eq_some_iff.mp h).1)
  rw [(safety_client_trace_obs S Ef cfg E rho O EL J i hi rho.events.length).2] at hm hm'
  exact KitFG.clientRunOnce_noSlash Ef cfg i _ u hm v hm'

/-- X1c no-slash at the canonical driver observations. -/
theorem safety_emitted_noSlash_driver (F : FGDependencyDriver V Body P)
    (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object) :
    SafetyEmittedNoSlashDriverStatement S Ef cfg E rho F T Op holder := by
  intro EL J W i hi
  exact safety_emitted_noSlash_obs S Ef cfg E rho _ EL J W i hi

include EL J in
/-- Permission gives current or strictly earlier exact-wire coverage at the duty cut. -/
theorem rowPermission_covered_obs (H : FGHeightView (Fin n))
    (timing : FGTiming) (hT : FGTimingLaws timing)
    (entry : Wire → Option (Height × BlockId)) (W : FGRowPermissionWireLaws S entry)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hheight : ∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
      ((H C).h, (H C).T_h.root))
    (j r : Nat) (i : Fin n)
    (hi : holder i ∈ rho.honest) (htick : rho.events[j]? = some (.tick (holder i)
      (timing.action r))) (C : FGBlock (Fin n))
    (hperm : FGRowPermissionInputs S H (obsDutyState O (holder i) j) C)
    (hhist : FGRowRecordHistory (S.record (obsDutyState O (holder i) j)))
    (horigin : ∀ b ∈ (S.record (O.stateBefore j (holder i))).sent,
      ∃ k rSent a, k < j ∧ obsHonestRowAt S rho O timing k (holder i) rSent a ∧
        entry a = namedEntry b.1)
    (hawake : E.awake (holder i) (timing.action r) = true)
    (henabled : S.enabled (timing.action r) = true) :
    FGHolderRowCoverage S rho O timing entry (holder i) j r ((H C).h, (H C).T_h.root) := by
  have hrec := holder_record_at_duty S Ef cfg E rho O EL J htick
  have hp := rowPermission_pair S H _ C hperm
  have hsrc : (S.inputs (obsDutyState O (holder i) j)).1.map
      (fun C => ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root)) =
      (S.inputs (obsDutyState O (holder i) j)).1.map
        (fun C => ((H C).h, (H C).T_h.root)) := by
    congr 1
    funext C
    exact hheight C
  rw [← hsrc] at hp
  rcases p0d2_once_coverage Ef cfg _ i _ _ _ _ hhist.invariant hhist.sent_history hp with
      ⟨u, hu, hn⟩ | ⟨b, hb, hn⟩
  · have hrows := J.holder_rows j (holder i) (timing.action r) i htick rfl
    dsimp only [obsDutyState] at hu
    rw [ite_eq_left ⟨hawake, henabled⟩, hu] at hrows
    have hm : u ∈ (obsOwnReleased O (holder i) j).filterMap S.decodeObject := by
      rw [hrows]
      exact List.mem_singleton_self _
    obtain ⟨o, ho, hd⟩ := List.mem_filterMap.mp hm
    obtain ⟨a, ha, _, he⟩ := W.decoded_wire o u hd
    exact Or.inl ⟨a, ⟨hi, htick, ha ▸ (List.mem_filter.mp ho).1⟩, he.trans hn⟩
  · rw [hrec] at hb
    obtain ⟨k, rSent, a, hkj, hk, ha⟩ := horigin b hb
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk.2.1
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp htick
    have hkey := (List.pairwise_iff_getElem.mp hs.sorted) k j hkl hjl hkj
    rw [hke, hje] at hkey
    have htime := V2.D.Engine.time_le_of_key_le _ _ hkey
    change timing.action rSent ≤ timing.action r at htime
    have hr : rSent ≤ r := by
      by_contra h
      have hcast : ((r * timing.roundSlots : Nat) : Time) <
          ((rSent * timing.roundSlots : Nat) : Time) := by
        exact_mod_cast (Nat.mul_lt_mul_of_pos_right (show r < rSent by omega)
          (show 0 < timing.roundSlots by have := hT.rounds; omega))
      rw [hT.action_eq, hT.action_eq, hT.gate_eq, hT.gate_eq,
        hT.proposal_eq, hT.proposal_eq] at htime
      have := hT.delta_pos
      nlinarith
    exact Or.inr ⟨k, rSent, a, hkj, hr, hk, ha.trans hn⟩

/-- X1c current/prior coverage at the canonical driver observations. -/
theorem rowPermission_covered_driver (F : FGDependencyDriver V Body P)
    (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (H : FGHeightView (Fin n)) (timing : FGTiming)
    (entry : Wire → Option (Height × BlockId)) :
    RowPermissionCoveredDriverStatement S Ef cfg E rho F T Op holder H timing entry := by
  intro EL J hT W hs hheight i j r C hi htick hperm hhist horigin hawake henabled
  exact rowPermission_covered_obs S Ef cfg E rho _ EL J H timing hT entry W hs hheight
    j r i hi htick C hperm hhist horigin hawake henabled

end AvailableChain.FGCompose
end

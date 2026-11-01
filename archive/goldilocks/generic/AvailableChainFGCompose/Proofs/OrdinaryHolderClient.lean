module
public import AvailableChainFGCompose.Statements.HolderClient
public import AvailableChainFGCompose.Proofs.ExecutionObs
public import AvailableChainFGCompose.Proofs.SafetyClient -- shake: keep (Compose import policy)

public section

/-! Ordinary-instance bridges for X1c. These concern client records and releases only;
no driver delivery is identified with ordinary `P.process`. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire : Type}
variable (S : FGSafetyReads P n Wire) (Ef : Electorate (Fin n)) (cfg : FGConfig)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Equality: the ordinary duty state of a tick is its post-clock state. -/
theorem ordinary_obsDutyState_tick {x : V} {j : Nat} {t : Time}
    (he : rho.events[j]? = some (.tick x t)) :
    obsDutyState (ordinaryFGExecutionObs E rho) x j =
      P.clock (V2.D.Run.stateBefore E rho j x) t := by
  have h := (ordinaryFGExecutionObs_laws E rho).tick_entry j x t he
  rw [(ordinaryFGExecutionObs_laws E rho).start_state j _ x he] at h
  exact h

/-- Equality of both client inputs in the ordinary specialization. -/
theorem ordinary_obsSafetyInputAt (x : V) (j : Nat) :
    obsSafetyInputAt S E rho (ordinaryFGExecutionObs E rho) x j =
      safetyInputAt S E rho x j := by
  rw [obsSafetyInputAt_def, safetyInputAt_def]
  cases he : rho.events[j]? with
  | none => rfl
  | some e =>
    cases e with
    | restart y t => rfl
    | deliver y o t => rfl
    | tick y t =>
      dsimp only
      split_ifs with h
      · have hy := h.1
        subst y
        rw [ordinary_obsDutyState_tick E rho he]
      · rfl

/-- Equality of exact self-visible release lists at each ordinary event. -/
theorem ordinary_obsOwnReleased (x : V) (j : Nat) :
    obsOwnReleased (ordinaryFGExecutionObs E rho) x j = V2.D.Engine.ownReleasedAt E rho x j := by
  rw [obsOwnReleased_def, V2.D.Engine.ownReleasedAt_def]
  change (((rho.events[j]?).map
    (ordinaryReleaseStep E rho x (V2.D.Run.stateBefore E rho j x))).getD []).filter _ = _
  cases he : rho.events[j]? with
  | none => rfl
  | some e =>
    cases e with
    | restart y t =>
      have hn : V2.D.Run.emitsAt E rho j = [] := by
        delta V2.D.Run.emitsAt
        rw [he]
      rw [hn]
      split_ifs <;> rfl
    | deliver y o t =>
      have hn : V2.D.Run.emitsAt E rho j = [] := by
        delta V2.D.Run.emitsAt
        rw [he]
      rw [hn]
      split_ifs <;> rfl
    | tick y t =>
      change (if y = x then dependencyReleased E rho
        (P.clock (V2.D.Run.stateBefore E rho j x) t) x t else []).filter _ =
          if some y = some x then (V2.D.Run.emitsAt E rho j).filter _ else []
      by_cases h : y = x
      · subst y
        rw [ite_eq_left rfl, ite_eq_left rfl, (V2.D.Run.step_tick_eq E rho he).2]
        rfl
      · rw [ite_eq_right h, ite_eq_right (fun hh => h (Option.some.inj hh))]
        rfl

/-- Equality of the ordinary prefix release lists. -/
theorem ordinary_obsOwnReleasedBefore (x : V) (k : Nat) :
    obsOwnReleasedBefore (ordinaryFGExecutionObs E rho) x k =
      V2.D.Engine.ownReleased E rho x 0 k := by
  rw [obsOwnReleasedBefore_def, V2.D.Engine.ownReleased_def]
  simp only [Nat.sub_zero, ← List.range_eq_range']
  congr 1
  funext j
  exact ordinary_obsOwnReleased E rho x j

/-- Iff: the observed no-slash predicate specializes exactly to the frozen predicate. -/
theorem ordinary_obsSafetyNoSlash_iff (x : V) :
    obsSafetyNoSlash S rho (ordinaryFGExecutionObs E rho) x ↔ safetyNoSlash S E rho x := by
  have he (a : Wire) : (∃ t, obsEmits (ordinaryFGExecutionObs E rho) rho x (S.encode a) t) ↔
      safetyEmits S E rho x a := by
    simp only [ordinary_obsEmits_iff, safetyEmits_def]
    exact exists_comm
  simp only [obsSafetyNoSlash_def, safetyNoSlash_def, he]

/-- Iff: honest action release retains exactly the old wire and event witnesses. -/
theorem ordinary_obsHonestRowAt_iff (T : FGTiming) (j : Nat) (x : V) (r : Nat) (a : Wire) :
    obsHonestRowAt S rho (ordinaryFGExecutionObs E rho) T j x r a ↔
      HonestRowAt S E rho T j x r a := by
  have hr (he : rho.events[j]? = some (.tick x (T.action r))) :
      (ordinaryFGExecutionObs E rho).released x j = V2.D.Run.emitsAt E rho j := by
    change ((rho.events[j]?).map
      (ordinaryReleaseStep E rho x (V2.D.Run.stateBefore E rho j x))).getD [] = _
    rw [he, (V2.D.Run.step_tick_eq E rho he).2]
    change (if x = x then _ else []) = _
    rw [ite_eq_left rfl]
    rfl
  constructor
  · rintro ⟨hx, hj, ha⟩
    exact ⟨hx, hj, hr hj ▸ ha⟩
  · rintro ⟨hx, hj, ha⟩
    exact ⟨hx, hj, (hr hj).symm ▸ ha⟩

/-- Iff: the holder trace specializes to the ordinary record and release trace. -/
theorem ordinary_FGHolderClientTrace_iff (holder : Fin n → V) :
    FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho) holder ↔
      ∀ i, holder i ∈ rho.honest → ∀ k,
        S.record (V2.D.Run.stateBefore E rho k (holder i)) =
          clientRecordOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (safetyInputAt S E rho (holder i))) ∧
        (V2.D.Engine.ownReleased E rho (holder i) 0 k).filterMap S.decodeObject =
          clientRunOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (safetyInputAt S E rho (holder i))) := by
  simp only [FGHolderClientTrace_def, ordinary_obsOwnReleasedBefore, ordinary_obsSafetyInputAt]
  rfl

/-- One-way: the current/prior split implies the frozen existential coverage conclusion.
That conclusion forgets whether the release was current or strictly earlier. -/
theorem ordinary_rowPermission_covered (T : FGTiming)
    (entry : Wire → Option (Height × BlockId)) (x : V) (j r : Nat)
    (target : Height × BlockId)
    (h : FGHolderRowCoverage S rho (ordinaryFGExecutionObs E rho) T entry x j r target) :
    ∃ k rSent a, rSent ≤ r ∧ HonestRowAt S E rho T k x rSent a ∧ entry a = some target := by
  rcases h with ⟨a, ha, he⟩ | ⟨k, rSent, a, _, hr, ha, he⟩
  · exact ⟨j, r, a, le_rfl, (ordinary_obsHonestRowAt_iff S E rho T j x r a).1 ha, he⟩
  · exact ⟨k, rSent, a, hr, (ordinary_obsHonestRowAt_iff S E rho T k x rSent a).1 ha, he⟩

private theorem record_entry (J : FGSafetyClientLaws S Ef cfg) (x : V) (j : Nat) :
    S.record (ordinaryEntry E rho x j) = S.record (V2.D.Run.stateBefore E rho j x) := by
  rw [ordinaryEntry_def]
  cases he : rho.events[j]? with
  | none => rfl
  | some e =>
    dsimp only [Option.map, Option.getD]
    cases e with
    | restart y t =>
      dsimp only [ordinaryEntryStep]
      split_ifs <;> simp only [J.restart_record]
    | tick y t =>
      dsimp only [ordinaryEntryStep]
      split_ifs <;> simp only [J.clock_record]
    | deliver y o t =>
      dsimp only [ordinaryEntryStep]
      split_ifs <;> simp only [J.process_record]

private theorem record_prefix (J : FGSafetyClientLaws S Ef cfg) (x : V) (j : Nat) :
    S.record (V2.D.Run.stateBefore E rho (j + 1) x) =
      (V2.D.Engine.ownReleasedAt E rho x j).foldl (safetyRecordStep S)
        (S.record (V2.D.Run.stateBefore E rho j x)) := by
  have h := Gen.V2.Duty.ownRecord_fold_restart S.record (safetyRecordStep S)
    J.clock_record J.process_record J.own_record E rho (Nat.le_succ j) x
    (fun _ t _ _ _ => J.restart_record _ t)
  rw [V2.D.Engine.ownReleased_succ E rho x (le_refl j), V2.D.Engine.ownReleased_self,
    List.nil_append] at h
  exact h

private theorem holder_cut_start (x : V) (j : Nat) :
    ordinaryCutState E rho x (3 * j) = V2.D.Run.stateBefore E rho j x := by
  rw [ordinaryCutState_def, ite_eq_left (by omega), show 3 * j / 3 = j by omega]

private theorem holder_cut_entry (x : V) (j : Nat) :
    ordinaryCutState E rho x (3 * j + 1) = ordinaryEntry E rho x j := by
  rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_left (by omega),
    show (3 * j + 1) / 3 = j by omega]

private theorem holder_cut_done (x : V) (j : Nat) :
    ordinaryCutState E rho x (3 * j + 2) = V2.D.Run.stateBefore E rho (j + 1) x := by
  rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_right (by omega),
    show (3 * j + 2) / 3 = j by omega]

/-- One-way: global ordinary client laws imply run-local holder laws when the caller
explicitly supplies a bijection. This specialization does not restrict the general driver. -/
theorem ordinary_FGHolderClientLaws (J : FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
    (he : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i) :
    FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho) e where
  holder_eq := he
  holder_inj := e.injective
  initial_record := J.initial_record
  record_step x k _ := by
    change S.record (ordinaryCutState E rho x (k + 1)) =
      (if k % 3 = 1 then obsOwnReleased (ordinaryFGExecutionObs E rho) x (k / 3)
        else []).foldl (safetyRecordStep S) (S.record (ordinaryCutState E rho x k))
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 3 ∧ k = 3 * j + r :=
      ⟨k / 3, k % 3, by omega, by omega⟩
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    · simp only [Nat.add_zero]
      rw [holder_cut_start, holder_cut_entry,
        ite_eq_right (by omega), List.foldl_nil]
      exact record_entry S Ef cfg E rho J x j
    · rw [show 3 * j + 1 + 1 = 3 * j + 2 by omega, holder_cut_entry, holder_cut_done,
        ite_eq_left (by omega), show (3 * j + 1) / 3 = j by omega,
        ordinary_obsOwnReleased, record_entry S Ef cfg E rho J]
      exact record_prefix S Ef cfg E rho J x j
    · rw [holder_cut_done, show 3 * j + 2 + 1 = 3 * (j + 1) by omega, holder_cut_start,
        ite_eq_right (by omega), List.foldl_nil]
  holder_rows j x t i ht hi := by
    rw [ordinary_obsOwnReleased]
    rw [V2.D.Engine.ownReleasedAt_def, ht]
    rw [ite_eq_left (show Option.map V2.Event.node
      (some (.tick x t : V2.Event V P.Object)) = some x from rfl)]
    rw [(V2.D.Run.step_tick_eq E rho ht).2, J.tick_rows E rho e he]
    have hd := ordinary_obsDutyState_tick E rho ht
    dsimp only [obsDutyState] at hd
    rw [hd, J.clock_record, ← hi, e.symm_apply_apply]
  nonholder_rows j x t ht hn := by
    obtain ⟨i, hi⟩ := e.surjective x
    exact False.elim (hn i hi)

end AvailableChain.FGCompose
end

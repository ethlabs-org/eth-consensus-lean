module
public import AvailableChainFGSARun.Proofs.ClockLaws -- shake: keep (re-export)
public import AvailableChainGeneric.Proofs.V2.Duty.Fields

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem emission_if_some {α : Type} (b : Bool) (o : Option α) (a : α) :
    (if b then o else none) = some a ↔ b = true ∧ o = some a := by
  cases b <;> simp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The record fold includes all ticks before `i`, across restarts. -/
theorem ownRecord_fold_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) :
    (V2.D.Run.stateBefore E rho i v).record =
      (ownReleased E rho v 0 i).foldl (recordRow? p) RecordOnce.initial := by
  have h := Gen.V2.Duty.ownRecord_fold_restart (P := fgsa p c) Node.record (recordRow? p)
    clock_rec process_rec recordOwn_rec E rho (Nat.zero_le i) v
    (fun k t _ _ _ => restore_rec p c ((fgsa p c).durable (V2.D.Run.stateBefore E rho k v)) t)
  exact h

/-- [ROOT-DIGEST-2 W2; DC HEAD] Exact identifier emission at a tick. -/
theorem fgsa_emits_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (s : Slot) (j : Fin p.n) (b : BlockId) :
    (⟨.seat (.base (.head s)) j, .head b⟩ : Obj p) ∈ (V2.D.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.voteTime p.toParams s = t ∧
      rho.seatOf (.base (.head s)) j = v ∧
      joinedNow p (FGSA.clock p nd.st t) = true ∧
      b = (headVote p (FGSA.clock p nd.st t) s).root := by
  refine (Gen.V2.Duty.mem_tick_singleDuty_iff (P := fgsa p c) E rho nd v t
    (.base (.head s)) (fgsa_head_singleDuty s) (.headAction s) rfl j (.head b)).trans ?_
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    (emission_if_some _ _ _).trans (and_congr_right fun _ => by
      simp only [Option.some.injEq, Msg.head.injEq]
      exact eq_comm)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Exact FG emission includes the scheduled action that produced the row. -/
theorem fgsa_emits_row (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (j : Fin p.n) (body : RowPayload) :
    ofRow p ⟨.seat .fg j, body⟩ ∈ (V2.D.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ rho.seatOf (.base .fg) j = v ∧
      ∃ r, p.actionTime r = t ∧
        (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 = some body := by
  change (⟨.seat (.base .fg) j, .row body⟩ : Obj p) ∈ _ ↔ _
  refine (mem_tick_seat_iff (P := fgsa p c) E rho nd v t (.base .fg) j (.row body)).trans ?_
  constructor
  · rintro ⟨hw, hi, d, hl, ht, ha⟩
    change RunDuty.signLabel d = .base .fg at hl
    cases d with
    | headAction s => cases hl
    | propAction s => cases hl
    | fgAction r =>
        refine ⟨hw, hi, r, ht, ?_⟩
        change (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.map Msg.row =
          some (.row body) at ha
        simpa only [Option.map_eq_some_iff, Msg.row.injEq, exists_eq_right] using ha
  · rintro ⟨hw, hi, r, ht, ha⟩
    refine ⟨hw, hi, .fgAction r, rfl, ht, ?_⟩
    change (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.map Msg.row = _
    rw [ha]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Exact row emission at a tick event, without a free row-round parameter. -/
theorem fgsa_emitsAt_row (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (v : V) (t : Time) (hk : rho.events[k]? = some (.tick v t))
    (j : Fin p.n) (body : RowPayload) :
    ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho k ↔
      E.awake v t = true ∧ rho.seatOf (.base .fg) j = v ∧
      ∃ r, p.actionTime r = t ∧
        (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho k v).st t)
          (V2.D.Run.stateBefore E rho k v).record ⟨0, p.nPos⟩).1 = some body := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2]
  exact fgsa_emits_row E rho _ v t j body

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Exact proposal emission uses the proposal label's unique duty. -/
theorem fgsa_emits_proposal (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (s : Slot) (m : Msg p.n) :
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩ : Obj p) ∈ (V2.D.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.proposalTime p.toParams s = t ∧
      rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = v ∧
      joinedNow p (FGSA.clock p nd.st t) = true ∧
      (propose p (FGSA.clock p nd.st t) s).map (withApp p (c.app (rho.input v t))) = some m :=
  by
    have h := Gen.V2.Duty.mem_tick_singleDuty_iff E rho nd v t (.prop s)
      (fgsa_prop_singleDuty s) (.propAction s) rfl ⟨0, Nat.one_pos⟩ m
    refine h.trans ?_
    exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      emission_if_some _ _ _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Sleep releases no object and keeps the record. -/
theorem fgsa_tick_asleep (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (h : E.awake v t = false) :
    (V2.D.tick E rho nd v t).2 = [] ∧ (V2.D.tick E rho nd v t).1.record = nd.record := by
  rw [V2.D.tick_asleep E rho nd h]
  exact ⟨rfl, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The wire decoder recovers the client row with the actual seat. -/
theorem fgsa_attest_decode (st : State p.n) (Λ : RecordOnce) (j : Fin p.n)
    (payload : RowPayload) (h : (attest p st Λ ⟨0, p.nPos⟩).1 = some payload) :
    RowWire.toRow? (⟨.seat .fg j, payload⟩ : RowWire p.n) =
      (createRowOnce p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1 := by
  have hj : (attest p st Λ j).1 = some payload := by
    rw [← attest_signer_irrel st Λ ⟨0, p.nPos⟩ j]
    exact h
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hj
  obtain ⟨_, _, _, _, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
  rw [ha, ← hp, he]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An own-record write retains every previous sent content. -/
theorem recordRow_sent_subset (Λ : RecordOnce) (o : Obj p) :
    Λ.sent ⊆ (recordRow? p Λ o).sent := by
  obtain ⟨auth, payload⟩ := o
  rcases auth with ⟨((_ | _) | _), _⟩ | _ <;> cases payload
  all_goals first
    | exact List.Subset.refl _
    | exact fun _ hk => List.mem_cons_of_mem _ hk

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A sequence of own-record writes retains previous sent content. -/
theorem recordRow_fold_sent_subset (ls : List (Obj p)) (Λ : RecordOnce) :
    Λ.sent ⊆ (ls.foldl (recordRow? p) Λ).sent := by
  induction ls generalizing Λ with
  | nil => exact List.Subset.refl _
  | cons o ls ih => exact fun _ hk => ih _ (recordRow_sent_subset Λ o hk)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every fixed-FG row in an own-record fold is in its final sent set. -/
theorem recordRow_fold_contains (ls : List (Obj p)) (Λ : RecordOnce)
    (i : Fin p.n) (body : RowPayload) (ho : ofRow p ⟨.seat .fg i, body⟩ ∈ ls) :
    (body.height_pair, body.finality_pair) ∈ (ls.foldl (recordRow? p) Λ).sent := by
  induction ls generalizing Λ with
  | nil => cases ho
  | cons o ls ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp ho with he | ho
      · subst o
        apply recordRow_fold_sent_subset ls (recordRow? p Λ (ofRow p ⟨.seat .fg i, body⟩))
        exact List.mem_cons_self
      · exact ih _ ho

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A released row is in the node's durable sent set at every later index,
including after restart. -/
theorem fgsa_row_sent_before (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (v : V) (i : Fin p.n) (body : RowPayload) {j k : Nat} (hjk : j < k) (t : Time)
    (hj : rho.events[j]? = some (.tick v t))
    (hem : ofRow p ⟨.seat .fg i, body⟩ ∈ V2.D.Run.emitsAt E rho j) :
    (body.height_pair, body.finality_pair) ∈ (V2.D.Run.stateBefore E rho k v).record.sent := by
  rw [ownRecord_fold_run]
  apply recordRow_fold_contains _ _ i body
  rw [ownReleased_def]
  refine List.mem_flatMap.mpr ⟨j, by simp [List.mem_range', hjk], ?_⟩
  simp only [ownReleasedAt_def, hj, Option.map_some, V2.Event.node, ↓reduceIte]
  exact List.mem_filter.mpr ⟨hem, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A payload signed at the fixed FG label is a row payload. -/
theorem fgsa_tick_fg_row (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (i : Fin p.n) (m : Msg p.n)
    (hem : (⟨.seat (.base .fg) i, m⟩ : Obj p) ∈ (V2.D.tick E rho nd v t).2) :
    ∃ body, m = .row body := by
  obtain ⟨_, _, d, hl, _, ha⟩ := (mem_tick_seat_iff E rho nd v t (.base .fg) i m).mp hem
  change RunDuty.signLabel d = .base .fg at hl
  cases d with
  | headAction s => cases hl
  | propAction s => cases hl
  | fgAction r =>
      change (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, _, hm⟩ := Option.map_eq_some_iff.mp ha
      exact ⟨body, hm.symm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
[R4] Each honest fixed seat emits each full content at most once. The
sent set is durable; restart cannot permit a second signature. -/
theorem fgsa_emitOnceUnder (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_valid : V2.D.ExecutionValid E rho) : Gen.V2.Duty.EmitOnceUnder E rho (.base .fg) := by
  intro i _ m j k t u hj hk hjm hkm
  have hjtick := hjm
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hjtick
  obtain ⟨body, rfl⟩ := fgsa_tick_fg_row E rho _ _ t i m hjtick
  have no_later : ∀ j k t u, j < k →
      rho.events[j]? = some (.tick (rho.seatOf (.base .fg) i) t) →
      rho.events[k]? = some (.tick (rho.seatOf (.base .fg) i) u) →
      ofRow p ⟨.seat .fg i, body⟩ ∈ V2.D.Run.emitsAt E rho j →
      ofRow p ⟨.seat .fg i, body⟩ ∈ V2.D.Run.emitsAt E rho k → False := by
    intro j k t u hjk hj hk hjm hkm
    obtain ⟨_, _, _, _, ha⟩ := (fgsa_emitsAt_row E rho k _ u hk i body).mp hkm
    exact (attest_some_fresh _ _ _ _ ha)
      (fgsa_row_sent_before E rho _ i body hjk t hj hjm)
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact no_later j k t u h hj hk hjm hkm
  · exact no_later k j u t h hk hj hkm hjm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A carried honest row has an earlier emission by its holder. -/
theorem fgsa_carried_row (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (h : V2.D.UnforgeableSignatures E rho) (v u : V) (o : Obj p) (t : Time)
    (hp : V2.D.Run.processes rho v o t) (a : RowWire p.n)
    (hc : (fgsa p c).carries o (ofRow p a)) (hu : u ∈ rho.honest)
    (hh : V2.D.Run.holder rho (ofRow p a).auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits E rho u (ofRow p a) t' :=
  h.carried v o t hp (ofRow p a) hc u hu hh

end AvailableChain.FGSA.Run
end

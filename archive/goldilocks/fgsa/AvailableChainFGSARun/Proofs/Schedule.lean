module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSA.Proofs.Join
public import AvailableChainGeneric.Proofs.V2.Duty.Induction
public import AvailableChainFGSA.Proofs.ActView
public import AvailableChainKitV2.DutyEngineClock -- shake: keep (re-export)
public import AvailableChainKitV2.DutyEmission

public section

/-! Schedule facts for T7.6. Restore keeps the durable store at the exact wake time.
Only the comparison with the strict time reader needs `NoRestart`. -/
namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In : Type} {c : AppCodec In}
variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A node's tick times increase strictly with their indices. -/
theorem fgsa_tick_time_strict (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {v : V} {t u : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hj : rho.events[j]? = some (.tick v u)) (hij : i < j) : t < u := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
  rw [hie, hje] at hk
  have htu := V2.D.Engine.time_le_of_key_le _ _ hk
  change t ≤ u at htu
  have hne : t ≠ u := by
    intro he
    have hevent : rho.events[i] = rho.events[j] := by rw [hie, hje, he]
    have := (List.Nodup.getElem_inj_iff hs.nodup).mp hevent
    omega
  exact lt_of_le_of_ne htu hne

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
There is one index for each local tick event. -/
theorem fgsa_tick_unique (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hj : rho.events[j]? = some (.tick v t)) : i = j := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff hs.nodup).mp (hie.trans hje.symm)

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An honest node ticks exactly once at each public time in the horizon. -/
theorem fgsa_tick_total (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ) (v : V)
    (hv : v ∈ rho.honest) (k : Nat) (hh : (k : Time) * p.Δ ≤ rho.horizon)
    (ha : E.awake v ((k : Time) * p.Δ) = true) :
    ∃! i : Nat, rho.events[i]? = some (.tick v ((k : Time) * p.Δ)) := by
  have hm := hs.tick_total v hv _ ⟨k, by rw [hΔ]⟩
    (by exact mul_nonneg (Int.natCast_nonneg k) (le_of_lt p.deltaPos)) hh ha
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨i, hi, fun j hj => fgsa_tick_unique E rho hs hj hi⟩

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The tick precedes every delivery at that time. -/
theorem fgsa_tick_before_delivery (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {v w : V} {t : Time} {o : Obj p}
    (hi : rho.events[i]? = some (.tick v t))
    (hj : rho.events[j]? = some (.deliver w o t)) : i < j :=
  V2.D.Engine.tick_index_lt_delivery E rho hs hi hj le_rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The clock sets the duty slot, with no schedule or restart premise. -/
theorem fgsa_postClock_slot (nd : Node p) (t : Time) :
    ((fgsa p c).clock nd t).st.base.now = t ∧
      ((fgsa p c).clock nd t).st.slot p = p.slotOf t := by
  have hn := (clock_vn nd.st t).2
  exact ⟨hn, congrArg (p.slotOf) hn⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The proposal duty reads slot `s`. -/
theorem fgsa_proposal_slot (nd : Node p) (s : Slot) :
    ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st.slot p = s := by
  rw [(fgsa_postClock_slot nd _).2]
  have ht : SA.proposalTime p.toParams s = 4 * p.Δ * s + 0 := by
    change 4 * p.Δ * (s : Int) = 4 * p.Δ * (s : Int) + 0
    exact (add_zero _).symm
  rw [ht]
  exact slotOf_offset p s 0 le_rfl (by have hDelta : (0 : Int) < p.Δ := p.deltaPos; omega)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The HEAD duty reads slot `s`. -/
theorem fgsa_vote_slot (nd : Node p) (s : Slot) :
    ((fgsa p c).clock nd (SA.voteTime p.toParams s)).st.slot p = s := by
  rw [(fgsa_postClock_slot nd _).2]
  exact slotOf_offset p s p.Δ (le_of_lt p.deltaPos)
    (by have hDelta : (0 : Int) < p.Δ := p.deltaPos; omega)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The FG duty reads slot `rR + 1` and round `r`. -/
theorem fgsa_action_slot_round (nd : Node p) (r : Nat) :
    ((fgsa p c).clock nd (p.actionTime r)).st.slot p = r * p.R + 1 ∧
      p.round (((fgsa p c).clock nd (p.actionTime r)).st.slot p) = r := by
  have ht : p.actionTime r = 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + 2 * p.Δ := by
    simp only [Params.actionTime, SA.gateTime, GridCO.gateTime, GridCO.proposalTime,
      SA.Params.engine]
    push_cast
    ring
  have hslot : ((fgsa p c).clock nd (p.actionTime r)).st.slot p = r * p.R + 1 := by
    rw [(fgsa_postClock_slot nd _).2, ht]
    exact slotOf_offset p _ (2 * p.Δ) (by have hDelta : (0 : Int) < p.Δ := p.deltaPos; omega)
      (by have hDelta : (0 : Int) < p.Δ := p.deltaPos; omega)
  refine ⟨hslot, ?_⟩
  rw [hslot]
  change (r * p.R + 1) / p.R = r
  rw [Nat.mul_comm r p.R,
    Nat.mul_add_div (by have := p.RLarge; omega),
    Nat.div_eq_of_lt (by have := p.RLarge; omega), Nat.add_zero]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The gate for label `s` reads slot `s + 1`. -/
theorem fgsa_gate_slot (nd : Node p) (s : Slot) :
    ((fgsa p c).clock nd (SA.gateTime p.toParams s)).st.slot p = s + 1 := by
  have ht : SA.gateTime p.toParams s = 4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ := by
    simp only [SA.gateTime, GridCO.gateTime, GridCO.proposalTime, SA.Params.engine]
    push_cast
    ring
  rw [(fgsa_postClock_slot nd _).2, ht]
  exact slotOf_offset p _ (2 * p.Δ) (by have hDelta : (0 : Int) < p.Δ := p.deltaPos; omega)
    (by have hDelta : (0 : Int) < p.Δ := p.deltaPos; omega)

private theorem fgsa_reconcile_labels (st : State p.n) :
    (reconcile st).base.genuine.map Prod.fst = st.base.genuine.map Prod.fst := by
  rw [reconcile_genuine, List.map_map]
  rfl

private theorem fgsa_grid_proposal_genuine (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block) (raw : List
        (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q st o b raw).genuine = st.genuine := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first
    | rfl
    | exact (foldVotes_fields q raw _).2.2.2.2.1

private theorem fgsa_process_labels (st : State p.n) (o : Wire p.n) :
    (FGSA.process p st o).base.genuine.map Prod.fst = st.base.genuine.map Prod.fst := by
  obtain ⟨auth, msg⟩ := o
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> cases msg <;> try rfl
  · change (admitHead p st _ _ _).base.genuine.map Prod.fst = _
    rw [admitHead_genuine]
  · change (admitRow p st _).base.genuine.map Prod.fst = _
    rcases admitRow_eq p st _ with he | he <;> rw [he]
  · rename_i s N
    change (admitBlock p st s N).base.genuine.map Prod.fst = _
    cases hn : namedParentHeld st N with
    | false =>
      rw [admitBlock_refused p st s N (Or.inl hn)]
    | true =>
      cases hp : parentFG st N.erase with
      | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
      | some P =>
        cases ha : blockAccepted p st s N P with
        | false => rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
        | true =>
          obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hp ha
          rw [he]
          dsimp only
          split
          · rw [fgsa_grid_proposal_genuine]
          · rw [fgsa_reconcile_labels, fgsa_grid_proposal_genuine]

private theorem fgsa_unsaved_iff (st : GridCO.State p.n .root) (s : Slot) :
    GridCO.savedGenuine st s = none ↔ s ∉ st.genuine.map Prod.fst := by
  constructor
  · exact notMem_keys_of_unsaved
  · intro hn
    apply Option.map_eq_none_iff.mpr
    apply List.find?_eq_none.mpr
    intro row hr he
    have hm : row.1 ∈ st.genuine.map Prod.fst := List.mem_map_of_mem hr
    exact hn ((beq_iff_eq.mp he) ▸ hm)

private theorem fgsa_clock_label_source (st : State p.n) (t : Time) (s : Slot)
    (hm : s ∈ (FGSA.clock p st t).base.genuine.map Prod.fst) :
    s ∈ st.base.genuine.map Prod.fst ∨ t = SA.gateTime p.toParams s := by
  by_cases hs : s ∈ st.base.genuine.map Prod.fst
  · exact Or.inl hs
  have hn : GridCO.savedGenuine (clockPre p st t).base s = none := by
    apply (fgsa_unsaved_iff _ _).mpr
    rwa [clockPre_genuine]
  unfold FGSA.clock at hm
  dsimp only at hm
  split at hm
  · rename_i hg
    have ht : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat := by
      have hh : (t == SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) = true :=
        (Bool.and_eq_true_iff.mp hg).2
      exact beq_iff_eq.mp hh
    let k := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    by_cases he : s = k
    · right; rwa [he]
    have hnone : GridCO.savedGenuine (gateStep p (clockPre p st t) k).base s = none := by
      rw [gateStep_other p _ k s he, hn]
    exact False.elim ((fgsa_unsaved_iff _ _).mp hnone hm)
  · rw [clockPre_genuine] at hm
    exact (hs hm).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A saved label comes from a prior local tick at its gate time.
The origin statement needs no schedule premise and allows restarts. -/
theorem fgsa_saved_label_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (s : Slot)
    (hm : s ∈ (V2.D.Run.stateBefore E rho i v).st.base.genuine.map Prod.fst) :
    ∃ j < i, rho.events[j]? = some (.tick v (SA.gateTime p.toParams s)) := by
  obtain ⟨j, hj, t, he, ht⟩ := V2.D.Engine.clock_field_origin
    (P := fgsa p c) (fun nd : Node p => nd.st.base.genuine.map Prod.fst) rfl
    (fun nd o => fgsa_process_labels nd.st (toWire p o))
    (fun _ _ _ h => h)
    (fgsa_hrestore_field_retained p c (fun st => st.base.genuine.map Prod.fst) (fun st w => by
      rw [acRestart_genuine]; exact List.nil_subset _))
    (fun _ t s => t = SA.gateTime p.toParams s)
    (fun nd t s h => fgsa_clock_label_source nd.st t s h) E rho i v s hm
  exact ⟨j, hj, ht ▸ he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The label is unsaved before its unique scheduled gate tick. -/
theorem fgsa_gate_fresh (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.gateTime p.toParams s))) :
    GridCO.savedGenuine (V2.D.Run.stateBefore E rho i v).st.base s = none := by
  apply Option.map_eq_none_iff.mpr
  apply List.find?_eq_none.mpr
  intro row hrow
  have hm : row.1 ∈ (V2.D.Run.stateBefore E rho i v).st.base.genuine.map Prod.fst :=
    List.mem_map_of_mem hrow
  intro heq
  have he : row.1 = s := beq_iff_eq.mp heq
  rw [he] at hm
  obtain ⟨j, hj, ht⟩ := fgsa_saved_label_origin E rho i v s hm
  have := fgsa_tick_unique E rho hs ht hi
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
At the scheduled fresh gate the clock is the anchored SA clock,
with the cumulative blocks and the fast-write row kept. -/
theorem fgsa_gate_clock_bridge (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.gateTime p.toParams s)))
    (hj : joinedAtTime p (V2.D.Run.stateBefore E rho i v).st.restartTime
      (SA.gateTime p.toParams s) = true) :
    let st := (V2.D.Run.stateBefore E rho i v).st
    FGSA.clock p st (SA.gateTime p.toParams s) = normalizeS { st with
      base := { SA.Root.clockFrom p.toParams (eraseFG st.fg.F) (actView st)
        (SA.gateTime p.toParams s) with blocks := st.base.blocks, headDomain :=
            st.base.headDomain },
      fastWrite := st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F)
        (actView (clockPre p st (SA.gateTime p.toParams s))) s)] } :=
  clock_eq_saClockFrom_gate' p _ _ s rfl (fgsa_gate_fresh E rho hs hi) hj

private theorem fgsa_grid_stamp_le (q : GridCO.Params) {n : Nat} (st : GridCO.State n .root)
    (o : GridCO.Wire n .root) (h : ∀ row ∈ st.voteStamp, row.2 ≤ st.now) :
    ∀ row ∈ (GridCO.admitVote q st o).voteStamp,
      row.2 ≤ (GridCO.admitVote q st o).now := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> cases msg <;> try exact h
  rename_i r seat b
  rw [Internal.grid_admitVote_now]
  change ∀ row ∈ (if (r < (st.now / (4 * q.Δ)).toNat - 1 ||
    (st.now / (4 * q.Δ)).toNat < r || decide (_ ∈ st.votes) ||
    GridCO.equivocates (GridCO.votesAt st r) seat) then st else
    { st with votes := _, voteStamp := _ }).voteStamp, row.2 ≤ _
  split
  · exact h
  · intro row hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h row hm
    · obtain rfl := List.mem_singleton.mp hm
      exact le_rfl

private theorem fgsa_grid_fold_stamp_le (q : GridCO.Params) {n : Nat}
    (raw : List (GridCO.HeadWire n .root)) (st : GridCO.State n .root)
    (h : ∀ row ∈ st.voteStamp, row.2 ≤ st.now) :
    ∀ row ∈ (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) st).voteStamp,
      row.2 ≤ st.now := by
  induction raw generalizing st with
  | nil => exact h
  | cons o raw ih =>
    rw [List.foldl_cons]
    have hn := Internal.grid_admitVote_now (q := q) st (GridCO.fromHead o)
    have hh := ih _ (fgsa_grid_stamp_le q st (GridCO.fromHead o) h)
    rwa [hn] at hh

private theorem fgsa_grid_proposal_stamp_le (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block) (raw : List
        (GridCO.HeadWire n .root))
    (h : ∀ row ∈ st.voteStamp, row.2 ≤ st.now) :
    ∀ row ∈ (GridCO.admitProposal q st o b raw).voteStamp, row.2 ≤ st.now := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first
    | exact h
    | exact fgsa_grid_fold_stamp_le q raw _ h

private theorem fgsa_process_bounds (st : State p.n) (o : Wire p.n)
    (hc : CStoreInv p st)
    (hb : ∀ b ∈ st.base.blocks, b.slot ≤ st.slot p)
    (hv : ∀ row ∈ st.base.voteStamp, row.2 ≤ st.base.now) :
    (∀ b ∈ (FGSA.process p st o).base.blocks, b.slot ≤ st.slot p) ∧
    (∀ row ∈ (FGSA.process p st o).base.voteStamp, row.2 ≤ st.base.now) := by
  obtain ⟨auth, msg⟩ := o
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> cases msg <;> try exact ⟨hb, hv⟩
  · rename_i seat slot target
    change (∀ b ∈ (admitHead p st slot seat target).base.blocks, _) ∧
      (∀ row ∈ (admitHead p st slot seat target).base.voteStamp, _)
    refine ⟨?_, ?_⟩
    · rwa [admitHead_base_blocks]
    · have hh := fgsa_grid_stamp_le p.toParams.engine st.base
        (⟨.seat slot seat, .head target⟩ : GridCO.Wire p.n .root) hv
      rw [Internal.grid_admitVote_now] at hh
      exact hh
  · change (∀ b ∈ (admitRow p st _).base.blocks, _) ∧
      (∀ row ∈ (admitRow p st _).base.voteStamp, _)
    rcases admitRow_eq p st _ with he | he <;> rw [he] <;> exact ⟨hb, hv⟩
  · rename_i s N
    change (∀ b' ∈ (admitBlock p st s N).base.blocks, _) ∧
      (∀ row ∈ (admitBlock p st s N).base.voteStamp, _)
    cases hn : namedParentHeld st N with
    | false =>
      rw [admitBlock_refused p st s N (Or.inl hn)]
      exact ⟨hb, hv⟩
    | true =>
      cases hp : parentFG st N.erase with
      | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]; exact ⟨hb, hv⟩
      | some P =>
        cases ha : blockAccepted p st s N P with
        | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          exact ⟨hb, hv⟩
        | true =>
          obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hp ha
          have hblocks := (accepted_st2 p st hc s N P hp ha).2.2.1
          rw [he]
          refine ⟨?_, ?_⟩
          · dsimp only
            rw [hblocks]
            intro b' hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hb b' hm
            · obtain rfl := List.mem_singleton.mp hm
              exact (blockAccepted_facts ha).2.1
          · dsimp only
            split
            · exact fgsa_grid_proposal_stamp_le p.toParams.engine st.base _ N.erase _ hv
            · rw [(reconcile_frame _).2.2.2.2.2.2.1]
              exact fgsa_grid_proposal_stamp_le p.toParams.engine st.base _ N.erase _ hv

private theorem fgsa_clock_now_of_reachable (st : State p.n) (hr : Reachable p st)
    (record : RecordOnce) : (fgsaClock p c).now (⟨st, record⟩ : Node p) = st.base.now := by
  have _ := hr
  exact fgsa_clock_now p c ⟨st, record⟩

private theorem fgsa_clock_now_stateBefore (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (i : Nat) (v : V) :
    (fgsaClock p c).now (V2.D.Run.stateBefore E rho i v) =
      (V2.D.Run.stateBefore E rho i v).st.base.now := by
  have h := fgsa_clock_now_of_reachable (c := c) _ (reachable_stateBefore E rho i v)
    (V2.D.Run.stateBefore E rho i v).record
  exact h

private theorem fgsa_processList_bounds (st : State p.n) (xs : List (Wire p.n))
    (hr : Reachable p st) (hb : ∀ b ∈ st.base.blocks, b.slot ≤ st.slot p)
    (hv : ∀ row ∈ st.base.voteStamp, row.2 ≤ st.base.now) :
    Reachable p (xs.foldl (FGSA.process p) st) ∧
      (∀ b ∈ (xs.foldl (FGSA.process p) st).base.blocks,
        b.slot ≤ (xs.foldl (FGSA.process p) st).slot p) ∧
      ∀ row ∈ (xs.foldl (FGSA.process p) st).base.voteStamp,
        row.2 ≤ (xs.foldl (FGSA.process p) st).base.now := by
  induction xs generalizing st with
  | nil => exact ⟨hr, hb, hv⟩
  | cons o xs ih =>
    have h := fgsa_process_bounds st o (storeBundle_of_reachable p st hr).cstore hb hv
    apply ih (FGSA.process p st o) (Reachable.deliver o hr)
    · intro b hmem
      change b.slot ≤ p.slotOf (FGSA.process p st o).base.now
      rw [process_base_now]
      exact h.1 b hmem
    · simpa only [process_base_now] using h.2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Scheduled stores keep blocks within the store slot and stamps within
its clock. Restarts keep blocks and replay accepted votes at the wake time. -/
theorem fgsa_stateBefore_bounds (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (v : V) :
    (∀ b ∈ (V2.D.Run.stateBefore E rho i v).st.base.blocks,
      b.slot ≤ (V2.D.Run.stateBefore E rho i v).st.slot p) ∧
    (∀ row ∈ (V2.D.Run.stateBefore E rho i v).st.base.voteStamp,
      row.2 ≤ (V2.D.Run.stateBefore E rho i v).st.base.now) := by
  let Q := fun nd : Node p => Reachable p nd.st ∧
    (∀ b ∈ nd.st.base.blocks, b.slot ≤ nd.st.slot p) ∧
    (∀ row ∈ nd.st.base.voteStamp, row.2 ≤ nd.st.base.now)
  have hinit : Q ((fgsa p c).init) := by
    refine ⟨Reachable.init, ?_, ?_⟩
    · intro b hb
      change b ∈ [Block.genesis] at hb
      obtain rfl := List.mem_singleton.mp hb
      exact Nat.zero_le _
    · intro row hr
      change row ∈ ([] : List (GridCO.Wire p.n .root × Time)) at hr
      exact (List.not_mem_nil hr).elim
  have hclock : ∀ nd t, (fgsaClock p c).now nd ≤ t → Q nd →
      Q ((fgsa p c).clock nd t) := by
    intro nd t ht h
    have hn : (fgsaClock p c).now nd = nd.st.base.now :=
        fgsa_clock_now_of_reachable (c := c) nd.st h.1 nd.record
    have ht' : nd.st.base.now ≤ t := hn ▸ ht
    refine ⟨Reachable.tick t h.1, ?_, ?_⟩
    · intro b hb
      change b ∈ (FGSA.clock p nd.st t).base.blocks at hb
      rw [clock_base_blocks] at hb
      exact le_trans (h.2.1 b hb) (by
        change p.slotOf nd.st.base.now ≤ p.slotOf (FGSA.clock p nd.st t).base.now
        rw [(clock_vn nd.st t).2]
        exact Internal.slotOf_mono ht')
    · intro row hr
      change row ∈ (FGSA.clock p nd.st t).base.voteStamp at hr
      rw [(clock_cumulative p nd.st t).2.2.2.1] at hr
      exact le_trans (h.2.2 row hr) (by
        change nd.st.base.now ≤ (FGSA.clock p nd.st t).base.now
        rw [(clock_vn nd.st t).2]; exact ht')
  have hprocess : ∀ nd o, Q nd → Q ((fgsa p c).process nd o) := by
    intro nd o h
    refine ⟨Reachable.deliver (toWire p o) h.1, ?_⟩
    have hh := fgsa_process_bounds nd.st (toWire p o)
      (storeBundle_of_reachable p _ h.1).cstore h.2.1 h.2.2
    change (∀ b ∈ (FGSA.process p nd.st (toWire p o)).base.blocks,
      b.slot ≤ p.slotOf (FGSA.process p nd.st (toWire p o)).base.now) ∧
      (∀ row ∈ (FGSA.process p nd.st (toWire p o)).base.voteStamp,
        row.2 ≤ (FGSA.process p nd.st (toWire p o)).base.now)
    rw [process_base_now]
    exact hh
  have h := V2.D.Engine.stateBefore_step_induction E rho Q (Nat.zero_le i) v
    (fun k e _ _ he heq h => by
      have ht := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hs he v
      cases e with
      | restart u w =>
        change u = v at heq; subst u
        simp only [V2.D.World.step, Function.update_self]
        change Q ⟨acRestart p (V2.D.Run.stateBefore E rho k v).st w, _⟩
        unfold acRestart
        apply fgsa_processList_bounds _ _ (Reachable.restart w h.1)
        · intro b hb
          rw [fgsa_clock_now_stateBefore E rho k v] at ht
          exact le_trans (h.2.1 b hb) (Internal.slotOf_mono ht)
        · intro row hr
          exact (List.not_mem_nil hr).elim
      | tick u t =>
        change u = v at heq; subst u
        simpa only [V2.D.World.step, Function.update_self] using
          V2.D.Engine.tick_preserve E rho Q (fun _ _ h => h) (hclock _ t ht h)
      | deliver u o t =>
        change u = v at heq; subst u
        simpa only [V2.D.World.step, Function.update_self] using hprocess _ o h) hinit
  exact h.2

/-- The pre-tick clock is at most the tick time, including a same-time wake. -/
theorem fgsa_preTick_now_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    (V2.D.Run.stateBefore E rho i v).st.base.now ≤ t := by
  have h := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hs hi v
  rw [fgsa_clock_now_stateBefore E rho i v] at h
  exact h

/-- The strict bound holds in an epoch with no same-time restart.
A joined read has its last restart at or before the previous slot start,
which is strictly before this tick. -/
theorem fgsa_preTick_now_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) (ht : 0 < t)
    (hEpoch : ∀ j w, j < i → rho.events[j]? = some (.restart v w) → w < t) :
    (V2.D.Run.stateBefore E rho i v).st.base.now < t := by
  rcases V2.D.Engine.stateBefore_now_source_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho i v with hz | ⟨j, hj, he⟩
  · rw [fgsa_clock_now_stateBefore E rho i v] at hz
    rw [hz]; exact ht
  · rw [fgsa_clock_now_stateBefore E rho i v] at he
    rcases he with he | he
    · exact fgsa_tick_time_strict E rho hs he hi hj
    · exact hEpoch j _ hj he

omit [DecidableEq V] in
private theorem fgsa_time_le_index (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat} {e f : V2.Event V (Obj p)}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some f) (hij : i < j) :
    e.time ≤ f.time := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl hij
  rw [hie, hje] at hk
  exact V2.D.Engine.time_le_of_key_le _ _ hk

/-- A same-time restart is the restart marker read by the following local tick. -/
theorem fgsa_preTick_restartTime_at_wake (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t))
    (hj : rho.events[j]? = some (.restart v t)) (hji : j < i) :
    (V2.D.Run.stateBefore E rho i v).st.restartTime = some t := by
  have heq := V2.D.Engine.stateBefore_other_node E rho (a := j + 1) (b := i)
    (Nat.succ_le_of_lt hji) (v := v) (fun k e hjk hki he hnode => by
      have hl := fgsa_time_le_index E rho hs (i := j) (j := k) hj he (by omega)
      have hu := fgsa_time_le_index E rho hs he hi hki
      have ht : e.time = t := le_antisymm hu hl
      cases e with
      | restart u w =>
        change u = v at hnode; subst u
        change w = t at ht; subst w
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
        have h := (List.Nodup.getElem_inj_iff hs.nodup).mp (hje.trans hke.symm)
        omega
      | tick u w =>
        change u = v at hnode; subst u
        change w = t at ht; subst w
        have h := fgsa_tick_unique E rho hs he hi
        omega
      | deliver u o w =>
        change u = v at hnode; subst u
        change w = t at ht; subst w
        have h := fgsa_tick_before_delivery E rho hs hi he
        omega)
  rw [heq, V2.D.Run.stateBefore_succ E rho hj]
  simp only [V2.D.World.step, Function.update_self]
  change (acRestart p _ t).restartTime = some t
  exact acRestart_restartTime p _ t

/-- Joined reads satisfy the strict pre-tick clock bound with arbitrary wakes. -/
theorem fgsa_preTick_now_lt_joined (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) (ht : 0 < t)
    (hj : joinedAtTime p (V2.D.Run.stateBefore E rho i v).st.restartTime t = true) :
    (V2.D.Run.stateBefore E rho i v).st.base.now < t := by
  apply fgsa_preTick_now_lt E rho hs hi ht
  intro j w hji he
  have hw := fgsa_time_le_index E rho hs (i := j) (j := i) he hi hji
  change w ≤ t at hw
  by_contra hn
  have hwt : w = t := le_antisymm hw (le_of_not_gt hn)
  subst w
  have hr := fgsa_preTick_restartTime_at_wake E rho hs hi he hji
  rw [hr] at hj
  change decide (t ≤ 4 * p.Δ * ((p.slotOf t : Int) - 1)) = true at hj
  have hj' := of_decide_eq_true hj
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hq : 0 ≤ t / (4 * p.Δ) := Int.ediv_nonneg (le_of_lt ht) (le_of_lt hd)
  have hf := Int.ediv_mul_le t (ne_of_gt hd)
  unfold Params.slotOf at hj'
  rw [Int.toNat_of_nonneg hq] at hj'
  nlinarith

/-- The epoch condition is exactly the strict clock condition at a positive tick. -/
theorem fgsa_preTick_now_lt_iff (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) (ht : 0 < t) :
    (V2.D.Run.stateBefore E rho i v).st.base.now < t ↔
      ∀ j w, j < i → rho.events[j]? = some (.restart v w) → w < t := by
  refine ⟨?_, fgsa_preTick_now_lt E rho hs hi ht⟩
  intro hn j w hji he
  have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hs (Nat.succ_le_of_lt hji) v
  rw [V2.D.Run.stateBefore_succ E rho he] at hm
  simp only [V2.D.World.step, Function.update_self] at hm
  rw [(fgsaRestoreTimeLaw p c).restore_now _ w] at hm
  rw [fgsa_clock_now_stateBefore E rho i v] at hm
  exact lt_of_le_of_lt hm hn

/-- At any tick, accepted and default vote stamps are at most the tick time. -/
theorem fgsa_preTick_votes_stamped_le (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    ∀ o : GridCO.Wire p.n .root,
      GridCO.stampVote (V2.D.Run.stateBefore E rho i v).st.base o ≤ t := by
  intro o
  have hn := fgsa_preTick_now_le E rho hs hi
  have hb := (fgsa_stateBefore_bounds E rho hs i v).2
  unfold GridCO.stampVote
  cases hf : (V2.D.Run.stateBefore E rho i v).st.base.voteStamp.find?
      (fun row => row.1 == o) with
  | none => exact hn
  | some row => exact le_trans (hb row (List.mem_of_find?_eq_some hf)) hn

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every stored vote, including carried votes, has a stamp before release.
The active view keeps both the votes and their stamps. -/
theorem fgsa_release_votes_stamped (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {r : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.releaseTime p.toParams r)))
    (hEpoch : ∀ j w, j < i → rho.events[j]? = some (.restart v w) →
      w < SA.releaseTime p.toParams r) :
    let st := (V2.D.Run.stateBefore E rho i v).st
    (∀ o : GridCO.Wire p.n .root, GridCO.stampVote st.base o < SA.releaseTime p.toParams r) ∧
      (actView st).votes = st.base.votes ∧ (actView st).voteStamp = st.base.voteStamp := by
  intro st
  have ht : 0 < SA.releaseTime p.toParams r := by
    change 0 < 4 * p.Δ * (r : Int) + 5 * p.Δ
    have hDelta : (0 : Int) < p.Δ := p.deltaPos
    have := Int.natCast_nonneg r
    positivity
  have hn := fgsa_preTick_now_lt E rho hs hi ht hEpoch
  refine ⟨?_, rfl, rfl⟩
  intro o
  have hb := (fgsa_stateBefore_bounds E rho hs i v).2
  unfold GridCO.stampVote
  cases hf : st.base.voteStamp.find? (fun row => row.1 == o) with
  | none => exact hn
  | some row =>
    have hm := List.mem_of_find?_eq_some hf
    exact lt_of_le_of_lt (hb row hm) hn

private theorem fgsa_grid_vote_keys (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    (h : st.voteStamp.map Prod.fst = st.votes) :
    (GridCO.admitVote q st o).voteStamp.map Prod.fst = (GridCO.admitVote q st o).votes := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> cases msg <;> try exact h
  rename_i r seat b
  change (let out := if (r < (st.now / (4 * q.Δ)).toNat - 1 ||
      (st.now / (4 * q.Δ)).toNat < r ||
      decide ((⟨.seat r seat, .head b⟩ : GridCO.Wire n .root) ∈ st.votes) ||
      GridCO.equivocates (GridCO.votesAt st r) seat) then st else
      { st with
        votes := st.votes ++ [⟨.seat r seat, .head b⟩]
        voteStamp := st.voteStamp ++ [(⟨.seat r seat, .head b⟩, st.now)] }
    out.voteStamp.map Prod.fst = out.votes)
  dsimp only
  split
  · exact h
  · change (st.voteStamp ++ [(_, st.now)]).map Prod.fst = st.votes ++ [_]
    rw [List.map_append, h]
    rfl

private theorem fgsa_grid_fold_vote_keys (q : GridCO.Params) {n : Nat}
    (raw : List (GridCO.HeadWire n .root)) (st : GridCO.State n .root)
    (h : st.voteStamp.map Prod.fst = st.votes) :
    let out := raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) st
    out.voteStamp.map Prod.fst = out.votes := by
  induction raw generalizing st with
  | nil => exact h
  | cons row raw ih =>
    exact ih _ (fgsa_grid_vote_keys q st (GridCO.fromHead row) h)

private theorem fgsa_grid_proposal_vote_keys (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block) (raw : List
        (GridCO.HeadWire n .root))
    (h : st.voteStamp.map Prod.fst = st.votes) :
    (GridCO.admitProposal q st o b raw).voteStamp.map Prod.fst =
      (GridCO.admitProposal q st o b raw).votes := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first
    | exact h
    | exact fgsa_grid_fold_vote_keys q raw _ h

private theorem fgsa_process_vote_keys (st : State p.n) (o : Wire p.n)
    (h : st.base.voteStamp.map Prod.fst = st.base.votes) :
    (FGSA.process p st o).base.voteStamp.map Prod.fst = (FGSA.process p st o).base.votes := by
  obtain ⟨auth, msg⟩ := o
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> cases msg <;> try exact h
  · exact fgsa_grid_vote_keys p.toParams.engine st.base _ h
  · change (admitRow p st _).base.voteStamp.map Prod.fst = (admitRow p st _).base.votes
    rcases admitRow_eq p st _ with he | he <;> rw [he] <;> exact h
  · rename_i s N
    change (admitBlock p st s N).base.voteStamp.map Prod.fst =
      (admitBlock p st s N).base.votes
    cases hn : namedParentHeld st N with
    | false =>
      rw [admitBlock_refused p st s N (Or.inl hn)]
      exact h
    | true =>
      cases hp : parentFG st N.erase with
      | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]; exact h
      | some P =>
        cases ha : blockAccepted p st s N P with
        | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]; exact h
        | true =>
          obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N P hn hp ha
          rw [he]
          dsimp only
          split
          · exact fgsa_grid_proposal_vote_keys p.toParams.engine st.base _ N.erase _ h
          · rw [(reconcile_frame _).2.2.2.2.2.2.1, (reconcile_frame _).2.2.2.2.2.1]
            exact fgsa_grid_proposal_vote_keys p.toParams.engine st.base _ N.erase _ h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Stored votes and stamps have the same keys, including carried votes.
No schedule or restart premise is needed. -/
theorem fgsa_vote_stamp_keys (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) :
    (V2.D.Run.stateBefore E rho i v).st.base.voteStamp.map Prod.fst =
      (V2.D.Run.stateBefore E rho i v).st.base.votes := by
  refine Gen.V2.Duty.invariant_triple (P := fgsa p c)
    (fun nd : Node p => nd.st.base.voteStamp.map Prod.fst = nd.st.base.votes)
    rfl ?_ ?_ (fun _ _ h => h) (fun nd w _ => acRestart_voteStamp_keys p nd.st w) E rho i v
  · intro nd t h
    change (FGSA.clock p nd.st t).base.voteStamp.map Prod.fst =
      (FGSA.clock p nd.st t).base.votes
    rw [(clock_cumulative p nd.st t).2.2.2.1, (clock_vn nd.st t).1]
    exact h
  · intro nd o h
    exact fgsa_process_vote_keys nd.st (toWire p o) h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
At `q_r`, freeze and early do not run. The release reads the active
view after the time write and expiry, before any same-time delivery. -/
theorem fgsa_release_clockPre (st : State p.n) (r : Slot)
    (hj : joinedAtTime p st.restartTime (SA.releaseTime p.toParams r) = true) :
    clockPre p st (SA.releaseTime p.toParams r) =
      onView (fun view => SA.Root.release p.toParams view r)
        { st with
          base := GridCO.expire { st.base with now := SA.releaseTime p.toParams r }
            (SA.releaseTime p.toParams r) } := by
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  have hf : SA.releaseTime p.toParams r - 3 * p.Δ = 4 * p.Δ * (r : Int) + 2 * p.Δ := by
    change 4 * p.Δ * (r : Int) + 5 * p.Δ - 3 * p.Δ = _
    ring
  have he : SA.releaseTime p.toParams r - 2 * p.Δ = 4 * p.Δ * (r : Int) + 3 * p.Δ := by
    change 4 * p.Δ * (r : Int) + 5 * p.Δ - 2 * p.Δ = _
    ring
  have hq : SA.releaseTime p.toParams r - 5 * p.Δ = 4 * p.Δ * (r : Int) := by
    change 4 * p.Δ * (r : Int) + 5 * p.Δ - 5 * p.Δ = _
    ring
  have hfs : ((SA.releaseTime p.toParams r - 3 * p.Δ) / (4 * p.Δ)).toNat = r := by
    rw [hf]
    exact slotOf_offset p r (2 * p.Δ) (by omega) (by omega)
  have hes : ((SA.releaseTime p.toParams r - 2 * p.Δ) / (4 * p.Δ)).toNat = r := by
    rw [he]
    exact slotOf_offset p r (3 * p.Δ) (by omega) (by omega)
  have hqs : ((SA.releaseTime p.toParams r - 5 * p.Δ) / (4 * p.Δ)).toNat = r := by
    rw [hq, Int.mul_ediv_cancel_left _ (by positivity), Int.toNat_natCast]
  have hfne : (SA.releaseTime p.toParams r == SA.freezeTime p.toParams r) = false := by
    apply beq_eq_false_iff_ne.mpr
    change 4 * p.Δ * (r : Int) + 5 * p.Δ ≠ 4 * p.Δ * (r : Int) + 3 * p.Δ
    intro h
    linarith
  have hene : (SA.releaseTime p.toParams r == SA.earlyTime p.toParams r) = false := by
    apply beq_eq_false_iff_ne.mpr
    change 4 * p.Δ * (r : Int) + 5 * p.Δ ≠ 4 * p.Δ * (r : Int) + 2 * p.Δ
    intro h
    linarith
  have hqn : 0 ≤ SA.releaseTime p.toParams r - 5 * p.Δ := by rw [hq]; positivity
  unfold clockPre
  dsimp only
  rw [hfs, hes, hqs]
  change _ = _
  simp only [hfne, hene, Bool.and_false, Bool.false_eq_true, ite_false,
    hqn, decide_true, beq_self_eq_true, Bool.true_and]
  change (if joinedAtTime p st.restartTime (SA.releaseTime p.toParams r) then _ else _) = _
  rw [hj]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
At the release input, after the time write and expiry, every stored
vote still has its earlier stamp. This is the view that release reads. -/
theorem fgsa_release_input_votes_stamped (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {r : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.releaseTime p.toParams r)))
    (hEpoch : ∀ j w, j < i → rho.events[j]? = some (.restart v w) →
      w < SA.releaseTime p.toParams r) :
    let st := (V2.D.Run.stateBefore E rho i v).st
    let view := GridCO.expire { actView st with now := SA.releaseTime p.toParams r }
      (SA.releaseTime p.toParams r)
    ∀ o ∈ view.votes, GridCO.stampVote view o < SA.releaseTime p.toParams r := by
  intro st view o ho
  have hk := fgsa_vote_stamp_keys E rho i v
  have hn : st.base.now < SA.releaseTime p.toParams r :=
    fgsa_preTick_now_lt E rho hs hi (by
      change 0 < 4 * p.Δ * (r : Int) + 5 * p.Δ
      have hDelta : (0 : Int) < p.Δ := p.deltaPos
      have hr := Int.natCast_nonneg r
      positivity) hEpoch
  have hb := (fgsa_stateBefore_bounds E rho hs i v).2
  change o ∈ st.base.votes at ho
  unfold GridCO.stampVote
  change ((st.base.voteStamp.find? (fun row => row.1 == o)).map Prod.snd).getD _ < _
  cases hf : st.base.voteStamp.find? (fun row => row.1 == o) with
  | none =>
    have hkey : o ∈ st.base.voteStamp.map Prod.fst := hk.symm ▸ ho
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hkey
    exact ((List.find?_eq_none.mp hf) row hr (by simp only [he, beq_self_eq_true])).elim
  | some row =>
    exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Stored blocks have smaller slots before the proposal tick and after
its clock, when `s > 0`. -/
theorem fgsa_stored_block_slots (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s))) (hs0 : 0 < s) :
    let nd := V2.D.Run.stateBefore E rho i v
    (∀ b ∈ nd.st.base.blocks, b.slot < s) ∧
      (∀ b ∈ ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st.base.blocks,
        b.slot < s) ∧ (∀ B ∈ nd.st.fg.TF, B.slot < s) ∧
      (∀ B ∈ ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st.fg.TF,
        B.slot < s) := by
  intro nd
  have hb : ∀ b ∈ nd.st.base.blocks, b.slot < s := by
    let Q := fun nd : Node p => ∀ b ∈ nd.st.base.blocks, b.slot < s
    refine V2.D.Engine.stateBefore_step_induction E rho Q (Nat.zero_le i) v ?_ ?_
    · intro k e _ hki he heq hk
      cases e with
      | restart u w =>
        change u = v at heq; subst u
        simp only [V2.D.World.step, Function.update_self]
        change ∀ b ∈ (acRestart p _ w).base.blocks, b.slot < s
        rw [acRestart_blocks]
        exact hk
      | tick u t =>
        change u = v at heq; subst u
        simp only [V2.D.World.step, Function.update_self]
        change ∀ b ∈ (V2.D.tick E rho _ v t).1.st.base.blocks, b.slot < s
        rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k v) v t,
          clock_base_blocks]
        exact hk
      | deliver u o t =>
        change u = v at heq; subst u
        have ht : t < SA.proposalTime p.toParams s := by
          by_contra hn
          have h := V2.D.Engine.tick_index_lt_delivery E rho hs hi he (le_of_not_gt hn)
          omega
        have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
          (fgsaRestoreTimeLaw p c) E rho hs he v
        rw [fgsa_clock_now_stateBefore E rho k v] at hn
        have hslot : (V2.D.Run.stateBefore E rho k v).st.slot p < s := by
          have hd : 0 < (4 * p.Δ : Int) := by linarith [p.deltaPos]
          apply (Int.toNat_lt' hs0).mpr
          apply (Int.ediv_lt_iff_lt_mul hd).mpr
          have hn' : (V2.D.Run.stateBefore E rho k v).st.base.now <
              SA.proposalTime p.toParams s := lt_of_le_of_lt hn ht
          change _ < 4 * p.Δ * (s : Int) at hn'
          nlinarith
        have hb := (fgsa_stateBefore_bounds E rho hs k v)
        have hproc := (fgsa_process_bounds _ (toWire p o)
          (cstoreInv_stateBefore E rho k v) hb.1 hb.2).1
        simp only [V2.D.World.step, Function.update_self]
        exact fun b hm => lt_of_le_of_lt (hproc b hm) hslot
    · intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact hs0
  have hfg : ∀ B ∈ nd.st.fg.TF, B.slot < s := by
    intro B hB
    have hm : eraseFG B ∈ nd.st.base.blocks :=
      ((cstoreInv_stateBefore E rho i v).baseTree _).mpr ⟨B, hB, rfl⟩
    have hh := hb (eraseFG B) hm
    rwa [eraseFG_slot] at hh
  refine ⟨hb, ?_, hfg, ?_⟩
  · change ∀ b ∈ (FGSA.clock p nd.st _).base.blocks, b.slot < s
    rw [clock_base_blocks]
    exact hb
  · change ∀ B ∈ (FGSA.clock p nd.st _).fg.TF, B.slot < s
    rw [clock_fg]
    exact hfg

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The raw equivocation pool equals its cutoff-filtered pool at release.
Thus the implementation count is the specification count on the active view. -/
theorem fgsa_release_count_bridge (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {r : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.releaseTime p.toParams r)))
    (hEpoch : ∀ j w, j < i → rho.events[j]? = some (.restart v w) →
      w < SA.releaseTime p.toParams r) (B : Block) :
    let view := GridCO.expire
      { actView (V2.D.Run.stateBefore E rho i v).st with now := SA.releaseTime p.toParams r }
      (SA.releaseTime p.toParams r)
    let raw := GridCO.votesAt view r
    let cut := raw.filter (fun o => GridCO.stampVote view o < SA.releaseTime p.toParams r)
    raw = cut ∧ (∀ seat, GridCO.equivocates raw seat = GridCO.equivocates cut seat) ∧
      GridCO.releaseCount p.toParams.engine view r B =
        let resolved := cut.filter (fun o =>
          GridCO.resolvedBefore view o (SA.releaseTime p.toParams r))
        ((GridCO.seats p.n resolved).filter (fun seat =>
          !GridCO.equivocates cut seat &&
          (GridCO.seatVotes resolved seat).any (fun o =>
            (GridCO.resolvedHead? view o).any (fun target => !Block.compatible target
                B)))).length := by
  intro view raw cut
  have hh := fgsa_release_input_votes_stamped E rho hs hi hEpoch
  have he : cut = raw := by
    apply List.filter_eq_self.mpr
    intro o ho
    exact decide_eq_true (hh o (List.mem_filter.mp ho).1)
  refine ⟨he.symm, fun seat => congrArg (fun xs => GridCO.equivocates xs seat) he.symm, ?_⟩
  rw [he]
  have hpred : (fun o : GridCO.Wire p.n .root => match GridCO.resolvedHead? view o with
      | some target => !Block.compatible target B
      | none => false) = (fun o => (GridCO.resolvedHead? view o).any
        (fun target => !Block.compatible target B)) := by
    funext o
    cases GridCO.resolvedHead? view o <;> rfl
  unfold GridCO.releaseCount
  dsimp only
  have hcut : GridCO.releaseTime p.toParams.engine r = SA.releaseTime p.toParams r := rfl
  rw [hcut]
  change _ = _
  congr 1
  apply congrArg (fun f => List.filter f _)
  funext seat
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes _ seat).any f)
  exact hpred

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The action time is the gate time of label `rR`. -/
theorem fgsa_action_gate_time (r : Nat) : p.actionTime r = SA.gateTime p.toParams (r * p.R) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An emitted FG action reads the clock state of its own tick.
The same clock runs the gate at `d_{rR}` before that action. -/
theorem fgsa_action_reads_gate (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (r : Nat) (seat : Fin p.n) (body : RowPayload) :
    (⟨.seat (.base .fg) seat, .row body⟩ : Obj p) ∈
      (V2.D.tick E rho nd v (p.actionTime r)).2 ↔
    E.awake v (p.actionTime r) = true ∧ rho.seatOf (.base .fg) seat = v ∧
      (attest p (FGSA.clock p nd.st (SA.gateTime p.toParams (r * p.R)))
        nd.record ⟨0, p.nPos⟩).1 = some body := by
  have hmem := V2.D.Engine.mem_tick_duty_iff (P := fgsa p c) E rho nd v
    (p.actionTime r) (.fgAction r) rfl (fgsa_dutiesInjectiveAt _) seat (.row body)
  refine hmem.trans ?_
  change (_ ∧ _ ∧ (attest p (FGSA.clock p nd.st (p.actionTime r))
      nd.record ⟨0, p.nPos⟩).1.map Msg.row = some (.row body)) ↔ _
  simp only [Option.map_eq_some_iff, Msg.row.injEq, exists_eq_right]
  rfl

private theorem fgsa_clock_gate_eq (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.gateTime p.toParams s) =
      gateStep p (clockPre p st (SA.gateTime p.toParams s)) s := by
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  have ht : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hslot : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
    rw [ht, Int.mul_ediv_cancel_left _ (by positivity), Int.toNat_natCast]
  have hg : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by rw [ht]; positivity
  unfold FGSA.clock
  dsimp only
  rw [hslot]
  simp only [hg, decide_true, beq_self_eq_true, Bool.true_and, ite_true]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The fresh scheduled gate saves the anchored confirmation of its
pre-gate active view, including an empty confirmation. -/
theorem fgsa_gate_saved_result (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.gateTime p.toParams s)))
    (hj : joinedAtTime p (V2.D.Run.stateBefore E rho i v).st.restartTime
      (SA.gateTime p.toParams s) = true) :
    let st := (V2.D.Run.stateBefore E rho i v).st
    GridCO.savedGenuine (FGSA.clock p st (SA.gateTime p.toParams s)).base s =
      some (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
        (actView (clockPre p st (SA.gateTime p.toParams s))) s) := by
  intro st
  have hn := fgsa_gate_fresh E rho hs hi
  have hn' : GridCO.savedGenuine (clockPre p st (SA.gateTime p.toParams s)).base s = none := by
    unfold GridCO.savedGenuine
    rw [clockPre_genuine]
    exact hn
  rw [fgsa_clock_gate_eq]
  have he := (gateStep_fresh p _ s hn' (by rwa [clockPre_joined])).1
  rw [clockPre_fg] at he
  exact he

/-- A fresh unjoined gate saves an empty confirmation. -/
theorem fgsa_gate_saved_unjoined (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.gateTime p.toParams s)))
    (hj : joinedAtTime p (V2.D.Run.stateBefore E rho i v).st.restartTime
      (SA.gateTime p.toParams s) = false) :
    GridCO.savedGenuine (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st
      (SA.gateTime p.toParams s)).base s = some none := by
  have hn := fgsa_gate_fresh E rho hs hi
  have hn' : GridCO.savedGenuine
      (clockPre p (V2.D.Run.stateBefore E rho i v).st (SA.gateTime p.toParams s)).base s =
      none := by
    unfold GridCO.savedGenuine
    rw [clockPre_genuine]
    exact hn
  rw [fgsa_clock_gate_eq]
  exact (gateStep_unjoined p _ s hn' (by rwa [clockPre_joined])).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every stored non-genesis block has a proposal delivered at an earlier
index in the current or an earlier local restart epoch. No schedule premise is needed. -/
theorem fgsa_stored_block_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (b : Block)
    (hb : b ∈ (V2.D.Run.stateBefore E rho i v).st.base.blocks) (hg : b ≠ .genesis) :
    ∃ w, w ∈ (V2.D.Run.stateBefore E rho i v).st.proposals ∧ Wire.block? w = some b ∧
      ∃ j o t, j < i ∧ rho.events[j]? = some (.deliver v o t) ∧ toWire p o = w ∧
        ∀ k, j + 1 ≤ k → k ≤ i →
          w ∈ (V2.D.Run.stateBefore E rho k v).st.proposals := by
  obtain ⟨B, hB, he⟩ := ((cstoreInv_stateBefore E rho i v).baseTree b).mp hb
  have hBg : B ≠ .genesis := by
    intro h
    subst B
    exact hg he.symm
  obtain ⟨w, ⟨hw, hwire⟩, -⟩ := (metaInv_stateBefore E rho i v).treeWire B hB hBg
  rw [he] at hwire
  obtain ⟨j, o, t, hj, hd, ho, -, hr⟩ := stored_proposal_delivered E rho i v w hw
  exact ⟨w, hw, hwire, j, o, t, hj, hd, ho, hr⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The strict time reader equals the actual pre-tick store only when the
run has no restarts. All other results in this module allow restarts. -/
theorem fgsa_preTick_eq_timeRead (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    V2.D.Run.stateBefore E rho i v = V2.D.Run.stateBeforeTime E rho t v :=
  V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs hnr hi

end AvailableChain.FGSA.Run
end

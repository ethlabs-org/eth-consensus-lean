module
public import AvailableChainSAPC.Proofs.LeaseProtection
public import AvailableChainSAPC.Proofs.HeadEmission
public import AvailableChainSAPC.Proofs.BaseArchive
public import AvailableChainGridCO.Proofs.Outage

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- An active floor or PC cannot bypass the finite root. The disabled
case is the shared SA walk. -/
theorem choice_extends_liveRoot (p : Params) {n : Nat} (st : State n)
    (tree : List Block) (raw support : List (GridCO.Wire n)) (r : Slot)
    (cert : Option (PC n)) :
    Block.Preceq (GridCO.liveRoot st.base) (choice p st tree raw support r cert) := by
  unfold choice
  split
  · exact GridCO.forkChoice_extends_liveRoot st.base tree raw support r
  · exact GridCO.prefix_trans _ _ _ (mandatoryRoot_covers _ _) (GridCO.ghost_extends _ _ _ _)

/-- A protected row constrains the actual signed HEAD after its clock.
The label-zero HEAD is genesis and is compatible with every prefix. -/
theorem emitted_head_compatible_of_protection {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (i : Nat) (v : V) (t : Time)
    (tick : rho.events[i]? = some (.tick v t)) (B : Block) (g : Nat) (d : Time)
    (hp : GridCO.ProtectsUntil (Run.stateBefore (sapc p) rho (i + 1) v).base B g d)
    (ht : t < d) (r : Slot) (seat : Fin p.n) (data : HeadData)
    (emitted : fromHead ⟨.seat r seat, data⟩ ∈ Run.emittedAt (sapc p) E rho i v t) :
    Block.Compatible data.target B := by
  set_option backward.isDefEq.respectTransparency false in
  have act := (emittedAt_seat_action (sapc p) E rho i v t r seat (.head data) emitted).2
  have target : headTarget p (clock p (Run.stateBefore (sapc p) rho i v) t) r = data.target := by
    exact congrArg HeadData.target (Msg.head.inj (Option.some.inj act))
  by_cases zero : r = 0
  · subst r
    have eq : data.target = .genesis := by simpa [headTarget] using target.symm
    rw [eq]
    exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix B))
  · have post : Run.stateBefore (sapc p) rho (i + 1) v =
        clock p (Run.stateBefore (sapc p) rho i v) t := by
      rw [stateBefore_succ_event tick]
      simp only [World.step, Function.update_self]
      rfl
    obtain ⟨deadline, hd, row⟩ := hp
    have live : (Run.stateBefore (sapc p) rho (i + 1) v).base.now < deadline := by
      rw [post, clock_now]
      exact ht.trans_le hd
    have root := GridCO.liveTarget_preceq_liveRoot _
      (lease_map_at_fold p _ v).2 g B deadline row live
    change Block.Preceq B (GridCO.liveRoot
      (Run.stateBefore (sapc p) rho (i + 1) v).base) at root
    rw [post] at root
    apply Bool.or_eq_true_iff.mpr
    right
    rw [← target]
    apply GridCO.prefix_trans B _ _ root
    simpa only [headTarget, beq_iff_eq, zero, ↓reduceIte] using
      choice_extends_liveRoot p (clock p (Run.stateBefore (sapc p) rho i v) t) _ _ _ r _

/-- Each conflicting release seat is faulty if earlier honest HEADs of
that label are compatible. Original archive signatures justify the count. -/
theorem releaseCount_le_faults_of_emissions {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hsig : UnforgeableSignatures (sapc p) E rho) (cut : Time) (reader : V)
    (r : Slot) (B : Block)
    (heads : ∀ seat data, rho.seatOf r seat ∈ rho.honest → voteTime p r < cut →
      Run.emits (sapc p) E rho (rho.seatOf r seat)
        (fromHead ⟨.seat r seat, data⟩) (voteTime p r) → Block.Compatible data.target B) :
    GridCO.releaseCount p.engine (Run.stateBeforeTime (sapc p) rho cut reader).base r B ≤
      (faulty rho).card := by
  rw [GridCO.releaseCount_eq_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf r)
  · intro seat member
    change seat ∈ GridCO.releaseConflictSeats p.engine
      (Run.stateBeforeTime (sapc p) rho cut reader).base r B at member
    change rho.seatOf r seat ∈ faulty rho
    simp only [GridCO.releaseConflictSeats, Finset.mem_filter, List.mem_toFinset] at member
    obtain ⟨o, ho, conflict⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp member.2).2
    have seatEq : GridCO.headSeat? o = some seat := by simpa using (List.mem_filter.mp ho).2
    have raw := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
    have label : GridCO.headLabel? o = some r := by simpa using (List.mem_filter.mp raw).2
    obtain ⟨target, rfl⟩ := GridCO.head_wire_shape o r seat label seatEq
    obtain ⟨data, archived, eq⟩ := baseArchived_head _ (baseArchived_at_fold p _ reader)
      r seat target (List.mem_filter.mp raw).1
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro honest
    have time : voteTime p r < cut := by
      apply Int.le_sub_one_iff.mp
      apply archived_honest_head_time_le_read p E rho hsig reader (cut - 1) r seat data
        _ honest
      simpa only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff] using archived
    have comp := heads seat data honest time
      (archive_authenticated_beforeTime p E rho hsig cut reader r seat data archived honest)
    rw [eq] at comp
    simp [GridCO.headTarget?, show Block.compatible target B = true from comp] at conflict
  · intro a _ b _ eq
    exact (rho.seatOf r).injective eq

/-- Only HEAD duties whose release is after the arming read need a seed.
There is no delivery or participation assumption after that read. -/
def ArmingHeadsCompatible {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (U : Time) (B : Block) : Prop :=
  ∀ r seat data, rho.seatOf r seat ∈ rho.honest →
    voteTime p r ≤ U → U < releaseTime p r →
    Run.emits (sapc p) E rho (rho.seatOf r seat)
      (fromHead ⟨.seat r seat, data⟩) (voteTime p r) → Block.Compatible data.target B

/-- The shared SA first-loss induction applies to SA-PC. A protected
HEAD respects the finite root, so release has at most the faulty count.
PC selection and cap changes impose no additional premises. -/
theorem protection_from_armed_index {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (B : Block) (g : V → Nat)
    (U d : Time) (start finish : Nat)
    (strong : ∀ v ∈ rho.honest, (faulty rho).card < g v)
    (base : ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.stateBefore (sapc p) rho start v).base B (g v) d ∧
      Block.Preceq B (Run.stateBefore (sapc p) rho start v).base.stableRecord)
    (seed : ArmingHeadsCompatible p E rho U B)
    (before : ∀ j v t, j < start → rho.events[j]? = some (.tick v t) → t ≤ U)
    (after : ∀ j v t, start ≤ j → rho.events[j]? = some (.tick v t) → U < t)
    (deadline : ∀ j e, start ≤ j → j < finish → rho.events[j]? = some e → e.time < d)
    (hfinish : start ≤ finish) :
    ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.stateBefore (sapc p) rho finish v).base B (g v) d ∧
      Block.Preceq B (Run.stateBefore (sapc p) rho finish v).base.stableRecord := by
  set_option backward.isDefEq.respectTransparency false in
  apply state_interval_induction (sapc p) rho
    (fun v st => GridCO.ProtectsUntil st.base B (g v) d ∧
      Block.Preceq B st.base.stableRecord) start finish hfinish base
  · intro v hv st o hp
    constructor
    · simpa only [sapc, GridCO.ProtectsUntil, process_obligations] using! hp.1
    · change Block.Preceq B (stable (process p st o))
      rw [process_stable]
      exact hp.2
  · intro i u t hsi hif tick hu hp past
    have htd := deadline i _ hsi hif tick
    apply clock_preserves_protection p _ t B (g u) d
      (base_receiptStamped_at_fold p _ u) (lease_map_at_fold p _ u).1 hp.1 hp.2 htd
    intro r hr
    change t = releaseTime p r at hr
    change GridCO.releaseCount p.engine (Run.stateBefore (sapc p) rho i u).base r B < g u
    rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick]
    apply lt_of_le_of_lt (releaseCount_le_faults_of_emissions p E rho
      hx.toUnforgeableSignatures t u r B ?_) (strong u hu)
    intro seat data honest ht emitted
    obtain ⟨j, hj, hmem⟩ := emitted
    have hji := eventIndex_lt_of_time_lt hx.toScheduleWellFormed hj tick ht
    by_cases hjstart : j < start
    · exact seed r seat data honest (before j _ _ hjstart hj)
        (hr ▸ after i u t hsi tick) ⟨j, hj, hmem⟩
    · exact emitted_head_compatible_of_protection p E rho j _ _ hj B (g _) d
        (past j (by omega) hji _ honest).1 (ht.trans htd) r seat data hmem

/-- Once every reader has the prefix lease and record, both remain until
the lease deadline. The endpoint is excluded because expiry is at equality. -/
theorem protection_from_armed_read {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (B : Block) (g : V → Nat) (U d : Time)
    (strong : ∀ v ∈ rho.honest, (faulty rho).card < g v)
    (base : ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.readAt (sapc p) rho U v).base B (g v) d ∧
      Block.Preceq B (Run.readAt (sapc p) rho U v).base.stableRecord)
    (seed : ArmingHeadsCompatible p E rho U B)
    (t : Time) (hUt : U ≤ t) (htd : t < d) :
    ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.readAt (sapc p) rho t v).base B (g v) d ∧
      Block.Preceq B (Run.readAt (sapc p) rho t v).base.stableRecord := by
  let start := (rho.events.filter (fun e => decide (e.time ≤ U))).length
  let finish := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have base' : ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.stateBefore (sapc p) rho start v).base B (g v) d ∧
      Block.Preceq B (Run.stateBefore (sapc p) rho start v).base.stableRecord := by
    simpa only [readAt_eq_stateBefore hx.toScheduleWellFormed U] using base
  rw [readAt_eq_stateBefore hx.toScheduleWellFormed t]
  apply protection_from_armed_index p E rho hx B g U d start finish strong base' seed
  · intro j v t' hj he
    exact (index_lt_read_length_iff hx.toScheduleWellFormed U he).mp hj
  · intro j v t' hj he
    have hn : ¬ t' ≤ U := by
      intro ht'
      have := (index_lt_read_length_iff hx.toScheduleWellFormed U he).mpr ht'
      omega
    exact lt_of_not_ge hn
  · intro j e _ hj he
    exact ((index_lt_read_length_iff hx.toScheduleWellFormed t he).mp hj).trans_lt htd
  · exact read_length_mono U t hUt

/-- The map at a public read is exactly the map after the local tick.
Equal-time PC receipts cannot change a finite lease. -/
theorem read_obligations_eq_clock {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (v : V) (t : Time) (tick : Event.tick v t ∈ rho.events) :
    (Run.readAt (sapc p) rho t v).base.obligations =
      (clock p (Run.stateBeforeTime (sapc p) rho t v) t).base.obligations :=
  Engine.read_field_eq_clock (sapc p) (fun st => st.base.obligations)
    (process_obligations p) E rho hs v t tick

theorem read_stable_eq_clock {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (v : V) (t : Time) (tick : Event.tick v t ∈ rho.events) :
    stable (Run.readAt (sapc p) rho t v) =
      stable (clock p (Run.stateBeforeTime (sapc p) rho t v) t) :=
  Engine.read_field_eq_clock (sapc p) stable (process_stable p) E rho hs v t tick

/-- At a completed gate, only the next label can have a release still
in flight. Its actual HEAD coverage is the entire arming seed. -/
theorem armingHeadsCompatible_of_heads {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (r : Slot) (B : Block)
    (heads : ∀ v ∈ rho.honest, Block.Preceq B (headData p rho (r + 1) v).target) :
    ArmingHeadsCompatible p E rho (gateTime p r) B := by
  intro label seat data honest hv hr emitted
  have eq : label = r + 1 := GridCO.in_flight_label_at_gate p.engine r label hv hr
  subst label
  obtain ⟨i, tick, member⟩ := emitted
  have act := (emittedAt_seat_action (sapc p) E rho i _ _ _ seat (.head data) member).2
  rw [stateBefore_tick_eq_stateBeforeTime hs tick] at act
  have eq : data.target = (headData p rho (r + 1) (rho.seatOf (r + 1) seat)).target := by
    exact (congrArg HeadData.target (Msg.head.inj (Option.some.inj act))).symm
  rw [eq]
  exact Bool.or_eq_true_iff.mpr (Or.inr (heads _ honest))

/-- A protected interval supplies the seed for a later renewal. This
includes the HEAD emitted before the pending first-renewal gate. -/
theorem armingHeadsCompatible_of_protection {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (B : Block) (g : V → Nat) (U d W : Time)
    (hUW : U ≤ W) (hWd : W < d)
    (strong : ∀ v ∈ rho.honest, (faulty rho).card < g v)
    (base : ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.readAt (sapc p) rho U v).base B (g v) d ∧
      Block.Preceq B (Run.readAt (sapc p) rho U v).base.stableRecord)
    (seed : ArmingHeadsCompatible p E rho U B) :
    ArmingHeadsCompatible p E rho W B := by
  intro r seat data honest ht hr emitted
  by_cases old : voteTime p r ≤ U
  · exact seed r seat data honest old (hUW.trans_lt hr) emitted
  · obtain ⟨i, tick, member⟩ := emitted
    have hp := (protection_from_armed_read p E rho hx B g U d strong base seed
      (voteTime p r) (le_of_not_ge old) (ht.trans_lt hWd) _ honest).1
    have post : GridCO.ProtectsUntil (Run.stateBefore (sapc p) rho (i + 1)
        (rho.seatOf r seat)).base B (g (rho.seatOf r seat)) d := by
      obtain ⟨deadline, hd, row⟩ := hp
      rw [read_obligations_eq_clock p E rho hx.toScheduleWellFormed _ _
        (List.mem_of_getElem? tick)] at row
      refine ⟨deadline, hd, ?_⟩
      rw [stateBefore_succ_event tick]
      simp only [World.step, Function.update_self]
      rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick]
      exact row
    exact emitted_head_compatible_of_protection p E rho i _ _ tick B _ d post
      (ht.trans_lt hWd) r seat data member

end AvailableChain.SAPC
end

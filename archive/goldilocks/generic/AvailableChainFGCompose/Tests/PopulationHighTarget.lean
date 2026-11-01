module
public import AvailableChainFGCompose.Proofs.Population.HighTarget -- shake: keep (private fixture)

set_option linter.privateModule false
noncomputable section
public section

/-! Generic ordinary event-fold controls. Both honest receivers retain the delivered row.
The first target at round 0 and the deduplicated prior target at round 1 use the same run. -/
namespace AvailableChain.FGCompose.Tests.PopulationHighTarget
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev head : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := RecordOnce × List (V2.Signed Unit (fun _ => 1) (Row (Fin 1)))
  Label := Unit
  Duty := Time
  signLabel _ := ()
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := RecordOnce × List (V2.Signed Unit (fun _ => 1) (Row (Fin 1)))
  init := (RecordOnce.initial, [])
  clock st _ := st
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act st t _ := if t % 8 = 6 then
    (createRowOnce electorate cfg st.1 0 (some .genesis) head).1 else none
  gossip _ _ := []
  process st o := (st.1, o :: st.2)
  selfVisible _ := true
  recordOwn st o := (match o.auth with
    | .none => st.1
    | .seat _ _ => record_row_once st.1 o.payload, o :: st.2)
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev wire : protocol.Object := ⟨.seat () 0, row⟩
private abbrev old : RecordOnce := record_row_once RecordOnce.initial row
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with | .none => none | .seat _ _ => some o.payload
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase _ := none
  proposalRows _ := []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := Prod.fst
  inputs _ := (some .genesis, head)
  enabled t := decide (t % 8 = 6)
  finalizedOut _ := .genesis
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core st := ⟨(), Store.init, [], st.2⟩
  erase _ := .genesis
  source _ := some .genesis
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := simplexHeightView electorate cfg
  finality := simplexFinalityView electorate cfg
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X
private abbrev history : FGHistoryWireReads reads where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer a := some a.payload.signer
  decode_height a u hd := by
    cases a with | mk auth payload => cases auth <;> cases hd; rfl
  decode_finality a u hd := by
    cases a with | mk auth payload => cases auth <;> cases hd; rfl
  decode_signer a u hd := by
    cases a with | mk auth payload => cases auth <;> cases hd; rfl
private abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * s
  vote s := 4 * s + 1
  early s := 4 * s + 2
  freeze s := 4 * s + 3
  release s := 4 * s + 5
  gate s := 4 * s + 6
  action r := 4 * (r * 2 : Nat) + 6
private abbrev point : FGServicePoint := ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 0⟩
private abbrev env (V : Type) : Generic.Env V where
  Δ := 2
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 16
  events := [.tick 9 0, .tick 7 0, .tick 9 2, .tick 7 2, .tick 9 4, .tick 7 4,
    .tick 9 6, .tick 7 6, .deliver 7 wire 7, .deliver 9 wire 7, .tick 9 8, .tick 7 8,
    .tick 9 10, .tick 7 10, .tick 9 12, .tick 7 12, .tick 9 14, .tick 7 14,
    .tick 9 16, .tick 7 16]
  seatOf _ _ := 9
  input _ _ := ()
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := Finset.univ
  horizon := 16
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .deliver 0 wire 7,
    .tick 0 8, .tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16]
  seatOf _ _ := 0
  input _ _ := ()

private theorem global_client_premises_sat : FGSafetyClientLaws reads electorate cfg where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record nd o := by cases o with | mk auth payload => cases auth <;> rfl
  tick_rows E rho e he nd x t := by
    have hx : e 0 = x := by
      rw [← e.apply_symm_apply x]
      congr 1
      exact Subsingleton.elim _ _
    have hs : e.symm x = 0 := Subsingleton.elim _ _
    have hseat : rho.seatOf () 0 = x := (he 0).trans hx
    cases ha : E.awake x t <;> by_cases ht : t % 8 = 6 <;>
      cases hr : (createRowOnce electorate cfg nd.1 0 (some .genesis) head).1 <;>
      simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, hs, hr, hseat, ht]
    rename_i u
    rfl

private theorem mixed_client_premises_sat :
    FGHolderClientLaws reads electorate cfg (env Nat) run (ordinaryFGExecutionObs (env Nat) run)
      (safetyHolder reads run) where
  holder_eq _ := rfl
  holder_inj _ _ _ := Subsingleton.elim _ _
  initial_record := rfl
  record_step x k _ := by
    let J := global_client_premises_sat
    have recEntry (j : Nat) : reads.record (ordinaryEntry (env Nat) run x j) =
        reads.record (V2.D.Run.stateBefore (env Nat) run j x) := by
      rw [ordinaryEntry_def]
      cases he : run.events[j]? with
      | none => rfl
      | some e =>
        dsimp only [Option.map, Option.getD]
        cases e with
        | restart y t =>
          dsimp only [ordinaryEntryStep]
          split_ifs <;> rfl
        | tick y t =>
          dsimp only [ordinaryEntryStep]
          split_ifs <;> rfl
        | deliver y o t =>
          dsimp only [ordinaryEntryStep]
          split_ifs <;> rfl
    have recPrefix (j : Nat) :
        reads.record (V2.D.Run.stateBefore (env Nat) run (j + 1) x) =
          (V2.D.Engine.ownReleasedAt (env Nat) run x j).foldl (safetyRecordStep reads)
            (reads.record (V2.D.Run.stateBefore (env Nat) run j x)) := by
      have h := Gen.V2.Duty.ownRecord_fold_restart reads.record (safetyRecordStep reads)
        J.clock_record J.process_record J.own_record (env Nat) run (Nat.le_succ j) x
        (fun _ t _ _ _ => J.restart_record _ t)
      rw [V2.D.Engine.ownReleased_succ (env Nat) run x (le_refl j),
        V2.D.Engine.ownReleased_self, List.nil_append] at h
      exact h
    have cutStart (j : Nat) : ordinaryCutState (env Nat) run x (3 * j) =
        V2.D.Run.stateBefore (env Nat) run j x := by
      rw [ordinaryCutState_def, ite_eq_left (by omega), show 3 * j / 3 = j by omega]
    have cutEntry (j : Nat) : ordinaryCutState (env Nat) run x (3 * j + 1) =
        ordinaryEntry (env Nat) run x j := by
      rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_left (by omega),
        show (3 * j + 1) / 3 = j by omega]
    have cutDone (j : Nat) : ordinaryCutState (env Nat) run x (3 * j + 2) =
        V2.D.Run.stateBefore (env Nat) run (j + 1) x := by
      rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_right (by omega),
        show (3 * j + 2) / 3 = j by omega]
    change reads.record (ordinaryCutState (env Nat) run x (k + 1)) =
      (if k % 3 = 1 then obsOwnReleased (ordinaryFGExecutionObs (env Nat) run) x (k / 3)
        else []).foldl (safetyRecordStep reads)
        (reads.record (ordinaryCutState (env Nat) run x k))
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 3 ∧ k = 3 * j + r :=
      ⟨k / 3, k % 3, by omega, by omega⟩
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    · simp only [Nat.add_zero]
      rw [cutStart, cutEntry, ite_eq_right (by omega), List.foldl_nil]
      exact recEntry j
    · rw [show 3 * j + 1 + 1 = 3 * j + 2 by omega, cutEntry, cutDone,
        ite_eq_left (by omega), show (3 * j + 1) / 3 = j by omega,
        ordinary_obsOwnReleased, recEntry]
      exact recPrefix j
    · rw [cutDone, show 3 * j + 2 + 1 = 3 * (j + 1) by omega, cutStart,
        ite_eq_right (by omega), List.foldl_nil]
  holder_rows j x t i ht hi := by
    have hx : x = 9 := hi.symm
    subst hx
    have hj : j < 20 := (List.getElem?_eq_some_iff.mp ht).1
    have hi' : i = 0 := Subsingleton.elim _ _
    subst i
    interval_cases j <;> try simp at ht
    · have ht' : t = 0 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 2 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 4 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 6 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 8 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 10 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 12 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 14 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 16 := by simpa using ht.symm
      subst t
      decide +kernel
  nonholder_rows j x t ht hn := by
    have hj : j < 20 := (List.getElem?_eq_some_iff.mp ht).1
    interval_cases j <;> try simp at ht
    all_goals
      rcases ht with ⟨rfl, rfl⟩
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel

set_option maxHeartbeats 1000000 in
-- Reduce the finite event prefix at every cut, including cuts beyond the horizon.
private theorem record_at_cut (k x : Nat) :
    reads.record (V2.D.Run.stateBefore (env Nat) run k x) =
      if x = 9 ∧ 6 < k then old else RecordOnce.initial := by
  by_cases h9 : x = 9
  · subst x
    by_cases hk : k < 20
    · interval_cases k <;> rfl
    · have ht : run.events.take k = run.events :=
        List.take_of_length_le (by simpa using hk)
      rw [ite_eq_left ⟨rfl, by omega⟩, V2.D.Run.stateBefore, ht]
      rfl
  · rw [ite_eq_right (fun h => h9 h.1)]
    by_cases h7 : x = 7
    · subst x
      by_cases hk : k < 20
      · interval_cases k <;> rfl
      · have ht : run.events.take k = run.events :=
          List.take_of_length_le (by simpa using hk)
        rw [V2.D.Run.stateBefore, ht]
        rfl
    by_cases hk : k < 20
    · interval_cases k <;>
        simp_all [V2.D.Run.stateBefore, V2.D.World.init, V2.D.World.step, V2.D.tick,
          V2.D.Run.ownSeats, List.finRange_succ, protocol, run, env]
    · have ht : run.events.take k = run.events :=
        List.take_of_length_le (by simpa using hk)
      rw [V2.D.Run.stateBefore, ht]
      simp_all [V2.D.World.init, V2.D.World.step, V2.D.tick,
          V2.D.Run.ownSeats, List.finRange_succ, protocol, run, env]

private theorem exact_row (j x q : Nat) (a : protocol.Object)
    (ha : HonestRowAt reads (env Nat) run timing j x q a) :
    j = 6 ∧ x = 9 ∧ q = 0 ∧ a = wire := by
  obtain ⟨_, hj, hw⟩ := ha
  have hlen : j < 20 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · have he : x = 9 ∧ q = 0 := by simpa using hj.symm
    rcases he with ⟨rfl, rfl⟩
    change a ∈ [wire] at hw
    exact ⟨rfl, rfl, rfl, List.mem_singleton.mp hw⟩
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw
  · change a ∈ [] at hw; cases hw

private structure TargetPremises {V : Type} [DecidableEq V] (rho : V2.D.Run V protocol) :
    Prop where
  entry_source : ∀ x r C, x ∈ rho.honest →
    actionSourceFG core (env V) rho timing x r = some (some C) →
    high core obs point.reset C → genesisRoot = (obs.height C).T_h.root
  records : ∀ j x, x ∈ rho.honest →
    HighRecordInvariant point.reset.M (fun _ => genesisRoot)
      (reads.record (V2.D.Run.stateBefore (env V) rho j x))
  finality : ∀ j x t Λ fp, x ∈ rho.honest →
    finality_pair Λ (reads.inputs (protocol.clock
      (V2.D.Run.stateBefore (env V) rho j x) t)).2 = some fp →
    point.reset.M + 1 ≤ fp.height → fp.target = genesisRoot
  prior : ∀ j x, x ∈ rho.honest →
    ∀ b ∈ (reads.record (V2.D.Run.stateBefore (env V) rho j x)).sent,
    ∃ k q a, k < j ∧ HonestRowAt reads (env V) rho timing k x q a ∧
      namedEntry (history.heightPair a) = namedEntry b.1
  emission : HighRecordEmission reads timing (env V) rho electorate cfg
  complete : ∀ j x r a, HonestRowAt reads (env V) rho timing j x r a →
    ∃ u, reads.decode a = some u ∧ RowComplete reads rho history.signer (fun _ => true) x a
  wires : FGRowPermissionWireLaws reads (fun a => namedEntry (history.heightPair a))
  client : FGHolderClientLaws reads electorate cfg (env V) rho
    (ordinaryFGExecutionObs (env V) rho) (safetyHolder reads rho)
  trace : FGHolderClientTrace reads electorate cfg (env V) rho
    (ordinaryFGExecutionObs (env V) rho) (safetyHolder reads rho)
  timing_laws : FGTimingLaws timing
  schedule : V2.D.ScheduleWellFormed (env V) rho
  receipt : TRowsReceipt core reads (env V) rho timing Prod.snd 2

private theorem mixed_premises_sat : TargetPremises run where
  entry_source x r C _ hs _ := by
    obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hs
    have hC : C = .genesis := (Option.some.inj he).symm
    subst C
    rfl
  records j x _ := by
    rw [record_at_cut]
    split_ifs
    · intro y _
      refine ⟨?_, rfl, Or.inl rfl, ?_⟩
      · by_cases hy : y = 1
        · subst y; exact Or.inr rfl
        · exact Or.inl (by
            change (if y = 1 then some genesisRoot else none) = none
            rw [ite_eq_right hy])
      · intro b hb U tm hp
        change b ∈ [row.onceKey] at hb
        have hb' : b = row.onceKey := List.mem_singleton.mp hb
        subst b
        have he : 1 = y ∧ genesisRoot = U ∧ false = tm := NamedHeightPair.vote.inj hp
        exact ⟨he.2.1.symm, he.2.2.symm⟩
    · intro y _
      exact ⟨Or.inl rfl, rfl, Or.inl rfl, fun b hb => (List.not_mem_nil hb).elim⟩
  finality j x t Λ fp _ hf _ := by
    change finality_pair Λ head = some fp at hf
    simp [finality_pair] at hf
  prior j x _ b hb := by
    rw [record_at_cut] at hb
    split_ifs at hb with hx
    · rcases hx with ⟨rfl, hpos⟩
      change b ∈ [row.onceKey] at hb
      have hb' : b = row.onceKey := List.mem_singleton.mp hb
      subst b
      exact ⟨6, 0, wire, hpos, ⟨by decide, rfl, by decide⟩, rfl⟩
    · cases hb
  emission j x r a u ha hd := by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := exact_row j x r a ha
    have hu : row = u := Option.some.inj hd
    subst u
    rfl
  complete j x r a ha := by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := exact_row j x r a ha
    exact ⟨row, rfl, rfl, 0, rfl, rfl⟩
  wires := by
    constructor
    intro o u hd
    refine ⟨o, rfl, hd, ?_⟩
    cases o with | mk auth payload => cases auth <;> cases hd; rfl
  client := mixed_client_premises_sat
  trace := safety_client_trace_obs reads electorate cfg (env Nat) run _
    (ordinaryFGExecutionObs_laws (env Nat) run) mixed_client_premises_sat
  timing_laws := ⟨by decide, by decide, fun _ => by simp, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  schedule := by
    constructor
    · decide
    · decide +kernel
    · decide +kernel
    · intro ev hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with
        rfl | rfl | rfl | rfl | rfl
         | rfl | rfl | rfl | rfl | rfl
         | rfl | rfl | rfl | rfl | rfl
         | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro ev hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with
        rfl | rfl | rfl | rfl | rfl
         | rfl | rfl | rfl | rfl | rfl
         | rfl | rfl | rfl | rfl | rfl
         | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro x t hm
      simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
        reduceCtorEq, or_false, false_or] at hm
      rcases hm with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
         | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
         | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
         | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨7, rfl⟩
      · exact ⟨7, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨8, rfl⟩
    · intro x hx t ht hzero hhor _
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      obtain ⟨k, hk⟩ := ht
      change t = (k : Time) * 2 at hk
      change t ≤ 16 at hhor
      rw [hk] at hhor
      have hb : k * 2 ≤ 16 := by exact_mod_cast hhor
      have hbound : k ≤ 8 := by omega
      subst t
      rcases hx' with rfl | rfl <;> interval_cases k <;> simp

  receipt j y r a ha _ x hx := by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := exact_row j y r a ha
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl
    · change wire ∈ (V2.D.Run.stateBeforeTime (env Nat) run 8 7).2 ∨ _
      exact Or.inl (by decide +kernel)
    · change wire ∈ (V2.D.Run.stateBeforeTime (env Nat) run 8 9).2 ∨ _
      exact Or.inl (by decide +kernel)

#print axioms mixed_premises_sat
#print axioms exact_row
#print axioms record_at_cut
#print axioms global_client_premises_sat
#print axioms mixed_client_premises_sat

private theorem mixed_actions_premises_sat :
    FGHonestSeats reads run = {0} ∧ ({0} : Finset (Fin 1)).Nonempty ∧
    electorate.IsQuorum {0} ∧ high core obs point.reset .genesis ∧
    (∀ r, r ≤ 1 → (∀ x ∈ run.honest,
      actionSourceFG core (env Nat) run timing x r = some (some .genesis)) ∧
      (env Nat).t_GST ≤ timing.action r ∧ timing.action r + 2 ≤ run.horizon) ∧
    (∀ x ∈ run.honest, ∀ t, (env Nat).t_GST ≤ t → t ≤ run.horizon →
      (env Nat).awake x t = true) ∧
    (∀ r, reads.enabled (timing.action r) = true) := by
  refine ⟨?_, ⟨0, by simp⟩, by change (1 : Nat) ≤ 1; decide,
    by change (1 : Nat) ≤ 1; decide, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder]
  · intro r hr
    interval_cases r <;> refine ⟨?_, by decide, by decide⟩
    all_goals
      intro x hx
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      rcases hx' with rfl | rfl <;> rfl
  · intro x _ t _ _; rfl
  · intro r
    apply decide_eq_true
    change (4 * (r * 2 : Nat) + 6 : Int) % 8 = 6
    omega

#print axioms mixed_actions_premises_sat

private theorem mixed_targets :
    (∃ j a, j = 6 ∧ a = wire ∧ HonestRowAt reads (env Nat) run timing j 9 0 a ∧
      RowComplete reads run history.signer (fun _ => true) 9 a ∧
      history.heightPair a = .vote 1 genesisRoot false) ∧
    (∃ j q a, j = 6 ∧ q = 0 ∧ a = wire ∧ q ≤ 1 ∧
      HonestRowAt reads (env Nat) run timing j 9 q a ∧
      RowComplete reads run history.signer (fun _ => true) 9 a ∧
      history.heightPair a = .vote 1 genesisRoot false) ∧
    (∃ rows : Fin 1 → protocol.Object, rows 0 = wire ∧
      history.signer (rows 0) = some 0 ∧
      HeldBefore core (env Nat) run Prod.snd 7 (rows 0) 8 ∧
      HeldBefore core (env Nat) run Prod.snd 9 (rows 0) 8) := by
  let p := mixed_premises_sat
  obtain ⟨hH, hne, hQ, hhigh, actions, awake, enabled⟩ := mixed_actions_premises_sat
  have hholder : safetyHolder reads run 0 ∈ run.honest := by decide
  have hsource0 := (actions 0 (by decide)).1 9 (by decide)
  have hsource1 := (actions 1 (by decide)).1 9 (by decide)
  obtain ⟨j, a, ha, hc, hp⟩ := high_target_first_row_holder (D := history) (pt := point)
    (fun _ => genesisRoot) p.entry_source p.records p.finality p.prior
    (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace p.emission
    p.complete p.wires p.timing_laws p.schedule enabled 0 hholder 0 .genesis hsource0 hhigh rfl
    (by intro j q a h hq; omega)
  have he := exact_row j 9 0 a ha
  refine ⟨⟨j, a, he.1, he.2.2.2, ha, hc, hp⟩, ?_⟩
  obtain ⟨j, q, a, hq, ha, hc, hp⟩ := high_target_row_covered_holder
    (D := history) (pt := point) (fun _ => genesisRoot) p.entry_source p.records p.finality
    p.prior (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace
    p.emission p.complete p.wires p.timing_laws p.schedule enabled
    0 hholder 1 .genesis hsource1 hhigh rfl
  have he := exact_row j 9 q a ha
  refine ⟨⟨j, q, a, he.1, he.2.2.1, he.2.2.2, hq, ha, hc, hp⟩, ?_⟩
  obtain ⟨_, rows, hr⟩ := high_target_quorum_covered_holder (D := history) (pt := point)
    (fun _ => genesisRoot) p.entry_source p.records p.finality p.prior
    (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace p.emission
    p.complete p.wires p.timing_laws p.schedule enabled {0}
    (by simpa only [hH] using (Finset.Subset.refl ({0} : Finset (Fin 1))))
    hne hQ Prod.snd 2 (by decide) p.receipt awake
    1 .genesis hhigh (by
      intro i _
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hsource1)
    (actions 1 (by decide)).2.1 (actions 1 (by decide)).2.2
  obtain ⟨j, q, _, ha, _, hs, _, receipts⟩ := hr 0 (by simp)
  obtain ⟨_, _, hq, hw⟩ := exact_row j 9 q (rows 0) ha
  subst q
  exact ⟨rows, hw, hs, receipts 7 (by decide), receipts 9 (by decide)⟩

#print axioms mixed_targets

-- Only the signer obstruction is used: every seat belongs to 9, never to 7.
private theorem old_nonholder_target_impossible :
    ¬ ∃ j q a, q ≤ 0 ∧ HonestRowAt reads (env Nat) run timing j 7 q a ∧
      RowComplete reads run history.signer (fun _ => true) 7 a ∧
      history.heightPair a = .vote 1 genesisRoot false := by
  rintro ⟨j, q, a, _, _, hc, _⟩
  obtain ⟨i, _, hi⟩ := hc.2
  change (9 : Nat) = 7 at hi
  omega

#print axioms old_nonholder_target_impossible
private abbrev emptyRun : V2.D.Run Nat protocol := { run with honest := {7} }

-- Pure-data fallback control: vacuous seat coverage cannot choose an arbitrary wire.
private theorem empty_seats_no_fallback :
    emptyRun.honest.Nonempty ∧ FGHonestSeats reads emptyRun = ∅ ∧
    (∀ i ∈ FGHonestSeats reads emptyRun, ∃ _a : Empty, True) ∧
    ¬ (FGHonestSeats reads emptyRun).Nonempty ∧ ¬ Nonempty (Fin 1 → Empty) := by
  have he : FGHonestSeats reads emptyRun = ∅ := by
    ext i
    simp [FGHonestSeats_def, safetyHolder]
  refine ⟨⟨7, by simp⟩, he, ?_, ?_, ?_⟩
  · intro i hi
    rw [he] at hi
    simp at hi
  · rw [he]; exact Finset.not_nonempty_empty
  · rintro ⟨rows⟩
    exact Empty.elim (rows 0)

#print axioms empty_seats_no_fallback
-- The extra honest receiver contributes no additional FG vote.
private theorem honest_nodes_are_not_seat_votes :
    (FGHonestSeats reads run).card = 1 ∧ run.honest.card = 2 ∧
    (FGHonestSeats reads run).card ≠ run.honest.card := by
  rw [mixed_actions_premises_sat.1]
  decide

#print axioms honest_nodes_are_not_seat_votes
private theorem frozen_premises_sat : TargetPremises frozenRun := by
  have cut (k : Nat) (x : Fin 1) :
      reads.record (V2.D.Run.stateBefore (env (Fin 1)) frozenRun k x) =
        if 3 < k then old else RecordOnce.initial := by
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    by_cases hk : k < 10
    · interval_cases k <;> rfl
    · have ht : frozenRun.events.take k = frozenRun.events :=
        List.take_of_length_le (by simpa using hk)
      rw [ite_eq_left (by omega), V2.D.Run.stateBefore, ht]
      rfl
  have onlyRow (j : Nat) (x : Fin 1) (q : Nat) (a : protocol.Object)
      (ha : HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a) :
      j = 3 ∧ x = 0 ∧ q = 0 ∧ a = wire := by
    obtain ⟨_, hj, hw⟩ := ha
    have hlen : j < 10 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
    · have he : x = 0 ∧ q = 0 := by simpa using hj.symm
      rcases he with ⟨rfl, rfl⟩
      change a ∈ [wire] at hw
      exact ⟨rfl, rfl, rfl, List.mem_singleton.mp hw⟩
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
    · change a ∈ [] at hw; cases hw
  have client : FGHolderClientLaws reads electorate cfg (env (Fin 1)) frozenRun
      (ordinaryFGExecutionObs (env (Fin 1)) frozenRun) (safetyHolder reads frozenRun) := by
    have he : safetyHolder reads frozenRun = fun i : Fin 1 => i :=
      funext (fun _ => Subsingleton.elim _ _)
    rw [he]
    exact ordinary_FGHolderClientLaws reads electorate cfg (env (Fin 1)) frozenRun
      global_client_premises_sat (Equiv.refl _) (fun _ => Subsingleton.elim _ _)
  refine {
    entry_source x r C _ hs _ := by
      obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hs
      have hC : C = .genesis := (Option.some.inj he).symm
      subst C
      rfl
    records j x _ := by
      rw [cut]
      split_ifs
      · intro y _
        refine ⟨?_, rfl, Or.inl rfl, ?_⟩
        · by_cases hy : y = 1
          · subst y; exact Or.inr rfl
          · exact Or.inl (by
              change (if y = 1 then some genesisRoot else none) = none
              rw [ite_eq_right hy])
        · intro b hb U tm hp
          change b ∈ [row.onceKey] at hb
          have hb' : b = row.onceKey := List.mem_singleton.mp hb
          subst b
          have he : 1 = y ∧ genesisRoot = U ∧ false = tm := NamedHeightPair.vote.inj hp
          exact ⟨he.2.1.symm, he.2.2.symm⟩
      · intro y _
        exact ⟨Or.inl rfl, rfl, Or.inl rfl, fun b hb => (List.not_mem_nil hb).elim⟩
    finality j x t Λ fp _ hf _ := by
      change finality_pair Λ head = some fp at hf
      simp [finality_pair] at hf
    prior j x _ b hb := by
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      rw [cut] at hb
      split_ifs at hb with hx
      · have hpos := hx
        change b ∈ [row.onceKey] at hb
        have hb' : b = row.onceKey := List.mem_singleton.mp hb
        subst b
        exact ⟨3, 0, wire, hpos, ⟨by simp, rfl, by decide⟩, rfl⟩
      · cases hb
    emission j x r a u ha hd := by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := onlyRow j x r a ha
      have hu : row = u := Option.some.inj hd
      subst u
      rfl
    complete j x r a ha := by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := onlyRow j x r a ha
      exact ⟨row, rfl, rfl, 0, rfl, rfl⟩
    wires := by
      constructor
      intro o u hd
      refine ⟨o, rfl, hd, ?_⟩
      cases o with | mk auth payload => cases auth <;> cases hd; rfl
    client := client
    trace := safety_client_trace_obs reads electorate cfg (env (Fin 1)) frozenRun _
      (ordinaryFGExecutionObs_laws (env (Fin 1)) frozenRun) client
    timing_laws := ⟨by decide, by decide, fun _ => by simp, fun _ => rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    schedule := by
      constructor
      · decide
      · decide +kernel
      · decide +kernel
      · intro ev hm
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · intro _ _; exact Finset.mem_univ _
      · intro x t hm
        simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
          reduceCtorEq, or_false, false_or] at hm
        rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩
        · exact ⟨7, rfl⟩
        · exact ⟨8, rfl⟩
      · intro x _ t ht _ hhor _
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        obtain ⟨k, hk⟩ := ht
        change t = (k : Time) * 2 at hk
        change t ≤ 16 at hhor
        rw [hk] at hhor
        have hb : k * 2 ≤ 16 := by exact_mod_cast hhor
        have hbound : k ≤ 8 := by omega
        subst t
        interval_cases k <;> simp
    receipt j y r a ha _ x _ := by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := onlyRow j y r a ha
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      change wire ∈ (V2.D.Run.stateBeforeTime (env (Fin 1)) frozenRun 8 0).2 ∨ _
      exact Or.inl (by decide +kernel)
  }

#print axioms frozen_premises_sat

-- At Q = H in the all-holder setting, the three conclusions are the old conclusions.
private theorem frozen_targets_bridge :
    (∀ x ∈ frozenRun.honest, ∃ j a,
      HonestRowAt reads (env (Fin 1)) frozenRun timing j x 0 a ∧
      RowComplete reads frozenRun history.signer (fun _ => true) x a ∧
      history.heightPair a = .vote 1 genesisRoot false) ∧
    (∀ x ∈ frozenRun.honest, ∃ j q a, q ≤ 1 ∧
      HonestRowAt reads (env (Fin 1)) frozenRun timing j x q a ∧
      RowComplete reads frozenRun history.signer (fun _ => true) x a ∧
      history.heightPair a = .vote 1 genesisRoot false) ∧
    (let honest := Finset.univ.filter
        (fun i : Fin 1 => safetyHolder reads frozenRun i ∈ frozenRun.honest);
      electorate.IsQuorum honest ∧ ∃ rows : Fin 1 → protocol.Object,
        ∀ i ∈ honest, ∃ j q, q ≤ 1 ∧
          HonestRowAt reads (env (Fin 1)) frozenRun timing j
            (safetyHolder reads frozenRun i) q (rows i) ∧
          RowComplete reads frozenRun history.signer (fun _ => true)
            (safetyHolder reads frozenRun i) (rows i) ∧
          history.signer (rows i) = some i ∧
          history.heightPair (rows i) = .vote 1 genesisRoot false ∧
          ∀ x ∈ frozenRun.honest, HeldBefore core (env (Fin 1)) frozenRun Prod.snd x (rows i)
            (max (timing.action q) (env (Fin 1)).t_GST + 2)) := by
  let p := frozen_premises_sat
  obtain ⟨_, _, _, _, _, _, enabled⟩ := mixed_actions_premises_sat
  have hx : safetyHolder reads frozenRun 0 ∈ frozenRun.honest := Finset.mem_univ _
  have hh : high core obs point.reset .genesis := by change (1 : Nat) ≤ 1; decide
  have source (r : Nat) (hr : r ≤ 1) :
      actionSourceFG core (env (Fin 1)) frozenRun timing 0 r = some (some .genesis) := by
    interval_cases r <;> rfl
  obtain ⟨j, a, ha, hc, hp⟩ := high_target_first_row_holder (D := history) (pt := point)
    (fun _ => genesisRoot) p.entry_source p.records p.finality p.prior
    (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace p.emission
    p.complete p.wires p.timing_laws p.schedule enabled 0 hx 0 .genesis (source 0 (by decide))
    hh rfl (by intro j q a h hq; omega)
  refine ⟨?_, ?_⟩
  · intro x _
    have he : x = 0 := Subsingleton.elim _ _
    subst x
    exact ⟨j, a, ha, hc, hp⟩
  obtain ⟨j, q, a, hq, ha, hc, hp⟩ := high_target_row_covered_holder
    (D := history) (pt := point) (fun _ => genesisRoot) p.entry_source p.records p.finality
    p.prior (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace
    p.emission p.complete p.wires p.timing_laws p.schedule enabled
    0 hx 1 .genesis (source 1 (by decide)) hh rfl
  refine ⟨?_, ?_⟩
  · intro x _
    have he : x = 0 := Subsingleton.elim _ _
    subst x
    exact ⟨j, q, a, hq, ha, hc, hp⟩
  have hH : FGHonestSeats reads frozenRun = Finset.univ := by
    ext i
    simp [FGHonestSeats_def, safetyHolder]
  have hQ : electorate.IsQuorum (FGHonestSeats reads frozenRun) := by
    rw [hH]
    change (1 : Nat) ≤ 1
    decide
  exact high_target_quorum_covered_holder (D := history) (pt := point)
    (fun _ => genesisRoot) p.entry_source p.records p.finality p.prior
    (fun _ => rfl) (fun _ => rfl) global_client_premises_sat p.client p.trace p.emission
    p.complete p.wires p.timing_laws p.schedule enabled (FGHonestSeats reads frozenRun)
    (Finset.Subset.refl _) (by rw [hH]; exact ⟨0, Finset.mem_univ _⟩) hQ
    Prod.snd 2 (by decide) p.receipt (by intro x _ t _ _; rfl) 1 .genesis hh
    (by
      intro i _
      have he : i = 0 := Subsingleton.elim _ _
      subst i
      exact source 1 (by decide)) (by decide) (by decide)

#print axioms frozen_targets_bridge
end AvailableChain.FGCompose.Tests.PopulationHighTarget
end

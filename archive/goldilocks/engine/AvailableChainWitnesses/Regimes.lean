module
public import AvailableChainWitnesses.Sanity

@[expose] public section

namespace AvailableChain.Witnesses.Regimes

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

abbrev Wire := Signed Unit 6 Unit

/-- An early object reaches all honest readers. A later faulty object
changes one local view. An honest proposer emits at slot 2. -/
def viewProtocol : ProtocolSpec 6 where
  State := List Wire
  Label := Unit
  Payload := Unit
  init := []
  clock := fun st _ => st
  actTime := fun _ => 0
  duties := fun t => if t = 0 then [()] else []
  duties_spec := (Sanity.alwaysGenesis 6).duties_spec
  duties_nodup := (Sanity.alwaysGenesis 6).duties_nodup
  act := fun _ _ => none
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := (Sanity.alwaysGenesis 6).slotsAt_spec
  slotsAt_nodup := (Sanity.alwaysGenesis 6).slotsAt_nodup
  propose := fun _ s => if s = 2 then some () else none
  gossip := fun _ _ => []
  process := fun st o => o :: st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun st o => st.contains o
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def interface : Interface viewProtocol where
  confirmed := fun _ => .genesis
  stable := fun _ => .genesis
  block := fun _ => some (.node .genesis 2 (nodeRoot (.genesis : Block).root 2 0) 0)
  opening := fun s => s = 2

def sleepyEnv : Env (Fin 6) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun v _ => v ≠ 4

def fullEnv : Env (Fin 6) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 1
  t_GST_nonneg := by decide
  awake := fun v t => if v = 4 then t ≠ 0 else true

def fastEnv : Env (Fin 6) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

def faultObject : Wire := ⟨.seat () 5, ()⟩
def earlyObject : Wire := ⟨.none, ()⟩

def witnessRun : Run (Fin 6) viewProtocol where
  honest := {0, 1, 2, 3, 4}
  horizon := 2
  events :=
    [.tick 0 0, .tick 1 0, .tick 2 0, .tick 3 0, .tick 4 0,
     .deliver 0 earlyObject 0, .deliver 1 earlyObject 0,
     .deliver 2 earlyObject 0, .deliver 3 earlyObject 0,
     .deliver 4 earlyObject 0,
     .tick 0 1, .tick 1 1, .tick 2 1, .tick 3 1, .tick 4 1,
     .tick 0 2, .tick 1 2, .tick 2 2, .tick 3 2, .tick 4 2,
     .deliver 0 faultObject 2]
  seatOf := fun _ => Equiv.refl (Fin 6)
  proposerOf := fun _ => 0

def constants : Constants where
  η := 1
  D_c := 0
  D_s := 0
  D_f := 0
  armingLag := 1
  fastArmingLag := 0
  budget := 1
  recoveryBound := 0
  proposerGap := 1
  θ := 3 / 4
  θrec := 3 / 4
  recoveryFull := true

theorem constantsValid : constants.Valid := by
  constructor <;> norm_num [constants]

theorem distinctViews : Run.readAt viewProtocol witnessRun 2 0 ≠
    Run.readAt viewProtocol witnessRun 2 1 := by
  change [faultObject, earlyObject] ≠ ([earlyObject] : List Wire)
  intro h
  have hn := congrArg List.length h
  simp at hn

theorem hasFault : (faulty witnessRun).Nonempty := by
  refine ⟨5, ?_⟩
  decide

theorem hasSleeper : sleepyEnv.awake 4 1 = false := by decide

theorem earlySleeper : fullEnv.awake 4 0 = false := by decide

private theorem event_mem (i : Nat) (e : Event (Fin 6) viewProtocol.Object)
    (h : witnessRun.events[i]? = some e) : e ∈ witnessRun.events :=
  List.mem_iff_getElem?.2 ⟨i, h⟩

/-- Each honest reader accepts the early object at time zero. -/
private theorem early_accepts (w : Fin 6) (hw : w ∈ witnessRun.honest) :
    ∃ j, Run.acceptsAt viewProtocol witnessRun j w earlyObject 0 := by
  fin_cases w
  · refine ⟨5, ⟨earlyObject, rfl, rfl⟩, ?_, ?_⟩ <;> decide
  · refine ⟨6, ⟨earlyObject, rfl, rfl⟩, ?_, ?_⟩ <;> decide
  · refine ⟨7, ⟨earlyObject, rfl, rfl⟩, ?_, ?_⟩ <;> decide
  · refine ⟨8, ⟨earlyObject, rfl, rfl⟩, ?_, ?_⟩ <;> decide
  · refine ⟨9, ⟨earlyObject, rfl, rfl⟩, ?_, ?_⟩ <;> decide
  · simp [witnessRun] at hw

private theorem accepted_case (i : Nat) (v : Fin 6) (o : Wire) (t : Time)
    (ha : Run.acceptsAt viewProtocol witnessRun i v o t) :
    (t = 0 ∧ o = earlyObject) ∨ (t = 2 ∧ o = faultObject) := by
  rcases ha.1 with ⟨o', hi, hh⟩
  have hm := event_mem i _ hi
  simp [witnessRun] at hm
  rcases hm with h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [viewProtocol] at hh
    subst o
    first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

theorem execution (E : Env (Fin 6)) (hΔ : E.Δ = 1) :
    ExecutionValid viewProtocol E witnessRun := by
  set_option backward.isDefEq.respectTransparency false in
  refine { horizon_nonneg := by decide
           sorted := by decide
           nodup := by simp [witnessRun]
           in_horizon := by decide
           honest_only := by decide
           tick_public := ?_
           tick_total := ?_
           wire := ?_
           deps := ?_
           fresh := ?_
           unforgeable := ?_
           carried := ?_ }
  · intro v t h
    have ht : t = 0 ∨ t = 1 ∨ t = 2 := by
      simp [witnessRun] at h
      aesop
    rcases ht with rfl | rfl | rfl
    · exact ⟨0, by simp [hΔ]⟩
    · exact ⟨1, by simp [hΔ]⟩
    · exact ⟨2, by simp [hΔ]⟩
  · intro v hv t ht h0 h2
    change t ≤ 2 at h2
    have hv' : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by
      simpa [witnessRun] using hv
    rcases hv' with rfl | rfl | rfl | rfl | rfl
    all_goals interval_cases t <;> simp [witnessRun]
  · intro i v o t h; rfl
  · intro i v o t h; rfl
  · intro i v o t h
    rcases List.getElem?_eq_some_iff.mp h with ⟨hb, he⟩
    change i < 21 at hb
    interval_cases i <;> simp [witnessRun] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩
    all_goals decide
  · intro v o t hp u hu holder
    rcases hp with ⟨i, hi⟩
    have hm := event_mem i _ hi
    simp [witnessRun] at hm
    rcases hm with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals simp [Run.holder, witnessRun, earlyObject, faultObject] at holder
    all_goals fin_cases u <;> simp_all [witnessRun]
  · intro v o t hp o' hc u hu holder
    exact False.elim hc

private theorem emission_at_end (E : Env (Fin 6)) (v : Fin 6)
    (o : viewProtocol.Object) (t : Time)
    (h : Run.emits viewProtocol E witnessRun v o t) : t = 2 := by
  rcases h with ⟨i, hi, ho⟩
  have hm := event_mem i _ hi
  simp [witnessRun] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨_, rfl⟩
    simp [Run.emittedAt, viewProtocol, witnessRun] at ho
  all_goals split_ifs at ho
  all_goals first
    | (change o ∈ ([] : List Wire) at ho; exact False.elim (List.not_mem_nil ho))
    | rfl

theorem synchrony (E : Env (Fin 6)) (hΔ : E.Δ = 1) (hGST : E.t_GST ≤ 2) :
    PartialSynchrony viewProtocol E witnessRun := by
  constructor
  · intro v hv o t hem w hw hd _
    have ht := emission_at_end E v o t hem
    simp [witnessRun, hΔ, ht, max_eq_left hGST] at hd
  · intro v hv i o t ha w hw hp hd _
    rcases accepted_case i v o t ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := early_accepts w hw
      refine ⟨0, by decide, ?_, j, hj.1⟩
      have hnonneg := E.t_GST_nonneg
      have hmax : 0 ≤ max (0 : Time) E.t_GST := le_max_left _ _
      change (0 : Time) < max 0 E.t_GST + E.Δ
      rw [hΔ]
      linarith
    · simp [witnessRun, hΔ, max_eq_left hGST] at hd

theorem sleepyMajority (t : Time) : AwakeMajority sleepyEnv witnessRun t := by
  unfold AwakeMajority
  simp [faulty, awakeAt, sleepyEnv, witnessRun]
  decide

theorem etaSleepy (t : Time) : EtaSleepy sleepyEnv constants witnessRun t := by
  have hwindow : awakeInClosed sleepyEnv witnessRun.honest (t - 1) t =
      ({0, 1, 2, 3} : Finset (Fin 6)) := by
    classical
    ext v
    fin_cases v <;> simp [awakeInClosed, sleepyEnv, witnessRun]
    all_goals exact ⟨t, le_add_of_nonneg_right (by decide : (0 : Int) ≤ 1), le_refl t⟩
  have hawake : awakeAt sleepyEnv witnessRun.honest t =
      ({0, 1, 2, 3} : Finset (Fin 6)) := by
    ext v
    fin_cases v <;> simp [awakeAt, sleepyEnv, witnessRun]
  have hfault : faulty witnessRun = ({5} : Finset (Fin 6)) := by decide
  change (3 / 4 : ℚ) *
    ((awakeInClosed sleepyEnv witnessRun.honest (t - 1) t ∪ faulty witnessRun).card : ℚ) <
      ((awakeAt sleepyEnv witnessRun.honest t).card : ℚ)
  rw [hwindow, hawake, hfault]
  have hc1 : ({0, 1, 2, 3, 5} : Finset (Fin 6)).card = 5 := by decide
  have hc2 : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 := by decide
  have hu : ({0, 1, 2, 3} : Finset (Fin 6)) ∪ {5} = {0, 1, 2, 3, 5} := by decide
  rw [hu, hc1, hc2]
  norm_num

theorem belowQuarter : BelowQuarter witnessRun := by
  change 4 * (Finset.univ \ witnessRun.honest).card < 6
  simp [witnessRun]
  decide

/-- Roots are computed from block content, so they are injective on every block. -/
theorem rootInjective (E : Env (Fin 6)) : RootInjective E interface witnessRun :=
  by
    have scope : ∀ B, BlockInRun E interface witnessRun B →
        B = .genesis ∨ B = .node .genesis 2 (nodeRoot genesisRoot 2 0) 0 := by
      intro B hB
      rcases hB with hg | ⟨v, o, t, tip, _, htip, hp⟩
      · exact Or.inl hg
      · have he : tip = .node .genesis 2 (nodeRoot genesisRoot 2 0) 0 :=
          (Option.some.inj htip).symm
        rw [he] at hp
        simpa only [Block.Preceq, Block.preceq, Bool.or_eq_true,
          decide_eq_true_eq, or_comm] using hp
    intro B C hB hC hr
    rcases scope B hB with rfl | rfl <;> rcases scope C hC with rfl | rfl <;>
      first | rfl | simp [Block.root, nodeRoot, genesisRoot] at hr

theorem sleepy : SleepyRegime viewProtocol sleepyEnv interface witnessRun 0 := by
  refine { rootInjective := rootInjective _
           execution := execution sleepyEnv (by decide)
           partialSynchrony := synchrony sleepyEnv (by decide) (by decide)
           gst_zero := by decide
           start_zero := rfl
           participation := ?_ }
  intro t h0 h2
  exact sleepyMajority t

/-- The accepted-relay deadline applies to two distinct honest readers. -/
theorem acceptedRelayNonvacuous :
    Run.acceptsAt viewProtocol witnessRun 5 0 earlyObject 0 ∧
    viewProtocol.processed (Run.stateBefore viewProtocol witnessRun 6 1)
      earlyObject = false ∧
    max (0 : Time) sleepyEnv.t_GST + sleepyEnv.Δ ≤ witnessRun.horizon ∧
    Run.acceptsAt viewProtocol witnessRun 6 1 earlyObject 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨⟨earlyObject, rfl, rfl⟩, by decide, by decide⟩
  · decide
  · decide
  · exact ⟨⟨earlyObject, rfl, rfl⟩, by decide, by decide⟩

theorem stableSleepy : StableSleepyRegime viewProtocol sleepyEnv interface
    constants witnessRun 0 := by
  refine { toSleepyRegime := sleepy, etaSleepy := ?_ }
  intro t h0 h2
  exact etaSleepy t

theorem fast : FastRegime viewProtocol fastEnv interface witnessRun 0 := by
  refine { rootInjective := rootInjective _
           execution := execution fastEnv (by decide)
           partialSynchrony := synchrony fastEnv (by decide) (by decide)
           gst_zero := by decide
           start_zero := rfl
           participation := ?_
           fullParticipation := ?_
           belowQuarter := belowQuarter }
  · intro t h0 h2
    unfold AwakeMajority
    simp [faulty, awakeAt, fastEnv, witnessRun]
    decide
  · intro v hv t h0 h2
    simp [fastEnv]

private theorem healthyPrefix : HealthyPrefixDelivery viewProtocol sleepyEnv witnessRun 1 := by
  constructor
  · intro v hv o t hem w hw hd _
    have ht := emission_at_end sleepyEnv v o t hem
    simp [sleepyEnv, ht] at hd
  · intro v hv i o t ha w hw hp hd _
    rcases accepted_case i v o t ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := early_accepts w hw
      exact ⟨0, by decide, by decide, j, hj.1⟩
    · simp [sleepyEnv] at hd

/-- This execution has honest majority and η-sleepy participation from
time zero, as required by Draft 4.1. -/
theorem outage : OutageRegime viewProtocol sleepyEnv interface constants
    witnessRun 0 1 2 := by
  refine { rootInjective := rootInjective _
           execution := execution sleepyEnv (by decide)
           healthy := healthyPrefix
           interval := by decide
           armed := by decide
           withinBudget := by decide
           sleepyBefore := ?_
           etaSleepyBefore := ?_ }
  · intro t h0 h1; exact sleepyMajority t
  · intro t h0 h1; exact etaSleepy t

/-- Fast arming permits a later protected read in the same healthy run.
The run includes both a fault and an honest sleeper. -/
theorem fastOutage : FastOutageRegime viewProtocol sleepyEnv interface constants
    witnessRun 1 1 2 := by
  refine { toOutageRegime := { outage with
    interval := by decide
    armed := by decide }, highParticipation := ?_ }
  intro t _ _
  change 3 ≤ (awakeAt sleepyEnv witnessRun.honest t).card
  norm_num [awakeAt, sleepyEnv, witnessRun]
  decide

/-- The fast regime does not retain the general lag test. -/
theorem fastOutage_not_general :
    ¬ OutageRegime viewProtocol sleepyEnv interface constants witnessRun 1 1 2 := by
  intro ho
  have := ho.armed
  norm_num [constants] at this

theorem recovery : RecoveryRegime viewProtocol fullEnv interface constants witnessRun := by
  refine { rootInjective := rootInjective _
           execution := execution fullEnv (by decide)
           partialSynchrony := synchrony fullEnv (by decide) (by decide)
           participation := ?_
           full := ?_
           recurrence := ?_
           horizon := by decide }
  · intro t h0 h2
    have ht : t ≠ 0 := by
      change (1 : Int) ≤ t at h0
      linarith
    have hf : (Finset.univ \ ({0, 1, 2, 3, 4} : Finset (Fin 6))).card = 1 := by
      decide
    have hh : ({0, 1, 2, 3, 4} : Finset (Fin 6)).card = 5 := by decide
    norm_num [constants, awakeAt, faulty, fullEnv, witnessRun, ht, hf, hh]
  · intro hfull v hv t h0 h2
    have ht : t ≠ 0 := by
      change (1 : Int) ≤ t at h0
      linarith
    simp [fullEnv, ht]
  · intro t h0 hgap
    change (1 : Int) ≤ t at h0
    have ht : t = 1 := by
      change t + 1 ≤ 2 at hgap
      linarith
    subst t
    refine ⟨2, by decide, by decide, by rfl, ?_⟩
    exact ⟨by decide, by decide⟩

theorem recoveryProposalEmitted : HonestProposalAt fullEnv interface witnessRun 2
    (.node .genesis 2 (nodeRoot (.genesis : Block).root 2 0) 0) := by
  refine ⟨by decide, (), rfl, ?_⟩
  refine ⟨15, rfl, ?_⟩
  change ({ auth := Auth.proposer 2, payload := () } : Wire) ∈
    [({ auth := Auth.proposer 2, payload := () } : Wire)]
  simp

theorem honestDistinctViews :
    0 ∈ witnessRun.honest ∧ 1 ∈ witnessRun.honest ∧
    Run.readAt viewProtocol witnessRun 2 0 ≠ Run.readAt viewProtocol witnessRun 2 1 :=
  ⟨by decide, by decide, distinctViews⟩

theorem sleepyWitness :
    SleepyRegime viewProtocol sleepyEnv interface witnessRun 0 ∧
    (faulty witnessRun).Nonempty ∧ sleepyEnv.awake 4 1 = false ∧
    4 ∈ witnessRun.honest ∧
    Run.readAt viewProtocol witnessRun 2 0 ≠ Run.readAt viewProtocol witnessRun 2 1 :=
  ⟨sleepy, hasFault, hasSleeper, by decide, distinctViews⟩

theorem stableSleepyWitness :
    StableSleepyRegime viewProtocol sleepyEnv interface constants witnessRun 0 ∧
    (faulty witnessRun).Nonempty ∧ sleepyEnv.awake 4 1 = false ∧
    4 ∈ witnessRun.honest ∧
    Run.readAt viewProtocol witnessRun 2 0 ≠ Run.readAt viewProtocol witnessRun 2 1 :=
  ⟨stableSleepy, hasFault, hasSleeper, by decide, distinctViews⟩

theorem fastWitness :
    FastRegime viewProtocol fastEnv interface witnessRun 0 ∧
    (faulty witnessRun).Nonempty ∧ fastEnv.awake 4 0 = true ∧
    4 ∈ witnessRun.honest ∧
    Run.readAt viewProtocol witnessRun 2 0 ≠ Run.readAt viewProtocol witnessRun 2 1 :=
  ⟨fast, hasFault, by decide, by decide, distinctViews⟩

theorem outageWitness :
    OutageRegime viewProtocol sleepyEnv interface constants witnessRun 0 1 2 ∧
    (faulty witnessRun).Nonempty ∧ sleepyEnv.awake 4 1 = false ∧
    4 ∈ witnessRun.honest ∧
    Run.readAt viewProtocol witnessRun 2 0 ≠ Run.readAt viewProtocol witnessRun 2 1 :=
  ⟨outage, hasFault, hasSleeper, by decide, distinctViews⟩

theorem recoveryWitness :
    RecoveryRegime viewProtocol fullEnv interface constants witnessRun ∧
    (faulty witnessRun).Nonempty ∧ fullEnv.awake 4 0 = false ∧
    4 ∈ witnessRun.honest ∧
    Run.readAt viewProtocol witnessRun 2 0 ≠ Run.readAt viewProtocol witnessRun 2 1 :=
  ⟨recovery, hasFault, earlySleeper, by decide, distinctViews⟩

end AvailableChain.Witnesses.Regimes
end

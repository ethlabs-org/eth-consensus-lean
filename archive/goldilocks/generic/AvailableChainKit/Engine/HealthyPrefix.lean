module
public import AvailableChainKit.Engine.RunPrefix

@[expose] public section
namespace AvailableChain.Engine
open AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}

/-- Proof environment for a closed healthy prefix. At the last instant,
all nodes are awake. This cannot change any state or any earlier emission.
The boundary must have no named proposal when transporting root scope. -/
def prefixEnv (E : Env V) (cut : Time) : Env V :=
  { E with t_GST := 0, t_GST_nonneg := le_refl 0
           awake := fun v t => if t = cut then true else E.awake v t }

variable {E : Env V} {rho : Run V P}

theorem prefixEnv_emittedAt (cut : Time) (i : Nat) (v : V) (t : Time)
    (ht : t ≠ cut) :
    Run.emittedAt P (prefixEnv E cut) rho i v t = Run.emittedAt P E rho i v t := by
  simp only [Run.emittedAt, prefixEnv, ite_eq_right ht]

theorem prefixEnv_emits_mono (cut : Time) (v : V) (o : P.Object) (t : Time)
    (h : Run.emits P E rho v o t) : Run.emits P (prefixEnv E cut) rho v o t := by
  obtain ⟨i, he, hm⟩ := h
  refine ⟨i, he, ?_⟩
  by_cases ht : t = cut
  · have awake : E.awake v t = true := by
      by_contra hn
      simp [Run.emittedAt, hn] at hm
    simpa only [Run.emittedAt, prefixEnv, ite_eq_left ht, ↓reduceIte, awake] using hm
  · rwa [prefixEnv_emittedAt cut i v t ht]

theorem prefixEnv_emits_iff (cut : Time) (v : V) (o : P.Object) (t : Time)
    (ht : t ≠ cut) :
    Run.emits P (prefixEnv E cut) rho v o t ↔ Run.emits P E rho v o t := by
  simp only [Run.emits, prefixEnv_emittedAt cut _ v t ht]

omit [DecidableEq V] in
theorem prefixEnv_schedule (hs : ScheduleWellFormed E rho) (cut : Time) :
    ScheduleWellFormed (prefixEnv E cut) rho :=
  ⟨hs.horizon_nonneg, hs.sorted, hs.nodup, hs.in_horizon, hs.honest_only,
    hs.tick_public, hs.tick_total⟩

theorem prefixEnv_execution (hx : ExecutionValid P E rho) (cut : Time) :
    ExecutionValid P (prefixEnv E cut) rho := by
  refine { prefixEnv_schedule hx.toScheduleWellFormed cut,
    hx.toDeliveryWellFormed with unforgeable := ?_, carried := ?_ }
  · intro v o t hp u hu holder
    obtain ⟨t', ht', he⟩ := hx.unforgeable v o t hp u hu holder
    exact ⟨t', ht', prefixEnv_emits_mono cut u o t' he⟩
  · intro v o t hp obj carries u hu holder
    obtain ⟨t', ht', he⟩ := hx.carried v o t hp obj carries u hu holder
    exact ⟨t', ht', prefixEnv_emits_mono cut u obj t' he⟩

/-- Healthy delivery supplies all synchronous deadlines in the closed
prefix. A boundary emission has no deadline inside that prefix. -/
theorem healthyPrefix_partialSynchrony (hx : ExecutionValid P E rho)
    (cut : Time) (healthy : HealthyPrefixDelivery P E rho cut) :
    PartialSynchrony P (prefixEnv E cut) (runPrefix rho cut) := by
  have hs := hx.toScheduleWellFormed
  have deadline (t : Time) (ht : 0 ≤ t) :
      max t (prefixEnv E cut).t_GST + (prefixEnv E cut).Δ = t + E.Δ := by
    exact congrArg (fun x => x + E.Δ) (max_eq_left ht)
  constructor
  · intro v hv o t he w hw bound excl
    obtain ⟨emit, time⟩ := (runPrefix_emits_iff hs cut (prefixEnv E cut) v o t).mp he
    obtain ⟨i, tick, _⟩ := emit
    have nonneg := (hs.in_horizon _ (List.mem_of_getElem? tick)).1
    change 0 ≤ t at nonneg
    rw [deadline t nonneg] at bound excl
    have before : t < cut := lt_of_lt_of_le (lt_add_of_pos_right t E.Δ_pos) bound
    have orig := (prefixEnv_emits_iff cut v o t before.ne).mp
      ((runPrefix_emits_iff hs cut (prefixEnv E cut) v o t).mp he).1
    rw [runPrefix_stateBeforeTime hs cut _ bound] at excl
    obtain ⟨t', lo, hi, j, handles⟩ := healthy.broadcast v hv o t orig w hw bound excl
    exact ⟨t', lo, (deadline t nonneg).symm ▸ hi, j,
      (runPrefix_handlesAt_iff hs cut j w o t').mpr ⟨handles, hi.le.trans bound⟩⟩
  · intro v hv i o t accept w hw fresh bound excl
    obtain ⟨orig, time⟩ := (runPrefix_acceptsAt_iff hs cut i v o t).mp accept
    obtain ⟨obj, delivery, _⟩ := orig.1
    have nonneg := (hs.in_horizon _ (List.mem_of_getElem? delivery)).1
    change 0 ≤ t at nonneg
    rw [deadline t nonneg] at bound excl
    rw [runPrefix_stateBeforeTime hs cut _ bound] at excl
    have hi := (index_lt_read_length_iff hs cut delivery).mpr time
    rw [runPrefix_stateBefore cut (i + 1) (Nat.succ_le_of_lt hi)] at fresh
    obtain ⟨t', lo, hi', j, handles⟩ := healthy.relay v hv i o t orig w hw fresh bound excl
    exact ⟨t', lo, (deadline t nonneg).symm ▸ hi', j,
      (runPrefix_handlesAt_iff hs cut j w o t').mpr ⟨handles, hi'.le.trans bound⟩⟩

theorem healthyPrefix_acceptedRelay (hx : ExecutionValid P E rho)
    (cut : Time) (relay : HealthyAcceptedObjectRelay P E rho cut) :
    AcceptedObjectRelay P (prefixEnv E cut) (runPrefix rho cut) := by
  have hs := hx.toScheduleWellFormed
  intro v hv i o t accept w hw fresh bound
  obtain ⟨orig, time⟩ := (runPrefix_acceptsAt_iff hs cut i v o t).mp accept
  obtain ⟨obj, delivery, _⟩ := orig.1
  have nonneg := (hs.in_horizon _ (List.mem_of_getElem? delivery)).1
  change 0 ≤ t at nonneg
  have deadline : max t (prefixEnv E cut).t_GST + (prefixEnv E cut).Δ = t + E.Δ := by
    exact congrArg (fun x => x + E.Δ) (max_eq_left nonneg)
  rw [deadline] at bound
  have hi := (index_lt_read_length_iff hs cut delivery).mpr time
  rw [runPrefix_stateBefore cut (i + 1) (Nat.succ_le_of_lt hi)] at fresh
  obtain ⟨t', lo, hi', j, accepts⟩ := relay v hv i o t orig w hw fresh bound
  exact ⟨t', lo, deadline.symm ▸ hi', j,
    (runPrefix_acceptsAt_iff hs cut j w o t').mpr ⟨accepts, hi'.le.trans bound⟩⟩

/-- There is no new root scope if boundary emissions contain no named
block. Earlier emissions and every delivered object are unchanged. -/
theorem healthyPrefix_rootInjective (hs : ScheduleWellFormed E rho)
    (I : Interface P) (cut : Time) (roots : RootInjective E I rho)
    (boundary : ∀ v o, Run.emits P (prefixEnv E cut) rho v o cut →
      I.block o.payload = none) :
    RootInjective (prefixEnv E cut) I (runPrefix rho cut) := by
  have scope (b : Block) (hb : BlockInRun (prefixEnv E cut) I (runPrefix rho cut) b) :
      BlockInRun E I rho b := by
    rcases hb with hg | ⟨v, o, t, tip, hp | he, block, ancestor⟩
    · exact Or.inl hg
    · exact Or.inr ⟨v, o, t, tip,
        Or.inl ((runPrefix_processes_iff hs cut v o t).mp hp).1, block, ancestor⟩
    · obtain ⟨orig, time⟩ := (runPrefix_emits_iff hs cut (prefixEnv E cut) v o t).mp he
      have ne : t ≠ cut := by
        rintro rfl
        rw [boundary v o orig] at block
        cases block
      exact Or.inr ⟨v, o, t, tip,
        Or.inr ((prefixEnv_emits_iff cut v o t ne).mp orig), block, ancestor⟩
  exact fun b c hb hc => roots b c (scope b hb) (scope c hc)

/-- A finite healthy prefix is a Sleepy run in a proof environment.
The only boundary side condition is that it emits no named block.
No participation premise at the cutoff is added to the original run. -/
theorem healthyPrefix_sleepy [Fintype V] (hx : ExecutionValid P E rho)
    (I : Interface P) (cut : Time) (positive : 0 < cut) (hh : cut ≤ rho.horizon)
    (roots : RootInjective E I rho)
    (healthy : HealthyPrefixDelivery P E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (boundary : ∀ v o, Run.emits P (prefixEnv E cut) rho v o cut →
      I.block o.payload = none) :
    SleepyRegime P (prefixEnv E cut) I (runPrefix rho cut) 0 := by
  refine ⟨runPrefix_execution (prefixEnv_execution hx cut) cut positive.le hh,
    healthyPrefix_rootInjective hx.toScheduleWellFormed I cut roots boundary,
    healthyPrefix_partialSynchrony hx cut healthy,
    rfl, rfl, ?_⟩
  intro t ht bound
  change t ≤ cut at bound
  by_cases eq : t = cut
  · subst t
    have hzero := majority 0 (le_refl _) positive
    have sub : awakeAt E rho.honest 0 ⊆ rho.honest := Finset.filter_subset _ _
    have count := lt_of_lt_of_le hzero (Finset.card_le_card sub)
    simpa [AwakeMajority, awakeAt, prefixEnv, runPrefix, faulty] using count
  · have before := lt_of_le_of_ne bound eq
    simpa only [AwakeMajority, awakeAt, prefixEnv, runPrefix, ite_eq_right eq, faulty]
      using majority t ht before

end AvailableChain.Engine
end

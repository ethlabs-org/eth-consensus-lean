module
public import AvailableChainKit.Engine.HealthyPrefix
public import AvailableChainSAPC.Proofs.RunClean

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- At a boundary with no proposal duty, extra awake nodes in the proof
environment cannot add a named block to the root-injectivity scope. -/
theorem no_proposal_boundary_block {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (cut : Time)
    (noProposal : ∀ s, proposalTime p s ≠ cut)
    (v : V) (o : Wire p.n) (emit : Run.emits (sapc p) E rho v o cut) :
    (sapcInterface p).block o.payload = none := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨i, _, hm⟩ := emit
  have slots : (sapc p).slotsAt cut = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro s hs
    exact noProposal s (((sapc p).slotsAt_spec s cut).mp hs)
  simp only [Run.emittedAt, slots, List.filterMap_nil, List.append_nil] at hm
  split at hm
  · rcases List.mem_append.mp hm with head | gossip
    · obtain ⟨s, _, payload⟩ := List.mem_filterMap.mp head
      obtain ⟨msg, act, eq⟩ := Option.map_eq_some_iff.mp payload
      change some (Msg.head _) = some msg at act
      have eqMsg := Option.some.inj act
      subst o
      rw [← eqMsg]
      rfl
    · obtain ⟨msg, mem, rfl⟩ := List.mem_map.mp gossip
      change msg ∈ (match (clock p (Run.stateBefore (sapc p) rho i v) cut).bestPC with
        | none => [] | some c => [Msg.pc c]) at mem
      cases hpc : (clock p (Run.stateBefore (sapc p) rho i v) cut).bestPC with
      | none =>
        rw [hpc] at mem
        exact (List.not_mem_nil mem).elim
      | some cert =>
        rw [hpc] at mem
        have eqMsg := List.mem_singleton.mp mem
        subst msg
        rfl
  · simp at hm

/-- Each actual source below the cutoff is the same source in the finite
prefix. This uses raw lease sources and preserves both active modes. -/
theorem cleanRunPath_to_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (cut : Time) (index : Nat)
    (bound : index ≤ (rho.events.filter (fun e => decide (e.time ≤ cut))).length)
    (b : Block) (hb : cleanRunPath p rho index b) :
    cleanRunPath p (runPrefix rho cut) index b := by
  have event (j : Nat) (hj : j < index) (e : Event V (sapc p).Object)
      (he : rho.events[j]? = some e) : (runPrefix rho cut).events[j]? = some e :=
    (runPrefix_event_iff hs cut j e).mpr
      ⟨he, (index_lt_read_length_iff hs cut he).mp (hj.trans_le bound)⟩
  have states (j : Nat) (hj : j ≤ index) :
      Run.stateBefore (sapc p) (runPrefix rho cut) j = Run.stateBefore (sapc p) rho j :=
    runPrefix_stateBefore cut j (hj.trans bound)
  rcases hb with hg | ⟨c, source, hp⟩
  · exact Or.inl hg
  · refine Or.inr ⟨c, ?_, hp⟩
    cases source with
    | genuine j hj v hv r c ht raw =>
      exact CleanRunSource.genuine (rho := runPrefix rho cut) j hj v hv r c
        (event j hj _ ht) ((states j hj.le).symm ▸ raw)
    | timely r c cap source =>
      obtain ⟨v, hv, j, hj, ht, saved⟩ := source
      exact CleanRunSource.timely (rho := runPrefix rho cut) r c cap ⟨v, hv, j, hj, event j hj _ ht,
        (states (j + 1) (Nat.succ_le_of_lt hj)).symm ▸ saved⟩
    | gate j hj v hv r c ht active selected =>
      exact CleanRunSource.gate (rho := runPrefix rho cut) j hj v hv r c (event j hj _ ht)
        ((states j hj.le).symm ▸ active) ((states j hj.le).symm ▸ selected)
    | head j hj v hv r c ht active selected =>
      exact CleanRunSource.head (rho := runPrefix rho cut) j hj v hv r c (event j hj _ ht)
        ((states j hj.le).symm ▸ active) ((states j hj.le).symm ▸ selected)
    | proposal j hj v hv r c ht active selected =>
      exact CleanRunSource.proposal (rho := runPrefix rho cut) j hj v hv r c (event j hj _ ht)
        ((states j hj.le).symm ▸ active) ((states j hj.le).symm ▸ selected)

/-- Transport the already proved chronological induction back to the
original run. Reconstruct authentication in the original environment;
the auxiliary boundary participation is not a run premise. -/
theorem jointClean_of_runPrefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E F : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (cut : Time) (index : Nat)
    (bound : index ≤ (rho.events.filter (fun e => decide (e.time ≤ cut))).length)
    (h : JointCleanInvariant p F (runPrefix rho cut) index) :
    JointCleanInvariant p E rho index := by
  have hs := hx.toScheduleWellFormed
  have event (j : Nat) (hj : j < index) (e : Event V (sapc p).Object)
      (he : rho.events[j]? = some e) : (runPrefix rho cut).events[j]? = some e :=
    (runPrefix_event_iff hs cut j e).mpr
      ⟨he, (index_lt_read_length_iff hs cut he).mp (hj.trans_le bound)⟩
  have states (j : Nat) (hj : j ≤ index) :
      Run.stateBefore (sapc p) (runPrefix rho cut) j = Run.stateBefore (sapc p) rho j :=
    runPrefix_stateBefore cut j (hj.trans bound)
  constructor
  · apply cleanPathFacts_of_chain_and_transfer p E rho hx ha index
    · exact ⟨Or.inl rfl, cleanRunPath_closed p rho index,
        fun a b ha hb => h.facts.chain.comparable a b
          (cleanRunPath_to_prefix p E rho hs cut index bound a ha)
          (cleanRunPath_to_prefix p E rho hs cut index bound b hb)⟩
    · intro j hj v hv r b ht raw k hk w hw s hrs tick
      have result := h.facts.transferred j hj v hv r b (event j hj _ ht)
        ((states j hj.le).symm ▸ raw) k hk w hw s hrs (event k hk _ tick)
      rwa [states k hk.le] at result
  · intro j hj k hk v hv w hw r s b c hrs htj htk rawj rawk
    exact h.ordered j hj k hk v hv w hw r s b c hrs (event j hj _ htj)
      (event k hk _ htk) ((states j hj.le).symm ▸ rawj) ((states k hk.le).symm ▸ rawk)

/-- The uncapped clean induction holds through a healthy cutoff with no
proposal duty, including all events at the cutoff. No suffix delivery or
participation is needed. In particular the cutoff may equal a gate. -/
theorem healthy_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (positive : 0 < cut) (hh : cut ≤ rho.horizon)
    (healthy : HealthyPrefixDelivery (sapc p) E rho cut)
    (_relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (noProposal : ∀ s, proposalTime p s ≠ cut)
    (index : Nat)
    (bound : index ≤ (rho.events.filter (fun e => decide (e.time ≤ cut))).length) :
    JointCleanInvariant p E rho index := by
  have sleepy := healthyPrefix_sleepy hx (sapcInterface p).toInterface cut positive hh
    roots healthy majority (no_proposal_boundary_block p (prefixEnv E cut) rho cut noProposal)
  have invariant := clean_run_invariant p (prefixEnv E cut) (runPrefix rho cut) hΔ 0 sleepy
    index (by rw [runPrefix_events hx.toScheduleWellFormed]; exact bound)
  exact jointClean_of_runPrefix p E (prefixEnv E cut) rho hx
    (sleepy_quorum_above_faults p (prefixEnv E cut) (runPrefix rho cut) 0 sleepy)
    cut index bound invariant

/-- An early cutoff is between proposal duties. It is also the preceding
label's gate when the label is positive. -/
theorem earlyTime_ne_proposalTime (p : Params) (r s : Slot) :
    proposalTime p s ≠ earlyTime p r := by
  intro eq
  change 4 * p.Δ * (s : Time) = 4 * p.Δ * (r : Time) + 2 * p.Δ at eq
  by_cases h : s ≤ r
  · have hc : (s : Time) ≤ r := by exact_mod_cast h
    nlinarith [p.deltaPos]
  · have hc : (r : Time) + 1 ≤ s := by exact_mod_cast Nat.lt_of_not_ge h
    nlinarith [p.deltaPos]

/-- The proof-only Sleepy prefix at the last healthy early cutoff. -/
theorem healthy_sleepy_through_early {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (healthy : HealthyPrefixDelivery (sapc p) E rho cut)
    (_relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    : SleepyRegime (sapc p) (prefixEnv E (earlyTime p r))
      (sapcInterface p).toInterface (runPrefix rho (earlyTime p r)) 0 := by
  have positive : 0 < earlyTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have net : HealthyPrefixDelivery (sapc p) E rho (earlyTime p r) := by
    constructor
    · intro v hv o t he w hw deadline
      exact healthy.broadcast v hv o t he w hw (deadline.trans hearly)
    · intro v hv i o t ha w hw fresh deadline
      exact healthy.relay v hv i o t ha w hw fresh (deadline.trans hearly)
  exact healthyPrefix_sleepy hx (sapcInterface p).toInterface (earlyTime p r)
    positive hh roots net (fun t ht hlt => majority t ht (hlt.trans_le hearly))
    (no_proposal_boundary_block p (prefixEnv E (earlyTime p r)) rho (earlyTime p r)
      (earlyTime_ne_proposalTime p r))

/-- The exact healthy-prefix invariant needed by the pending gate.
Equality of the early cutoff and the outage boundary is permitted. -/
theorem healthy_run_invariant_through_early {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (healthy : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (index : Nat)
    (bound : index ≤ (rho.events.filter (fun e => decide (e.time ≤ earlyTime p r))).length) :
    JointCleanInvariant p E rho index := by
  have sleepy := healthy_sleepy_through_early p E rho hx roots cut healthy relay
    majority r hearly hh
  have invariant := clean_run_invariant p (prefixEnv E (earlyTime p r))
    (runPrefix rho (earlyTime p r)) hΔ 0 sleepy index
    (by rw [runPrefix_events hx.toScheduleWellFormed]; exact bound)
  exact jointClean_of_runPrefix p E (prefixEnv E (earlyTime p r)) rho hx
    (sleepy_quorum_above_faults p (prefixEnv E (earlyTime p r))
      (runPrefix rho (earlyTime p r)) 0 sleepy) (earlyTime p r) index bound invariant

end AvailableChain.SAPC
end

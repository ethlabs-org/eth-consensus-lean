module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable

public section

/-! # Non-framing through an honest engine tick

Retention applies only to the signing history through this observation, not to a
static honest-origin invariant reconstructed across later compromises.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every labelled cut before an event's end has time at most that event's time. -/
theorem simTraceAt_time_le_event (hv : rho.ExecutionValid) {i k : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocksWith S)) E).Object}
    (he : rho.events[i]? = some ev) (hk : k < cutMap S rho hn (i + 1))
    (hl : (simTraceAt S rho hn).label k ≠ none) :
    (simTraceAt S rho hn).time k ≤ ev.time := by
  rw [simTraceAt_eq] at hl ⊢
  obtain ⟨r, j, e, _, hj, hstart, _, _, _, ht, _⟩ := simTrace_cut S rho hn hl
  have hji : j ≤ i := by
    by_contra h
    have hm := cutMap_mono S rho hn (show i + 1 ≤ j by omega)
    omega
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hlaws := (Model.sysOf_laws schema (compiled (goldilocksWith S)) V).trace ⟨E, rho⟩ hv
  have hm := hlaws.cutTime_mono (j + 1) (i + 1) (by omega)
    (show i + 1 ≤ rho.events.length by omega)
  change rho.cutTime (j + 1) ≤ rho.cutTime (i + 1) at hm
  simpa only [Model.Run.cutTime, hj, he, ht] using hm

/-- The signings through a tick of its honest node cannot conflict. -/
theorem simTraceAt_signings_nonFraming_before (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t))
    {k k' : Nat} {a b : FG.Att (Fintype.card V)}
    (hk : k < cutMap S rho hn (i + 1)) (hk' : k' < cutMap S rho hn (i + 1))
    (ha : (simTraceAt S rho hn).SignAt (rho.ownKey v) k a)
    (hb : (simTraceAt S rho hn).SignAt (rho.ownKey v) k' b) : ¬ FG.slashable a b := by
  have ht := hv.in_horizon _ (List.mem_of_getElem? he)
  have hh := honest_ownKey_at S rho (hv.honest_only _ (List.mem_of_getElem? he)) ht.2
  have hr := (simTraceAt_goldilocksRun S rho hn hv).upTo ht.1
  have ha' := (RunTrace.upTo_signAt (simTraceAt S rho hn) (d := t)).mpr
    ⟨simTraceAt_time_le_event S rho hn hv he hk (by obtain ⟨_, _, h⟩ := ha; rw [h]; simp), ha⟩
  have hb' := (RunTrace.upTo_signAt (simTraceAt S rho hn) (d := t)).mpr
    ⟨simTraceAt_time_le_event S rho hn hv he hk' (by obtain ⟨_, _, h⟩ := hb; rw [h]; simp), hb⟩
  exact Regimes.goldilocksRun_nonFraming hr hh ha' hb'

end Consensus.Goldilocks.Simulation

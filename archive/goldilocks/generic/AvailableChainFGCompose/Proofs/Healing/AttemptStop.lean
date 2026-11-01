module
public import AvailableChainFGCompose.Statements.Attempt

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (A : FGAttemptGateReads Prot) (pair : Wire → NamedHeightPair) (Jst : Time)

/-- Blueprint 21 H.10:1428–1429, 1494–1498. An earlier event stops the attempt.
No service past that event is required. -/
theorem healing_attempt_ends_of_event {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V Prot.Object} {j : Nat}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget)
    (heff : EffectiveEvent R E rho O j) : AttemptEndsBy R S E rho O T pair k budget :=
  ⟨ev, hstart, j, ev', hj, hnext, htime, Or.inl heff⟩

/-- One later matching honest row completes the first-row task. -/
theorem healing_attempt_ends_of_row {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V Prot.Object} {j : Nat} {y : V} {r : Nat}
    {a : Wire} {e : BlockId}
    (hstart : rho.events[k.start]? = some ev) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget)
    (htask : k.task = .firstRow) (hrow : HonestRowAt S E rho T j y r a)
    (hnamed : namedEntry (pair a) = some (k.frontier, e)) :
    AttemptEndsBy R S E rho O T pair k budget :=
  ⟨ev, hstart, j, ev', hj, hnext, htime, Or.inr (Or.inr ⟨htask, y, r, a, e, hrow, hnamed⟩)⟩

theorem healing_attempt_ends_mono {k : AttemptKey} {budget budget' : Time}
    (hends : AttemptEndsBy R S E rho O T pair k budget) (hbudget : budget ≤ budget') :
    AttemptEndsBy R S E rho O T pair k budget' := by
  obtain ⟨ev, hstart, j, ev', hj, hnext, ht, hend⟩ := hends
  exact ⟨ev, hstart, j, ev', hj, hnext,
    ht.trans (add_le_add le_rfl hbudget), hend⟩

/-- A failed stopped-task bound excludes every effective event within its budget. -/
theorem healing_attempt_no_event {k : AttemptKey} {budget : Time}
    {ev ev' : V2.Event V Prot.Object} {j : Nat}
    (hstart : rho.events[k.start]? = some ev)
    (hstop : ¬ AttemptEndsBy R S E rho O T pair k budget) (hj : k.start < j)
    (hnext : rho.events[j]? = some ev') (htime : ev'.time ≤ ev.time + budget) :
    ¬ EffectiveEvent R E rho O j := fun heff =>
  hstop (healing_attempt_ends_of_event R S E rho O T pair hstart hj hnext htime heff)

/-- The second frozen start arm is required when the start event is not effective.
This extracts that arm; it makes no settlement claim. -/
theorem healing_attempt_inclusive_start {k : AttemptKey}
    (hvalid : AttemptValid R S E rho O T I A pair Jst k)
    (hne : ¬ EffectiveEvent R E rho O k.start) :
    ∃ ev rG, rho.events[k.start]? = some ev ∧ Jst ≤ ev.time ∧
      Jst ≤ T.action rG ∧
      (∀ r, Jst ≤ T.action r → rG ≤ r) ∧
      ev.time = T.action (rG + 2) ∧
      timeIdx rho (T.action (rG + 2)) = k.start + 1 := by
  obtain ⟨ev, hi, hgst, hstart, _⟩ := hvalid
  rcases hstart with heff | ⟨rG, hG, hmin, ht, hcut⟩
  · exact (hne heff).elim
  · exact ⟨ev, rG, hi, hgst, hG, hmin, ht, hcut⟩

end AvailableChain.FGCompose
end

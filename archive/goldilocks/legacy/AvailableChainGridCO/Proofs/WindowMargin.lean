module
public import AvailableChainGridCO.Proofs.Handling
public import AvailableChainKit.Engine.EngineClock

@[expose] public section

/-! WindowMargin (design §2): the relay lemmas take the premise that the
reader does not exclude the relayed object up to the lemma's cutoff. This
module proves that premise for each caller. A label-`r` HEAD is excluded
before `proposalTime p (r + 2)` only for equivocation, and every caller's
cutoff is at most `gateTime p r`, a margin of 2Δ. If `excludes` ever
covers more objects, only this module changes, not the relay lemmas. -/

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The instance field is the model's `excludes`. -/
theorem gridCO_excludes (p : Params) (st : State p.n) (o : Wire p.n) :
    (gridCO p).excludes st o = excludes p st o := rfl

/-- A strict time read has a zero clock or a clock before the read. -/
theorem time_read_now_lt {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (u : Time) (w : V) :
    (Run.stateBeforeTime (gridCO p) rho u w).now = 0 ∨
      (Run.stateBeforeTime (gridCO p) rho u w).now < u := by
  rw [stateBeforeTime_eq_readAt_pred, readAt_eq_stateBefore hs]
  rcases AvailableChain.Engine.stateBefore_now_source (P := gridCO p)
      ⟨State.now, rfl, clock_now p, process_now p⟩ rho _ w with hz | ⟨j, hj, he⟩
  · exact Or.inl hz
  · exact Or.inr (Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (u - 1) he).mp hj))

/-- A strict read at or before `proposalTime p (r + 2)` names a label of at
most `r + 1`. -/
theorem time_read_label_le {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (w : V) (u : Time)
    (r : Slot) (hu : u ≤ proposalTime p (r + 2)) :
    ((Run.stateBeforeTime (gridCO p) rho u w).now / (4 * p.Δ)).toNat ≤ r + 1 := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hq : (Run.stateBeforeTime (gridCO p) rho u w).now / (4 * p.Δ) < (r : Int) + 1 + 1 := by
    rcases time_read_now_lt p E rho hs u w with hz | hlt
    · rw [hz, Int.zero_ediv]
      have := Int.natCast_nonneg r
      linarith
    · apply (Int.ediv_lt_iff_lt_mul hd).mpr
      have h := hlt.trans_le hu
      simp only [proposalTime] at h
      push_cast at h
      linarith
  apply Int.toNat_le.mpr
  push_cast
  exact Int.lt_add_one_iff.mp hq

/-- A label-`r` HEAD whose seat does not equivocate in the reader's votes is
not excluded at any time before `proposalTime p (r + 2)`. -/
theorem head_not_excluded_before {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (w : V) (u : Time)
    (r : Slot) (i : Fin p.n) (x : Block) (hu : u ≤ proposalTime p (r + 2))
    (heq : equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho u w) r) i = false) :
    (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) ⟨.seat r i, .head x⟩ =
      false := by
  set_option backward.isDefEq.respectTransparency false in
  have hl := time_read_label_le p E rho hs w u r hu
  rw [gridCO_excludes]
  simp [excludes, heq, Nat.not_lt.mpr hl]

/-- A label-`r` HEAD that the reader excludes before `proposalTime p (r + 2)`
is excluded for equivocation: the reader already holds two label-`r` HEADs
of that seat. -/
theorem head_excluded_before_equivocates {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (w : V)
    (u : Time) (r : Slot) (i : Fin p.n) (x : Block) (hu : u ≤ proposalTime p (r + 2))
    (hx : (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w)
        ⟨.seat r i, .head x⟩ = true) :
    equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho u w) r) i = true := by
  cases heq : equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho u w) r) i with
  | true => rfl
  | false =>
      rw [head_not_excluded_before p E rho hs w u r i x hu heq] at hx
      contradiction

/-- Today every proposal; the one place to change if `excludes` ever covers
proposals (I9, non-minimal variant). -/
theorem proposal_not_excluded {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (w : V) (o : Wire p.n) (B : Block)
    (raw support : List (HeadWire p.n)) (hp : o.payload = .proposal B raw support) :
    ∀ u, (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) o = false := by
  set_option backward.isDefEq.respectTransparency false in
  intro u
  obtain ⟨auth, payload⟩ := o
  subst hp
  rw [gridCO_excludes]
  cases auth <;> rfl

/-- Caller `synchronous_honest_head_stored_early`: an honest HEAD is never
excluded before `proposalTime p (r + 2)`. -/
theorem honest_head_not_excluded_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho) (w : V)
    (r : Slot) (i : Fin p.n) (x : Block) (hh : rho.seatOf r i ∈ rho.honest)
    (cut : Time) (hc : cut ≤ proposalTime p (r + 2)) :
    ∀ u, u ≤ cut →
      (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) ⟨.seat r i, .head x⟩ =
        false := by
  intro u hu
  apply head_not_excluded_before p E rho hx.toScheduleWellFormed w u r i x (hu.trans hc)
  rw [stateBeforeTime_eq_readAt_pred, readAt_eq_stateBefore hx.toScheduleWellFormed]
  exact honest_not_equivocating_at_event p E rho hx _ w r i hh

/-- Callers `synchronous_accepted_head_before` and
`stored_head_before_ready_proposal` relay a label-`r` HEAD of any seat. Either
the reader does not exclude it up to `cut`, or at some read up to `cut` the
reader already holds equivocation evidence for its seat. -/
theorem head_not_excluded_or_equivocates {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (w : V)
    (r : Slot) (i : Fin p.n) (x : Block) (cut : Time)
    (hc : cut ≤ proposalTime p (r + 2)) :
    (∀ u, u ≤ cut →
      (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) ⟨.seat r i, .head x⟩ =
        false) ∨
      ∃ u, u ≤ cut ∧
        equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho u w) r) i = true := by
  by_cases h : ∀ u, u ≤ cut →
      (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u w) ⟨.seat r i, .head x⟩ = false
  · exact Or.inl h
  · push Not at h
    obtain ⟨u, hu, hne⟩ := h
    exact Or.inr ⟨u, hu, head_excluded_before_equivocates p E rho hs w u r i x (hu.trans hc)
      (by simpa using hne)⟩

end AvailableChain.GridCO
end

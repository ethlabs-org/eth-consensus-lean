module
public import AvailableChainKitV2.DutyStable
public import AvailableChainGeneric.Statements.V2.Duty.Regimes

public section

namespace AvailableChain.Gen.V2.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- Source: AvailableChainGeneric/Proofs/V2/Induction.lean:16.
theorem invariant_triple (Q : P.State → Prop)
    (hinit : Q P.init)
    (hclock : ∀ st t, Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t))
    (E : Generic.Env V) (rho : D.Run V P) (j : Nat) (v : V) :
    Q (D.Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q (Nat.zero_le j) v ?_ ?_
  · intro k e _ _ _ hv hk
    cases e with
    | restart u t =>
        change u = v at hv
        subst u
        change Q (Function.update (D.Run.stateBefore E rho k) v _ v)
        rw [Function.update_self]
        exact hrestore _ t hk
    | tick u t =>
        change u = v at hv
        subst u
        change Q (Function.update (D.Run.stateBefore E rho k) v _ v)
        rw [Function.update_self]
        exact tick_preserve E rho Q hrecord (hclock _ t hk)
    | deliver u o t =>
        change u = v at hv
        subst u
        change Q (Function.update (D.Run.stateBefore E rho k) v _ v)
        rw [Function.update_self]
        exact hprocess _ o hk
  · change Q P.init
    exact hinit

-- Source: AvailableChainGeneric/Proofs/V2/Induction.lean:52.
theorem invariant_clock_free {β : Type} (proj : P.State → β) (Q : β → Prop)
    (hinit : Q (proj P.init))
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, Q (proj st) → Q (proj (P.process st o)))
    (hrecord : ∀ st o, Q (proj st) → Q (proj (P.recordOwn st o)))
    (hrestore : ∀ st t, Q (proj st) → Q (proj (P.restore (P.durable st) t)))
    (E : Generic.Env V) (rho : D.Run V P) (j : Nat) (v : V) :
    Q (proj (D.Run.stateBefore E rho j v)) := by
  refine stateBefore_step_induction E rho (fun st => Q (proj st))
    (Nat.zero_le j) v ?_ ?_
  · intro k e _ _ _ hv hk
    cases e with
    | restart u t =>
        change u = v at hv
        subst u
        change Q (proj (Function.update (D.Run.stateBefore E rho k) v _ v))
        rw [Function.update_self]
        exact hrestore _ t hk
    | tick u t =>
        change u = v at hv
        subst u
        change Q (proj (Function.update (D.Run.stateBefore E rho k) v _ v))
        rw [Function.update_self]
        apply tick_preserve E rho (fun st => Q (proj st)) hrecord
        rwa [hclock]
    | deliver u o t =>
        change u = v at hv
        subst u
        change Q (proj (Function.update (D.Run.stateBefore E rho k) v _ v))
        rw [Function.update_self]
        exact hprocess _ o hk
  · change Q (proj P.init)
    exact hinit

-- Source: AvailableChainGeneric/Proofs/V2/Induction.lean:90.
theorem interval_induction_all (E : Generic.Env V) (rho : D.Run V P)
    (Q : V → P.State → Prop) {i j : Nat}
    (hi : ∀ v, Q v (D.Run.stateBefore E rho i v))
    (hstep : ∀ v k e, i ≤ k → k < j → rho.events[k]? = some e → e.node = v →
      Q v (D.Run.stateBefore E rho k v) →
        Q v (D.World.step E rho (D.Run.stateBefore E rho k) e v)) :
    ∀ k, i ≤ k → k ≤ j → ∀ v, Q v (D.Run.stateBefore E rho k v) := by
  intro k hik hkj v
  exact stateBefore_step_induction E rho (Q v) hik v
    (fun n e hin hnk => hstep v n e hin (Nat.lt_of_lt_of_le hnk hkj)) (hi v)

-- Source: AvailableChainGeneric/Proofs/V2/Induction.lean:106.
theorem write_once_along_run {α : Type} (field : P.State → Option α)
    (E : Generic.Env V) (rho : D.Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hstep : ∀ k e, i ≤ k → k < j → rho.events[k]? = some e → e.node = v →
      ∀ a, field (D.Run.stateBefore E rho k v) = some a →
        field (D.World.step E rho (D.Run.stateBefore E rho k) e v) = some a)
    (a : α) (hi : field (D.Run.stateBefore E rho i v) = some a) :
    field (D.Run.stateBefore E rho j v) = some a := by
  exact stateBefore_step_induction E rho (fun st => field st = some a) hij v
    (fun k e hik hkj he hv => hstep k e hik hkj he hv a) hi

-- Source: AvailableChainGeneric/Proofs/V2/Induction.lean:119.
theorem kept_from_seed (E : Generic.Env V) (rho : D.Run V P)
    (Q : V → P.State → Prop) {start stop : Nat}
    (seed : SeedAt E rho start Q)
    (step : ∀ v k e, start ≤ k → k < stop → rho.events[k]? = some e → e.node = v →
      Q v (D.Run.stateBefore E rho k v) →
        Q v (D.World.step E rho (D.Run.stateBefore E rho k) e v)) :
    ∀ j, start ≤ j → j ≤ stop → SeedAt E rho j Q :=
  fun j h1 h2 v => interval_induction_all E rho Q seed step j h1 h2 v

end AvailableChain.Gen.V2.Duty

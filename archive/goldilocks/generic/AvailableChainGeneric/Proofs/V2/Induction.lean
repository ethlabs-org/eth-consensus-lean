module
public import AvailableChainKitV2.Stable
public import AvailableChainGeneric.Statements.V2.Regimes

public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- Preservation by the three hooks and by restore gives an invariant of
every run. The clock premise holds for every time, with no time-order guard.
Source: GLY:847–854; KitV2/Stable.lean:49–52,69–96. Consumer: T7.5. -/
theorem invariant_triple (Q : P.State → Prop)
    (hinit : Q P.init)
    (hclock : ∀ st t, Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t))
    (E : Generic.Env V) (rho : Run V P) (j : Nat) (v : V) :
    Q (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q (Nat.zero_le j) v ?_ ?_
  · intro k e _ _ _ hv hk
    cases e with
    | restart u t =>
        change u = v at hv
        subst u
        change Q (Function.update (Run.stateBefore E rho k) v _ v)
        rw [Function.update_self]
        exact hrestore _ t hk
    | tick u t =>
        change u = v at hv
        subst u
        change Q (Function.update (Run.stateBefore E rho k) v _ v)
        rw [Function.update_self]
        exact tick_preserve E rho Q hrecord (hclock _ t hk)
    | deliver u o t =>
        change u = v at hv
        subst u
        change Q (Function.update (Run.stateBefore E rho k) v _ v)
        rw [Function.update_self]
        exact hprocess _ o hk
  · change Q P.init
    exact hinit

/-- A predicate of a projection that the clock leaves unchanged is an
invariant when process, recordOwn and restore preserve it.
Source: GLY:847–854. Designed projection form; the clock equation supplies
the clock case of the same core. Consumers: G08 field invariants (T7.9/F1/F2). -/
theorem invariant_clock_free {β : Type} (proj : P.State → β) (Q : β → Prop)
    (hinit : Q (proj P.init))
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, Q (proj st) → Q (proj (P.process st o)))
    (hrecord : ∀ st o, Q (proj st) → Q (proj (P.recordOwn st o)))
    (hrestore : ∀ st t, Q (proj st) → Q (proj (P.restore (P.durable st) t)))
    (E : Generic.Env V) (rho : Run V P) (j : Nat) (v : V) :
    Q (proj (Run.stateBefore E rho j v)) := by
  refine stateBefore_step_induction E rho (fun st => Q (proj st))
    (Nat.zero_le j) v ?_ ?_
  · intro k e _ _ _ hv hk
    cases e with
    | restart u t =>
        change u = v at hv
        subst u
        change Q (proj (Function.update (Run.stateBefore E rho k) v _ v))
        rw [Function.update_self]
        exact hrestore _ t hk
    | tick u t =>
        change u = v at hv
        subst u
        change Q (proj (Function.update (Run.stateBefore E rho k) v _ v))
        rw [Function.update_self]
        apply tick_preserve E rho (fun st => Q (proj st)) hrecord
        rwa [hclock]
    | deliver u o t =>
        change u = v at hv
        subst u
        change Q (proj (Function.update (Run.stateBefore E rho k) v _ v))
        rw [Function.update_self]
        exact hprocess _ o hk
  · change Q (proj P.init)
    exact hinit

/-- Node-dependent state predicates hold at every index in a closed
interval if each local event preserves them on the half-open interval.
Source: GLY:860–863 (designed statement), KitV2/Stable.lean:49–52.
Consumers: G08 interval invariants in F1, F2 and F5. -/
theorem interval_induction_all (E : Generic.Env V) (rho : Run V P)
    (Q : V → P.State → Prop) {i j : Nat}
    (hi : ∀ v, Q v (Run.stateBefore E rho i v))
    (hstep : ∀ v k e, i ≤ k → k < j → rho.events[k]? = some e → e.node = v →
      Q v (Run.stateBefore E rho k v) →
        Q v (World.step E rho (Run.stateBefore E rho k) e v)) :
    ∀ k, i ≤ k → k ≤ j → ∀ v, Q v (Run.stateBefore E rho k v) := by
  intro k hik hkj v
  exact stateBefore_step_induction E rho (Q v) hik v
    (fun n e hin hnk => hstep v n e hin (Nat.lt_of_lt_of_le hnk hkj)) (hi v)

/-- A field that cannot change once it is set keeps its value along the
run. The local-event premise includes restarts; a volatile field needs a
restart-free interval to supply that premise.
Source: GLY:860–863 (designed statement), KitV2/Stable.lean:49–52.
Consumers: G08 saved-value facts in F1, F2 and F5. -/
theorem write_once_along_run {α : Type} (field : P.State → Option α)
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hstep : ∀ k e, i ≤ k → k < j → rho.events[k]? = some e → e.node = v →
      ∀ a, field (Run.stateBefore E rho k v) = some a →
        field (World.step E rho (Run.stateBefore E rho k) e v) = some a)
    (a : α) (hi : field (Run.stateBefore E rho i v) = some a) :
    field (Run.stateBefore E rho j v) = some a := by
  exact stateBefore_step_induction E rho (fun st => field st = some a) hij v
    (fun k e hik hkj he hv => hstep k e hik hkj he hv a) hi

/-- A seed at `start` persists to every index up to `stop` if each local event
in `[start, stop)` preserves it. Signature from fgsa-lean (ruling D17); one
application of `interval_induction_all`. Sources: GLY:860–863; D09 row. -/
theorem kept_from_seed (E : Generic.Env V) (rho : Run V P)
    (Q : V → P.State → Prop) {start stop : Nat}
    (seed : SeedAt E rho start Q)
    (step : ∀ v k e, start ≤ k → k < stop → rho.events[k]? = some e → e.node = v →
      Q v (Run.stateBefore E rho k v) →
        Q v (World.step E rho (Run.stateBefore E rho k) e v)) :
    ∀ j, start ≤ j → j ≤ stop → SeedAt E rho j Q :=
  fun j h1 h2 v => interval_induction_all E rho Q seed step j h1 h2 v

end AvailableChain.Gen.V2

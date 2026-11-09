module
public import ConsensusLean.Lemmas.Model.Canonical.InjectFilter

@[expose] public section

/-! # The filtered injection schedule: statements and axioms

The characterising equations added to `Lemmas/Model/Canonical/Inject` (`duePool_eq`,
`injectDeliveries_eq`, `injectStages_zero`) and the serve-all equalities of
`Lemmas/Model/Canonical/InjectFilter` (with a filter that serves everything, the filtered schedule
is `Run.injectEvents`) restated as named theorems, with their axioms pinned. -/

namespace Consensus.Model.InjectFilterTest

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V} (rho : Run F E) (delay : Event V (protoOf F E).Object → Time)
    (inj : Time → V → List (protoOf F E).Object)

/-- The due pool, unfolded. -/
theorem duePool_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.duePool delay es t = (by
      classical
      exact ((List.range es.length).flatMap fun j =>
        if ∃ e, es[j]? = some e ∧ e.time + delay e ≤ t then (rho.withEvents es).releasesAt j
        else []).dedup) :=
  Run.duePool_eq rho delay es t

/-- The injection deliveries, unfolded. -/
theorem injectDeliveries_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injectDeliveries delay inj es t = (by
      classical
      exact (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).flatMap
        (fun v => (inj t v ++ rho.duePool delay es t).dedup.map (fun o => .deliver v o t))) :=
  Run.injectDeliveries_eq rho delay inj es t

/-- No stage before time `0`. -/
theorem injectStages_zero : rho.injectStages delay inj 0 = [] :=
  Run.injectStages_zero rho delay inj

variable {delay inj}
  {pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool}

/-- Serving everything, the filtered deliveries are the unfiltered ones. -/
theorem injfDeliveries_eq_injectDeliveries (hpol : ∀ es v o t, pol es v o t = true)
    (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injfDeliveries delay inj pol es t = rho.injectDeliveries delay inj es t :=
  Run.injfDeliveries_eq_injectDeliveries rho hpol es t

/-- Serving everything, the filtered schedule is `Run.injectEvents`. -/
theorem injfEvents_eq_injectEvents (hpol : ∀ es v o t, pol es v o t = true) :
    rho.injfEvents delay inj pol = rho.injectEvents delay inj :=
  Run.injfEvents_eq_injectEvents rho hpol

/-- Serving everything, the filtered run is `Run.injectRun`. -/
theorem injfRun_eq_injectRun (hpol : ∀ es v o t, pol es v o t = true) :
    rho.injfRun delay inj pol = rho.injectRun delay inj :=
  Run.injfRun_eq_injectRun rho hpol

end Consensus.Model.InjectFilterTest

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Model.InjectFilterTest.duePool_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.InjectFilterTest.duePool_eq

/-- info: 'Consensus.Model.InjectFilterTest.injectDeliveries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.InjectFilterTest.injectDeliveries_eq

/-- info: 'Consensus.Model.InjectFilterTest.injectStages_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.InjectFilterTest.injectStages_zero

/--
info: 'Consensus.Model.InjectFilterTest.injfDeliveries_eq_injectDeliveries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Model.InjectFilterTest.injfDeliveries_eq_injectDeliveries

/-- info: 'Consensus.Model.InjectFilterTest.injfEvents_eq_injectEvents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.InjectFilterTest.injfEvents_eq_injectEvents

/-- info: 'Consensus.Model.InjectFilterTest.injfRun_eq_injectRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.InjectFilterTest.injfRun_eq_injectRun

end

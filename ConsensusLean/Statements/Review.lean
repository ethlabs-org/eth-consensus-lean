module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Spec.Shape.OnRuns
public import ConsensusLean.Spec.Shape.Active
public import ConsensusLean.Spec.Model.Served

@[expose] public section

/-! # The review statements

The statements a reviewer reads, as `Prop` definitions; no theorem lives here. Each body is
exactly the type of an existing theorem (binder for binder), and
`Solution.lean` proves each one by that theorem. `ConsensusLeanTest/ReviewAxioms.lean`
checks that each definition's body is alpha-equal to its theorem's type, and the comparator
(`comparator.json`, CI) checks the proofs against these statements built from Spec alone.

`ObligationsSufficient` is *the* review statement and `ObligationsSufficientOn` its form on a class
of runs (at constant faults, the static adversary); `RegimesRealizable`, `LogFaithful` and
`HeldIffServed` are the secondary statements that `CorrectProtocol` does not imply. -/

namespace Consensus.Review

open Consensus.Shape Consensus.Model Consensus.Blocks

/-- **The review statement (L2 ⇒ L0).** Every shape instance that meets its obligations is a correct
protocol (L0 `CorrectProtocol`) for every finite validator type. Exactly the type of
`Consensus.Shape.ShapeObligations.correct`. -/
def ObligationsSufficient : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ChainShapeFamily O Info} {K : Contract ProgressReq}, ShapeObligations F K →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      CorrectProtocol (sysOf O (compiled F) V) (shapeProgress F V) K

/-- **The review statement on a class of runs.** For every predicate `Q` on environment points,
every shape instance that meets its obligations on the runs whose point satisfies `Q`
(`ShapeObligationsOn`) is a correct protocol on those runs (`CorrectProtocolOn`: the property table
there, with the adequacy and realizability of the whole system) for every finite validator type. At
`Q = fun _ p => p.ConstantFaults` it implies the review statement of the static adversary at full
strength, plus the adequacy and realizability (growth witnesses included) of the whole growing-fault
system. Exactly the type of `Consensus.Shape.ShapeObligationsOn.correct`. -/
def ObligationsSufficientOn : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ChainShapeFamily O Info} {K : Contract ProgressReq} (Q : ∀ V : Type, EnvPoint V → Prop),
    ShapeObligationsOn F K Q → ∀ (V : Type) [Fintype V] [DecidableEq V],
      CorrectProtocolOn (sysOf O (compiled F) V) (shapeProgress F V) K (Q V)

/-- L2 beyond `CorrectProtocol`: with ≥ 5 validators, a family whose progress fits its skeleton and
an admissible, progress-tolerant contract have active witnesses, including the bad-proposer witness
that gives `ProgressTolerant` its meaning (`RealizableActive.badProposer`). `ShapeObligations F K`
carries the three premises as fields. Exactly the type of `Consensus.Shape.regimes_realizable`. -/
def RegimesRealizable : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq),
    K.params.Admissible → ProgressFits K F → ProgressTolerant O K →
    ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V → RealizableActive F K V

/-- L1: the system's log is the engine's communication. Exactly the type of
`Consensus.Model.sysOf_log_faithful`. -/
def LogFaithful : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    (r : (sysOf O F V).Run),
    (∀ v o t, ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t) ∧
    (∀ v o t, ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t) ∧
    (∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩) ∧
    ((sysOf O F V).log r).inbox = r.2.inbox

/-- L1: on valid runs, for a node honest at the deadline and deadlines in the horizon, L0 `Held`
is engine `Run.Served`. Exactly the type of `Consensus.Model.Run.held_iff_served`. -/
def HeldIffServed : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O} {E : Env V}
    (rho : Run F E), rho.ExecutionValid → ∀ (o : (protoOf F E).Object) {w : V} {d : Time},
    w ∉ rho.faultyAt d → d ≤ rho.horizon →
      (CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d)

end Consensus.Review

end

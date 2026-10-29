module
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Spec.Shape.Active
public import ConsensusLean.Spec.Model.Served

@[expose] public section

/-! # The review statements

The statements a reviewer reads, as `Prop` definitions; no theorem lives here. Each body is
exactly the type of an existing theorem (binder for binder), and
`Solution.lean` proves each one by that theorem. `ConsensusLeanTest/ReviewAxioms.lean`
checks that each definition's body is alpha-equal to its theorem's type, and the comparator
(`comparator.json`, CI) checks the proofs against these statements built from Spec alone.

`AcceptedGood` is *the* review statement; `RegimesRealizable`, `LogFaithful` and `HeldIffServed`
are the secondary statements that `Good` does not imply. -/

namespace Consensus.Review

open Consensus.Shape Consensus.Model Consensus.Blocks

/-- **The review statement (L2 ⇒ L0).** Every accepted shape instance is a good protocol (L0
`Good`) for every finite validator type. Exactly the type of `Consensus.Shape.Accepted.good`. -/
def AcceptedGood : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : ShapeFamily O Info} {K : Contract ProgressReq}, Accepted F K →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      Good (sysOf O (compiled F) V) (shapeProgress F V) K

/-- L2 beyond `Good`: with ≥ 5 validators, a family whose progress fits its skeleton and an
admissible, progress-tolerant contract have active witnesses, including the bad-proposer witness
that gives `ProgressTolerant` its meaning (`RealizableActive.badProposer`). `Accepted F K` carries
the three premises as fields. Exactly the type of `Consensus.Shape.regimes_realizable`. -/
def RegimesRealizable : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ShapeFamily O Info) (K : Contract ProgressReq),
    K.params.Admissible → ProgressFits K F → ProgressTolerant O K →
    ∀ (V : Type) [Fintype V] [DecidableEq V], 5 ≤ Fintype.card V → RealizableActive F K V

/-- L1: the system's log is the engine's communication. Exactly the type of
`Consensus.Model.sysOf_log_faithful`. -/
def LogFaithful : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O}
    (r : (sysOf O F V).Run),
    (∀ v o t, ((sysOf O F V).log r).sent v ⟨r.1, o⟩ t ↔ r.2.releases v o t) ∧
    (∀ v o t, ((sysOf O F V).log r).recv v ⟨r.1, o⟩ t ↔ r.2.receives v o t) ∧
    (∀ v m t, ((sysOf O F V).log r).sent v m t ∨ ((sysOf O F V).log r).recv v m t →
      ∃ o, m = ⟨r.1, o⟩) ∧
    ((sysOf O F V).log r).inbox = r.2.inbox

/-- L1: on valid runs, for honest nodes and deadlines in the horizon, L0 `Held` is engine
`Run.Served`. Exactly the type of `Consensus.Model.Run.held_iff_served`. -/
def HeldIffServed : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
    (rho : Run F E), rho.ExecutionValid → ∀ {w : V}, w ∈ rho.honest →
    ∀ (o : (protoOf F E).Object) {d : Time}, d ≤ rho.horizon →
      (CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d)

end Consensus.Review

end

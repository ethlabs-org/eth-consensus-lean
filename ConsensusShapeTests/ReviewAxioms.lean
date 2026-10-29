module
public import ConsensusShape
@[expose] public section

/-! # Review pins

The review theorems, pinned by the build: each `example` restates the theorem's type in full
(a later change of the statement breaks the build here), and each `#guard_msgs` pins the exact
axiom list (`propext`, `Classical.choice`, `Quot.sound`; an unfinished proof or a new axiom changes the
message and fails the build). Pattern of verified-consensus `scripts/ReviewAxioms.lean`, compiled
instead of parsed. `scripts/check.sh` asserts that `ConsensusShapeTests` imports this module. -/

-- `#guard_msgs in #print axioms` puts the command off column 0; the linter's warning would
-- otherwise be part of the guarded messages; the pinned messages are longer than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

open Consensus

example : ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    {F : Shape.ShapeFamily O Info} {K : Contract Blocks.ProgressReq},
    Shape.Accepted F K →
      ∀ (V : Type) [Fintype V] [DecidableEq V],
        Good (Model.sysOf O (Shape.compiled F) V) (Shape.shapeProgress F V) K :=
  @Shape.Accepted.good

example : ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : Shape.ShapeFamily O Info) (K : Contract Blocks.ProgressReq),
    K.params.Admissible → Shape.ProgressFits K F → Shape.ProgressTolerant O K →
      ∀ (V : Type) [Fintype V] [DecidableEq V],
        5 ≤ Fintype.card V → Shape.RealizableActive F K V :=
  @Shape.regimes_realizable

example : ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Model.Family O}
    (r : (Model.sysOf O F V).Run),
    (∀ (v : V) (o : (Model.protoOf F r.fst).Object) (t : Time),
        ((Model.sysOf O F V).log r).sent v ⟨r.fst, o⟩ t ↔ r.snd.releases v o t) ∧
      (∀ (v : V) (o : (Model.protoOf F r.fst).Object) (t : Time),
          ((Model.sysOf O F V).log r).recv v ⟨r.fst, o⟩ t ↔ r.snd.receives v o t) ∧
        (∀ (v : V) (m : (Model.sysOf O F V).Obs) (t : Time),
            ((Model.sysOf O F V).log r).sent v m t ∨ ((Model.sysOf O F V).log r).recv v m t →
              ∃ (o : (Model.protoOf F r.fst).Object), m = ⟨r.fst, o⟩) ∧
          ((Model.sysOf O F V).log r).inbox = r.snd.inbox :=
  @Model.sysOf_log_faithful

example : ∀ {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Model.Family O}
    {E : Env V} (rho : Model.Run F E),
    rho.ExecutionValid →
      ∀ {w : V}, w ∈ rho.honest →
        ∀ (o : (Model.protoOf F E).Object) {d : Time},
          d ≤ rho.horizon → (CommLog.Held rho.point rho.log w o d ↔ rho.Served w o d) :=
  @Model.Run.held_iff_served

/-- info: 'Consensus.Shape.Accepted.good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shape.Accepted.good

/-- info: 'Consensus.Shape.regimes_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shape.regimes_realizable

/-- info: 'Consensus.Model.sysOf_log_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Model.sysOf_log_faithful

/-- info: 'Consensus.Model.Run.held_iff_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Model.Run.held_iff_served

end

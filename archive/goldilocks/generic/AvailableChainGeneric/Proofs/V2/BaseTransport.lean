module
public import AvailableChainGeneric.Proofs.V2.Reads

public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- A base predicate holds at every index if it holds initially and is
closed under the listed base changes of actual local events. `hstep`
covers delivery, the full atomic tick (clock and the own-record fold),
and restore after a restart. It imposes no law on unreachable states.
For a relation of smaller store writes, use its transitive closure so
that one event can contain several writes, including reconciliation.
Source: GLY r3.17 BASE TRANSPORT:901–903. Consumers: T7.W, F1, F3; SAPC. -/
theorem base_invariant {B : Type*} (base : P.State → B) (R : B → B → Prop)
    (Q : B → Prop) (E : Generic.Env V) (rho : Run V P)
    (hinit : Q (base P.init))
    (hclosed : ∀ b b', Q b → R b b' → Q b')
    (hstep : ∀ k e, rho.events[k]? = some e →
      base (World.step E rho (Run.stateBefore E rho k) e e.node) =
          base (Run.stateBefore E rho k e.node) ∨
        R (base (Run.stateBefore E rho k e.node))
          (base (World.step E rho (Run.stateBefore E rho k) e e.node)))
    (i : Nat) (v : V) : Q (base (Run.stateBefore E rho i v)) := by
  refine stateBefore_step_induction E rho (fun st => Q (base st))
    (Nat.zero_le i) v ?_ ?_
  · intro k e _ _ he hv hk
    have h := hstep k e he
    rw [hv] at h
    rcases h with hsame | hchange
    · rwa [hsame]
    · exact hclosed _ _ hk hchange
  · change Q (base P.init)
    exact hinit

/-- The same base invariant holds strictly before every read time.
The schedule premise makes the time cut a prefix of the actual run;
no monotonicity law on other executions or separate restore law is needed.
Source: GLY r3.17 BASE TRANSPORT:901–903; Statements/V2/Reads. -/
theorem base_invariant_holdsBefore {B : Type*} (base : P.State → B) (R : B → B → Prop)
    (Q : B → Prop) (E : Generic.Env V) (rho : Run V P)
    (hS : ScheduleWellFormed E rho)
    (hinit : Q (base P.init))
    (hclosed : ∀ b b', Q b → R b b' → Q b')
    (hstep : ∀ k e, rho.events[k]? = some e →
      base (World.step E rho (Run.stateBefore E rho k) e e.node) =
          base (Run.stateBefore E rho k e.node) ∨
        R (base (Run.stateBefore E rho k e.node))
          (base (World.step E rho (Run.stateBefore E rho k) e e.node)))
    (d : Time) (v : V) : HoldsBefore E rho (fun st => Q (base st)) d v := by
  rw [HoldsBefore_def, ← stateBefore_idxBefore E rho d hS]
  exact base_invariant base R Q E rho hinit hclosed hstep (Run.idxBefore rho d) v

end AvailableChain.Gen.V2

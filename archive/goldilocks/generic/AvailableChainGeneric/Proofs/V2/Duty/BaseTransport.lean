module
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

public section

namespace AvailableChain.Gen.V2.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- Source: AvailableChainGeneric/Proofs/V2/BaseTransport.lean:19.
theorem base_invariant {B : Type*} (base : P.State → B) (R : B → B → Prop)
    (Q : B → Prop) (E : Generic.Env V) (rho : D.Run V P)
    (hinit : Q (base P.init))
    (hclosed : ∀ b b', Q b → R b b' → Q b')
    (hstep : ∀ k e, rho.events[k]? = some e →
      base (D.World.step E rho (D.Run.stateBefore E rho k) e e.node) =
          base (D.Run.stateBefore E rho k e.node) ∨
        R (base (D.Run.stateBefore E rho k e.node))
          (base (D.World.step E rho (D.Run.stateBefore E rho k) e e.node)))
    (i : Nat) (v : V) : Q (base (D.Run.stateBefore E rho i v)) := by
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

-- Source: AvailableChainGeneric/Proofs/V2/BaseTransport.lean:44.
theorem base_invariant_holdsBefore {B : Type*} (base : P.State → B) (R : B → B → Prop)
    (Q : B → Prop) (E : Generic.Env V) (rho : D.Run V P)
    (hS : D.ScheduleWellFormed E rho)
    (hinit : Q (base P.init))
    (hclosed : ∀ b b', Q b → R b b' → Q b')
    (hstep : ∀ k e, rho.events[k]? = some e →
      base (D.World.step E rho (D.Run.stateBefore E rho k) e e.node) =
          base (D.Run.stateBefore E rho k e.node) ∨
        R (base (D.Run.stateBefore E rho k e.node))
          (base (D.World.step E rho (D.Run.stateBefore E rho k) e e.node)))
    (d : Time) (v : V) : HoldsBefore E rho (fun st => Q (base st)) d v := by
  rw [HoldsBefore_def, ← stateBefore_idxBefore E rho d hS]
  exact base_invariant base R Q E rho hinit hclosed hstep (D.Run.idxBefore rho d) v

end AvailableChain.Gen.V2.Duty

module
public import AvailableChainGeneric.Proofs.V2.Fields -- shake: keep (examples)

public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- The frozen core is a special case. -/
example {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrf : restartFree rho v i j) :
    proj (Run.stateBefore E rho j v) =
      (ownReleased E rho v i j).foldl g (proj (Run.stateBefore E rho i v)) :=
  ownRecord_fold_restart proj g hclock hprocess hrecord E rho hij v
    fun k t hik hkj he => absurd he (hrf k t hik hkj)

/-- The global-premise form (a0-generic's draft) is a special case. -/
example {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (hrestore : ∀ st t, proj (P.restore (P.durable st) t) = proj st)
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V) :
    proj (Run.stateBefore E rho j v) =
      (ownReleased E rho v i j).foldl g (proj (Run.stateBefore E rho i v)) :=
  ownRecord_fold_restart proj g hclock hprocess hrecord E rho hij v
    fun _ t _ _ _ => hrestore _ t

end AvailableChain.Gen.V2

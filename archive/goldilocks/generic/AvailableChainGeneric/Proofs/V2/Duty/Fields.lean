module
public import AvailableChainKitV2.DutyRecord

public section

namespace AvailableChain.Gen.V2.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- Source: AvailableChainGeneric/Proofs/V2/Fields.lean:14.
theorem ownRecord_fold_restart {β : Type} (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (E : Generic.Env V) (rho : D.Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrestart : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.restart v t) →
      proj (P.restore (P.durable (D.Run.stateBefore E rho k v)) t) =
        proj (D.Run.stateBefore E rho k v)) :
    proj (D.Run.stateBefore E rho j v) =
      (ownReleased E rho v i j).foldl g (proj (D.Run.stateBefore E rho i v)) :=
  ownRecord_fold_interval_restart proj g hclock hprocess hrecord E rho hij v hrestart

end AvailableChain.Gen.V2.Duty

module
public import ConsensusLean.Lemmas.Model.Canonical.Parts

@[expose] public section

/-! # Where the signed parts of a run's objects come from: statements and axioms

The facts of `Lemmas/Model/Canonical/Parts` restated as named theorems, with their axioms pinned. -/

namespace Consensus.Model.PartsTest

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V} (rho : Run F E)

/-- A signed part of a release was released by its honest signer first. -/
theorem part_released (hv : rho.ExecutionValid) {u : V} {o : (protoOf F E).Object} {t : Time}
    (hr : rho.releases u o t) {d : (protoOf F E).Object} (hd : Obj.Contains o d)
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (hs : d.auth = .signed k r)
    (hk : rho.point.HonestAt (rho.key k) t) :
    ∃ t', t' ≤ t ∧ rho.releases (rho.key k) d t' :=
  Run.part_released rho hv hr hd hs hk

/-- A signed part of a receipt was released by its honest signer first. -/
theorem part_released_of_receives (hv : rho.ExecutionValid) {w : V} {o : (protoOf F E).Object}
    {t : Time} (hr : rho.receives w o t) {d : (protoOf F E).Object} (hd : Obj.Contains o d)
    {k : Fin (Fintype.card V)} {r : (protoOf F E).Role} (hs : d.auth = .signed k r)
    (hk : rho.point.HonestAt (rho.key k) t) :
    ∃ t', t' ≤ t ∧ rho.releases (rho.key k) d t' :=
  Run.part_released_of_receives rho hv hr hd hs hk

/-- In the filtered injection schedule, a part signed by a never-honest key comes from an
injection. -/
theorem injfRun_part_injected (delay : Event V (protoOf F E).Object → Time)
    (inj : Time → V → List (protoOf F E).Object)
    (pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)
    (hdelay : ∀ e, 0 ≤ delay e)
    {k : Fin (Fintype.card V)} (hk : ∀ t, rho.key k ∈ rho.faultyAt t) {w : V}
    {o : (protoOf F E).Object} {t : Time} (hr : (rho.injfRun delay inj pol).receives w o t)
    {d : (protoOf F E).Object} (hd : Obj.Contains o d) {r : (protoOf F E).Role}
    (hs : d.auth = .signed k r) :
    ∃ t' v o', t' ≤ t ∧ o' ∈ inj t' v ∧ Obj.Contains o' d ∧
      (rho.injfRun delay inj pol).receives v o' t' :=
  Run.injfRun_part_injected rho delay inj pol hdelay hk hr hd hs

end Consensus.Model.PartsTest

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Model.PartsTest.part_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.PartsTest.part_released

/-- info: 'Consensus.Model.PartsTest.part_released_of_receives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.PartsTest.part_released_of_receives

/-- info: 'Consensus.Model.PartsTest.injfRun_part_injected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.PartsTest.injfRun_part_injected

end

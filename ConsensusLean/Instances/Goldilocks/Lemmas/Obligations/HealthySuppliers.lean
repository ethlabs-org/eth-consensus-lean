module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.WeakBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # The healthy preparation query

`HealthyPreparationQuery` fixes the engine run, regime and nonfinal capability without adding
progress. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Healthy context carries no progress beyond the separately supplied interval. -/
structure HealthyPreparationQuery where
  run : (Sys (goldilocks S) V).Run
  constant : run.2.point.ConstantFaults
  hn : 1 ≤ Fintype.card V
  cap : Capability
  nonfinal : cap = .available ∨ cap = .stable
  index : (K S A).Idx
  gst : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (goldilocks S) V).Healthy (K S A) gst run

namespace HealthyPreparationQuery
variable {S A V}
abbrev params (Q : HealthyPreparationQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : HealthyPreparationQuery S A V) := simTrace ⟨S, stock⟩ Q.run.2 Q.hn
noncomputable abbrev heal (Q : HealthyPreparationQuery S A V) :=
  (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run
noncomputable abbrev ready (Q : HealthyPreparationQuery S A V) :=
  (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run
noncomputable abbrev cut (Q : HealthyPreparationQuery S A V) :=
  cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.heal)
end HealthyPreparationQuery

/-- Global inventory obligation, exactly the initialization required by
oldHonest_inventory_preserved. OldHonest includes signed entries not yet held by
the receiver. OldEntryCovered has an eventual whole-run origin: this predicate
is NOT prefix-local preparation and supplies no vote-label/causal strengthening. -/
def HealthyOldInventory (Q : HealthyPreparationQuery S A V) (s₀ i : Nat) : Prop :=
  ∀ y ∈ honestKeys ⟨S, stock⟩ Q.run.2, ∀ E h,
    Healing.OldHonest Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) s₀ E h →
      Healing.OldEntryCovered Q.trace (honestKeys ⟨S, stock⟩ Q.run.2) s₀ E ∨
        h < (Q.trace.state y i).fg.hj

/-- Proven preservation of an explicitly supplied old-entry inventory. Since R0 no
inventory is produced on the obligations route, and no declaration consumes the preserved
inventory. It ranges over ALL later cuts, not merely end-of-time observations. It does not
turn eventual coverage into prefix-produced coverage or give a vote label bound. -/
theorem healthy_old_inventory_preserve (Q : HealthyPreparationQuery S A V)
    {s₀ : Nat} (base : HealthyOldInventory S A V Q s₀ Q.cut) :
    ∀ i, Q.cut ≤ i → HealthyOldInventory S A V Q s₀ i := by
  exact Healing.oldHonest_inventory_preserved
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid) base

end Consensus.Goldilocks.Obligations
end

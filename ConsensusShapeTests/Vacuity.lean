module
public import ConsensusShapeTests.Realizable
public import Mathlib.Tactic
@[expose] public section

/-! # Vacuity and credential tests (L2)

* `credential_forgery_excluded`: the L2 form of the model-level credential
  test (`forged_role_invalid`): a delivered proposal signed by a key not
  selected as the slot's proposer violates `ExecutionValid`, for every family;
  `forgedProposal` is a concrete such run of the trivial shape (admissible
  selection, key 2 proposes, key 1 forges), `forgedProposal_invalid`.
* `noService_not_accepted`: a schema with no output at all, or only a stable
  one, is not `Accepted`, whatever its claims (`OutputSchema.Serves`).

The premise-language vacuity checks of earlier iterations are gone with the
premise language: the regimes are fixed L0 definitions. -/

namespace Consensus.Shape.Tests.Vacuity
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- Credential forgery (L2 form): a delivered object containing a
proposal signed by a key not selected as the slot's proposer makes the run
invalid, for every family. -/
theorem credential_forgery_excluded {F : ShapeFamily O Info} {V : Type} [Fintype V]
    [DecidableEq V] {E : Env V} (rho : Model.Run (compiled F) E) {i : Nat} {w : V}
    {o : (protoOf (compiled F) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver w o t)) {o' : (protoOf (compiled F) E).Object}
    (hc : Obj.Contains o o') {k : Fin (Fintype.card V)} {s : Nat}
    (ha : o'.auth = .signed k (ShapeRole.proposer s))
    (hk : k ∉ rho.sel (ShapeRole.proposer s)) : ¬ rho.ExecutionValid := fun hv =>
  hk (hv.credentials i w o t he o' hc k _ ha)

open Consensus.Shape.Tests.Shapes (trivialFamily)
open Consensus.Shape.Tests.Realizable (point3 key3 sel3 sel3_admits)

/-- A run of the trivial shape at the 3-node point with the admissible
selection `sel3` (key 2 proposes every slot) that delivers to validator 1 a
header of slot 0 signed by key 1 as proposer. -/
def forgedProposal : Model.Run (compiled trivialFamily) point3.env :=
  Model.mkRun point3.honest point3.horizon key3 sel3 (fun _ _ => []) (fun _ _ => [])
    (fun _ => 1)
    [.deliver 1 (.mk (.signed ⟨1, by simp⟩ (ShapeRole.proposer 0))
      (.item ⟨.root, 0, 0, ()⟩) []) 0]

/-- The forged run has an admissible selection, and is invalid. -/
theorem forgedProposal_invalid : forgedProposal.SelValid ∧ ¬ forgedProposal.ExecutionValid := by
  refine ⟨sel3_admits, credential_forgery_excluded forgedProposal (i := 0) rfl (.refl _) rfl ?_⟩
  change (⟨1, by simp⟩ : Fin (Fintype.card (Fin 3))) ∉ ({⟨2, by simp⟩} : Finset _)
  simp

/-- A schema that provides neither a final nor an available output. -/
def noService (stable : Bool) : OutputSchema :=
  ⟨Unit, fun c => if stable ∧ c = .stable then some () else none⟩

/-- An instance without a ledger service is never accepted (`Accepted.serves`),
whatever its claims. -/
theorem noService_not_accepted (b : Bool) (F : ShapeFamily (noService b) Info)
    (K : Contract (noService b) ProgressReq) : ¬ Accepted F K := by
  intro h
  rcases h.serves with h | ⟨h, -⟩ <;> simp [noService, OutputSchema.BFTCore] at h

end Consensus.Shape.Tests.Vacuity

end

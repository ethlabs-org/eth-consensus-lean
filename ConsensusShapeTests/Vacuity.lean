module
public import ConsensusShapeTests.Realizable
public import Mathlib.Tactic
@[expose] public section

/-! # Bad contracts, bad protocols, credentials (L2)

* **Admissibility rejections** (M10): a contract cannot buy its claims with a
  stronger environment. Each of `θ = 3/5`, `φ = 9/10`, `cover = 3/5`,
  `α = 1/4` (with `φ = 2/3`: `1 − φ > α`), `budget = 0` and `catchUp = 0`,
  changed alone from admissible standard numbers, is rejected
  (`reject_theta` … `reject_catchUp`, bundled as `admissibility_rejections`);
  `standard_admissible` is the control (the standard numbers are admissible).
* **Progress fit** (M29): `allProposers_unfit` (review B2: a recurrence does
  not fit a family that selects every key as proposer; the matching run-level
  fact is `Realizable.allProposers_no_witness`); `noProgressFit`,
  `noProgressFit_contract` (a recurrence on a poll skeleton, which has no slot
  proposers); `notReadyAtMost_fits` (round robin fits every skeleton).
* `credential_forgery_excluded`: the L2 form of the model-level credential
  test (`forged_role_invalid`): a delivered proposal signed by a key not
  selected as the slot's proposer violates `ExecutionValid`, for every family;
  `forgedProposal` is a concrete such run of the trivial shape (admissible
  selection, key 2 proposes, key 1 forges), `forgedProposal_invalid`.
* `noService_not_accepted`: a schema with no output at all, or only a stable
  one, is not `Accepted`, whatever its claims (`OutputSchema.Serves`).

Vacuous *systems* (empty validity, excuse everywhere, a progress reader that
never holds) are rejected by L0 `Good` itself: `Good.lean` tests. -/

namespace Consensus.Shape.Tests.Vacuity
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)
open Consensus.Shape.Tests.Shapes (schema pollSkel pollShape)

section Admissibility

/-- Standard numbers (catch-up `1`, lag `0`, budget `1`, heal and latency
`1`) over a one-point index. -/
def std : Params Unit := Params.standard 1 0 1 (fun _ _ => 1) (fun _ _ => 1)

/-- Control: the standard numbers are admissible. -/
theorem standard_admissible : std.Admissible :=
  Params.standard_admissible le_rfl le_rfl

/-- A sleepy threshold above ½ is rejected. -/
theorem reject_theta : ¬ ({ std with θ := 3 / 5 } : Params Unit).Admissible :=
  fun h => by have := h.θ_range.2; norm_num at this

/-- A healthy threshold above ⅔ is rejected. -/
theorem reject_phi : ¬ ({ std with φ := 9 / 10 } : Params Unit).Admissible :=
  fun h => by have := h.φ_range.2; norm_num at this

/-- A cover above ½ is rejected. -/
theorem reject_cover : ¬ ({ std with cover := 3 / 5 } : Params Unit).Admissible :=
  fun h => by have := h.cover_range.2; norm_num at this

/-- An accountable fraction below `1 − φ` is rejected (`α = 1/4`, `φ = 2/3`):
the healthy regime would not bound the faults below `α`. -/
theorem reject_alpha : ¬ ({ std with α := 1 / 4 } : Params Unit).Admissible :=
  fun h => by have := h.α_range.1; simp [std, Params.standard] at this; norm_num at this

/-- An empty outage budget is rejected (no outage would be admitted). -/
theorem reject_budget : ¬ ({ std with budget := 0 } : Params Unit).Admissible :=
  fun h => by have := h.budget_pos; simp at this

/-- A zero catch-up is rejected. -/
theorem reject_catchUp : ¬ ({ std with catchUp := 0 } : Params Unit).Admissible :=
  fun h => by have := h.catchUp_pos; simp at this

/-- All six rejections, beside the control. -/
theorem admissibility_rejections :
    std.Admissible ∧ ¬ ({ std with θ := 3 / 5 } : Params Unit).Admissible ∧
      ¬ ({ std with φ := 9 / 10 } : Params Unit).Admissible ∧
      ¬ ({ std with cover := 3 / 5 } : Params Unit).Admissible ∧
      ¬ ({ std with α := 1 / 4 } : Params Unit).Admissible ∧
      ¬ ({ std with budget := 0 } : Params Unit).Admissible ∧
      ¬ ({ std with catchUp := 0 } : Params Unit).Admissible :=
  ⟨standard_admissible, reject_theta, reject_phi, reject_cover, reject_alpha, reject_budget,
    reject_catchUp⟩

/-- `α = 1/4` is rejected at every admissible-range `φ` (`1 − φ ≥ 1/3`). -/
theorem reject_alpha_any {Idx : Type} (P : Params Idx) (hα : P.α = 1 / 4) : ¬ P.Admissible :=
  fun h => by have := h.α_range.1; have := h.φ_range.2; rw [hα] at *; linarith

end Admissibility

section ProgressFit

/-- Acceptance rejects the all-proposers family up front: a recurrence
requirement does not fit `.sized (max 1 n)` once `n ≥ 2`. -/
theorem allProposers_unfit {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Encodable Info] {F : ShapeFamily O Info}
    (hF : ∀ pub, (F pub).skel.proposerSel = .sized (max 1 pub.n))
    (K : Contract O ProgressReq) (cap : Capability) (i : K.Idx) (ρ : Recurrence)
    (hK : K.progress cap i = .recur ρ) : ¬ K.ProgressFits F := by
  intro h
  have := h cap i ⟨2, 1, by decide⟩
  rw [hK] at this
  change (F ⟨2, 1, by decide⟩).skel.proposerSel = .sized 1 at this
  rw [hF] at this
  cases this

/-- A recurrence does not fit a poll skeleton (no slot proposers). -/
theorem noProgressFit (n : Nat) (ρ : Recurrence) : ¬ (ProgressReq.recur ρ).Fits (pollSkel n) := by
  intro h
  cases h

/-- No contract with a recurrence requirement fits the poll shape. -/
theorem noProgressFit_contract (K : Contract schema ProgressReq) (cap : Capability) (i : K.Idx)
    (ρ : Recurrence) (hK : K.progress cap i = .recur ρ) :
    ¬ K.ProgressFits (fun pub => pollShape pub) := by
  intro h
  have := h cap i ⟨1, 1, by decide⟩
  rw [hK] at this
  exact noProgressFit 1 ρ this

/-- A bound on the validators not ready fits every skeleton (round robin). -/
theorem notReadyAtMost_fits {n : Nat} (sk : Skeleton n) (m : ℕ+) :
    (ProgressReq.notReadyAtMost m).Fits sk := trivial


end ProgressFit

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

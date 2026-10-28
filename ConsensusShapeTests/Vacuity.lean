module
public import ConsensusShapeTests.Realizable
public import ConsensusShapeTests.Common
public import ConsensusShapeTests.Regimes
public import Mathlib.Tactic
@[expose] public section

/-! # Bad contracts, bad protocols, credentials (L2)

* A bound of one validator not ready fails the sleepy stress requirement.
* **Admissibility rejections** (M10): a contract cannot buy its claims with a
  stronger environment. Each of `θ = 3/5`, `φ = 9/10`, `cover = 3/5`,
  `α = 1/4` (with `φ = 2/3`: `1 − φ > α`), `budget = 0` and `catchUp = 0`,
  changed alone from admissible standard numbers, is rejected
  (`reject_theta` … `reject_catchUp`, bundled as `admissibility_rejections`);
  `standard_admissible` is the control (the standard numbers are admissible).
* **Progress fit** (M29): `allProposers_unfit` (a recurrence does
  not fit a family that selects every key as proposer; the matching run-level
  fact is `Realizable.allProposers_no_witness`);
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
open Consensus.Shape.Tests.Shapes (pollSkel pollShape)

/-- Near-full participation cannot meet sleepy stress below a supermajority. -/
theorem notReadyAtMost_one_not_realizable {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Encodable Info] (F : ShapeFamily O Info)
    (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V]
    (hn : 5 ≤ Fintype.card V) (ho : (O.output .available).isSome)
    (hp : ∀ i, K.progress .available i = .notReadyAtMost 1) :
    ¬ Realizable (sysOf O (compiled F) V) (shapeProgress F V) K := by
  intro h
  obtain ⟨i, r, -, hd, ⟨-, hprog, hlive⟩, hawake⟩ :=
    h.sleepyStress .available (Or.inl rfl) ho 1 one_pos
  let S := sysOf O (compiled F) V
  have hc : 0 ≤ S.cDur K r := mul_nonneg (by positivity) (S.pt r).env.Δ_pos.le
  have hD : 0 ≤ S.lat K .available i r :=
    mul_nonneg (by positivity) (S.pt r).env.Δ_pos.le
  obtain ⟨x, t, t', u, w, ht, -, -, -, -, -, -, hdl, hth, -⟩ := hlive
  have hH : 0 ≤ (S.pt r).horizon := by
    have := le_max_left t 0
    dsimp [S] at *
    linarith [(S.pt r).env.Δ_pos]
  change shapeHolds F (K.progress .available i) _ _ _ _ _ at hprog
  rw [hp i] at hprog
  have hready := hprog 0 (by simp) hH hH
  have hsub := Finset.card_le_card ((S.pt r).readyAt_subset_awakeAt hc le_rfl)
  have hb := hawake 0 le_rfl hH
  change ((S.pt r).awakeAt 0).card ≤ 2 * Fintype.card V / 3 at hb
  change Fintype.card V ≤ ((S.pt r).readyAt (S.cDur K r) 0).card + 1 at hready
  omega

/-- A fixed bound of one cannot tolerate arbitrary numbers not ready. -/
theorem notReadyAtMost_one_not_tolerant {O : OutputSchema} (K : Contract ProgressReq)
    (ho : (O.output .available).isSome)
    (hp : ∀ i, K.progress .available i = .notReadyAtMost 1) : ¬ Contract.ProgressTolerant O K := by
  intro h
  obtain ⟨i, hi⟩ := h .available ho 2
  rw [hp i] at hi
  norm_num [ProgressReq.Tolerates] at hi

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

/-- `α = 1/4` is rejected at every admissible-range `φ` (`1 − φ ≥ 1/3`). -/
theorem reject_alpha_any {Idx : Type} (P : Params Idx) (hα : P.α = 1 / 4) : ¬ P.Admissible :=
  fun h => by have := h.α_range.1; have := h.φ_range.2; rw [hα] at *; linarith

/-- An accountable fraction below `1 − φ` is rejected (`α = 1/4`, `φ = 2/3`):
the healthy regime would not bound the faults below `α`. -/
theorem reject_alpha : ¬ ({ std with α := 1 / 4 } : Params Unit).Admissible :=
  reject_alpha_any _ rfl

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

end Admissibility

section ProgressFit

/-- Acceptance rejects the all-proposers family up front: a recurrence
requirement does not fit `.sized (max 1 n)` once `n ≥ 2`. -/
theorem allProposers_unfit {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Encodable Info] {F : ShapeFamily O Info}
    (hF : ∀ pub, (F pub).skel.proposerSel = .sized (max 1 pub.n))
    (K : Contract ProgressReq) (cap : Capability) (i : K.Idx) (ρ : Recurrence)
    (hK : K.progress cap i = .recur ρ) : ¬ K.ProgressFits F := by
  intro h
  have := h cap i ⟨2, 1, by decide⟩
  rw [hK] at this
  change (F ⟨2, 1, by decide⟩).skel.proposerSel = .sized 1 at this
  rw [hF] at this
  cases this

/-- No contract with a recurrence requirement fits the poll shape: a recurrence
fits only `.sized 1` proposers, and the poll skeleton has none. -/
theorem noProgressFit_contract (K : Contract ProgressReq) (cap : Capability) (i : K.Idx)
    (ρ : Recurrence) (hK : K.progress cap i = .recur ρ) :
    ¬ K.ProgressFits (show ShapeFamily schema Unit from fun pub => pollShape pub) := by
  intro h
  have := h cap i ⟨1, 1, by decide⟩
  rw [hK] at this
  cases this

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
open Consensus.Shape.Tests.Realizable (point3 sel3 sel3_admits)

/-- A run of the trivial shape at the 3-node point with the admissible
selection `sel3` (key 2 proposes every slot) that delivers to validator 1 a
header of slot 0 signed by key 1 as proposer. -/
def forgedProposal : Model.Run (compiled trivialFamily) point3.env :=
  Model.mkRun point3.honest point3.horizon (pkiFin 3) sel3 (fun _ _ => []) (fun _ _ => [])
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
    (K : Contract ProgressReq) : ¬ Accepted F K := by
  intro h
  rcases h.serves with h | h <;> simp [noService] at h

end Consensus.Shape.Tests.Vacuity

end

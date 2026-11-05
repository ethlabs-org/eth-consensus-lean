module
public import ConsensusLeanTest.Shape.Realizable
public import ConsensusLeanTest.Fixtures.Common
public import ConsensusLeanTest.Problem.Regimes
public import Mathlib.Tactic
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Bad contracts, bad protocols, credentials (L2)

* A bound of one validator not ready, or any bound below `n − 2` at every
  index, fails the sleepy stress requirement (at most two honest awake).
* **Admissibility rejections** (M10): a contract cannot buy its claims with a
  stronger environment. Each of `θ = 3/5`, `β = 1/4` (fewer faults than a
  third), `cover = 3/5`, `α = 1/4` (with `β = 1/3`: `β > α`), `budget = 0` and
  `catchUp = 0`,
  changed alone from admissible standard numbers, is rejected
  (`reject_theta` … `reject_catchUp`, bundled as `admissibility_rejections`);
  `standard_admissible` is the control (the standard numbers are admissible).
* **Progress fit** (M29): `allProposers_unfit` (a recurrence does
  not fit a family that selects every key as proposer; the matching run-level
  fact is `Realizable.allProposers_no_witness`);
  `noProgressFit_contract` (a recurrence on a poll skeleton, which has no slot
  proposers); `notReadyAtMost_fits` (round robin fits every skeleton).
* **Bad proposer slots** (decision 3): `recur_single_one_not_tolerant`
  (an honest ready proposer in every slot, `recur ⟨single, 1⟩`, at every
  index is not `ProgressTolerant`), generally `recur_noSlack_not_tolerant`
  (`gap < span + 2` at every index); `recur_single_one_bad_slots` (why: it
  fails on a point whose slots all have faulty proposers).
* `credential_forgery_excluded`: the L2 form of the model-level credential
  test (`forged_role_invalid`): a delivered proposal signed by a key not
  selected as the slot's proposer violates `ExecutionValid`, for every family;
  `forgedProposal` is a concrete such run of the trivial shape (admissible
  selection, key 2 proposes, key 1 forges), `forgedProposal_invalid`.
* `noService_not_obligations`: a schema with no output at all, or only a stable
  one, is not `ShapeObligations`, whatever its claims (`OutputSchema.Serves`).

Vacuous *systems* (empty validity, excuse everywhere, a progress reader that
never holds) are rejected by L0 `CorrectProtocol` itself: `CorrectProtocol.lean` tests. -/

namespace Consensus.Shape.Tests.Vacuity
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)
open Consensus.Shape.Tests.Shapes (pollSkel pollShape)

/-- A bound below `n − 2` validators not ready at every index cannot meet
the sleepy stress witness (at most two honest validators awake): any fixed
participation requirement of three or more ready validators fails. -/
theorem notReadyAtMost_below_not_realizable {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] (F : ChainShapeFamily O Info)
    (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V]
    (_hn : 5 ≤ Fintype.card V) (ho : (O.output .available).isSome) (m : K.Idx → ℕ+)
    (hm : ∀ i, (m i : Nat) + 3 ≤ Fintype.card V)
    (hp : ∀ i, K.progress .available i = .notReadyAtMost (m i)) :
    ¬ Realizable (sysOf O (compiled F) V) (shapeProgress F V) K := by
  intro h
  obtain ⟨i, hi⟩ := h.sleepyStress .available (Or.inl rfl) ho
  obtain ⟨r, ⟨-, hd, -⟩, ⟨-, hprog, hlive⟩, hawake⟩ := hi 2 2 (by norm_num) (by norm_num)
  let S := sysOf O (compiled F) V
  have hc : 0 ≤ S.cDur K r := mul_nonneg (by positivity) (S.pt r).env.ΔAC_pos.le
  have hD : 0 ≤ S.lat K .available i r :=
    mul_nonneg (by positivity) (S.pt r).env.ΔAC_pos.le
  obtain ⟨x, t, t', u, w, ht, -, -, -, -, -, -, hdl, hth, -⟩ := hlive
  have hH : 0 ≤ (S.pt r).horizon := by
    have := le_max_left t 0
    dsimp [S] at *
    linarith [(S.pt r).env.ΔAC_pos]
  change shapeHolds F (K.progress .available i) _ _ _ _ _ at hprog
  rw [hp i] at hprog
  have hready := hprog 0 (by simp) hH hH
  have hsub := Finset.card_le_card ((S.pt r).readyAt_subset_awakeAt hc le_rfl)
  have hb := hawake 0 le_rfl hH
  change ((S.pt r).awakeAt 0).card ≤ 2 at hb
  change Fintype.card V ≤ ((S.pt r).readyAt (S.cDur K r) 0).card + (m i : Nat) at hready
  have := hm i
  omega

/-- Near-full participation (at most one validator not ready) cannot meet
sleepy stress. -/
theorem notReadyAtMost_one_not_realizable {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] (F : ChainShapeFamily O Info)
    (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V]
    (hn : 5 ≤ Fintype.card V) (ho : (O.output .available).isSome)
    (hp : ∀ i, K.progress .available i = .notReadyAtMost 1) :
    ¬ Realizable (sysOf O (compiled F) V) (shapeProgress F V) K :=
  notReadyAtMost_below_not_realizable F K V hn ho (fun _ => 1) (fun _ => by simp; omega) hp

/-- A fixed bound of one cannot tolerate arbitrary numbers not ready. -/
theorem notReadyAtMost_one_not_tolerant {O : OutputSchema} (K : Contract ProgressReq)
    (ho : (O.output .available).isSome)
    (hp : ∀ i, K.progress .available i = .notReadyAtMost 1) : ¬ ProgressTolerant O K := by
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

/-- A healthy fault bound below ⅓ (a stronger premise) is rejected. -/
theorem reject_beta : ¬ ({ std with β := 1 / 4 } : Params Unit).Admissible :=
  fun h => by have := h.β_range; norm_num at this

/-- A cover above ½ is rejected (an `Admissible` range check only: no regime
reads `cover`). -/
theorem reject_cover : ¬ ({ std with cover := 3 / 5 } : Params Unit).Admissible :=
  fun h => by have := h.cover_range.2; norm_num at this

/-- `α = 1/4` is rejected at every admissible-range `β` (`β ≥ 1/3`). -/
theorem reject_alpha_any {Idx : Type} (P : Params Idx) (hα : P.α = 1 / 4) : ¬ P.Admissible :=
  fun h => by have := h.α_range.1; have := h.β_range; rw [hα] at *; linarith

/-- An accountable fraction below `β` is rejected (`α = 1/4`, `β = 1/3`):
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
      ¬ ({ std with β := 1 / 4 } : Params Unit).Admissible ∧
      ¬ ({ std with cover := 3 / 5 } : Params Unit).Admissible ∧
      ¬ ({ std with α := 1 / 4 } : Params Unit).Admissible ∧
      ¬ ({ std with budget := 0 } : Params Unit).Admissible ∧
      ¬ ({ std with catchUp := 0 } : Params Unit).Admissible :=
  ⟨standard_admissible, reject_theta, reject_beta, reject_cover, reject_alpha, reject_budget,
    reject_catchUp⟩

end Admissibility

section ProgressFit

/-- Acceptance rejects the all-proposers family up front: a recurrence
requirement does not fit `.sized (max 1 n)` once `n ≥ 2`. -/
theorem allProposers_unfit {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Countable Info] {F : ChainShapeFamily O Info}
    (hF : ∀ pub s, (F pub).skel.proposerSel s = .sized (max 1 pub.n))
    (K : Contract ProgressReq) (cap : Capability) (i : K.Idx) (ρ : Recurrence)
    (hK : K.progress cap i = .recur ρ) : ¬ ProgressFits K F := by
  intro h
  have := h cap i ⟨2, 1, by decide, 1, by decide⟩
  rw [hK] at this
  change ∀ s, (F ⟨2, 1, by decide, 1, by decide⟩).skel.proposerSel s = .sized 1 at this
  have := this 0
  rw [hF] at this
  cases this

/-- No contract with a recurrence requirement fits the poll shape: a recurrence
fits only `.sized 1` proposers, and the poll skeleton has none. -/
theorem noProgressFit_contract (K : Contract ProgressReq) (cap : Capability) (i : K.Idx)
    (ρ : Recurrence) (hK : K.progress cap i = .recur ρ) :
    ¬ ProgressFits K (show ChainShapeFamily schema Unit from fun pub => pollShape pub) := by
  intro h
  have := h cap i ⟨1, 1, by decide, 1, by decide⟩
  rw [hK] at this
  cases this 0

/-- A bound on the validators not ready fits every skeleton (round robin). -/
theorem notReadyAtMost_fits {n : Nat} (sk : Skeleton n) (m : ℕ+) :
    ProgressReq.Fits sk (ProgressReq.notReadyAtMost m) := trivial

/-- A recurrence without room for a bad proposer slot in every window
(`gap < span + 2`) at every index of a provided output is not progress
tolerant. -/
theorem recur_noSlack_not_tolerant {O : OutputSchema} (K : Contract ProgressReq)
    {cap : Capability} (ho : (O.output cap).isSome)
    (hp : ∀ i, ∃ ρ : Recurrence, K.progress cap i = .recur ρ ∧ (ρ.gap : Nat) < ρ.pattern.span + 2) :
    ¬ ProgressTolerant O K := by
  intro h
  obtain ⟨i, hi⟩ := h cap ho 0
  obtain ⟨ρ, hρ, hlt⟩ := hp i
  rw [hρ] at hi
  change ρ.pattern.span + 2 ≤ (ρ.gap : Nat) at hi
  omega

/-- "Every slot's proposer is honest and ready" (`recur ⟨single, 1⟩` at every
index) is rejected by acceptance (`ProgressTolerant`). -/
theorem recur_single_one_not_tolerant {O : OutputSchema} (K : Contract ProgressReq)
    {cap : Capability} (ho : (O.output cap).isSome)
    (hp : ∀ i, K.progress cap i = .recur ⟨Pattern.single, 1⟩) : ¬ ProgressTolerant O K :=
  recur_noSlack_not_tolerant K ho fun i => ⟨_, hp i, by decide⟩

/-- Why: `recur ⟨single, 1⟩` fails as soon as one whole window fits in
`[start, stop]` and the horizon and every slot has a nonempty, entirely faulty
proposer selection; with slack (`BadSlotSlack`) it holds with a bad slot in
every window (`patternRecurrence_of_periodic`). -/
theorem recur_single_one_bad_slots {V : Type} [Fintype V] (p : EnvPoint V)
    (key : Fin (Fintype.card V) ≃ V) (sel : Slot → Finset (Fin (Fintype.card V)))
    (G : TimeGrid) (c start stop : Time)
    (hbad : ∀ s, (sel s).Nonempty ∧ ∀ k ∈ sel s, key k ∉ p.honest)
    (hs : max start 0 + ((⟨Pattern.single, 1⟩ : Recurrence).len : Time) * G.slotLen ≤ stop)
    (ht : max start 0 + ((⟨Pattern.single, 1⟩ : Recurrence).len : Time) * G.slotLen ≤
      p.horizon) :
    ¬ PatternRecurrence p key sel G ⟨Pattern.single, 1⟩ c start stop := by
  intro h
  obtain ⟨s, hall⟩ := h.exists_inside hs ht
  obtain ⟨-, hr⟩ := hall 0 (List.mem_singleton_self _)
  obtain ⟨k, hk⟩ := (hbad (s + 0)).1
  exact (hbad (s + 0)).2 k hk (hr.2 k hk).1


end ProgressFit

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- Credential forgery (L2 form): a delivered object containing a
proposal signed by a key not selected as the slot's proposer makes the run
invalid, for every family. -/
theorem credential_forgery_excluded {F : ChainShapeFamily O Info} {V : Type} [Fintype V]
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
  Model.Run.mk point3.honest point3.horizon
      [.deliver 1 (.mk (.signed ⟨1, by simp⟩ (ShapeRole.proposer 0))
        (.item ⟨.root, 0, 0, ()⟩) []) 0]
      (pkiFin 3) sel3 (fun _ _ => []) (fun _ _ => []) (fun _ => 1)

/-- The forged run has an admissible selection, and is invalid. -/
theorem forgedProposal_invalid : forgedProposal.SelValid ∧ ¬ forgedProposal.ExecutionValid := by
  refine ⟨sel3_admits, credential_forgery_excluded forgedProposal (i := 0) rfl (.refl _) rfl ?_⟩
  change (⟨1, by simp⟩ : Fin (Fintype.card (Fin 3))) ∉ ({⟨2, by simp⟩} : Finset _)
  simp

/-- A schema that provides neither a final nor an available output. -/
def noService (stable : Bool) : OutputSchema :=
  ⟨Unit, fun c => if stable ∧ c = .stable then some () else none⟩

/-- An instance without a ledger service is never accepted (`ShapeObligations.serves`),
whatever its claims. -/
theorem noService_not_obligations (b : Bool) (F : ChainShapeFamily (noService b) Info)
    (K : Contract ProgressReq) : ¬ ShapeObligations F K := by
  intro h
  rcases h.serves with h | h <;> simp [noService] at h

end Consensus.Shape.Tests.Vacuity

end

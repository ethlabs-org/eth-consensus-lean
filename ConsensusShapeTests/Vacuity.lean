module
public import ConsensusShapeTests.Realizable
public import Mathlib.Tactic
@[expose] public section

/-! # Vacuity refutations

Contracts that would make `ShapeClaims` vacuous, or easier than intended, are
rejected by its structural fields, for every family:

* `zero_catchUp_not_shapeClaims`: catch-up `0` (`Ready 0` is still
  satisfiable, but the transaction-liveness bridge needs a positive catch-up,
  `ShapeClaims.catchUp_pos`);
* `escape_zero_rejected`, `recoveryEscape_zero_rejected`,
  `accountable_zero_rejected`: an escape or accountable fraction `0` (being
  "slashable for `0`" holds in every run, so the claim would be empty);
* `resilient_without_recovery_rejected`: a resilient capability without a
  recovery spec (`¬ CapSpec.Complete`);
* `noSync_live_rejected`, `noSync_recovery_rejected`: a liveness or recovery
  premise without `sync` (D-20).

`noService_not_accepted`: a schema with no output at all, or only a resilient
one, is not `Accepted`, whatever its claims (`OutputSchema.Serves`); a
provided but silent or empty output is excluded by `delivers`.

`goldilocks_structural` is the control: every well-formed Goldilocks contract
passes these structural fields.

`credential_forgery_excluded` is the layer-1 form of the model-level credential
test (`forged_role_invalid`): a delivered proposal signed by a key not selected as the slot's
proposer violates `ExecutionValid`, for every family; `forgedProposal` is a
concrete such run of the trivial shape (admissible selection, key 2 proposes,
key 1 forges). (A zero progress gap needs no test: `ProgressReq.gap : ℕ+`.) -/

namespace Consensus.Shape.Tests.Vacuity
open Consensus Blocks Shape
open Consensus.Model (Public Key Obj pubOf protoOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- Catch-up `0` is rejected. -/
theorem zero_catchUp_not_shapeClaims (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    (h : K.catchUp = 0) : ¬ ShapeClaims F K := fun hc => by
  have := hc.catchUp_pos
  omega

/-- A safety escape `some 0` is rejected. -/
theorem escape_zero_rejected (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    {c : Capability} {s : CapSpec ProgressReq K.Idx} (hs : K.spec c = some s)
    (h : s.safety.escape = some 0) : ¬ ShapeClaims F K := fun hc =>
  lt_irrefl _ ((hc.wf.caps c s hs).safetyEscape 0 h).1

/-- A recovery escape `some 0` is rejected. -/
theorem recoveryEscape_zero_rejected (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    {c : Capability} {s : CapSpec ProgressReq K.Idx} {R : RecoverySpec ProgressReq K.Idx}
    (hs : K.spec c = some s) (hR : s.recovery = some R) (h : R.escape = some 0) :
    ¬ ShapeClaims F K := fun hc =>
  lt_irrefl _ (((hc.wf.caps c s hs).recovery R hR).2 0 h).1

/-- An accountable fraction `some 0` is rejected. -/
theorem accountable_zero_rejected (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    {c : Capability} {s : CapSpec ProgressReq K.Idx} (hs : K.spec c = some s)
    (h : s.accountable = some 0) : ¬ ShapeClaims F K := fun hc =>
  lt_irrefl _ ((hc.wf.caps c s hs).accountable 0 h).1

/-- A resilient capability without a recovery spec is rejected. -/
theorem resilient_without_recovery_rejected (F : ShapeFamily O Info)
    (K : Contract O ProgressReq) {s : CapSpec ProgressReq K.Idx}
    (hs : K.spec .resilient = some s) (hr : s.recovery = none) : ¬ ShapeClaims F K := fun hc => by
  have := (hc.complete _ s hs rfl).2
  simp [hr] at this

/-- A liveness premise without `sync` is rejected (D-20). -/
theorem noSync_live_rejected (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    {c : Capability} {s : CapSpec ProgressReq K.Idx} (hs : K.spec c = some s) (i : K.Idx)
    (h : ¬ (s.live.premise i).HasSync) : ¬ ShapeClaims F K := fun hc =>
  h (hc.liveSync c s hs i).1

/-- A recovery premise without `sync` is rejected (D-20). -/
theorem noSync_recovery_rejected (F : ShapeFamily O Info) (K : Contract O ProgressReq)
    {c : Capability} {s : CapSpec ProgressReq K.Idx} {R : RecoverySpec ProgressReq K.Idx}
    (hs : K.spec c = some s) (hR : s.recovery = some R) (i : K.Idx)
    (h : ¬ (R.premise i).HasSync) : ¬ ShapeClaims F K := fun hc =>
  h ((hc.liveSync c s hs i).2 R hR)

/-- The rejections have teeth: full participation alone (no `sync`) is such a
premise, while the sleepy model has `sync`. -/
example : ¬ (Premise.always .full : Premise ProgressReq).HasSync := id
example : (Premise.sleepy (1 / 2) : Premise ProgressReq).HasSync :=
  Or.inr (Or.inl trivial)

/-- Credential forgery (layer-1 form): a delivered object containing a
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

/-- The structural fields do not reject the real value: every well-formed
Goldilocks contract has positive catch-up, provides exactly what it
specifies, has its mandatory parts, and has `sync` in every liveness and
recovery premise. -/
theorem goldilocks_structural (P : GoldilocksParams) (hP : P.WellFormed) :
    0 < (goldilocksContract P).catchUp ∧
      (∀ c, (goldilocksSchema.output c).isSome = ((goldilocksContract P).spec c).isSome) ∧
      (∀ c s, (goldilocksContract P).spec c = some s → s.Complete c) ∧
      (∀ c s, (goldilocksContract P).spec c = some s → ∀ i, (s.live.premise i).HasSync ∧
        ∀ R, s.recovery = some R → (R.premise i).HasSync) := by
  have hrec : ∀ k, (P.recoveryPremise k).HasSync := fun _ => Or.inl trivial
  have hlive : ∀ k, (P.livePremise k).HasSync := fun _ => Or.inl (Or.inr (Or.inl trivial))
  refine ⟨hP.catchUp_pos, fun c => by cases c <;> rfl, fun c s h => ?_, fun c s h i => ?_⟩
  · cases c <;> obtain rfl := Option.some.inj h <;> intro hc <;> first | exact ⟨rfl, rfl⟩ | cases hc
  · cases c <;> obtain rfl := Option.some.inj h
    · exact ⟨hlive i, fun R hR => by cases hR; exact hrec i⟩
    · exact ⟨hlive i, fun R hR => by cases hR; exact hrec i⟩
    · exact ⟨Or.inl (hrec i), fun R hR => nomatch hR⟩

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
def noService (resilient : Bool) : OutputSchema :=
  ⟨Unit, fun c => if resilient ∧ c = .resilient then some () else none⟩

/-- An instance without a ledger service is never accepted (`Accepted.serves`),
even though its `ShapeClaims` and `Contract.Realizable` may hold vacuously. -/
theorem noService_not_accepted (b : Bool) (F : ShapeFamily (noService b) Info)
    (K : Contract (noService b) ProgressReq) : ¬ Accepted F K := by
  intro h
  rcases h.serves with h | ⟨h, -⟩ <;> simp [noService, OutputSchema.BFTCore] at h

end Consensus.Shape.Tests.Vacuity

end

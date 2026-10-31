module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Evidence
public import ConsensusLean.Spec.Shape.Claims

public section

/-! # R.7/R.8 engine transport skeleton

Paper references are CLAIMS `goldilocks-claims.tex` R.7, R.8, F.2/F.3 and G1.5,
and SPEC `shared/composition.tex` §Blocks/§Model, pinned in
`docs/goldilocks-mapping.md` §Refinement. Open leaves below separate structural chains,
observed objects, evidence binding and validator counts. They are not completed proofs.

**NO PAPER PROOF** for the unproved implementation bridges in this file: the cited paper
arguments establish the node-level source theorems, not the engine encoding, event-cut, or
cardinality transport. The docstrings identify the intended reduction, not a certified proof.

The current `NoCollTransport` and `FinalizedAccountable` interfaces still carry raw
`GenesisFresh`. It cannot be inferred from arbitrary engine hashes. The encoding owner must
replace that obligation before these endpoints can discharge unconditional Accepted claims.
No theorem here asserts raw freshness or silently adds it to Accepted. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- CLAIMS R.8/F.2: a valid node output has a parent-closed chain with strictly increasing
slots and digest-correct roots. The canonical header walk transports these to `Linked` and
`PosIncreasing`; `held_in_view` supplies the signed proposal provenance. The confirmed read
uses the shape's clock, not the time of the next simulating cut. No collision escape. -/
theorem engine_outputValid (hv : rho.ExecutionValid) (g : Out) : OutputValid rho g := by
  sorry

/-- CLAIMS R.8/C0.1: instantiate engine simulation, then transport node nesting through
`outputs_nested`. The empty-validator case has no readers. No collision escape. -/
theorem engine_nested (hv : rho.ExecutionValid) :
    (chainTrace rho).Nested .finalized .confirmed := by
  sorry

/-- CLAIMS R.8/C0.2: simulation's monotone cut map and `finalized_monotone` transport the
durable finalized chain across ticks, deliveries and restarts. No collision escape. -/
theorem engine_finalMonotone (hv : rho.ExecutionValid) :
    (chainTrace rho).Monotone .finalized 0 := by
  sorry

variable (V) in
/-- CLAIMS F.3/§Premises, SPEC §Blocks: each occurring block's header is observed; equal
non-genesis digests reduce to equal observed headers and the encoding is injective. Genesis
is handled separately. This is the CURRENT interface, pending the tagged-root repair. -/
theorem noCollTransport : NoCollTransport V S := by
  sorry

/-- CLAIMS R.7/G1.3–G1.5: compatibility of honest node tips gives structural compatibility
of their header chains. Parent closure and coherent honest blocks identify the ancestor walk
in either store, even when the readers hold different supersets. -/
theorem compatible_reads (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {u v : V} (hu : u ∈ rho.honest) (hv' : v ∈ rho.honest) {i j : Nat}
    (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length)
    (hc : Compatible ((simTrace S rho hn).HonestBlocks (honestKeys S rho))
      ((simTrace S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i))
      ((simTrace S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j))) :
    Consensus.Compatible ((chainTrace rho).read .finalized u i)
      ((chainTrace rho).read .finalized v j) := by
  sorry

omit [DecidableEq V] in
/-- CLAIMS G1.5's validator-count step. NO PAPER PROOF for the engine encoding bridge:
`conflicts_iff` gives E1/E2 on the two canonical attestation objects; their signed poll keys
are transported by `rho.key`. Its injectivity preserves distinct witnesses in the count. -/
theorem convicted_count {A : Set (Model.protoOf (compiled (family S)) E).Object}
    (W : Finset (Fin (Fintype.card V)))
    (hw : ∀ k ∈ W, ∃ a b : FG.Att (Fintype.card V),
      attObj a ∈ A ∧ attObj b ∈ A ∧ a.val = k ∧ FG.slashable a b) :
    W.card ≤ (convicted rho.Slashable A).card := by
  sorry

/-- CLAIMS R.7/G1.5: bind every witness attestation on the TWO HELD CHAINS from
`Regimes.final_accountable` via `held_att_in_view`; `conflicts_iff` converts slashability,
and the run's key equivalence preserves the number of distinct convicted validators. -/
theorem final_accountable_of_noColl (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {u v : V} (hu : u ∈ rho.honest) (hv' : v ∈ rho.honest) {i j : Nat}
    (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length) :
    Consensus.Compatible ((chainTrace rho).read .finalized u i)
        ((chainTrace rho).read .finalized v j) ∨
      2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V ≤
        (convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card := by
  sorry

variable (V) in
/-- CLAIMS Refinement G1.5 (c), R.7: assemble simulation, collision transport, structural
compatibility and held-chain evidence/count transport. Current raw-freshness interface only;
the encoding repair is required to remove that extra premise from the Accepted route. -/
theorem finalizedAccountable : FinalizedAccountable V S := by
  sorry

section Claims

variable (V)

/-- R.8 output validity, exact first `ShapeClaimsAt` field. NO PAPER PROOF for the engine
bridge: instantiate `engine_outputValid` at every provided capability/output and valid run.
No nonempty-validator premise and no hash-collision escape. -/
theorem shape_outputValid : (Sys (family S) V).HoldsAlways
    (fun r => ∀ c g, schema.output c = some g → OutputValid r.2 g) := by
  sorry

/-- R.8 nesting, exact second `ShapeClaimsAt` field. NO PAPER PROOF for the engine bridge:
the schema aliases available/stable to confirmed and maps final to finalized; the only
strict-rank nontrivial pair is finalized-prefix-confirmed (`engine_nested`). -/
theorem shape_nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
      (Sys (family S) V).HoldsAlways (fun r => (chainTrace r.2).Nested g₁ g₂) := by
  sorry

/-- R.8 final monotonicity, exact third `ShapeClaimsAt` field. NO PAPER PROOF for the
engine bridge: identify the schema's final output and apply `engine_finalMonotone`. -/
theorem shape_finalMonotone : ∀ g, schema.output .final = some g →
    (Sys (family S) V).HoldsAlways (fun r => (chainTrace r.2).Monotone g 0) := by
  sorry

/-- R.7/G1.1/G1.5, exact fourth `ShapeClaimsAt` field for any contract with `α ≤ 1/3`.
NO PAPER PROOF for the engine bridge: `q = ceil(2n/3)` gives `n/3 ≤ 2q−n`, and key
equivalence preserves conviction counts. Only this field permits the collision escape.
ENCODING BLOCKER: raw `GenesisFresh` cannot be derived; the tagged-root repair is required.
This endpoint intentionally has no freshness premise, including for the empty validator set. -/
theorem shape_finalAccountable (K : Contract ProgressReq) (hα : K.params.α ≤ 1 / 3) :
    ∀ g, schema.output .final = some g → (Sys (family S) V).Holds (fun _ => True)
      (fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0) := by
  sorry

end Claims

end Consensus.Goldilocks.Refinement

end

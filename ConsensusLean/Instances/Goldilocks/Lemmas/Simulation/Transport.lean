module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Evidence
public import ConsensusLean.Spec.Shape.Claims
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.BlockView
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # R.7/R.8 engine transport

Paper references are CLAIMS `goldilocks-claims.tex` R.7, R.8, F.2/F.3 and G1.5,
and SPEC `specs/goldilocks/tex/shared/composition.tex` §Blocks/§Model, pinned in
`docs/goldilocks-mapping.md` §"AsChainShape, Simulation and Obligations". The proofs separate
structural chains, observed objects, evidence binding and validator counts.

The cited paper establishes the node-level source theorems. The docstrings below supply
separate mathematical arguments for the engine bridges, not quotations.

Collision transport (`noCollRun_simTrace`) targets the canonical trace. `GenesisFresh` is
proved by tagged roots, not assumed. Canonical occurrence coverage includes refused deliveries;
tagging and observed-header injectivity discharge collision transport. The validator count of
G1.5 (`convicted_count`) needs no run premise. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- CLAIMS F.3/§Premises, SPEC §Blocks: each occurring block's header is observed; equal
non-genesis digests reduce to equal observed headers and the encoding is injective. Genesis
is handled separately.

Paper argument: `occurring_in_view` proves that EVERY block in the canonical trace's `Occurs`
has an observed canonical header and a nonempty parent (including REFUSED block calls,
not just held blocks).
For two such blocks, equal `dgOf` values are equal header hashes; absence of `HashCollision`
gives equal headers. Apply `parentRoot_parentRef` to the nonempty parents and decode the
equal `encodeInfo` values to recover all five fields required by `NoCollOn`. Proposer identity
is irrelevant: that conclusion does not compare proposers. For genesis versus a non-genesis
block, `GenesisFresh` excludes equal digests; two genesis entries are immediate.
`Occurs` has no honesty guard, but `simTrace_cut` identifies its engine event;
`ExecutionValid.honest_only` then proves that its node is honest. No separate non-honest
canonical call case remains in a valid run. Tick provenance uses `tick_releases` for
either acceptance flag. For deliveries, `mem_deliverRecs_exec` retains decoded-object
membership in the delivered list, including refused calls. The received object's containment
then places the canonical block object in the final engine view without acceptance or relay.
The target no longer quantifies arbitrary simulation witnesses, whose laws do not supply
this provenance.
Tagged freshness holds because tagged roots differ from genesis (`taggedRoot_ne`); it does not by
itself prove occurrence coverage. -/
theorem noCollRun_simTrace {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (hnc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf { S with vote := stock } rho)
      (simTrace { S with vote := stock } rho hn) := by
  refine noCollRun_of_observed { S with vote := stock } rho hn hnc fun B hB => ?_
  obtain ⟨hp, v, hv', hb⟩ := occurring_in_view S rho hn hf hv hB
  exact ⟨hp, blockObj _ B, ⟨v, rho.events.length, le_rfl,
    (rho.point.honestAt_iff_zero hf v _).mpr hv', hb⟩, rfl⟩

omit [DecidableEq V] in
/-- CLAIMS G1.5's validator-count step:
`conflicts_iff` gives E1/E2 on the two canonical attestation objects; their signed poll keys
are transported by `rho.key`. Its injectivity preserves distinct witnesses in the count.

Paper argument: for each `k ∈ W`, take its witnesses a,b. `slashable a b` includes
`a.val = b.val`; with `a.val = k`, both canonical objects have signer `rho.key k`.
`conflicts_iff` makes their conflict test true, so `rho.Slashable A (rho.key k)` holds.
Thus the finset image of W under the equivalence `rho.key` is contained in `convicted ... A`.
Injectivity gives image cardinality `W.card`; finset cardinal monotonicity gives the bound.
No execution validity, honesty, collision freedom or nonempty-V premise is needed.
Status: proved directly from definitions. -/
theorem convicted_count {A : Set (Model.protoOf (compiled (goldilocks S)) E).Object}
    (W : Finset (Fin (Fintype.card V)))
    (hw : ∀ k ∈ W, ∃ a b : FG.Att (Fintype.card V),
      attObj a ∈ A ∧ attObj b ∈ A ∧ a.val = k ∧ FG.slashable a b) :
    W.card ≤ (convicted rho.Slashable A).card := by
  classical
  have hsub : W.image rho.key ⊆ convicted rho.Slashable A := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, b, ha, hb, hak, hab⟩ := hw k hk
    have hbk : b.val = k := hab.1.symm.trans hak
    simp only [convicted, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨attObj a, ha, attObj b, hb, ?_, ?_, ?_⟩
    · simp [Model.Run.signerOf, attObj, Model.Obj.signer?, Model.Obj.auth, hak]
    · simp [Model.Run.signerOf, attObj, Model.Obj.signer?, Model.Obj.auth, hbk]
    · exact (conflictsIff_iff.mp conflicts_iff S.vote _ _ _).mpr ⟨a, b, rfl, rfl, hab⟩
  simpa only [Finset.card_image_of_injective W rho.key.injective] using
    Finset.card_le_card hsub

end Consensus.Goldilocks.Simulation

end

module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement

public section

/-! # Goldilocks Refinement: the shape's pure steps

The obligations on the Goldilocks shape (`Refinement/Defs`) that involve no run: the canonical
objects decode back to what they encode, so a delivered canonical object is the node's event
(`canonEvent`); the slashing rule is E1/E2 (`ConflictsIff`); the engine's own-object guard
`protects` passes every block and vote (only two attestation objects ever `conflict`).

Each theorem is a named step; the `sorry` ones are open. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ## Decoding the canonical objects -/

/-- **`decodeBlock` round-trip.** The canonical object of a non-genesis block whose header the
engine's digests map to its root, with well-formed attestations and a valid AC payload, decodes
to the block. -/
theorem decodeBlock_blockObj (hs : List (Header Info × Nat)) (B : Blk sp)
    (hpar : B.parent ≠ none) (hroot : rootOf hs (headerOf sp B) = some B.root)
    (hwf : ∀ a ∈ B.fgPayload, a.WellFormed) (hval : SA.validPayload B) :
    decodeBlock sp hs (blockObj sp B) = some B := by
  sorry

/-- The canonical object of such a block stands for the node's `block` event. -/
theorem canonEvent_blockObj (hs : List (Header Info × Nat)) (B : Blk sp)
    (hpar : B.parent ≠ none) (hroot : rootOf hs (headerOf sp B) = some B.root)
    (hwf : ∀ a ∈ B.fgPayload, a.WellFormed) (hval : SA.validPayload B) :
    canonEvent sp ro hs (blockObj sp B) = some (.block B) := by
  sorry

/-- The canonical object of a vote stands for the node's `message` event. -/
theorem canonEvent_voteObj (hs : List (Header Info × Nat)) (v : Vote sp.n) :
    canonEvent sp ro hs (voteObj v) = some (.message v) := by
  sorry

/-- The canonical object of a well-formed attestation stands for the node's `attestation`
event. -/
theorem canonEvent_attObj (hs : List (Header Info × Nat)) (a : FG.Att sp.n)
    (hwf : a.WellFormed) : canonEvent sp ro hs (attObj a) = some (.attestation a) := by
  sorry

/-! ## The slashing rule and the own-object guard -/

/-- **G1.5 (a).** `conflicts` holds of two objects exactly when they are the canonical objects
of two `slashable` attestations. -/
theorem conflicts_iff : ConflictsIff := by
  sorry

/-- `conflicts` is false unless both objects are attestation data signed in the poll role. -/
theorem conflicts_eq_false_of_not_att {n : Nat} (o o' : Wire n)
    (h : ∀ k w, o ≠ .mk (.signed k .poll) (.data (.att w)) []) : conflicts o o' = false := by
  sorry

/-- The engine's own-object guard never blocks a block object: `protects` is true of `blockObj`
against any seen list. -/
theorem protects_blockObj {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (k : Fin (Fintype.card V))
    (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (B : Blk (S.params (Model.pubOf E) hn)) :
    Model.protects (Model.protoOf (compiled (family S)) E) k seen
      (blockObj (S.params (Model.pubOf E) hn) B) = true := by
  sorry

/-- The engine's own-object guard never blocks a vote object. -/
theorem protects_voteObj {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (k : Fin (Fintype.card V)) (seen : List (Model.protoOf (compiled (family S)) E).Object)
    (v : Vote (Fintype.card V)) :
    Model.protects (Model.protoOf (compiled (family S)) E) k seen (voteObj v) = true := by
  sorry

end Consensus.Goldilocks.Refinement

end

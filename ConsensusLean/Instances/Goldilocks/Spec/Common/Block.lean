module
public import ConsensusLean.Init

@[expose] public section

/-! # Goldilocks: blocks

A block of the Goldilocks node (`specs/goldilocks/tex/shared/composition.tex`
§"Blocks"): root, parent (named by root; genesis has none), slot, proposer, the FG payload,
the AC payload and the input, the encoded transactions the engine writes into every header
(`Consensus.Blocks.Header.input`): the spec folds it into the AC payload ("the AC
fixes the encoding of its payload"), the Lean keeps it as its own field so that the engine's
header, hashed with its input, is a block of this type (the refinement, `docs/decisions.md`
§"Goldilocks model choices"). No handler reads it.
The block is parametric in both payload types (`FGP`, `ACP`), so that the AC side never names
the FG's attestations and the FG side never names the AC's payload; the node instantiates
`FGP := List (FG.Att n)`. The order and the repeats of each payload are part of the block.

The root is the fixed digest of `(parent root, slot, input, FG payload, AC payload)`; the
collision-freedom of the digest is a hypothesis where a statement needs it (claims F.3), never an
axiom.

This module holds only what the Challenge statements reach; the digest `Digest` and `Block.RootOk`
are in `Milestones/Spec/Common/Block` (`docs/decisions.md`
§"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks

/-- A block with FG payload type `FGP` and AC payload type `ACP`, among `n` validators. -/
structure Block (n : Nat) (FGP ACP : Type) where
  /-- The root of the block. -/
  root : Nat
  /-- The root of the parent; `none` for genesis, which has no parent. -/
  parent : Option Nat
  /-- The slot of the block. -/
  slot : Nat
  /-- The proposer index. -/
  proposer : Fin n
  /-- The input: the encoded transactions (the engine's header field; part of the AC payload in
  the spec's reading, never read by a handler). -/
  input : Nat
  /-- The FG payload (for the node: the attestation list). -/
  fgPayload : FGP
  /-- The AC payload. -/
  acPayload : ACP

end Consensus.Goldilocks

end

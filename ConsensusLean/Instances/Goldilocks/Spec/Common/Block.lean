module
public import ConsensusLean.Init

@[expose] public section

/-! # Goldilocks: blocks

A block of the Goldilocks node (fradamt-agent/goldilocks `spec/shared/composition.tex`
§"Blocks"): root, parent (named by root; genesis has none), slot, proposer, the FG payload,
the AC payload and the input, the encoded transactions the engine writes into every header
(`Consensus.Blocks.Header.input`): the spec folds it into the AC payload ("the AC
fixes the encoding of its payload"), the Lean keeps it as its own field so that the engine's
header, hashed with its input, is a block of this type (the refinement, `docs/decisions.md`
§"Goldilocks instance"). No handler reads it.
The block is parametric in both payload types (`FGP`, `ACP`), so that the AC side never names
the FG's attestations and the FG side never names the AC's payload; the node instantiates
`FGP := List (FG.Att n)`. The order and the repeats of each payload are part of the block.

The root is the fixed digest of `(parent root, slot, input, FG payload, AC payload)`; `Block.RootOk`
says that a block's root is that digest (the wire check), and the collision-freedom of the
digest is a hypothesis where a statement needs it (claims F.3), never an axiom. -/

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

/-- A block digest: the root of the content `(parent root, slot, input, FG payload, AC
payload)`. -/
abbrev Digest (FGP ACP : Type) := Option Nat → Nat → Nat → FGP → ACP → Nat

/-- The root of `B` is the digest of its content (composition.tex §"Blocks": `B.root` is the
fixed digest of `(B.parent.root, B.slot, B.attestations, B.acp)`, the input inside `B.acp`). -/
def Block.RootOk {n : Nat} {FGP ACP : Type} (dg : Digest FGP ACP) (B : Block n FGP ACP) : Prop :=
  B.root = dg B.parent B.slot B.input B.fgPayload B.acPayload

end Consensus.Goldilocks

end

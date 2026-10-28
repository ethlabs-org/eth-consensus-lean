module
public import ConsensusBlocks.Chains
public import ConsensusProblem.Basic

@[expose] public section

/-! # Payload (building block)

The engine encodes a list of transactions into a header's `input`
(`encodeTxs`); a chain's ledger is the concatenation of the decoded inputs,
keeping the first occurrence of each transaction (`ledgerOf`, core
`List.eraseDups`). `ledgerOf` is monotone under prefixes (`ledgerOf_prefix`,
`Facts`), which carries chain-level safety, nesting and monotonicity to
ledgers. -/

namespace Consensus.Blocks

/-- Encode a list of transactions as a natural number. -/
def encodeTxs (xs : List Tx) : Nat := Encodable.encode xs

/-- Decode a header input; an invalid code decodes to no transactions. -/
def decodeTxs (n : Nat) : List Tx := (Encodable.decode n).getD []

/-- The ledger of a chain: the decoded inputs in chain order, first occurrence
of each transaction kept. -/
def ledgerOf {Info : Type} (c : Chain Info) : Ledger :=
  (c.flatMap (decodeTxs ∘ Header.input)).eraseDups

end Consensus.Blocks
end

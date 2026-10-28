module
public import ConsensusBlocks.Chains
public import ConsensusProblem.Basic

@[expose] public section

/-! # Payload (building block)

The engine encodes a list of transactions into a header's `input`
(`encodeTxs`); a chain's ledger is the concatenation of the decoded inputs,
keeping the first occurrence of each transaction (`ledgerOf`). `ledgerOf` is
monotone under prefixes, which carries chain-level safety, nesting and
monotonicity to ledgers. -/

namespace Consensus.Blocks

/-- Encode a list of transactions as a natural number. -/
def encodeTxs (xs : List Tx) : Nat := Encodable.encode xs

/-- Decode a header input; an invalid code decodes to no transactions. -/
def decodeTxs (n : Nat) : List Tx := (Encodable.decode n).getD []

@[simp] theorem decode_encodeTxs (xs : List Tx) : decodeTxs (encodeTxs xs) = xs := by
  simp [decodeTxs, encodeTxs]

/-- Keep the first occurrence of each element not in `seen`, in order. -/
def keepFresh (seen : List Tx) : List Tx → List Tx
  | [] => []
  | x :: xs => if x ∈ seen then keepFresh seen xs else x :: keepFresh (x :: seen) xs

/-- Keep the first occurrence of each element, in order. -/
def keepFirst (xs : List Tx) : List Tx := keepFresh [] xs

theorem keepFresh_append (seen xs ys : List Tx) :
    ∃ zs, keepFresh seen (xs ++ ys) = keepFresh seen xs ++ zs := by
  induction xs generalizing seen with
  | nil => exact ⟨keepFresh seen ys, rfl⟩
  | cons x xs ih =>
    simp only [List.cons_append, keepFresh]
    split
    · exact ih seen
    · obtain ⟨zs, hz⟩ := ih (x :: seen)
      exact ⟨zs, by rw [hz]; rfl⟩

theorem mem_keepFresh (x : Tx) (seen xs : List Tx) :
    x ∈ keepFresh seen xs ↔ x ∈ xs ∧ x ∉ seen := by
  classical
  induction xs generalizing seen with
  | nil => simp [keepFresh]
  | cons y ys ih =>
    simp only [keepFresh]
    by_cases hxy : x = y
    · subst y; by_cases hx : x ∈ seen <;> simp [hx, ih]
    · by_cases hy : y ∈ seen <;> simp [hy, ih, hxy]

theorem keepFirst_prefix {xs ys : List Tx} (h : xs <+: ys) :
    keepFirst xs <+: keepFirst ys := by
  obtain ⟨zs, rfl⟩ := h
  obtain ⟨ws, hw⟩ := keepFresh_append [] xs zs
  exact ⟨ws, hw.symm⟩

variable {Info : Type}

/-- The ledger of a chain: the decoded inputs in chain order, first occurrence
of each transaction kept. -/
def ledgerOf (c : Chain Info) : Ledger := keepFirst (c.flatMap (decodeTxs ∘ Header.input))

/-- `ledgerOf` is monotone under prefixes. -/
theorem ledgerOf_prefix {c d : Chain Info} (h : c <+: d) : ledgerOf c <+: ledgerOf d := by
  obtain ⟨es, rfl⟩ := h
  apply keepFirst_prefix
  exact ⟨es.flatMap (decodeTxs ∘ Header.input), by simp⟩

@[simp] theorem mem_ledgerOf (x : Tx) (c : Chain Info) :
    x ∈ ledgerOf c ↔ ∃ h ∈ c, x ∈ decodeTxs h.input := by
  simp [ledgerOf, keepFirst, mem_keepFresh, List.mem_flatMap, Function.comp_def]

/-- Compatible chains have compatible ledgers. -/
theorem compatible_ledgerOf {c d : Chain Info} (h : Compatible c d) :
    Compatible (ledgerOf c) (ledgerOf d) :=
  h.imp ledgerOf_prefix ledgerOf_prefix

end Consensus.Blocks
end

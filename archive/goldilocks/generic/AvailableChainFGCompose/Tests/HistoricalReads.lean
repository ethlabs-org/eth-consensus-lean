module
public import AvailableChainFGCompose.Proofs.HistoricalReads -- shake: keep (axioms)

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.HistoricalReads

private def p0c4_parent : Block := .node .genesis 1 ⟨1⟩ 5
private def p0c4_body : Block × Nat := (.node p0c4_parent 7 ⟨2⟩ 42, 101)
private def p0c4_alias : Block × Nat := (.node .genesis 7 ⟨2⟩ 99, 202)
private def p0c4_root (b : Block × Nat) : BlockId := b.1.root

/-- Exact payload, parent and original carrier label are returned. -/
private theorem p0c4_exact_full_body :
    historicalLookup p0c4_root [(.genesis, 0), (p0c4_parent, 5), p0c4_body] ⟨2⟩ =
      some p0c4_body ∧ p0c4_body.1.parent = p0c4_parent ∧
      p0c4_body.1.slot = 7 ∧ p0c4_body.2 = 101 := by decide +kernel

/-- Distinct full content at one root must remain unresolved. -/
private theorem p0c4_ambiguous_domain :
    p0c4_body ≠ p0c4_alias ∧ p0c4_root p0c4_body = p0c4_root p0c4_alias ∧
      historicalLookup p0c4_root [p0c4_body, p0c4_alias] ⟨2⟩ = none := by decide +kernel

private theorem p0c4_missing_and_repeated :
    historicalLookup p0c4_root [p0c4_body] ⟨99⟩ = none ∧
      historicalLookup p0c4_root [p0c4_body, p0c4_body] ⟨2⟩ = some p0c4_body := by
  decide +kernel

/-- A filter changes the active list, never the domain passed to lookup. -/
private theorem p0c4_ambiguity_after_any_filter (active : (Block × Nat) → Bool) :
    ([p0c4_body, p0c4_alias].filter active).length ≤ 2 ∧
      historicalLookup p0c4_root [p0c4_body, p0c4_alias] ⟨2⟩ = none :=
  ⟨List.length_filter_le _ _, p0c4_ambiguous_domain.2.2⟩

/-- Retained membership alone cannot imply lookup stability after a step. -/
private theorem p0c4_later_uniqueness_necessary :
    (∀ b ∈ [p0c4_body], b ∈ [p0c4_body, p0c4_alias]) ∧
      historicalLookup p0c4_root [p0c4_body] ⟨2⟩ = some p0c4_body ∧
      historicalLookup p0c4_root [p0c4_body, p0c4_alias] ⟨2⟩ ≠ some p0c4_body ∧
      ¬ (∀ b ∈ [p0c4_body, p0c4_alias], ∀ c ∈ [p0c4_body, p0c4_alias],
        p0c4_root b = p0c4_root c → b = c) := by decide +kernel

/-- Equal erased geometry does not identify two full bodies. -/
private theorem p0c4_same_geometry_different_payload :
    historicalLookup p0c4_root [p0c4_body, (p0c4_body.1, 102)] ⟨2⟩ = none := by
  decide +kernel

#print axioms p0c4_exact_full_body
#print axioms p0c4_ambiguous_domain
#print axioms p0c4_missing_and_repeated
#print axioms p0c4_ambiguity_after_any_filter
#print axioms p0c4_later_uniqueness_necessary
#print axioms p0c4_same_geometry_different_payload

end AvailableChain.FGCompose.Tests.HistoricalReads
end

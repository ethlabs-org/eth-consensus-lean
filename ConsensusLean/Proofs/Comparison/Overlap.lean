module
public import ConsensusLean.Comparison.Overlap

public section

/-! # Frontier lemmas: proofs of the overlap lemmas

If the heal point were at or before `t`, safety from it would make the divergent read (cut `j`, at
`t`) compatible with the target's ready read at the end of `t′` (its cut is at `t′ ≥ t`); protection
makes that read extend the source read, so the source read and the divergent read would be
compatible. In the two-run version the target's read and readiness carry over from `r₁` to `r₂`
by the common observation. -/

namespace Consensus.Comparison

/-- A prefix of `y` is compatible with every list compatible with `y`. -/
private theorem compatible_of_prefix {α : Type} {x y z : List α} (hxy : x <+: y)
    (hzy : Compatible z y) : Compatible x z := by
  rcases hzy with h | h
  · exact List.prefix_or_prefix_of_prefix hxy h
  · exact Or.inl (hxy.trans h)

/-- Safety from `h₀ ≤ t` makes the read at cut `j` of time `t` of a reader ready then compatible
with the end-of-`t′` read of a reader ready at `t′ ≥ t`, when `t′` is the time of that cut. -/
private theorem compatible_of_readySafe {V α Id : Type} {tr : Trace V α Id} {c h₀ : Time} {g : Id}
    (hs : tr.ReadySafe c g h₀) {u w : V} {j : ℕ} {t t' : Time} (hj : j ≤ tr.cuts)
    (htj : tr.cutTime j = t) (hu : tr.point.Ready c u t) (htt' : t ≤ t')
    (hw : tr.point.Ready c w t') (hcut : tr.cutTime (tr.endCut t') = t') (hh : h₀ ≤ t) :
    Compatible (tr.read g u j) (tr.readAt g w t') := by
  subst htj
  refine hs.1 u w j (tr.endCut t') ⟨hj, hh⟩ ⟨Nat.findGreatest_le _, ?_⟩ hu ?_
  · rw [hcut]; exact hh.trans htt'
  · rw [hcut]; exact hw

theorem overlap_two_run : OverlapTwoRun := by
  intro V S r₁ r₂ c₁ c₂ src dst T t₀ b₁ k v u w j t t' hprot hv hs hj htj hu hdiv ht₀ htt' hth
    hw hobs hcut
  refine lt_of_not_ge fun hh => hdiv (compatible_of_prefix (hprot v hv t' ht₀ hth w hw) ?_)
  rw [hobs.1 dst t' le_rfl]
  exact compatible_of_readySafe hs hj htj hu htt' ((hobs.2 t' le_rfl).mp hw) hcut hh

theorem overlap_same_run : OverlapSameRun :=
  fun V S r c src dst T t₀ b₁ k v u w j t t' hprot hs hv hj htj hu hdiv ht₀ htt' hth hw hcut =>
    overlap_two_run V S r r c c src dst T t₀ b₁ k v u w j t t' hprot hv hs hj htj hu hdiv ht₀ htt'
      hth hw ⟨fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩ hcut

end Consensus.Comparison

end

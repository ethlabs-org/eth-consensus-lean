module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Boundary

public section

/-! # Slice 1 coverage for chain shapes (proofs)

* `shapeHealDomainCoverage`: the Slice 1 witness run (`cov1_witness`) at every point of the
  coverage domain with a finite claim.
* `shapeHealBoundaryCoverage`: at a point of class `any`, the same witness, which attains every
  environment parameter (the class `any` needs no exercise); at a split class (held or not), the
  exercised witness (`cov1_split_witness`). -/

namespace Consensus.Comparison

theorem shapeHealDomainCoverage : ShapeHealDomainCoverage := by
  intro O Info _ _ F K V _ _ hf hfg cap i hs hl lat ho hsup
  refine ⟨fun q hq hfin => ⟨ho, ?_⟩⟩
  obtain ⟨hadm, hforge⟩ := hsup q hq hfin
  obtain ⟨r, b₀, b₁, hv, hne, hcl, hpr, -, hsa, hla⟩ :=
    cov1_witness F K hf hfg cap i q hq hadm hforge (hs q) (hl q) (lat q)
  exact ⟨r, b₀, b₁, hv, hne, hcl, hpr, hsa, hla⟩

theorem shapeHealBoundaryCoverage : ShapeHealBoundaryCoverage := by
  intro O Info _ _ F K V _ _ hcl hf hnfg hfg cap i hs hl lat ho hsup
  refine ⟨fun q hq hfin => ⟨ho, ?_⟩⟩
  obtain ⟨hadm, hforge⟩ := hsup.1 q hq hfin
  have hβ := hsup.2 q hq hfin
  rcases q with ⟨L, hpre, hpost, m, fcap, a, θ, catchUp⟩
  cases a with
  | any =>
    obtain ⟨r, b₀, b₁, hv, hne, hc, hpr, hcore, hsa, hla⟩ :=
      cov1_witness F K hf hfg cap i _ hq hadm hforge (hs _) (hl _) (lat _)
    exact ⟨r, b₀, b₁, hv, hne, hc, hpr, attains_of_core hcore trivial, hsa, hla⟩
  | split G =>
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ho
    exact cov1_split_witness F K hcl hf hnfg hfg cap i g hg _ hq trivial hadm hforge
      (hβ trivial) (hs _) (hl _) (lat _)
  | splitHeld G =>
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ho
    exact cov1_split_witness F K hcl hf hnfg hfg cap i g hg _ hq trivial hadm hforge
      (hβ trivial) (hs _) (hl _) (lat _)

end Consensus.Comparison

end

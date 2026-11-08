module
public import ConsensusLean.Proofs.ComparisonCoverage.Witness

public section

/-! # Slice 0 coverage for chain shapes (proofs)

* `shapeTxLatencyCoverage0`, `shapeProposalLatencyCoverage0`: the synchronous canonical run at the
  witness point (`sync_witness`) with exactly `f` validators compromised.
* `shapeHealCoverage0`: at a point of class `any`, the synchronous witness with the incident
  `[0, L·ΔAC)` (`healCoverage0_any`); at a point of class `split G`, the witness that holds an
  honest proposal across the groups until the incident ends (`healCoverage0_split`). -/

namespace Consensus.Comparison

open Shape

theorem shapeTxLatencyCoverage0 : ShapeTxLatencyCoverage0 :=
  fun F K _ _ _ hf cap i lat ho hsup => txLatencyCoverage0_of F K hf cap i lat ho hsup

theorem shapeProposalLatencyCoverage0 : ShapeProposalLatencyCoverage0 :=
  fun F K _ _ _ hf cap i lat ho hsup => proposalLatencyCoverage0_of F K hf cap i lat ho hsup

theorem shapeHealCoverage0 : ShapeHealCoverage0 := by
  intro O Info _ _ F K V _ _ hcl hf hnfg hfg cap i hs hl lat ho hsup
  refine ⟨fun q hq hfin => ⟨ho, ?_⟩⟩
  obtain ⟨hadm, hsplit⟩ := hsup q hq hfin
  rcases q with ⟨L, f, a⟩
  cases a with
  | any => exact healCoverage0_any F K hf hfg cap i hs hl lat L f hq.1 hadm
  | split G =>
    obtain ⟨hfn, hL, hT, hF⟩ := hq
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ho
    exact healCoverage0_split F K hcl hf hnfg hfg cap i g hg hs hl lat L f G hL hfn hT hF hadm
      hsplit

end Consensus.Comparison

end

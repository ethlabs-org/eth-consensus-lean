module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC

public section

/-! # Goldilocks Healing: H.2, AC inclusion from the retention premise

H.2 over driven AC traces of the SA with their frames, under `Healthy(g)`, `Catch(2Δ)` and
`Inv(t₀)`. The claims mark H.2 **unverified** (status M, goldilocks-claims §"Healing: top-level
statements"): its proof is H.1's (healing-simple `t1-proof.md` §§2–6) with each use of the
trivial frame replaced, and five steps are open on paper:

1. the retained-head score comparison (A1.1's pool and score part with retained heads, as HS.2);
2. ancestor-target transfer (A1.8 transfers the actual result, an ancestor needs its own score
   argument; phase-service §4);
3. proposal-boundary transfer;
4. sufficiency of `Geo(P)` for (i);
5. `Carry` when a protected block is at or below `fc_root`, and the frame's move back during the
   drain.

Interface: the proof is open. -/

namespace Consensus.Goldilocks.SA

/-- **H.2, AC inclusion from the retention premise** (open on paper: items 1–5 above). -/
theorem ac_inclusion (sp : SAParams) : ACInclusion (sp := sp) := by
  sorry

end Consensus.Goldilocks.SA

end

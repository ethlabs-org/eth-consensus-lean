module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC

public section

/-! # Goldilocks Healing: H.1, AC healing standalone (trivial frames), and its corollary

H.1 over driven AC traces of the SA with trivial frames (the frame of every honest call is the
tree of the blocks the node has accepted, rooted at genesis), under `Healthy(g)`, `Catch(2Δ)`,
`NoColl` and unforgeable signatures. Proved on paper (healing-simple `t1-proof.md` §§2–6, both
reviews in `t1-t4-reviews.md`): with `r = r_AC(ḡ)`, (§2) results of one slot `≥ r` are
compatible; (§§3–4) a fast origin of label `≥ r`, and a slow origin whose window is `≥ r`,
transfers to the next slot's honest votes and every later one (A1.2, A1.4, A1.3, A1.8); (§5) every
other lock expires before `t_r + 2Θ`; (§6) at `P` the voter's tree is contained in the
proposer's and the scores agree, so every honest slot-`p` vote is `P`, and from `t_p + 6Δ` the
record extends `P`.

The corollary is H.1 at the honest proposal that `Prop(G_p)` provides in `[t, t + G_p]`.

Interface: the proofs are open. -/

namespace Consensus.Goldilocks.SA

/-- **H.1, AC healing standalone** (T1 §§2–6). -/
theorem ac_healing_standalone (sp : SAParams) : ACHealingStandalone (sp := sp) := by
  sorry

/-- **H.1, corollary**: H.1 at an honest proposal of `Prop(G_p)`. -/
theorem ac_healing_standalone_corollary (sp : SAParams) :
    ACHealingStandaloneCorollary (sp := sp) := by
  sorry

end Consensus.Goldilocks.SA

end

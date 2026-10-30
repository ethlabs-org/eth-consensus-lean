module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction

public section

/-! # Goldilocks Healing: HR.4, height-scoped retention

(R1)–(R4) for the reset `a_z` over a Goldilocks run under `Healthy(g)` and `NoColl`. The author's
paper results (claims HR.4, status M; `producer-reset-continuation.md` §5 (R4, R5), §10, §11
(HBoot, reviewed), §13 (JointRet, reviewed), §16 (high records); healing-simple `t1-proof.md` §9
(the base case)): C1.1's first-violating-event induction over the run's cut index, with G1.10 at
the height-scoped scope (`𝓔_B` the entries of height `≥ H_z + 1` that conflict with `B`,
`T₀ = a_z − Δ`, every row signed at `a_z` covered by HR.1 (c)). It is not an instance of C1.1:
(K0) and (K1) need not hold at `a_z`.

Interface: the proof is open. -/

namespace Consensus.Goldilocks.Healing

/-- **HR.4, height-scoped retention** (HBoot §11, JointRet §13, high records §16). -/
theorem height_scoped_retention : HeightScopedRetention := by
  sorry

end Consensus.Goldilocks.Healing

end

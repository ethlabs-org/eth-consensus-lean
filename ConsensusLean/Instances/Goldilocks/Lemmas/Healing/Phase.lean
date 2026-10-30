module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

public section

/-! # Goldilocks Healing: HR.2, phase count

HR.2, an FG store node over FG traces (`FGLocalRun`) with `f < 2q − n`. Proved on paper (claims
HR.2, status S; healing-simple `t1-proof.md` §8 (F2, first part), `producer-reset-continuation.md`
§14, slides 25, 26, 30): (a) two honest accepted states with the same `h_j` have the same `J`
(G1.1, G0.5: two justifications at one height have intersecting quorums, and an honest validator
signs one target per height); (b) while the frontier `m` is fixed the effective phase moves only
forward through gap, top `J`, contest — a justification at `m − 1`, once held by an honest node,
stays held (durable stores), (a) makes its `J` unique, and a contest's witness block stays held —
so at most two changes per value of `m`.

Interface: the proof is open. -/

namespace Consensus.Goldilocks.Healing

/-- **HR.2, phase count.** -/
theorem phase_count (P : Params) (ACP : Type) : PhaseCount P ACP := by
  sorry

end Consensus.Goldilocks.Healing

end

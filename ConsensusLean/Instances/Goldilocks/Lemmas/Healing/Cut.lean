module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks Healing: HR.1, cut and reset

HR.1 over a Goldilocks run under `Healthy(g)` and `NoColl`, with `c_z = t_{slot(ḡ)+3}` and `H_z`
the greatest honest `Σ.h_max` after all events at `c_z`. Proved on paper (claims HR.1, status S;
healing-simple `t1-proof.md` §7 (F1), `producer-reset-continuation.md` §4 (R0) and §10 (the
first-time tick lemma)):
(a) an honest row signed at or before `c_z` has height `≤ Σ.h_max ≤ H_z` (the frontier only
rises); from `c_z` on, `ac_to_fg` returns the block of a fast lock written after `ḡ` (A1.5 with
`τ = ḡ`, `SA.SourceAge`, on the AC projection);
(b) the chain of a block of state height `≥ H_z + 2` carries an honest row of height `H_z + 1`
(G0.2 (f): a justification at `H_z + 1` needs `q > f` rows);
(c) at the reset `a_z`: `a_z > c_z`, no honest high row before it, the frontier at the ticks at
`a_z` is `≤ H_z + 1`, and the namers of the high entries before `a_z − Δ` stay below `q`
(first clause of (K1_𝓔) of G1.10).

Interface: the proof is open. -/

namespace Consensus.Goldilocks.Healing

/-- **HR.1, cut and reset.** -/
theorem cut_and_reset : CutAndReset := by
  sorry

end Consensus.Goldilocks.Healing

end

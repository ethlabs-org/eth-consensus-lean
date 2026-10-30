module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage

public section

/-! # Goldilocks milestone Regimes: R.5 (outage), parked

`OutageStatements` (`Statements/Regimes/Outage`) is not proved: A1.2, A1.3 and C1.1 do not reach
it, and three pieces are missing (consensus-lean#17, amp-orbs (acbase), 2026-10-30):

1. **Before `b₀`, the Sleepy invariant under the outage's participation.** R.5's reads at `T` and
   the origins they rest on need the record invariant (S1–S3) for the cuts up to `b₀` under
   `Sync[0, b₀ − Δ]` and η-sleepy participation (`EtaSleepyAt`, which gives `f <` the ready
   honest validators, so `FaultBound` once ready implies joined, F.4). This is the prefix form the
   Sleepy box is proving for `SleepySafePrefix` (`SleepyInvariantUpTo`), with the participation
   premise replaced.
2. **Through `[b₀, b₁)`, outage continuation under (V).** A confirmed read at `T` survives the
   outage through the lifetime `(4k − 2)Δ` of its lock under the budget (V) (fgsa-protocol.tex,
   "Outage continuation under (V)"). No proved node covers it: C1.1 needs `Sync[t_s, t_m + Δ]`,
   which fails in the window (the old fgsa `OutageContinuationClaim` was an assumption). Needed by
   `outageWindow` (with 1) and by `persists` and `outage_final_compatible`.
3. **After `b₁`, continuation from GST.** C1.1's premises from `b₁` on, including (K0)–(K2)
   (`Clean`): claims §C1.1, "R.3 and R.5 only once honest finality has passed the pre-GST dirt (see
   O.1)", and O.1 is an open target. Needed by `persists` and `outage_final_compatible` (which
   also needs `Σ.F` on the origin chain through the outage and after `b₁`). -/

namespace Consensus.Goldilocks.Regimes

/-- **Milestone Regimes, the outage rows (R.5)**, parked: see the module docstring for the three
missing pieces. -/
theorem outage_statements : OutageStatements := by
  sorry

end Consensus.Goldilocks.Regimes

end

## P-Cl2 — Round 2 CLOSED (2026-10-10)

Base: 502ab6b9 on sleep-pcl2b. This replaces the Round 1 PREPARED fragment.
All six owned TARGETS and the complete S1 package domain are GREEN.
No owned EXPECTED-FAIL remains. Public claim statements are unchanged.
CLOSED here covers P-Cl2 and its accepted owner handoffs; P-Ou growth is still conditional.

- P10/P11: the approved Claims/Clean definitions are unchanged. Production
  Clean/Export compiles against the closed P-Cl1 and Shared suppliers.
- Zero lane: cleanHistoryAt_zero, cleanTruncAt_zero and cleanCutZero_export
  use the compiled cleanCut_zero_body, Clean/Zero.lean:204. Impossible pre-zero
  gate origins discharge enabled/current-epoch requirements. No quorum input.
- Internal safety repair: cleanSafetyAt_of_trunc, Clean/Export.lean:107, takes
  the exact all-node state pair required by Clean/Safety.lean:25. Its former
  scoped truncation input did not match that transport. Public CleanSafetyAt
  and CleanSafetyClaim are unchanged. No all-honest output scope is added.
- cleanSafety_of_cut, Clean/Export.lean:164, takes an internal hstate callback.
  Producer: clean_sCompatible, Clean/Safety.lean:74, and sExtends,
  Clean/Closure.lean:380, under the actual Clean sleep cut. P-Fd foundation and
  source exports at Foundations/Export.lean:139/:134 discharge their inputs.
  The exact composition and consumer pass a two-command strict audit.
  O-SAFETY-WIRING and O-ZERO-TEST-WIRING belong to P-As; exact code is in the handoff.
- P7/P20: clean_growth_body, Outage/Growth.lean:21, is unchanged and GREEN.
  The recurrence produces a joined proposer with its actual restart cutoff.
  Compatibility plus no-future proves strict trigger growth. Scoped inclusion
  proves inclusion at t + G + 6 * Δ. The two reader guards remain independent.
- O-GROWTH-COMPAT, owner P-Ou: exact trigger compatibility callback at
  Outage/Growth.lean:24. GrowthConsumer.lean:14 and InclusionGateBody.lean:284
  consume actual scoped output compatibility and a confirmed gate witness.
  The complete receiver inputs and witness are not produced by this base.
- O-GROWTH-INCLUSION, owner P-Ou: exact deadline scoped inclusion callback at
  Outage/Growth.lean:30. InclusionGateBody.lean:87 and Outage/Export.lean:188
  give conditional routes. hInputs and enabled/current-epoch hScopes remain
  P-Ou obligations. A conversion or consumer is not marked as a producer.
- P-As supplies later-reader gate projection and bounded scoped monotonicity
  at Assembly/Outage.lean:20/:49. These do not close either P-Ou callback.

SCOPE-NARROW: every explicit Clean export input is listed in the Round 2 report.
Actual nodes, enabled gates, receiver epochs and the zero/positive split are retained.
The exact owner obligations above are the handoff permitted by the Round 2 close task.
No public premise, public meaning change, endpoint-reader implication or STOP.
No P-Ou, P-As, P-Cl1, Shared, facade, checker, baseline or allowance file changed.

Evidence: .lake/sleep-pcl2-r2/. Final validation counts are in the Round 2 report.
Handoff: claude-files/sleep-pcl2-pou-handoff.md, Round 2.
Apply this fragment and the existing coverage fragment in the serial integration window.

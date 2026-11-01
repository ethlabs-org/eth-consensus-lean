# FG-SA stage-4 non-vacuity plan

Base: df5ca51. Plan §1.3–§1.7 witness shapes and §5.4 checks apply.
C/ and P/ have the same meanings as in the producer map.
Every row states the witness shape, current test evidence, and remaining duty.
No test of a contract type is a proof of a LAW instance.

W1–W4 on lf-w2 use the old model and are paused until S4.6. Then the lead
assigns one Astra port of W1 to W. That lane must supply a valid, positive
execution with actual admitted carriers, honest emissions and receipts.
Stage 5 must supply the listed package and service witnesses on that execution.

S4.4a N6: no package with a horizon field has a non-vacuity witness. Horizon
0 in HealingW cannot meet its positive healing/reset bounds. FinalityW uses
horizon 512, but supplies only schedules and conditional package constructions.
S4.3 N7: the no-replay birth case can only be a raw fold. Its finality payload
at the birth height fails R3; do not count it as an admitted execution.

Witness rows: 91.

```text
┌──────────────────────────────┬────────────────────────────────────────────────────────────┬────────────────────────────────────────────────────────────┬────────────────────────────────────────────────────────────┐
│ Package / contract           │ Plan witness shape                                         │ Exists now (file:line)                                     │ Stage 5 / W lane must supply                               │
├──────────────────────────────┼────────────────────────────────────────────────────────────┼────────────────────────────────────────────────────────────┼────────────────────────────────────────────────────────────┤
│ FinalityKernelClaim_W        │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ KernelACSideClaim_W          │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ FinalityKernelJoinedClaim_W  │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ TailKernelClaim_W            │ Honest Tail_W pattern, full common HealingInput, high U    │ C/Tests/FinalityW:26–27 checks arithmetic only; no Tail    │ Stage 5 / W1: actual Tail opening and source/service       │
│                              │ and selected opening. Its M+1 height is derived. All later │ package inhabitant.                                        │ witnesses, birth-count retention, stale carriage and       │
│                              │ proposals cover high U in J or F through the receipt       │                                                            │ acceptance before T_(r+1)+β+Δ.                             │
│                              │ horizon.                                                   │                                                            │                                                            │
│ FirstFinalityRecFEClaim_W    │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ FirstFinalityRecF4Claim_W    │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ FinalityLivenessRecFEClaim_W │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ FinalityLivenessRecF4Claim_W │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ ProposalFinalRecFEClaim_W    │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ ProposalFinalRecF4Claim_W    │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ AboveFrontierRecFEClaim_W    │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ AboveFrontierRecF4Claim_W    │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ RowPermissionClaim           │ Actual W execution and exact named producer input.         │ No complete witness found.                                 │ Supply the named package, not only a conditional           │
│                              │                                                            │                                                            │ projection.                                                │
│ HealingInputClaim            │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HTimeConcl                   │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HTimeClaim                   │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ResetArrivalConcl            │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ResetArrivalClaim            │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ RenewedPromotionClaim        │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ KernelBeforeNextActionW      │ κ=R and ΔF>2Δ; receipt-ready boundary equality.            │ C/Tests/FinalityW:26–30; C/Tests/HealingW:144.             │ No run witness follows from numeric bounds; use full       │
│                              │                                                            │                                                            │ positive execution.                                        │
│ LivenessBoundW               │ κ=R and ΔF>2Δ; receipt-ready boundary equality.            │ C/Tests/FinalityW:26–30; C/Tests/HealingW:144.             │ No run witness follows from numeric bounds; use full       │
│                              │                                                            │                                                            │ positive execution.                                        │
│ FE_W                         │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ F4_W                         │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ FGoodE_Wp                    │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ FGood4_Wp                    │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ Tail_Wp                      │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ TimingContract               │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ FGFoundation                 │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ WalkBatch                    │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ CoreServices                 │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ AttemptKey                   │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ResetArrivalStatement        │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ResetArrivalFullStatement    │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ KernelPt                     │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ KernelConclusion_W           │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ KernelPrem_W                 │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ TailKernelPt                 │ Honest Tail_W pattern, full common HealingInput, high U    │ C/Tests/FinalityW:26–27 checks arithmetic only; no Tail    │ Stage 5 / W1: actual Tail opening and source/service       │
│                              │ and selected opening. Its M+1 height is derived. All later │ package inhabitant.                                        │ witnesses, birth-count retention, stale carriage and       │
│                              │ proposals cover high U in J or F through the receipt       │                                                            │ acceptance before T_(r+1)+β+Δ.                             │
│                              │ horizon.                                                   │                                                            │                                                            │
│ TailKernelPrem_W             │ Honest Tail_W pattern, full common HealingInput, high U    │ C/Tests/FinalityW:26–27 checks arithmetic only; no Tail    │ Stage 5 / W1: actual Tail opening and source/service       │
│                              │ and selected opening. Its M+1 height is derived. All later │ package inhabitant.                                        │ witnesses, birth-count retention, stale carriage and       │
│                              │ proposals cover high U in J or F through the receipt       │                                                            │ acceptance before T_(r+1)+β+Δ.                             │
│                              │ horizon.                                                   │                                                            │                                                            │
│ HealTContract                │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealRContract                │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ProgressAttemptStatement     │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ CoveredByChild               │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ PreBatchPrem                 │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ NoMixedPreBatchParent        │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ BatchPrem                    │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ BatchCoverage                │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ FinalityCoveredByChild_W     │ Derived non-ready exact entry; actual action-q quorum and  │ P/Tests/FinalityW:34,57,65,115 (model only).               │ Complete valid emitted-row run, receipt, holding, R7 and   │
│                              │ honest carrier after receipt deadline.                     │                                                            │ selected acceptance.                                       │
│ FinalityBatchPrem_W          │ Derived non-ready exact entry; actual action-q quorum and  │ P/Tests/FinalityW:34,57,65,115 (model only).               │ Complete valid emitted-row run, receipt, holding, R7 and   │
│                              │ honest carrier after receipt deadline.                     │                                                            │ selected acceptance.                                       │
│ FinalityBatchCoverage_W      │ Derived non-ready exact entry; actual action-q quorum and  │ P/Tests/FinalityW:34,57,65,115 (model only).               │ Complete valid emitted-row run, receipt, holding, R7 and   │
│                              │ honest carrier after receipt deadline.                     │                                                            │ selected acceptance.                                       │
│ PendingFold_W                │ Derived non-ready exact entry; actual action-q quorum and  │ P/Tests/FinalityW:34,57,65,115 (model only).               │ Complete valid emitted-row run, receipt, holding, R7 and   │
│                              │ honest carrier after receipt deadline.                     │                                                            │ selected acceptance.                                       │
│ HealT                        │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealAC                       │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealingInput                 │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HTimeStatement               │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ FinalitySet_W                │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ FirstFinalityPrem_W          │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ FinalityLivenessPrem_W       │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ ProposalFinalPrem_W          │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ AboveFrontierPrem_W          │ All-honest positive run with full input and recurrence;    │ C/Tests/FinalityW:87–119,126 (conditional                  │ Unconditional inhabitants of all four W finality packages; │
│                              │ FF7 two complete forward searches.                         │ constructions/projections).                                │ FF7 second horizon.                                        │
│ PtU                          │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ PtW                          │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ PtM                          │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ PtR                          │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ PtK                          │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealingPrem                  │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealingWitnessPrem           │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealingTimePrem              │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ResetArrivalPrem             │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ ResetArrivalFullPrem         │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ KernelJoinedPrem             │ All-honest positive run, common full HealingInput; real    │ C/Tests/FinalityW:115 (assumed input; not an inhabitant).  │ KernelPrem_W, KernelJoinedPrem and TailKernelPrem_W with   │
│                              │ opening and later terminal carrier.                        │                                                            │ proved input/services/receipt.                             │
│ HealingAttemptPrem           │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealingInputPrem             │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ RenewedPromotionPrem         │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ FreshPrem                    │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ JustifyFresh_W               │ Fresh target quorum before next action; no honest finality │ P/Tests/FinalityW:79,151; no-replay :163 is raw fold.      │ Admitted execution with full FreshPrem / BatchPrem and     │
│                              │ row yet; separate earlier-or-current height batch.         │                                                            │ raw-history cuts.                                          │
│ ReceiptWitness_W             │ Valid delivered carrier with dependencies and actual       │ P/Tests/FinalityW:179,187 (handler fixture/projection      │ Execution-valid delivery and honest witnesses before       │
│                              │ handler acceptance at shared selected receipt.             │ only).                                                     │ deadline; pure fold is insufficient.                       │
│ BlockDelivery_W              │ Valid delivered carrier with dependencies and actual       │ P/Tests/FinalityW:179,187 (handler fixture/projection      │ Execution-valid delivery and honest witnesses before       │
│                              │ handler acceptance at shared selected receipt.             │ only).                                                     │ deadline; pure fold is insufficient.                       │
│ AcceptGuards_W               │ Valid delivered carrier with dependencies and actual       │ P/Tests/FinalityW:179,187 (handler fixture/projection      │ Execution-valid delivery and honest witnesses before       │
│                              │ handler acceptance at shared selected receipt.             │ only).                                                     │ deadline; pure fold is insufficient.                       │
│ AcceptPrem_W                 │ Valid delivered carrier with dependencies and actual       │ P/Tests/FinalityW:179,187 (handler fixture/projection      │ Execution-valid delivery and honest witnesses before       │
│                              │ handler acceptance at shared selected receipt.             │ only).                                                     │ deadline; pure fold is insufficient.                       │
│ AcceptBefore_W               │ Valid delivered carrier with dependencies and actual       │ P/Tests/FinalityW:179,187 (handler fixture/projection      │ Execution-valid delivery and honest witnesses before       │
│                              │ handler acceptance at shared selected receipt.             │ only).                                                     │ deadline; pure fold is insufficient.                       │
│ FinalizePrem_W               │ Derived non-ready exact entry; actual action-q quorum and  │ P/Tests/FinalityW:34,57,65,115 (model only).               │ Complete valid emitted-row run, receipt, holding, R7 and   │
│                              │ honest carrier after receipt deadline.                     │                                                            │ selected acceptance.                                       │
│ FinalizePending_W            │ Derived non-ready exact entry; actual action-q quorum and  │ P/Tests/FinalityW:34,57,65,115 (model only).               │ Complete valid emitted-row run, receipt, holding, R7 and   │
│                              │ honest carrier after receipt deadline.                     │                                                            │ selected acceptance.                                       │
│ FreshFinalityRows_W          │ K=2 protected older entry, one newer birth, then older     │ AvailableChainFGSA/Tests/WindowRetention:153,184,318;      │ Run anchors at actual action/terminal parent and same      │
│                              │ quorum.                                                    │ P/Tests/FinalityW:140.                                     │ fresh complete wires.                                      │
│ TerminalCarriagePrem_W       │ K=2 protected older entry, one newer birth, then older     │ AvailableChainFGSA/Tests/WindowRetention:153,184,318;      │ Run anchors at actual action/terminal parent and same      │
│                              │ quorum.                                                    │ P/Tests/FinalityW:140.                                     │ fresh complete wires.                                      │
│ Recovery₂                    │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ HealingSet                   │ Plan schedule witness plus actual H0 proposal, reset gate, │ C/Tests/HealingW:105,109; horizon=0 at :19.                │ Positive-horizon H0/HealingInput and every healing package │
│                              │ common phase/service witness.                              │                                                            │ with horizon fields.                                       │
│ FGoodE_W                     │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ FGood4_W                     │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ Tail_W                       │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ RecFE_W                      │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
│ RecF4_W                      │ All positive slots honest, g=1, R≥κ; horizon contains all  │ C/Tests/FinalityW:20,26,50,61,63.                          │ Concrete valid W execution; finite schedule alone proves   │
│                              │ carrier and receipt times.                                 │                                                            │ no healing package.                                        │
└──────────────────────────────┴────────────────────────────────────────────────────────────┴────────────────────────────────────────────────────────────┴────────────────────────────────────────────────────────────┘
```

Focused cases already exist: WindowRetention:72,84 (eviction without coverage
and later coverage), :98 (both R6W arms), :205 (several ready entries),
:220 (raw no replay). P/Tests/FinalityW:34,79 separates exact-q finality and
earlier-or-current height batches; :115 covers the lower key with a greater
ready key. C/Tests/FinalityW:26–27 checks κ=R, large ΔF and boundary equality.
The FF7 second horizon at C/Tests/FinalityW:126 is a projection only.
LocalHealing, PhaseWitness and UniversalLeases remain internal stage-5 witness
plans. No frozen standalone claim or new premise is introduced for them.

S4.5b follow-up (refreshed at the G-F0b freeze, S4.7 Astra F6): G1–G4 are restored on W.
G4 premises have positive witnesses: C/Tests/FinalitySafety.lean:205 (a one-node Clean₂
execution, Δ=1, ΔF=3, horizon 17), :243 (CleanInclusionPrem) and :246 (ExactProposalPrem).
HonestNeverSlashedClaim has a producer: fgsa_honestNeverSlashedClaim
(P/Foundations/Export.lean, from fgsa_honestNeverSlashed). The six G3/G4 output claims stay
stage-5 contracts. S4.6 removed the old non-W FinForm packages; S4.6c removed the deferred
best/search statements (post-freeze companion). Their old shapes are not W witness requirements.
Authority: f07w-rulings:107–108; d35bac1-coverage.md.

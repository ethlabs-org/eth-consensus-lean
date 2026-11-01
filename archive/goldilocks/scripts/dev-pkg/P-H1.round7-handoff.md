# P-H1 Round 7 handoff to P-H2 and P-As

Status: PREPARED. JOINED-START replaces the Round 6 early FAST request.
Statement commits: 4ad808d4, 396d90cc. Cut proofs: 4e506874.
The following sites are the exact D3 list from joined-start-plan.md.
Line numbers in that list refer to plan pin 9a814001, not this worktree.
No H2 source was ported in this round.

The single new phase premise is:

```lean
hready : recoveryStart p E ≤ u
```

Use this bound for every phase and phase-service callback. Derive GST for
transport with healing_recovery_start_lower. Keep saved-window hgw at GST.
Do not add LocalFastPermanence, OneLeaseReadCut, or an early dispatcher.

Permanence calls now have the following final argument sequence:

```lean
healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices
  hhead hgate hbody
```

The call returns Transfers for the actual body and endpoint. hCut is derived
inside this call. The universal healing_tPerm takes RecoverySleep₂ and a
factory returning SupportPermanenceServices for each ready, bounded phase.
That factory is the exact P5 OPEN/P-H1 obligation in round7-producers.md.
It is not supplied by this wrapper.

repair_lease_cover_one/two take `writes perm hready hphase`, followed by
the existing branch threshold and bounded vote. They construct their covers
from the same TPerm. No hCover input remains. The retained-read and
repair_head_one/two adapters also take this perm and hready. They derive
hCut/hWindow from the actual repaired proposal; those arguments are removed.
RepairHeadServices and both ScoreRunGeometry endpoint floors remain.

Exact P-H2 sites and their new inputs follow.

P-H2 phase, opening, promotion, and search

- H/Repair.lean:21,89,174,229,278,344,386,431: aggregate permanence and all phase entry points use
hready. The two budget branches pass that fact to their last-write producers. At gap calls :293 and
:404, pass Jst≤proposal(threshold), not only GST≤proposal(threshold). -
H/OpeningServiceGate.lean:24,26,37,92,373 and H/OpeningServiceBody.lean:229: bound aggregate
requests by the actual joined phase. Seed q and later rR/w sources all use unified TPerm.
H/CommonEntry.lean:106 uses the same phase service. - H/Promotion.lean:181–196;
PromotionRows:79–107; PromotionAdvance:15–60; PromotionAge:11,131,220,287; PromotionRenewed:30,102;
PromotionTerminal:100,191: replace phase-entry hGST by hready and preserve it through phase
extension. source_parent derives source readiness from u≤vote(rR). No extra LocalFastPermanence
argument. - H/RiseOneRepair.lean:75,118,169,239,292 and RiseOneAccept.lean:77,128: use Jst in
phase-entry premises and in their quantified phase-service callbacks. Keep the saved-window
transport bound at GST. H/RiseOneRise.lean:73 carries the same new phase start. -
H/RiseOneAdvance.lean:17,58; RiseOneRise:112,147; FrontierSearchAge:12,167,237;
FrontierSearchGap:37,212,239; FrontierSearchTop:227,403,432: thread the same bound. Keep existing
q≤rR and proposal-source arithmetic. - H/FrontierSeed.lean:121,132,168,199,223 and
FrontierSeedDefs:14,44: qualify seeds from the new phase start. The qualification predicate itself
remains the two-branch label predicate. Its readers retain the prior-label cut. Its one-lease proof
uses the joined-start last-write split. - H/FrontierService.lean:21,23,25,87,144,334;
FrontierServiceGate and FrontierServiceSupport; FrontierRead:21,234,291,305,437,524,561: service
factories use hready and the real seed. The saved-window hgw at slow calls stays a GST
synchronization fact. - H/FrontierSearchDefs.lean:23,34,53,64,140,154,235,250,274: change
StrongServed, FrontierSearchStart, and TerminalPromotionFact start premises to Jst. Keep the
existing canonical first-Jst-action alternative. Propagate the start through
InterruptedRepairStatement and FrontierTailStatement via their arguments. -
H/FrontierSearchCompose.lean:18,120,143; FrontierSearchTasks:60,91,135,186,213;
FrontierSearchFull:19,79,96,134: use Jst for phase/event-start bounds. Prefer hdelay:Jst+2P≤event
in the search task interfaces, since the canonical start already supplies it and event monotonicity
preserves it. Derive GST synchronization facts separately. Do not change their budget sums. -
H/AttemptSettle.lean:17,32,59,78,97,116;
AttemptRows:88,178,189,206,223,273,343,387,451,475,507,541,584; AttemptStop:48; PhaseBoot:130:
replace event/phase start assumptions with Jst. The four Attempt adapters keep the same
attemptBudget. - H/PhaseSettle.lean:376,380,388,402 and the RPhase wrapper :316;
H/PhaseFrame.lean:175: update public-facing start premises. Keep local structural frame lemmas
global. heldServices requests remain witness-specific, with a proved compatible receiver floor, a
post-GST anchor, and a real bounded read.

Changing FrontierSearch's original GST+2P delay interface to Jst+2P is safe for the reset/search
path, whose u₀ already has that bound. Do not impose this extra 2P wait on ordinary AttemptValid or
TRepair; they need only Jst. They continue to use the two-lease attempt budget or the explicitly
guarded one-lease arm.

D4 handoff, owned by P-H2/P-As:

- PostReset: rebuild HealTContract with these new services. TDel's source
  factory takes recoveryStart <= vote(rR). delReset and geom keep their meaning.
- Export: pass RecoverySleep₂ to healing_tPerm; supply the exact P5 factory.
- HealingInputExport and PostResetHealed: input horizon starts at recoveryStart,
  including every field-supplier callback. Time now uses this origin directly.
- Assembly/Healing and Assembly/ResetArrival: pass sleep recovery, the new
  phase bound and the new reset/full-reset horizon. No whole-run NoRestart.
- Ordinary/reset source delivery callbacks: request W only after selected
  source ancestry (`K <= W`, or `CStar <= eraseFG W`) and the actual receiver
  floor at early(s). The proof pulls this floor back from the consumer read
  with RMonoAll. SourceTiming, DeliveryReset and ResetTransfer have these guards.
- PostResetKeep.postReset_tDel: pass H0Reset, sourceDiscipline_emittedNonempty
  and sourceDiscipline_emittedName. Its readiness follows from high and mu_le;
  the old explicit GST source argument is removed. P-As supplies these existing
  Foundation producers across the family boundary.

DCK classification:

Promotion, AttemptStop, PhaseSettle and PhaseBoot are the four directly
failed H2 modules after the Claims change. Their 18-module import closure
is EXPECTED-FAIL/P-H2 in P-H1.txt. This includes the old full healing audit.
The new HealingJoinedStartAxioms covers only the compiled P-H1 slice.
The full canonical audit fragment remains a P-As integration obligation.

The full auxiliary manifest snapshot imports every proof/Inhabit source.
Its missing compiled roots and open H2/Outage modules are not an allowance.
The shallow and deep FG-SA products are current; the auxiliary product
must be regenerated after those source owners build their complete modules.

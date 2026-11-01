# FG-SA G-F0b freeze record (W model)

**Historical record — superseded 2026-10-09.** This document records its
original source basis. Freeze rules, port totals, ownership paths, and exact
exception rows are not current acceptance data. Future changes use generated
current snapshots and reviewed diffs. Open proof obligations remain open.
The old API data remains in Git at
`6c36d4810cb070655f2f4aadb3346db6c76aa0a3`. No checker reads this record.


Candidate content: fgsa-s46e (S4.6 + S4.6b + S4.6c + TDel / review fixes + S4.7 pre-freeze round), reviewed at
845d13e; the S4.7 fix round adds 0848d69 and this record (037ea95); B21, B25, B31 and B32 follow. The S4.8 freeze commit
replaces docs/FGSA-API-frozen.md with docs/FGSA-API.md at that head (scripts/fgsa-freeze.sh), resets
scripts/fgsa-manifest-allow.txt to its header line, and checks the new freeze with
`NEG=0 bash scripts/check-fgsa-manifest.sh`.

## Reviews

S4.7 freeze review, brief codex/jobs/s47-freeze-review.md (sha256 fee6aeb3b0f4), two models:
- Opus: FREEZE WITH FIXES, 0 blockers (TS/codex/reports/s47-freeze-review-opus-full.md).
- Astra: FREEZE WITH FIXES, 0 blockers (TS/codex/reports/s47-freeze-review-astra-full.md).
Combined lead ruling: TS/codex/reports/f07w-rulings.md, "S4.7 FREEZE REVIEW — combined ruling" (2026-10-02 20:41).
Both reviews found the genesis growth gap; CleanGrowthClaim + AwakeProposerRecurrenceFrom + the aggregate field
`cleanGrowth` close it (0848d69). The TDel ancestor question is closed (Astra checked in Lean).

## Ruled exceptions to the review-brief wording

The brief's literal checks "byte-identical to G-F0a" and "no ΔF dependency in any safety statement" do not hold
literally on this migrated surface. These are the exact, ruled exceptions:

1. FGSASafetyInterfaces (AvailableChainFGSAClaims/FGSAClaims.lean) is NOT byte-identical to G-F0a: its five
   explicit run binders changed from V2.Run to V2.D.Run (06 Duty port, 3d48ca8), and one comment changed. The
   hash moves have allow lines and semantic-ledger rows (Astra F4; Opus F7). FGSASafetyClaims keeps its G-F0a
   field list.
2. "No ΔF dependency in any safety statement": the G1/G2 finality-safety claims and the G-F0a structural safety
   claims have no row-delay, κ, recurrence or timeout premise. The exceptions are the Clean safety claims
   CleanSafetyClaim, CleanCutClaim, CleanHistoryClaim and CleanPrefixTruncationClaim (and CleanCutZeroClaim):
   they quantify `{ΔF : Time}` through their Clean regime packages (CleanPrem / CleanCutPrem / CleanPrefixPrem:
   "FG-SA rows have their own delivery bound", user 2026-10-01). Their conclusions hold for every row delay; ΔF
   only describes the healthy prefix (Astra §5 check 6 and :412).
3. DC table: Recovery₂.gap has the STRENGTH of DC SingleProposerRecurrence (from GST, over windows that end within
   the horizon) in the ROLE of DC RecoveryRegime.recurrence (DC: MultiProposerRecurrence). INTENTIONAL: it follows
   blueprint 21 ProposalGap; it is not strengthened (Astra F5; Opus S4.6c F5). The clean case uses
   AwakeProposerRecurrenceFrom (SingleProposerRecurrence role + the INTENTIONAL awake condition).

4. Exact-row service (Centaur Astra finality-route audit, TS/codex/reports/centaur/fgsa-s5-b1-core.md §8, M2):
   TRowsSelect and TRowsSync state exact-row service. The modeled proposer carries every valid held non-ancestor row
   (full inclusion, Model/Frame.lean proposalRows), so the exact-row disjunction is the modeled policy. The blueprint
   also permits an optional effect-preserving selection (22:323, 22:695; 01:83–86); that selection is not modeled,
   and paper T-ROWS must not be used to inhabit this stronger exact-row contract. No statement change.

## Post-review statement change (ruling B21)

After both reviews, the H-PHASE Opus review (F3) found that PhaseInterval, AttemptValid and RPhase required a
frontier of at least 2, but H.10 runs attempts at m = 1 (21:1467–1468, 2570–2571); the rise 1 → 2 then had no
contract route. Lead ruling B21 (evidence TS/codex/reports/m1-check-opus-full.md): relax to 1 ≤ m in PhaseInterval
(ChannelProps), RPhase clauses 1, 2, 3, 5 and RPhase_def, and AttemptValid (1 ≤ k.frontier). The premises become
weaker; each statement stays true at m = 1 (the frontier-1 frame is top J with J = genesis; 21:286, 1236). The gap
frame keeps R.j + 2 ≤ m (21:1191–1203). No G-F0a frozen name moves.

## Post-review statement change (ruling B25)

An Opus check of Centaur's H-FRAME plan found that PhaseInterval's lower cut `timeIdx rho u ≤ i` lies after all
events at u, but a HEAD at v_s = u reads stateBefore its tick, at an index before timeIdx u (ticks come before
deliveries at u). TPerm (`u ≤ voteTime s`) and TRepair branch 2 then had no blueprint route at equality (bp 754–755,
824, 1151–1162: "settled at u" includes HEADs at v_s = u). Lead ruling B25 (s5-plan-amendments.md §G): the lower cut
is `V2.D.Run.idxBefore rho u ≤ i`. Nothing else changes; TFrontier's h_max cap keeps timeIdx. No G-F0a frozen name
moves.

## Post-review statement change (ruling B31)

lean-framework's H-SUPPORT writer found a counterexample to TPerm through Transfers S3, and an Opus check found the
same end-of-run defect in two more clauses: a range that starts at afterTicksIdx / HealSuffix of a cut c is
{events.length} when c is past the interval end or the horizon, so the clause asserted coverage of the final state
although the gate at c never ran (the blueprint speaks only of outputs after that gate). Lead ruling B31
(s5-plan-amendments.md §I) adds guards only: Transfers S3 `SA.gateTime s + 4Δ ≤ v` (21:717); H2A output
`p.actionTime r + 4Δ ≤ rho.horizon` (21:3289–3291); H5RawTransfer output `SA.gateTime j + 4Δ ≤ rho.horizon`
(21:3321); and RFProv takes `H0 p c E rho w` as its first premise, as TDelReset does. No G-F0a frozen name moves.

## Post-review statement change (ruling B32)

Centaur's FREEZE-HORIZON audit (365 definitions screened) confirmed the four B31 items and found two more. Lead
ruling B32 (s5-plan-amendments.md §J): RKeep takes `H0 p c E rho w` as its first premise, as TDelReset (with an
arbitrary witness its conclusion `w.M + 1 ≤ st.fg.h_max` is false on a real run); CleanGrowthClaim takes `0 ≤ t`
before its horizon bound, because Time = Int and a negative trigger gives a deadline before 0 (DC LiveFrom has
`t₀ ≤ t`, Generic/Properties.lean:105). AvailableGrowthConcl is unchanged. No G-F0a frozen name moves.

## Gates

- aaeb71c and 037ea95: FULL gates stopped before completion (superseded by later pre-freeze heads; lead).
- f7eafbe (B21 head): FULL gate stopped at fgsa-manifest (superseded by B25; lead).
- 572da1a (f7eafbe + main eacee7b + B25): FULL gate PASS on the NUC (gate wall 3290 s) and fg(mac) PASS. Landed:
  main = 572da1a. The B31 and B32 changes followed, so this head is not the freeze head.
- 46b8f58 (final head = 572da1a + B31 + B32): FULL gate PASS on the NUC (gate wall 3256 s; build, check-build,
  check-fgsa, check-fgsa-run, catalog-lock, manifests, fgsa-manifest, fgsa-claims, axioms) and fg(mac) PASS (313 s).
  Landed: main = 46b8f58.
- S4.8 freeze commit: docs/FGSA-API-frozen.md = docs/FGSA-API.md at 46b8f58 (1127 entries, 45 modules; the trailing
  blank line that `scripts/fgsa-freeze.sh` copies is removed and the SHA-256 is recomputed);
  scripts/fgsa-manifest-allow.txt reset to its header line; `NEG=0 bash scripts/check-fgsa-manifest.sh` PASS.

## Post-freeze re-freezes (user decisions)

- TF-REFREEZE (cf15513, user decision 2026-10-03): `TFrontier` carries DC's H.6 / H.6-S seed
  qualification after `ExactService`. Allow line: `TFrontier` expect=a6e2203cd67de153.
- HISTORICAL: GAPALIGNED (bca83df, user decision 2026-10-03, "Require 4Δ divides G"):
  `Recovery₂` gains the
  last field `gapAligned : 4 * p.Δ ∣ G`; no bound changes. Basis: the TERM gap (H-ATTEMPT-3 P1;
  Centaur fgsa-s5-term-check.md): for G mod 4Δ > Δ the gap window ends after the raise terminal
  deadline. Allow line: `Recovery₂.mk` expect=18d9154d2012f72f. `StrongRecoverySearchPrefix₂` and
  every `HealingSet` consumer gain the premise with unchanged hashes, because the manifest hashes
  reference names; this is intended. Review: Opus LAND-WITH-NITS (docstring corrected after landing).

Later freeze changes include LIVE-DC (958106c) and GUP (ad66f0e). GUP removes
`gapAligned` and rounds Γ up to a multiple of 4Δ. Later exceptions are ROOT-DIGEST,
ROOT-DIGEST-2 (be214b3), and WC plan r2.1 (7b1fe01). Their records are in
[the API manifest](FGSA-API.md) and the [ROOT-DIGEST-2 record](lock-log/root-digest-2/README.md).

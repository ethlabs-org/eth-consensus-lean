READY FOR FULL GATE

**Historical record — superseded 2026-10-09.** This document records its
original source basis. Freeze rules, port totals, ownership paths, and exact
exception rows are not current acceptance data. Future changes use generated
current snapshots and reviewed diffs. Open proof obligations remain open.
The old API data remains in Git at
`6c36d4810cb070655f2f4aadb3346db6c76aa0a3`. No checker reads this record.


# port-w16d — final data closure

Branch: `port-w16d`. Source base: `4924efecd4635740060126d4ac9946063ef65ad6`.
Data tip before this report: `1b25cf53a0e67eff0eadbfa538c42c86129ba1da`.
Required precheck base: `318074ba`.
Date: 2026-10-09. Evidence: `.lake/port-w16d/`.

All required precheck and data checks pass. The default build passes with
warnings as errors: exit 0, 4,697 jobs, all 25 default targets. No `.lean` file,
claim statement, checker, Lake configuration, or fixed baseline was edited.
The lead can now run the FULL gate. This report does not claim a FULL-gate pass.

The exact reviewed shallow patch is applied at `79c3390c`.
Reachable's pin is `6dbbc505d29881d3`. The same commit applies all 897 approved
deep deltas: 886 existing exception updates and 11 new entries. Each old digest
is the handoff's `baseline_digest`; each new digest is its exact `new_digest`.
There are 908 exact exceptions. Approval evidence is
`codex/reports/reviews/rev-port-w16c-astra.md`; lead: `fg-sa-manager`.

The recovered `.lake/port-switch/current-snapshot.json` matches all 1,242
accepted pre-Y roots. All pre-Y and current root SHA-256 values were recomputed
with the repository's tagged serialization. Four existing node digests change;
two nodes are added. The local handoff now has actual prior node digests and
the saved graph path. Its stale missing-graph note is removed.

The five retained restore replacements were already applied at `2862a33a`
and included in this branch. Their declarations, owners, and audit commands
are measured again. Complete normal coverage passes: 6,681 rows, 14 audits,
1,034 proof modules, 1,033 accepted equation exports, zero unaccepted exports.
The inventory keeps its current bytes. The ledger records all 36 port-weq
export removals as exact module/name keys. The equation baseline is unchanged.

All 2,578 FG-SA expected names and all 209 FG expected names pass.
The earlier 2,214 measurements are unchanged. The 364 names blocked in w16c
are now measured; 303 further changed evidence rows have measured source
dependencies. No expected name is removed. Every measured axiom set is standard.

P13 and blueprint pass. All 36 OPEN items and all PARTIAL statuses remain.
The aggregate fingerprint is `f0d9a772701a8a1a`, with one binder and zero
proposition binders. The aggregate and six restart claims compile from Params
alone. Old reads and all controls pass: 10,148 constants, 520 active modules,
six old/finality readers and 244 height-only readers. WCProposalPivot remains
height-only. The old-read baseline keeps its bytes. The final rebuilt scan has
55 fewer constants than the initial local scan; all 520 active modules remain.

API generation uses `V2Manifest.lean --scope fgsa --write` with a local output
path. All 1,243 generated entries match the stored document exactly. The stored
document and its historical prose keep their bytes. Shallow, deep, and frame
pass. Frame retains 43 entries and five exact exceptions.

S0 has one further byte change: `scripts/fgsa-manifest-allow.txt`, commit
`79c3390cbddc1939dbe7735aabd37b03063f47e5`, actual parent `4924efec`.
Before SHA-256: `c86a1e8c0ee181e2ca855f8766c43d2481afe2ee5d0896ac58ffbbee750e69d4`.
After SHA-256: `b4d8cd96a5fb23ac6f62a74d4beb89d1e0f6106668cf96da00d87f900a776972`.
Freeze bytes, history, and packages pass: 122 paths, 20 differences,
47 history records, 23 packages. Both fixed S0 manifest hashes are unchanged.

The source attribution covers nine file events at `3acf74ea`, `7a7e1eee`,
`de993213`, `8c22d862`, and `66af0148`, with actual parents and file hashes.
All declaration headers and definition bodies match their parents. There are
zero statement changes. Reviews: `rev-port-weq-astra.md` and
`rev-port-wfix3-astra.md`. This job repairs no source module; the integrated
jobs repaired seven export-producing proof modules, the FGSA facade, and
Inhabit WeakContinuationW1. All operational blockers in the ledger are closed.

Changed tracked paths: `scripts/fgsa-manifest-allow.txt`,
`scripts/fgsa-deep-allow.json`, `docs/FGSA-PORT-CHANGES.json`,
`docs/FG-FINALITY-SAFETY-S0-inherited.json`, and this report.
The local handoff and local job report remain excluded from Git.

Before/after results follow. Before is measured on the initial local tree,
except the rows that explicitly name the saved w16c result.

```text
┌────────────────────────────┬────────────────────────────┬────────────────────────────┬──────┐
│ Check                      │ Before                     │ After                      │ Exit │
├────────────────────────────┼────────────────────────────┼────────────────────────────┼──────┤
│ Precheck: base             │ PASS                       │ PASS                       │ 0    │
│ Precheck: diff-check       │ PASS                       │ PASS                       │ 0    │
│ Precheck: guard-lists      │ PASS                       │ PASS                       │ 0    │
│ Precheck: import-policy    │ PASS                       │ PASS                       │ 0    │
│ Precheck: check-layers     │ PASS                       │ PASS                       │ 0    │
│ Precheck:                  │ PASS                       │ PASS                       │ 0    │
│ check-module-headers       │                            │                            │      │
│ Precheck: check-expose     │ PASS                       │ PASS                       │ 0    │
│ Precheck:                  │ PASS                       │ PASS                       │ 0    │
│ check-transparency         │                            │                            │      │
│ Precheck: check-gly-rules  │ PASS                       │ PASS                       │ 0    │
│ Precheck: check-fgsa       │ PASS                       │ PASS                       │ 0    │
│ Precheck: check-fgsa-run   │ PASS                       │ PASS                       │ 0    │
│ Precheck:                  │ PASS                       │ PASS                       │ 0    │
│ check-fgsa-claims          │                            │                            │      │
│ Required precheck          │ PASS                       │ PASS; base 318074ba        │ 0    │
│ S0 bytes                   │ PASS; 46 history records   │ PASS; 122 paths / 20 diffs │ 0    │
│ S0 history                 │ PASS in w16c; 46 records   │ PASS; 47 records           │ 0    │
│ S0 packages                │ PASS in w16c; 22 packages  │ PASS; 23 packages          │ 0    │
│ Store source (standalone)  │ PASS                       │ PASS                       │ 0    │
│ Run source (standalone)    │ PASS                       │ PASS                       │ 0    │
│ Default --wfail build      │ Objects stale locally      │ PASS; 25 targets / 4697    │ 0    │
│                            │                            │ jobs                       │      │
│ FG-SA expected names       │ Exit 2; stale Inhabit      │ PASS; all 2578             │ 0    │
│                            │ object                     │                            │      │
│ FG expected names          │ Not run in this job        │ PASS; all 209              │ 0    │
│ Expected evidence          │ 2214 measured / 364        │ PASS; 2787 names / 303 new │ 0    │
│                            │ blocked                    │ rows                       │      │
│ Proof coverage             │ Exit 2; stale Inhabit      │ PASS; 6681 rows / 14       │ 0    │
│                            │ object                     │ audits                     │      │
│ Old reads / controls       │ PASS; baseline unchanged   │ PASS; 10148 constants /    │ 0    │
│                            │                            │ 520                        │      │
│ P13 / blueprint            │ PASS; 36 OPEN items        │ PASS; 36 OPEN items        │ 0    │
│                            │                            │ retained                   │      │
│ Aggregate / six witnesses  │ PASS in w16c               │ PASS; Params alone; 1/0    │ 0    │
│                            │                            │ binders                    │      │
│ API generation             │ 1243 stored entries        │ PASS; 1243 entries match   │ 0    │
│ Shallow                    │ FAIL; old Reachable pin    │ PASS; exact approved pin   │ 0    │
│ Deep                       │ FAIL; 897 exact deltas     │ PASS; 1243 roots / 908     │ 0    │
│                            │                            │ exceptions                 │      │
│ Frame                      │ PASS; same fixed data      │ PASS; 43 entries / 5       │ 0    │
│                            │                            │ exceptions                 │      │
│ Finality coverage          │ PASS                       │ PASS; 24 modules / 221     │ 0    │
│                            │                            │ names                      │      │
│ Ownership                  │ PASS; 746 paths            │ PASS; 746 paths            │ 0    │
│ Source / baseline scope    │ Clean base                 │ PASS; no Lean or baseline  │ 0    │
│                            │                            │ edit                       │      │
└────────────────────────────┴────────────────────────────┴────────────────────────────┴──────┘
```

Every command, exit, runtime, and evidence hash is recorded in
`docs/FGSA-PORT-CHANGES.json` under `last_data_closure.checks`.
The required commands were run exactly:

```sh
bash /Users/francesco/.claude/jobs/22f59f85/tmp/precheck.sh \
  /Users/francesco/.claude/jobs/22f59f85/tmp/wt-pcsa-formation 318074ba
python3 -B scripts/check-fg-finality-freeze.py --check
SOURCE_ONLY=1 bash scripts/check-fgsa.sh
SOURCE_ONLY=1 bash scripts/check-fgsa-run.sh
LEAN_SLOTS=2 lake build --wfail
LEAN_SLOTS=2 python3 -B scripts/check-proof-coverage.py
```

Initial sandbox Lean attempts could not acquire shared slot locks. Only this
job's four inspected waiting wrappers were stopped. Runs with normal shared
lock access used `LEAN_SLOTS=2`. The first expected/coverage attempts found
stale local Inhabit objects. Manifest attempts during the build also found
objects invalidated by Lake. All final compiled measurements ran after the
successful build. Replayed scheduling stderr is not a Lean warning.

No failure remains in the required checks. New WP16 data still needs its
normal data review. Ruling Z's independent source simulation and claim transfer,
and the existing AA/AB obligations, remain explicit later work. No claim text
or status was changed to close them.

Not run: FULL/MERGE gates, compiled FGSA/Run checker gates and their negative
controls, or extra coverage generation. Complete normal coverage verifies the
fixed inventory. No review, agent, Codex/Claude child process, push, rebase,
or lake update was started.

Claude-Session: https://claude.ai/code/session_01QreJ9BuHuNn5MNfMUXRdLN

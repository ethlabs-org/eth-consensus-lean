# Phase 2a report: engine v2 core and Kit v2

_Gate 2026-09-29. Plan: `docs/plans/2026-09-29-phase2a-engine-v2-core.md`
(r3). Astra audited the plan and checked it again twice (each REVISE; the
fixes are in `f795cd8`). DC-simplify reviewed it (ADOPT WITH FIXES; N1
check PASS WITH ONE FIX). Branch `v2-2a` in
`~/worktrees/available-chain-v2`, from `f795cd8`. Executed under the user's rule, as DC-simplify relayed it: act
independently; get a review from Astra and DC before big decisions._

Gate verdict: the gate review found 0 critical, 2 important and 7 minor
issues (freeze mechanism); the fix round `ec5db1e` addressed all of them. The
re-review APPROVED it and found 5 new minors, fixed in `6cecee2`. Main
(1944bb8, with I9, the Grid CO walk anchor and the FG-SA spec sync) was merged
into `v2-2a` as `833bd6a`, and every check below ran on that tree. Main was
then fast-forwarded to the branch head on 2026-09-29.

## Result

Phase 2a is complete up to the merge (Task 7 Step 7).

- **Engine v2** (`AvailableChainEngineV2`: `Engine`, `Conditions`,
  `Laws`; namespace `AvailableChain.V2`). It has the protocol spec with the
  input type as a parameter, the atomic tick with the own-signature record,
  runs with restart events, the schedule, committee, restart and delivery
  conditions, the interface, and the laws `Isolation`, `HooksSound`,
  `OutputsFactor`, `EmitOk` and self-delivery. The frozen shapes are in
  `docs/FRAMEWORK-DESIGN.md` §2, "As implemented in Phase 2a".
- **Kit v2** (`AvailableChainKitV2`; namespace `AvailableChain.V2.Engine`).
  It has the v1 engine lemmas that the T7 plan names, over v2 runs, with the
  restore premises of plan D9 and a `recordOwn` premise on every stability
  or invariant lemma. It also has generic emission lemmas (DC N7) and finite
  run checks (`RunCheck`).
- **Freeze.** `docs/V2-API.md` lists 280 declarations. The 224 engine
  entries are locked through the anchor definitions under the locked prefix
  (today one,
  `AvailableChain.Framework.V2.anchor`), in the new locked prefix
  `AvailableChainFramework.V2`. Every manifest line (engine and Kit) also
  carries its own entry hash. The lock gained one ADDED line. The 56 Kit
  entries are frozen by rule, and `V2Manifest --check` compares a hash of
  each Kit statement.
- **Evidence.** A toy protocol has `Interface`, `Isolation`,
  `OutputsFactor` and `HooksSound` values. A complete finite run
  (`toyRun`) is `ExecutionValid`, satisfies `SelfDelivery`,
  `PartialSynchrony` and `HealthyPrefixDelivery`, and has a self-delivery
  at the emission time where the hypotheses of `selfDelivery_admissible`
  hold. A second run (`pre`) uses the append form
  `ExecutionValid.snoc_selfDelivery`. Both are in
  `AvailableChainKitV2/Tests/Toy.lean`.
- No v1 file changed: no file of `AvailableChainModel`,
  `AvailableChainStatements`, the v1 Kit or a protocol library. The only
  Framework change is the anchor module and its import.

## Tasks and commits

Review counts are Critical/Important/Minor.

```text
┌────────┬────────────────────────────────────┬────────────────────────────┬────────────────────────────┐
│ Task   │ Content                            │ Commits                    │ Review                     │
├────────┼────────────────────────────────────┼────────────────────────────┼────────────────────────────┤
│ 0      │ Libraries and layout:              │ 09e38a4                    │ with Task 1                │
│        │ AvailableChainKitV2 root, lakefile │                            │                            │
│        │ globs, axiom scan of both          │                            │                            │
│        │ libraries                          │                            │                            │
│ 1      │ Objects, spec, tick, runs; tests   │ 7fd93fd; 8c14410 (review   │ SPEC PASS, APPROVED; 0/0/4 │
│        │ (a)–(c)                            │ minors m1, m2, m4)         │                            │
│ 2      │ Schedule, committee and restart    │ 4ddad17; 7f3a4e8 (review   │ SPEC PASS, APPROVED; 0/0/4 │
│        │ conditions                         │ minors)                    │                            │
│ 3      │ Isolation, hooks, self-delivery,   │ 013b01b; 51d0a5a (fix      │ NEEDS FIXES 0/1/5;         │
│        │ append form                        │ round 1)                   │ re-review: 5/5 addressed   │
│ 4      │ Kit v2: engine lemmas with the D9  │ b382091; 7da8732 (review   │ APPROVED 0/0/4             │
│        │ premises; counterexamples          │ minors)                    │                            │
│ 5      │ Delivery conditions, Interface,    │ 469463f; e423c82 (fix      │ NEEDS FIXES 0/1/4;         │
│        │ outputs (post-I9 texts)            │ round 1)                   │ re-review: approved        │
│ 6      │ Toy protocol, complete valid run   │ 51db510; 81dae24; 836ac48; │ APPROVED 0/0/4             │
│        │ with a self-delivery, append-form  │ 1cece1d                    │                            │
│        │ run, RunCheck                      │                            │                            │
│ 7      │ Gate: merge main, V2-API manifest, │ 783bd1c (merge main        │ NEEDS FIXES 0/2/7;         │
│ (0–5)  │ anchor, V2Manifest script, lock;   │ 3403e58); fa190ec;         │ re-review: approved, 5     │
│        │ Sketch deleted; entry hashes;      │ 64a48cd; ec5db1e; 6cecee2; │ minors fixed               │
│        │ anchor rules                       │ 833bd6a                    │                            │
│        │                                    │ (merge main 1944bb8)       │                            │
│ 7 (6)  │ Docs: MAP rows, design §2 note, §8 │ this commit                │ —                          │
│        │ row, this report                   │                            │                            │
│ merges │ main into v2-2a (plan edits; 2b    │ e0b596c; 2b08ee5; 9f4d6c2  │ —                          │
│        │ outline note); I9 Tasks 0–8        │                            │                            │
│        │ (e42bb37) for Tasks 5–6            │                            │                            │
└────────┴────────────────────────────────────┴────────────────────────────┴────────────────────────────┘
```

## Checks at the gate

```text
┌──────────────────────────────────┬────────────────────────────────────────────────────┬──────────┐
│ Check                            │ Result                                             │ At       │
├──────────────────────────────────┼────────────────────────────────────────────────────┼──────────┤
│ lake build --wfail (all default  │ 3654 jobs, exit 0                                  │ 833bd6a  │
│ targets, AvailableChainKitV2     │                                                    │          │
│ included)                        │                                                    │          │
│ CatalogLock --check              │ no output, exit 0. Against the lock of main        │ 833bd6a  │
│                                  │ (3403e58): 1 ADDED line,                           │          │
│                                  │ AvailableChain.Framework.V2.anchor                 │          │
│                                  │ d7bf19c118bcf687; no CHANGED, no REMOVED; 251      │          │
│                                  │ lines                                              │          │
│ V2Manifest --check               │ 280 entries in 17 modules, complete: 224 engine    │ 833bd6a  │
│                                  │ entries, each in the closure of the anchor         │          │
│                                  │ (locked); 56 Kit entries, each with a matching     │          │
│                                  │ ownHash (frozen, not locked); exit 0               │          │
│ CheckFrameworkAxioms             │ 1372 constants scanned, EngineV2 and KitV2         │ 833bd6a  │
│                                  │ included (with 6 test modules); exit 0             │          │
│ Registry --check                 │ no output, exit 0                                  │ 833bd6a  │
│ check-fg.sh                      │ all FG checks pass, exit 0                         │ 833bd6a  │
│ check-fgsa.sh                    │ all FGSA checks pass, exit 0                       │ 833bd6a  │
│ grep sorry|native_decide|^axiom; │ no match in the new and changed files              │ 833bd6a  │
│ grep -w admit                    │                                                    │          │
│ V2Manifest negative tests        │ A: an unlisted entry gives NOT LISTED; B: an entry │ fa190ec, │
│                                  │ outside the anchor gives NOT ANCHORED; C: no       │ 833bd6a  │
│                                  │ anchor import gives MISSING ANCHOR; D: a changed   │          │
│                                  │ Kit statement gives CHANGED; each exit 1, then     │          │
│                                  │ restored                                           │          │
└──────────────────────────────────┴────────────────────────────────────────────────────┴──────────┘
```

All rows ran on the merged tree `833bd6a` (main 1944bb8 merged in). The
V2Manifest negative tests ran during the fix rounds (`fa190ec`, `64a48cd`,
`ec5db1e`, `6cecee2`): D (a changed statement), E (a pattern-only change in
`allTicks`; the pre-fix hash missed it), F (a new engine module anchored by a
new anchor def: the lock shows only an ADDED line), G (a changed engine lemma
is named by its entry hash while the anchor line also changes), N1a/N1b (an
unrelated earlier declaration no longer gives a false CHANGED).

## Freeze rules for later stages

- **ADD only.** After the gate, no declaration in `docs/V2-API.md` changes
  its name, type or body. A 2a structure never gains a field, a 2a
  inductive never gains a constructor, and a 2a definition never gains a
  parameter. Stages 2b and 2c add declarations or separate structures (for
  example `RestoreLaw` and `InputInstance` in 2c).
- **Engine entries are locked.** The anchor definitions under
  `AvailableChainFramework.V2` reference the 224 engine entries, so their lock
  lines hash the closure. Never edit `anchor`: a later stage adds a new anchor
  definition (an ADDED lock line). Put new declarations AFTER the existing
  ones in a 2a module, or in a new module, because Lean reuses a `match`
  helper of the same shape on a first-come basis. A change to a model module
  in the closure (for example `Objects.Blocks`) also changes the anchor line.
- **Entry hashes.** Every manifest line carries a hash of the entry and of the
  generated or private constants in its closure that lie in a v2 module or in
  its own module (for example `match` helpers). The hash covers the type, the
  value of a definition (not the proof of a theorem), the binder names
  (hygienic scopes erased) and binder infos, the reducibility status and the
  instance flag. `--check` reports `CHANGED` per entry, so a later CHANGED
  anchor line can always be traced. Dependencies outside v2 (for example a
  Model declaration that only Kit entries use) are not in the entry hash;
  they are frozen by rule only.
- **`V2Manifest --check` enforces completeness.** It exits 1 if a public
  declaration of a scope module (`AvailableChainEngineV2.Engine.*`,
  `.Conditions.*`, `.Laws.*`, and every `AvailableChainKitV2` module
  outside `Tests`) has no manifest line, or a scope module has no heading.
  So 2b either lists each new public declaration there (it is then frozen)
  or puts it in a module outside the scope prefixes.
- **The dependency rules are copies.** `generated`, `deps`, the closure
  traversal and `ownHash` in `scripts/V2Manifest.lean` are copied from
  `scripts/CatalogLock.lean`. A change to one needs the same change in the
  other.
- **Append-only.** The module blocks of `docs/V2-API.md` are append-only; a
  changed or removed entry line is a freeze break unless a named user
  decision allows it. The counts table and the date change with every ADD.
- Derived instances and structure constructors are entries (for example
  `instDecidableEqAuth`), so a change to a `deriving` clause breaks the
  freeze.

## Decisions taken without the user

The plan decisions D3 (the input is a type parameter), D6 (2a code outside
the Framework; an anchor at the gate) and D8 (Tasks 0–4 before I9, Tasks
5–7 after it) are controller decisions; Astra and DC-simplify reviewed them
with the plan. The table lists every "Ruling:" line of the ledger
(`.superpowers/sdd/2026-09-29-phase2a-engine-v2-core/progress.md`) and the
two Task 7 choices that the controller accepted (#27, #28). "Not stated"
means that the ledger gives no cost; a sentence after it is an estimate of
this report.

```text
┌────┬────────────────────────────────────────┬────────────────────────────────────┬────────────────────────────┐
│ #  │ Ruling                                 │ Reason                             │ Cost if wrong              │
├────┼────────────────────────────────────────┼────────────────────────────────────┼────────────────────────────┤
│ 1  │ Batch Task 0 into the Task 1 dispatch. │ Task 0 is layout only, and Task 1  │ One larger review.         │
│    │                                        │ needs it.                          │                            │
│ 2  │ Tasks 5–7 wait for the I9 merge (plan  │ They copy post-I9 texts that       │ Superseded by #16.         │
│    │ D8).                                   │ mention Block.                     │                            │
│ 3  │ Carry Task 1 minors m1 (axiom scan of  │ They pin frozen semantics before   │ Small test additions.      │
│    │ Tests), m2 (tick semantics tests) and  │ the gate.                          │                            │
│    │ m4 (pin the 24 ProtocolSpec field      │                                    │                            │
│    │ names) into the Task 2 dispatch.       │                                    │                            │
│ 4  │ Park Task 1 m3: keep                   │ A weaker variant can be ADDED      │ Not stated. A caller       │
│    │ ScheduleWellFormed.nodup as in v1,     │ later.                             │ without nodup needs a new  │
│    │ although mem_emittedAt_iff_emits needs │                                    │ lemma.                     │
│    │ less.                                  │                                    │                            │
│ 5  │ Resume the Task 1 implementer for Task │ Same run types; context helps a    │ Fewer independent eyes;    │
│    │ 2.                                     │ v1-copy task.                      │ the fresh reviewer covers  │
│    │                                        │                                    │ it.                        │
│ 6  │ Carry all four Task 2 minors into the  │ They touch frozen shapes. Inline   │ One signature.             │
│    │ first Task 3 commit; make P explicit   │ lambda families are the common     │                            │
│    │ for SingleSeat only.                   │ use.                               │                            │
│ 7  │ Accept the Task 2 choices:             │ emitsAt needs E; rho fixes P;      │ Not stated.                │
│    │ SelfDelivery takes E; CStar is a       │ CStar.seats_eq derives the count   │                            │
│    │ bijective seat map per label; P is     │ under Fintype V.                   │                            │
│    │ implicit in the conditions.            │                                    │                            │
│ 8  │ A fresh implementer for Task 3.        │ Design-heavy task; independent     │ Not stated.                │
│    │                                        │ eyes on the engine.                │                            │
│ 9  │ Merge the main plan edits (c5b8706,    │ Keep the Task 4 brief in step with │ Not stated.                │
│    │ Task 4 Produces) into v2-2a after Task │ the plan.                          │                            │
│    │ 3; the I9 D9 row fix goes with the I9  │                                    │                            │
│    │ report.                                │                                    │                            │
│ 10 │ Task 3 I1: F.APObject includes         │ gossip_base makes the AP           │ A stronger obligation for  │
│    │ unsigned objects (.none ⇒ True).       │ projection emit unsigned gossip    │ a future gossiping         │
│    │                                        │ (SA-PC PCs); the weaker law is too │ composite.                 │
│    │                                        │ weak for E5 transport. No known    │                            │
│    │                                        │ cost: FG-SA gossip is [], the toy  │                            │
│    │                                        │ has no gossip, the legacy base is  │                            │
│    │                                        │ id.                                │                            │
│ 11 │ Task 3 m1: the hook factors are data   │ The 2b projection needs concrete   │ More fields to fill per    │
│    │ (depsB, processedB, excludesB,         │ hooks.                             │ instance.                  │
│    │ handlesB).                             │                                    │                            │
│ 12 │ Task 3 m2–m4 in the same fix round;    │ m5 is a T7 check, not a 2a change. │ Not stated.                │
│    │ relay m5 to DC-simplify: T7 must check │                                    │                            │
│    │ that AP and unsigned hooks read        │                                    │                            │
│    │ nothing outside base (not Λ, not       │                                    │                            │
│    │ pending).                              │                                    │                            │
│ 13 │ Accept the premises that the Task 3    │ The review found that nothing is   │ Not stated. T7.10 text     │
│    │ implementer removed from               │ lost; the lemmas are stronger.     │ uses the shorter premise   │
│    │ selfDelivery_admissible and            │                                    │ lists.                     │
│    │ snoc_selfDelivery.                     │                                    │                            │
│ 14 │ Fix Task 4 m1–m3 at once               │ m1–m3 touch frozen or scanned      │ Not stated.                │
│    │ (counterexamples to KitV2/Tests; named │ code.                              │                            │
│    │ check theorems; docstring). m4         │                                    │                            │
│    │ (per-node restart forms) goes to the   │                                    │                            │
│    │ 2c outline.                            │                                    │                            │
│ 15 │ The manifest Kit section is every      │ One freeze rule for the whole Kit. │ A larger frozen surface.   │
│    │ public KitV2 declaration outside the   │                                    │                            │
│    │ tests. A "helpers, not frozen" group   │                                    │                            │
│    │ is allowed; the gate did not use it.   │                                    │                            │
│ 16 │ Merge the I9 branch at e42bb37 into    │ Tasks 9–11 of I9 did not touch     │ A re-merge. Did not occur: │
│    │ v2-2a and run Tasks 5–6 before I9      │ Model or Statements.               │ 783bd1c changed no         │
│    │ reaches main (the user's wish for      │                                    │ EngineV2 or KitV2 file.    │
│    │ parallelism, relayed by DC).           │                                    │                            │
│ 17 │ Add Interface.propLabel_injective (a   │ Aliasing has no use; it couples    │ A field that a future      │
│    │ frozen field).                         │ proposers outside a visible regime │ protocol cannot meet (none │
│    │                                        │ condition; v1 had one proposer per │ known); only a v3 break    │
│    │                                        │ slot; slot-quantified floor claims │ fixes it.                  │
│    │                                        │ get weaker. FG-SA .prop s and the  │                            │
│    │                                        │ 2b lift discharge it by            │                            │
│    │                                        │ constructor injectivity.           │                            │
│    │                                        │ DC-simplify: no objection.         │                            │
│ 18 │ Do not port AcceptedObjectRelay and    │ No v1 regime uses them; only       │ One ADDED declaration      │
│    │ HealthyAcceptedObjectRelay.            │ derived L4 and Kit proofs do.      │ later.                     │
│ 19 │ Keep broadcast to the emitter (v1,     │ v1 behaviour; both self-delivery   │ Not stated.                │
│    │ plan D4). Task 6 adds a witness with   │ timings satisfy it.                │                            │
│    │ an honest emitter and a relay case.    │                                    │                            │
│ 20 │ Accept the epoch reading of the        │ Under NoRestart the reading equals │ Not stated. 2c restart     │
│    │ delivery premises for 2a (docstring).  │ v1.                                │ regimes must not use these │
│    │ 2c adds the rejoin condition and tests │                                    │ conditions alone.          │
│    │ of (a) a lost processed object and (b) │                                    │                            │
│    │ a handler call before a restart.       │                                    │                            │
│ 21 │ Keep the Task 5 helpers (propSeat,     │ Two are in the closure anyway; T7  │ Not stated.                │
│    │ eq_propSeat, holder_propLabel, Output, │ and 2b need the others.            │                            │
│    │ the OutputsFactor lemmas) and list     │                                    │                            │
│    │ them.                                  │                                    │                            │
│ 22 │ Task 6: add a non-degenerate           │ The lemma is frozen at the gate,   │ Not stated.                │
│    │ append-form run and doc notes now.     │ and T7.10 uses it.                 │                            │
│ 23 │ Move allTicks, allDeliveries,          │ T7.10 would otherwise import a     │ None material.             │
│    │ emittedBy and their _spec lemmas to    │ test module.                       │                            │
│    │ AvailableChainKitV2/RunCheck.lean      │                                    │                            │
│    │ (revises the deferral to 2b).          │                                    │                            │
│ 24 │ The toy moves to                       │ Layer rule: EngineV2 tests may not │ One file move.             │
│    │ AvailableChainKitV2/Tests/Toy.lean.    │ import KitV2.                      │                            │
│ 25 │ Delete                                 │ The Laws supersede it; a freeze    │ Restore from git.          │
│    │ AvailableChainEngineV2/Sketch.lean at  │ would freeze a clashing older API. │                            │
│    │ the gate.                              │                                    │                            │
│ 26 │ Add Kit hashes to the manifest (later  │ Without them the Kit freeze has no │ Small script work.         │
│    │ per-entry hashes, rows 29–31).         │ statement check; T7 depends on     │                            │
│    │                                        │ RunCheck.                          │                            │
│ 27 │ Accept derived instances and           │ The CatalogLock rule lists them.   │ A deriving change breaks   │
│    │ constructors as manifest entries (Task │                                    │ the freeze.                │
│    │ 7 concern 2).                          │                                    │                            │
│ 28 │ Accept a separate script V2Manifest,   │ The completeness check imports     │ Two copies of the          │
│    │ not a CatalogLock option (Task 7).     │ AvailableChainKitV2; the lock must │ dependency rules to keep   │
│    │                                        │ not.                               │ equal.                     │
│ 29 │ Per-entry hashes for engine entries    │ A CHANGED anchor line alone would  │ Hash regeneration, before  │
│    │ too, and new anchor defs instead of    │ hide which frozen entry changed;   │ the baseline.              │
│    │ edits to anchor (gate review I1).      │ an edit of anchor breaks ADD-only. │                            │
│ 30 │ Entry hash covers generated/private    │ A pattern-only change in a Kit def │ Script work.               │
│    │ auxiliaries in v2 modules (I2).        │ escaped the own-hash (test E0).    │                            │
│ 31 │ Binder hash erases macro scopes        │ An unrelated earlier declaration   │ 203 hashes regenerated.    │
│    │ (re-review N1).                        │ gave a false CHANGED (test N1a).   │                            │
└────┴────────────────────────────────────────┴────────────────────────────────────┴────────────────────────────┘
```

Answered by DC-simplify (plan, survey R6): the FG-SA HEAD labels are in the
`fresh` family, the FG labels in the `linked` family, and the FG-SA regimes
do not require `SelfDelivery`.

## Open items

**For the user.**

- Claim ids for v2 (survey R7): the scheme of the new ids for the 14 claims
  and 3 profiles is a 2b question for the user.

**2b (the lift and v2 claims).**

- The generic parts in `AvailableChainFramework/V2` and `Catalog/V2`
  (ADDED lock lines only): v2 properties and regimes, each with `NoRestart`
  and `CStar` on the fresh family; the v2 `Instance` (it binds
  `LabelFamilies`, `Isolation`, `OutputsFactor`, `HooksSound`,
  `Interface`); `ClaimDomain.v2 In`; v2 `StrongInstance`; `Simulation`,
  `ClaimSim`, `ClaimSim.holds`.
- The concrete parts in L4: lifted instances, transported results,
  Counter certificates, Sanity refutations and finite checked traces of
  the lifted instances. Scope (settled with DC-simplify, 2026-09-29): SA is
  `gridCO` at `slowLeasePolicy`, so every Grid CO proof that is generic in
  `[LeasePolicy]` stays and is used for SA; only the work for Grid CO's own
  policy instance (its lifted instance, `grid_holds`, its certificates and
  trace) is deferred, not removed.
- Input in the context correspondence (Astra A04); hooks for lifted
  instances proved on v2 with the legacy restart behaviour and the Kit
  restore premises (A05); `n` against `Fintype.card V` from `CStar` (A06).
- AP projection masks (Task 3 re-review d1): the `Isolation` factors are
  constrained only on `F.APObject`, so the 2b AP projection must mask them
  off `F.APObject` with a permissive value.
- If a 2b proof needs acceptance relay, ADD an exempt form of
  `AcceptedObjectRelay` (ruling #18).
- A weaker form of `mem_emittedAt_iff_emits` without `nodup` can be ADDED
  (ruling #4).
- Every new public declaration in a scope module needs a manifest line
  (freeze rules above).

**T7 (FG-SA run lift, on v2).**

- fgsa-impl writes the v2 revision of the T7 plan against the manifest
  (plan Task 7 Step 7).
- T7 checks that the AP and unsigned hooks read nothing outside `base`,
  in particular not Λ or `pending` (ruling #12, m5).
- T7.3 discharges `propLabel_injective` for `.prop s` (ruling #17).
- The v1 name `stateBefore_eq_of_other_nodes` is not ported; use
  `stateBefore_other_node` or `Run.stateBefore_eq_of_node_ne`.
- `stateBefore_field_prefix_restore` does not apply for
  `restore := fun _ => init` when the field is not empty; FG-SA uses the
  `restartFree` form or `NoRestart`.
- T7.10 builds its witness with `ExecutionValid.snoc_selfDelivery` and the
  checks of `AvailableChainKitV2.RunCheck`. The append form ends the run at
  the delivery time (premise `hkey` and field `tick_total`); a witness that
  continues needs a direct proof, as `toyRun` shows.

**2c (restart, toy protocol, I1).**

- The E6 restore law `RestoreLaw` (`restore_base`, `durable_base`),
  epochs, rejoin conditions, `catchUp`, restart regimes, and a schedule
  condition for restart times (`ScheduleWellFormed` puts none on them).
- Restart-aware Kit lemmas, ADDED beside the frozen ones: per-node forms of
  `stateBefore_tick_eq_stateBeforeTime` and `delivery_now_ge_public`
  (Task 4 m4); public run-local restore forms for durable clocks.
- A rejoin condition beside `PartialSynchrony` and
  `HealthyPrefixDelivery`, and a test of both epoch effects (ruling #20).
- The toy Linked, self-visible, restart protocol (a non-trivial restart,
  receipt loss outside the durable state, a later fresh delivery). The 2a
  toy does not exercise exclusion, carried objects, the fresh family or
  restarts (`restore` is the identity).
- The I1 fix: a decoder `decode : Block → Option In` in a 2c facet
  (`InputInstance`), the binding equality, `InputClosed` and
  `core.input.bound.v2` at one fixed infinite `In`. The 2c plan audit
  decides the final form of items (iii) and (iv) of the plan outline.
- FG-SA restarts: the interim form (Λ durable, store reset) until the
  anchor-and-pruning feature gives the faithful form.

**Plan 1c (on engine v2).**

- `Eligible` (`EmitWellFormed`, `HandlerCoverage`, `Deliverable`,
  `RelayFeasible`) and the run-extension theorem. The Phase 1 acceptance
  item "eligibility per migrated instance" stays open until then.
- Inhabitation: complete regime runs with the DC self-delivery timing.
  `selfDelivery_admissible` shows only that one such delivery is
  admissible.
- If 1c states the run-extension theorem for every skeleton and every
  input, `InputClosed` (2c) is one general corollary.
- The other direction of E4 (a refusal for good implies `excludes`), which
  `RelayFeasible` needs (from plan 1b).

## User priority

The user priority (2026-09-29): FG-SA verified first, then SA. No feature
work on Grid CO, SA-PC, L* or SimplexFG; their builds and checks stay
green. This work is deferred, not removed. The 2b outline keeps the lifts
of Grid CO and SA-PC; the 2b plan decides when they occur. Phase 2a
changed no file of these libraries. Order after 2a (proposed by DC-simplify,
waiting for the user): 1c for FG-SA (run construction and inhabitation for
every horizon) before 2b and 2c, because the main FG-SA claims need 2a, T7 and
that part of 1c; 2b is optional for them and 2c is not needed.

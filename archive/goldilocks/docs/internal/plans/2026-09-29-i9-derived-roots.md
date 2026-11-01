# I9: derived block roots (store-only) — Implementation Plan (r4)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A block has no supplied root. `Block.root` is computed from the parent's root, the slot and a body by one injective function, so root injectivity is a theorem for every block, with no run premise.

**Architecture:** `Block.node parent slot body` replaces `Block.node parent slot root`. A new model module gives a self-delimiting pairing on `Nat` whose size stays small under nesting, with its injectivity. `Block.root` applies it recursively. The store-only variant keeps every payload type, `Interface.block` and the contract statements: the store check stays "the parent is stored" (`blockKnown st b.parent`), and a lemma shows that this is the same as "the store has a block with root `b.parent.root`". There is no wire-validity root check, and `excludes` gains no clause. For FG-SA, the FG block gets a body, and the ordered signed rows are packed into the base body, so `ContentAgree` becomes a theorem. The five regime root fields stay, filled by the universal lemma; their removal is a later, separate API change. The work runs on a branch in a worktree, because the type change breaks every downstream library until the last task. Main moves only when the branch is green.

**Tech Stack:** Lean 4 v4.30.0-rc2, Mathlib (no `lake update`), Lake libraries of this repository.

**Spec:** `docs/FRAMEWORK-DESIGN.md` §12 (I9, with the user's decisions of 2026-09-29) and §2 E4. Design study: `~/ethereum/research/async-resilient-committees/tip-stability/codex/derived-root.md` (r203), with `codex/scratch/r203-followups.md` and the evidence in `codex/scratch/r203/` (both under that research directory, not under this repository). Survey of the merged tree: `claude-files/i9/survey.md`. Plan 1b report: `docs/PHASE1B-REPORT.md`. Audits: `docs/audit/i9-plan-audit-report.md` (Astra, REVISE 3/5/2) and `~/ethereum/research/async-resilient-committees/tip-stability/codex/scratch/i9-plan-fgsa-review.md` (fgsa-impl, ADOPT WITH FIXES 0/3/3). See "Audit disposition".

## Decisions that this plan implements

```text
┌────┬───────────────────────────────────────────────┬──────────────────────────────┐
│ D  │ Decision                                      │ By                           │
├────┼───────────────────────────────────────────────┼──────────────────────────────┤
│ D1 │ The root is a function of content; a block    │ user, 2026-09-29             │
│    │ does not carry its own root; it carries its   │                              │
│    │ parent's root                                 │                              │
│ D2 │ The parent-root check is the store dependency │ user, 2026-09-29             │
│    │ lookup only; an unknown parent root is a      │                              │
│    │ temporary missing dependency; no wire root    │                              │
│    │ check; wire forwarding waits for a P2P spec   │                              │
│ D3 │ Store-only variant: payloads keep resolved    │ controller; DC-simplify      │
│    │ blocks (the parent's root is `b.parent.root`);│ agreed; the user was asked   │
│    │ no Msg, Interface or contract change. This is │                              │
│    │ a resolved-block model with an equivalent     │                              │
│    │ store lookup, not a root-only wire (A05)      │                              │
│ D4 │ Codec `epair` (length-delimited, r2), not     │ controller; Astra A01        │
│    │ `Nat.pair` and not r1's `lpair` alone: both   │                              │
│    │ grow too fast under nesting (Finding 1).      │                              │
│    │ Task 0 checks it before any other task        │                              │
│ D5 │ Honest proposers use body 0; FG-SA's base     │ r203 §1, §3                  │
│    │ body packs (application body, signed rows)    │                              │
│ D6 │ Regime root fields stay, filled by            │ r203 §4, §9 step 5           │
│    │ `rootInjective_all`; removal is a later plan  │                              │
│ D7 │ One joint change on the merged tree, FG-SA    │ r203 §9; DC-simplify         │
│    │ included                                      │                              │
│ D8 │ Order: I9 before Phase 2 and plan 1c          │ user, 2026-09-29             │
│ D9 │ FG-SA `rowsOk` is a full reconstruction check │ controller; Astra A02,       │
│    │ of the base body in `wellFormed` and          │ fgsa-impl F1/F6; DC m5       │
│    │ `blockAccepted`. It is a content check, not a │ accepts; not a user decision │
│    │ root check, so it is inside D2. It is a wire- │                              │
│    │ validity choice; I9-REPORT lists it           │                              │
│ D10│ The FG codec is a type class `RowCodec V`     │ controller; fgsa-impl F2     │
│    │ with an instance for `Fin n`, so statement    │                              │
│    │ texts keep their form                         │                              │
└────┴───────────────────────────────────────────────┴──────────────────────────────┘
```

## Findings that shape the plan (survey of d0d913a; corrected by the audits)

1. **Nesting makes pairings grow.** An FG row names earlier roots, and the row encoder nests those roots many levels deep in the second argument of the pairing. `Nat.pair` about doubles the bit length at each level: the signed-row sketch `claude-files/i9/pairsize.py` gives B1 = 10,054 bits and extrapolates to about `1.1·10^13` bits at B3 (the script computes B1 only; the body-0 generic G02 encoding gives about `2.1·10^10` bits at B3). r1's `lpair` has `|lpair a b| ≤ |a| + 2|b| + 1`, so it also doubles the second argument: Astra measured 1.6·10^9 to 5.5·10^10 bits at B3. The r2 codec `epair` (Task 0) codes the length of `b`, not `b` twice: `|epair a b| ≤ |a| + |b| + 2·|bitLen b| + 1`. Astra's arithmetic check gives 337, 3,045 and 22,181 bits for B1–B3 of the signed-row sketch. This is a candidate until Task 0 checks it in Lean.
2. **Kernel evaluation.** The v4.30.0-rc2 kernel has GMP fast paths for `Nat` `+ - * / %`, `^` (exponent below `2^24`), `gcd`, `beq`/`ble`, `land`/`lor`/`xor` and both shifts. `Nat.log2` has no fast path, but its definition is a `Nat.rec` on its argument with `ble` and `div` steps, so the kernel unfolds it in about `log2 n` steps. The trailing-zero count for decoding needs a definition of the same form. Task 0 must check kernel evaluation, and also `#eval`. Controller spike (2026-09-29, scratch, core Lean): with `epair`, a 5-row nested sketch gives 244, 3,057 and 34,108 bits for B1–B3; `decide +kernel` proves a B3 root inequality, a B3 order and a B3 decode round trip in about 20 s with no axioms. Plain `decide` fails: the elaborator does not evaluate `2 ^ k` above `exponentiation.threshold` (256), and a raised threshold reaches the recursion limit. So fixtures with large roots use `decide +kernel`. Second controller spike (r4 shape: doubling then binary search on `>>>`, fuel `n + 1`; `#guard` against `Nat.log2 n + 1` for `n < 3000` and at `2^100000`, `2^100000 − 1`): B4 has 375,796 bits; `decide +kernel` proves a B4 inequality and `B3 < B4` in about 2.5 s wall time, 0.5 GB peak RSS, no axioms.
3. **The unchanged FG-SA payload has no application-body field.** The base body packs an application value and the ordered signed rows. Admission checks that the base body equals the packing of its own decoded application value with the carried rows (D9).
4. **Parent-content reads.** Every handler reads the carried parent only after the store membership check (Grid CO/SA `admitProposal`, `GridCO/Model/Protocol.lean:319`; SA-PC `proposalEnters`, `SAPC/Model/Handlers.lean:38,54`; L*, `LStar/Model/Protocol.lean:283`; FG-SA `parentFG`, `FGSA/Model/Handlers.lean:62`). The only reads without a store check are the state-free `wellFormed` parent-slot tests: `GridCO/Model/Protocol.lean:337`, `SAPC/Model/Handlers.lean:65`, `LStar/Model/Protocol.lean:300`, `FGSA/Model/Handlers.lean:96`.
5. **Lock.** `docs/catalog.lock` has 250 lines. Astra ran the lock dependency algorithm on the compiled tree: 91 locked declarations reach `AvailableChain.Block`. r203's `lock-impact.tsv` also marked ten scalar `_le_trans` theorems as CHANGE; they do not reach `Block`. The expected set is `docs/plans/i9-lock-expected.tsv` (91 names).
6. **Drift.** Since r203's snapshots, only three main Lean files changed (`GridCO/Model/Protocol` docstring, `GridCO/Proofs/Handling` +1, `GridCO/Proofs/Hooks` −6). All 21 FG-SA files are byte-identical to r203's FG-SA snapshot.
7. **Missing-dependency behaviour is a handler fact, not a run fact.** "Outside `ExecutionValid`" is not the same as "delivered but waits forever": `PartialSynchrony` and `HealthyPrefixDelivery` have relay obligations with no dependency guard (`AvailableChainStatements/Generic/Conditions.lean:104-151`). This plan proves only the lookup lemma and the per-protocol no-op facts. The relay feasibility question stays open for plan 1c.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- No `sorry`, `admit`, `native_decide` or new axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`. `decide +kernel` is allowed (the kernel checks it; it adds no axiom). A switch from `decide` or `rfl` to `decide +kernel` in a base fixture (Tasks 3–6) is a proof change: list it in the task report (DC m3).
- The Mac `lean` is a 3-slot throttle wrapper. Run `pgrep -fl lean` before a build. Use `lake env lean --run <file>` for scripts; never a `lean_exe`.
- **Worktree.** All work is in `~/worktrees/available-chain-i9` on branch `i9-derived-roots`, created from main at the plan's approval commit. Clone `.lake/packages` with `cp -c -R`. Main does not change until Task 11. Every commit ends with the `Claude-Session:` line. Commit by explicit path (`git add <paths>`, then `git commit -m` with no pathspec).
- **Build states.** After Task N, every library that Task N or an earlier task owns builds with `--wfail`. Downstream libraries may fail until their task. This replaces, for this plan only, the full-default-target checkpoint rule of `docs/PHASE1B-REPORT.md:120`; Task 11 restores it. A task never weakens a downstream file to make it build.
- **Statements.** These statements do not change as text: `gridContract_from_engine`, `saContract_from_engine`, `sapcContract_from_engine`, `sapcStrong_from_engine`, plan 1b's `holds*` rows and WindowMargin and hook facts, and every `AvailableChainFramework` declaration. Other statements may change only in these ways: (a) the old root field, the old root formula, or a numeric root value is replaced; (b) a `[RowCodec V]` instance binder is added (D10); (c) a change named in the exception table below. Each change is listed in the task report with the old and new text. No `#print axioms` line is removed from a `Tests/Axioms.lean` file, and every printed theorem shows only the allowed axioms.
- **No wire root check.** Do not add a root or parent-root conjunct to any `wellFormed` or to any handler. Do not add a clause to any `excludes`. `blockKnown` keeps its definition. FG-SA's `rowsOk` is a content check (D9), not a root check.
- **Payloads.** No `Msg`, `Wire`, `Payload` or `Interface` type changes. `fgBlock` and `blockAccepted` in FG-SA change their bodies only as Task 9 states.
- **Fixtures keep their intent.** A test that shows a fork, a counterexample, a refusal or a tie keeps showing it, for the same cause. A refusal fixture that tests a check other than `rowsOk` has `rowsOk = true`. A fixture that asserted a root collision becomes a positive injectivity or duplicate-refusal test (r203 §8). Record the old and new intent of each changed test in the task report.
- **Layering.** Proofs stay out of `AvailableChainStatements` (AGENTS.md). FG-SA packing fixtures stay in FG-SA; SimplexFG does not import FG-SA.
- **Lock.** Tasks 0–10 do not run `CatalogLock --write`. Task 11's stop rule applies. This is a declared lock break (see "Lock break").
- Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md` or `docs/audit/*.log`.
- Prose in ASD-STE100 Simplified Technical English; tables in Unicode box drawing inside fenced `text` blocks. No time estimates.

### Named statement exceptions (A03)

```text
┌──────────────────────────────────────┬────────────────────────────────────────────┐
│ Theorem (file)                       │ Allowed change                             │
├──────────────────────────────────────┼────────────────────────────────────────────┤
│ SAPC.honest_proposal_views           │ `.node parent s ⟨s * (parent.root.value+1)⟩│
│ (SAPC/Proofs/Proposals.lean:49)      │ becomes `.node parent s 0`                 │
│ GridCO proposal statements           │ the same constructor replacement           │
│ (GridCO/Proofs/Proposals.lean:65,223)│                                            │
│ FGSA.eraseFG_fgBlock                 │ adds `rowsOk b rows = true`                │
│ (FGSA/Proofs/Admission.lean:49)      │                                            │
│ FGSA.fgBlock_root (:64)              │ adds `b ≠ .genesis`, `eraseFG P = b.parent`│
│                                      │ and `rowsOk b rows = true`                 │
│ FGSA.metaInv_accepted                │ adds `(hrows : rowsOk b rows = true)`;     │
│ (FGSA/Proofs/Metadata.lean:340)      │ `metaInv_process` passes it from `hacc`    │
│ FGSA `MetaInv.wireTree` (Statements/ │ strengthened with the stored content       │
│ Invariants.lean)                     │ equality (`rowsOk`), Task 9 Step 3         │
│ FGSA `not_contentAgree` and the      │ replaced by the positive tests of Task 9   │
│ negative cross-store example         │ Step 5 (collision tests, r203 §8)          │
│ (Tests/RootCollision.lean)           │                                            │
│ SimplexFG collision-driven frame     │ replaced by the distinct-roots proof of    │
│ fallback (Frame.lean:176–200)        │ Task 7 Step 3                              │
│ FGSA.fgBlock_notMem (:70)            │ adds the same three premises, so that the  │
│                                      │ freshness premise names the FG root        │
│ Generic FG theorems that use `derive`│ gain `[RowCodec V]` only (class (b)):      │
│ or root readers (SimplexFG, KitFG,   │ `RootInjectiveOn.symm`, `uniqueJust_chains`│
│ FGSA Carrier: `eraseFG_slot`,        │ `finalLock`, `accountable`, `causalCap`,   │
│ `eraseFG_root`, `eraseFG_parent`,    │ `causalCap_notRoot`, and the twelve        │
│ `eraseFG_eq_genesis`, …)             │ Carrier theorems                           │
│ Deleted private helpers (5 names;    │ allowed; controller ruling on I9-A01       │
│ see the note below)                  │ (added 2026-09-29)                         │
└──────────────────────────────────────┴────────────────────────────────────────────┘
```

*Added 2026-09-29 (controller ruling on Astra's pre-final audit I9-A01, `docs/audit/i9-branch-audit-0-8-report.md`):* the deletion of private helper theorems that served only a removed root-field or root-formula proof is allowed, when the public statement they served is kept or is in this table. The deleted helpers are `delivered_blocks`, `emitted_blocks`, `named_block` and `roots` (`SAPC/Tests/CleanInvariantCounterexample.lean`) and `emitted_proposed` (`Witnesses/Sanity.lean`); `docs/I9-REPORT.md` lists them. A statement change outside (a), (b) and this table stops the task: report it to the controller. The constructor terms inside `GridCO.honest_proposal_exists` and `SAPC.honest_proposal_exists` are proof terms, not statement text.

## Review Focus

1. **A handler path that skips the parent lookup.** Every insertion of a block into a store must follow `blockKnown st b.parent` (or FG-SA's `parentFG`). Test: Task 1's lookup lemmas, the per-protocol no-op lemmas of Tasks 3, 4, 5 and 9, and the audit of every insertion site.
2. **FG and base content disagree.** `eraseFG (fgBlock P b rows) = b` must hold for every accepted proposal. Test: Task 9's erasure lemma under `rowsOk`, and the Smoke check that a wrong outer row list with the right signed-row code is refused.
3. **Signed-row rounds are lost.** Two row lists with the same decoded rows and different rounds must give different bodies and roots. Test: Task 9 Step 5.
4. **Tie outcomes change silently.** `ghostStep`, `liveRoot`, `deepest`, `lexKey`, `lexMax` and `bestEligible` order roots numerically. New roots change the order. Every fixture with an order outcome states its expected winner again, computed from the new roots, and proves the root order that makes it win. Test: each task's fixture step.
5. **A refusal test passes for the wrong reason.** After the change, a fixture can be refused by `rowsOk` or by a new root order instead of the check that it names. Test: each refusal fixture has a companion that satisfies every other check (Task 9 Step 5, Task 7 Step 3).

## Lock break

The change of `Block`'s third constructor argument (from `root : BlockId` to `body : Nat`) changes the closure of every lock line that reaches `Block`. The expected set is the 91 names of `docs/plans/i9-lock-expected.tsv` (Finding 5); 159 lines stay unchanged. No declaration in `AvailableChainFramework` changes its source text or its type; the lines change because their closure changes.

## Tasks

### Task 0: Codec

**Files:**
- Create: `AvailableChainModel/Objects/Codec.lean`
- Modify: `AvailableChainModel.lean` (import)
- Scratch: `claude-files/i9/spike/` (outside the Lake libraries)

**Interfaces:**
- Produces: `bitLen : Nat → Nat`, `tz : Nat → Nat` (trailing zeros), `lpair`, `epair : Nat → Nat → Nat`, `efst`, `esnd`, `efst_epair`, `esnd_epair`, `epair_inj`, `bitLen_epair_le`; `encList`, `encOption`, `encBool` with injectivity lemmas.

- [ ] **Step 1: Definitions.** In arithmetic form (Astra A01):
  - `bitLen` (DC-simplify M1; Astra R01): TOTAL and globally correct, with log-step evaluation. Phase 1 doubles `w` (1, 2, 4, …) until `n >>> w = 0`; phase 2 is a binary search for the exact bit length inside `[w/2, w]` with `>>>`. Both phases are structural recursion on an input-dependent fuel (for example `n + 1`), which the kernel unfolds only as far as the search goes; no fixed fuel constant. Prove the fuel sufficient (the search ends before the fuel runs out) and prove, for EVERY `n`: `bitLen 0 = 0`, `n < 2 ^ bitLen n`, and `n ≠ 0 → 2 ^ (bitLen n - 1) ≤ n` (equivalently `bitLen n = if n = 0 then 0 else Nat.log2 n + 1`). No branch returns a truncated length: a truncated length makes `epair` collide (`epair 1 (2^(M−1)) = epair 0 (2^M + 2^(M−1))` if both give length `M`). Do not use `Nat.log2` in the evaluated path: its kernel unfolding is quadratic in the bit length (DC measured about 50 s at 10^5 bits, and no result in 10 min for a 175,564-bit depth-4 FG-SA comparison; a log-step form took under 1 s).
  - `lpair a b := 2 ^ bitLen b * (2 * (a * 2 ^ bitLen b + b) + 1) - 1`. The factor in parentheses is odd, so `tz (lpair a b + 1) = bitLen b`.
  - `epair a b := lpair (a * 2 ^ bitLen b + b) (bitLen b)`. The delimiter codes the length of `b`, not `b`.
  - `tz` by structural recursion on the fuel `m + 1` for input `m`, with `%` and `/` steps (Finding 2); prove it exact for every nonzero `m`: `m = 2 ^ tz m * r` with `r` odd. A fixed fuel is not enough: the outer delimiter can have more than 64 trailing zeros (Astra R01). The decoders `efst`, `esnd` use `tz`, `/`, `%` and `2 ^ ·` only.
- [ ] **Step 2: Laws.** All laws hold for every input, with no range premise: `efst (epair a b) = a`, `esnd (epair a b) = b`, hence `epair_inj`. `bitLen (epair a b) ≤ bitLen a + bitLen b + 2 * bitLen (bitLen b) + 1`. Prove through the factorisation `lpair a b + 1 = 2^k * odd`, not through bitwise reasoning. `encList enc xs` (right fold of `epair` with a length or a terminator, so that order and duplicates stay) with `encList_inj` for an injective `enc`; `encOption`, `encBool` likewise.
- [ ] **Step 3: Size and kernel spike** (A01, F4). In the scratch directory, build with `epair`:
  - the generic G02 FG chain (three blocks with the rows of `SimplexFG/Store.lean:163–212`, rows naming earlier roots, body 0), with r203's row encoders (§3);
  - the FG-SA signed-row packing of that chain (`packBody` of Task 9, with the `RowWire` rounds of `FGSA/Tests/Smoke.lean`'s `stA`).
  - a B4 block on the generic chain, and one store-level fixture: FG-SA `stA` with `process` (admission of a packed proposal).
  Record the bit length of every root, by `#eval`. Then prove one root inequality and one root order comparison between B3-depth roots and between B4-depth roots by `decide +kernel`, and one `efst`/`esnd` round trip on a B3-size value by `decide +kernel`. Record the wall time and the peak RSS of each check (`/usr/bin/time -l`) against `LEAN_CAP_GB`. Before a kernel check counts as "does not finish", `#eval` its Boolean: a false `decide +kernel` goal shows as "maximum recursion depth" or "deep recursion", not as false (DC m2). **Stop rule:** if a B3 root has more than 10^6 bits, if a true kernel check does not finish, or if a check comes near `LEAN_CAP_GB`, stop and report; do not continue with Task 1.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainModel`; `#print axioms` for the laws. Commit `Model: length-delimited codec` (the spike files stay uncommitted in `claude-files/`).

### Task 1: Block with a body; universal root injectivity

**Files:**
- Modify: `AvailableChainModel/Objects/Blocks.lean`
- Modify: `AvailableChainStatements/Generic/Conditions.lean` (docstring of `RootInjective` only)
- Create: `AvailableChainKit/Roots.lean` (new theorem `rootInjective_all`; it imports `AvailableChainStatements.Generic.Conditions`, where `RootInjective` is (`Conditions.lean:28`); `AvailableChainKit/Core.lean` imports only `Generic.Properties`; DC m1). Match the section binders of `RootInjective` (including any `[Fintype V]`).

**Interfaces:**
- Consumes: Task 0's `epair`, `epair_inj`.
- Produces: `Block.node (parent : Block) (slot : Slot) (body : Nat)`; `nodeRoot`; `Block.root`, `Block.body`; `Block.root_injective : Function.Injective Block.root`; `Block.root_ne_genesis_of_node`; `parent_mem_iff_root` and `parent_mem_and_iff_root` (list store); `rootInjective_all` (Kit).

- [ ] **Step 1: Type.** Change the third argument of `Block.node` to `body : Nat`. `nodeRoot (pr : BlockId) (s : Slot) (x : Nat) : BlockId := ⟨epair pr.value (epair s x) + 1⟩`. `Block.root .genesis = genesisRoot`; `Block.root (.node p s x) = nodeRoot p.root s x`. Keep `slot`, `parent?`, `parent`, `depth`, `preceq` and the `Ancestry` section unchanged in shape.
- [ ] **Step 2: Injectivity.** Prove `Block.root_injective` by induction on the first block, generalizing the second (r203 §4, with `epair_inj`). Genesis versus a node is impossible because node roots are positive; no slot premise is needed, so a slot-0 node differs from genesis.
- [ ] **Step 3: Store lookup** (A04, F3). Run-free, in `AvailableChainModel`:
  - `parent_mem_iff_root : b.parent ∈ blocks ↔ ∃ p ∈ blocks, p.root = b.parent.root`;
  - `parent_mem_and_iff_root : (b.parent ∈ blocks ∧ q b.parent) ↔ ∃ p ∈ blocks, p.root = b.parent.root ∧ q p`, for any predicate `q` on blocks. This covers the four state-free parent-slot tests (Finding 4) once the child-shape and authentication checks are kept separate.
  Docstring (A05): the lookup is over the image of `Block.root`, genesis included. The model is a resolved-block model: every carried parent is some `Block`, and the store check is equivalent to a lookup by its root. A root-only wire needs more than this lemma and a decoder: its adapter must also preserve authentication, dependencies, handler calls, refusals and proposal origin (r203 `derived-root.md:106`). That refinement is open.
- [ ] **Step 4: Kit.** `rootInjective_all (E) (I) (rho) : RootInjective E I rho` from `Block.root_injective`, in `AvailableChainKit/Roots.lean`. Update the `RootInjective` docstring in Statements (text only): it is now a theorem for every run, proved in the Kit.
- [ ] **Step 5: Checkpoint.** `lake build --wfail AvailableChainModel AvailableChainStatements`. Commit `Model: derived block roots; universal root injectivity`. (`AvailableChainKit` builds in Task 2.)

### Task 2: Kit, engine v2 sketch, Framework

**Files:**
- Modify: `AvailableChainKit/Engine/HealthyPrefix.lean` (`healthyPrefix_rootInjective` keeps its name and statement, proved from `rootInjective_all`), `AvailableChainKit/Engine/HealthyInterior.lean`, `AvailableChainKit/Core.lean` (`block_preceq_trans` binder names), `AvailableChainEngineV2/Sketch.lean` (the two folds at :95, :104: body `k`, not root `⟨k+1⟩`; update both consistently), `AvailableChainFramework/Catalog/Mono.lean` (only if it breaks; its two copies of `rootInjective` stay valid).
- Audit (no change expected): `AvailableChainKit/Engine/Execution.lean` (its `Event.node` match is not a `Block.node`), `AvailableChainStatements/Generic/Regimes.lean`, `AvailableChainStatements/Strong/Regimes.lean`.

- [ ] **Step 1:** Repair constructor binders (a binder that named a root now names a body; do not reuse a `BlockId` term as a body). Keep every statement.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainKit AvailableChainEngineV2 AvailableChainFramework`. Run `CatalogLock --check`; save the output as `claude-files/i9/lock-task2.out`; do not write. The CHANGED names must already be a subset of the expected set. Commit `Kit, EngineV2, Framework: derived roots`.

### Task 3: Grid CO and SA

**Files:**
- Modify: `AvailableChainGridCO/Model/Protocol.lean` (`propose` :287–293: `Block.node parent s 0`), `AvailableChainGridCO/Proofs/Proposals.lean` (:65, :223, class (a)), `AvailableChainGridCO/Proofs/Roots.lean` (`RootInjectiveBelow` and the six scope lemmas: prove from `Block.root_injective`, keep names and statements), the other `AvailableChainGridCO/Proofs/*` files of the survey's list that fail, `AvailableChainGridCO/Tests/Smoke.lean`, `AvailableChainSA/Proofs/{Outage,FastOutage}.lean`, `AvailableChainSA/Tests/Smoke.lean`.

- [ ] **Step 1:** Change `propose`. Rebuild; repair each failing proof. Use named projections, not positional ones, where a conjunction changed.
- [ ] **Step 2: Lookup and no-op.** Instantiate `parent_mem_and_iff_root` for `wellFormed` at :337 (`b.parent?.isSome && b.parent.slot < s`). Prove `admitProposal_missingParent : ¬ blockKnown st b.parent → admitProposal … st … = st` (the existing return before carried votes, `Protocol.lean:319`), if no such lemma exists.
- [ ] **Step 3: Fixtures.** Smoke `:56, 61, 62, 108`: bodies instead of literal roots; keep the sibling fork; `badChild` keeps "same slot as its parent". SA Smoke `:10–12`: `X` stays a sibling of `B` at slot 1 with a different body. State each order outcome again and prove the root order (Review Focus 4).
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainGridCO AvailableChainSA`; the `Tests/Axioms.lean` files show only the allowed axioms; plan 1b's WindowMargin and hook facts build unchanged in statement. Commit `GridCO, SA: derived roots`.

### Task 4: SA-PC

**Files:**
- Modify: `AvailableChainSAPC/Model/Choice.lean` (`propose` :86–87, body 0), `AvailableChainSAPC/Model/Handlers.lean` (instantiation of the lookup lemma; no change to handler bodies), `AvailableChainSAPC/Proofs/Proposals.lean` (:49–55 `honest_proposal_views`, named exception; :106), the SA-PC proof files of the survey's list that fail, `AvailableChainSAPC/Tests/Smoke.lean`, `AvailableChainSAPC/Tests/CleanInvariantCounterexample.lean`.
- Audit (no change expected): `AvailableChainSAPC/Model/Objects.lean`, `AvailableChainSAPC/Statements/QuorumRecovery.lean`.

- [ ] **Step 1:** As Task 3 Step 1. `excludes` stays `fun _ _ => false`, and `receipt_acceptedRelay` keeps its `rfl`.
- [ ] **Step 2: Lookup and no-op.** Instantiate `parent_mem_and_iff_root` for `wellFormed` at `Handlers.lean:65`. No-op facts: `proposalEnters` is false for a missing parent; a direct PC with missing paths returns `st` through `pcEnvelopeReady` (`Handlers.lean:38,54`).
- [ ] **Step 3: Fixtures.** `CleanInvariantCounterexample:27–28`: `x` and `y` keep the same parent and slot with different bodies; the docstring at :9 says "its root is larger": choose bodies so that `x.root > y.root` holds, prove it by `decide`, and check that the complete valid-run counterexample still holds. The `roots` field at :247 uses `rootInjective_all`. Smoke `:9–12, 97, 151`: bodies; give `x` an explicit body 0, because `completeRoundCheck` compares `x` with the honest proposal (:179).
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainSAPC`; `Tests/Axioms.lean` shows only the allowed axioms. Commit `SAPC: derived roots`.

### Task 5: L*

**Files:**
- Modify: `AvailableChainLStar/Model/Protocol.lean` (`propose` :253–259, body 0), `AvailableChainLStar/Proofs/Hooks.lean`, `AvailableChainLStar/Tests/Smoke.lean`.

- [ ] **Step 1:** As Task 3 Step 1. Re-prove `excludes_stable`, `excludes_proposal_iff` and the stored-block clause facts (r203-followups item 1); their statements do not change.
- [ ] **Step 2: Lookup and no-op.** Instantiate `parent_mem_and_iff_root` for `wellFormed` at :300. The handler (`Protocol.lean:283`) returns `st` for a missing parent and does not repeat the parent-slot test: state only the lookup equivalence and the no-op fact, not an equivalence of the two paths.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainLStar`. Commit `LStar: derived roots`.

### Task 6: Witnesses, then Registry

**Files:**
- Modify, in this order: `AvailableChainWitnesses/{Sanity,Regimes,Accumulation}.lean`; then `AvailableChainRegistry/Counter.lean` (:13–15 chain: body `k`), `AvailableChainRegistry/CounterRun.lean` (`chain_root` :287 is false after the change: replace it with an index lemma `chain_injective` or use `Block.root_injective`; `counter_rootInjective` :325–330 becomes `rootInjective_all`), `AvailableChainRegistry/Gaps/NoInput.lean` (`clockBlock` :38–40, `clockBlock_root` :191, `clock_rootInjective` :231–238, the same way; the I1 witness keeps its `KNOWN-GAP` status), `AvailableChainRegistry/Instances/*` (re-elaborate only), `docs/REGISTRY.md`, `docs/MATRIX.md` (regenerated).

- [ ] **Step 1: Witnesses** (`AvailableChainRegistry/Sanity.lean:3` imports `AvailableChainWitnesses.Sanity`). Recode every repeated block literal. `Accumulation`: the slot-0 parent stays; `visible` and `hidden` keep the same parent and slot 1 with different bodies. `lake build --wfail AvailableChainWitnesses`.
- [ ] **Step 2: Registry.** Recode the chains; keep the slot-0 first node of `Counter`. Keep every certificate, refutation and gap row.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainRegistry AvailableChainWitnesses`. `lake env lean --run scripts/Registry.lean` then `--check` exit 0; every row keeps its status (the REGISTRY.md and MATRIX.md diffs may change only hashes or text that names roots). The self-test compare exits 0. Commit `Witnesses, Registry: derived roots`.

### Task 7: SimplexFG

**Files:**
- Modify: `AvailableChainSimplexFG/Objects.lean` (`FGBlock` :43–46: `node (parent) (slot) (body : Nat) (rows : List (Row V))`; `FGBlock.root` derived), `ChainState.lean`, `Frame.lean`, `Store.lean`, `Client.lean` (root reads and inline fixtures).

**Interfaces:**
- Produces: `class RowCodec (V : Type) where encodeSigner : V → Nat; encodeSigner_inj : Function.Injective encodeSigner`; `instance : RowCodec (Fin n)`; `encRow`, `encFGBody (body : Nat) (rows : List (Row V)) : Nat` (injective in the pair, under `[RowCodec V]`); `FGBlock.root`; `FGBlock.root_injective`.

- [ ] **Step 1:** Row encoders as r203 §3 lists them, built on Task 0's `epair` and `encList` (not `Nat.pair`). Every root-valued row field is in the code (`NamedHeightPair`, `FinalityPair`, `Evidence` fields, `Client.Record` fields that the rows carry; r203 §6 SimplexFG).
- [ ] **Step 2:** `FGBlock.root (.node p s x rows) = nodeRoot p.root s (encFGBody x rows)`, under `[RowCodec V]` as a section variable, so the source text of the root readers keeps its form (`process_row`, `derive`, `ViewRootInj`, `lexKey`, `lexMax`, `HeadFields.ofBlock`, `record_row`, `createRow`, `update_finality`). Prove `FGBlock.root_injective`.
- [ ] **Step 3: Fixtures.** Recode B1, BX, B1b, childA, childB, B1c, childC, Y, X, B2, B3, B1', Bs, clientB1alt.
  - `ChainState:176–191`: quorum and timeout intent stays.
  - `Frame:144–172`: prove the root order of B1a/B1b that the test needs.
  - `Frame:176–200` (the B1a/B1c collision): a collision-driven fallback is impossible now. Replace it with the proof that distinct content gives distinct roots. Do not substitute an empty-candidate fallback: that is a different test.
  - `Frame:185–212`: keep the distinct B1c, the childC justification, the Y contest and the X viability change.
  - `Store:163–212`: retarget rows to the derived roots; keep finality and each separate refusal cause.
  - `Client:176–199, 238–250`: replace roots that name B1 or clientB1alt; keep the different-entry and the lock/timeout guards.
  State each order outcome again with its root order.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainSimplexFG`. Commit `SimplexFG: FG blocks with a body; derived roots`.

### Task 8: KitFG

**Files:**
- Modify: the KitFG files of the survey (`Accountable`, `Ancestry`, `Certificates`, `ClientSafety`, `Correspondence`, `CrossingNoFinal`, `InBandLock`, `Pins`, `Provenance`, `TwoChanges`) and `CausalCap` (both theorems use `derive`; A06).

- [ ] **Step 1:** Repair constructor binders; add `[RowCodec V]` where a statement reads roots (class (b)). Prove `RootInjectiveOn` and `ViewRootInj` globally from `FGBlock.root_injective`; keep their names.
- [ ] **Step 2:** `Pins.lean`: update the annotations that call root injectivity a run idealization; keep the archived source pins. `bash scripts/check-fg.sh` exits 0. Do not edit `docs/FG-COMPOSITION.md` (DC-simplify owns it); list the entries that need a note in the report.
- [ ] **Step 3: Fixtures.** `TwoChanges:757–767` (`K3`): recode; keep K3's finality-only rows and the `Fmove_atTop` witness; use the universal `ViewRootInj`.
- [ ] **Step 4: Checkpoint.** `lake build --wfail AvailableChainKitFG`; `check-fg.sh` exit 0. Commit `KitFG: derived roots`.

### Task 9: FG-SA

**Files:**
- Modify: `AvailableChainFGSA/Model/{Objects,Frame,Handlers,Store}.lean`, `AvailableChainFGSA/Statements/Invariants.lean`, `AvailableChainFGSA/Proofs/{Admission,Carrier,CrossNode,StoreInv,Metadata,ActView,BlockAncestry,Fields,Nesting,Reconcile}.lean`, `AvailableChainFGSA/Tests/{Smoke,RootCollision,Axioms}.lean`, `scripts/CheckFGSAAxioms.lean` (names only, if names change).
- Audit (no change expected): `AvailableChainFGSA/Model/Clock.lean`, `AvailableChainFGSA/Statements/Store.lean`.
- No import of `AvailableChainStatements` in FG-SA (F3).

**Interfaces:**
- Consumes: Task 7's `RowCodec`, `encFGBody`, `FGBlock.root`; Task 0's `epair`, `efst`, `esnd`, `encList`.
- Produces: `packInner (app : Nat) (rw : List (RowWire n)) : Nat := epair app (encList encRowWire rw)`; `packBody app rw := encFGBody (packInner app rw) (rw.filterMap RowWire.toRow?)`; `appOf : Nat → Nat` with `appOf (packBody app rw) = app`; `rowsOk b rw : Bool := b.body == packBody (appOf b.body) rw` (D9); `fgBlock P b rw := FGBlock.node P b.slot (packInner (appOf b.body) rw) (rw.filterMap RowWire.toRow?)`; `contentAgree` as a theorem.

- [ ] **Step 1: Content packing** (A02, F1). Define `packInner`, `packBody`, `appOf`, `rowsOk` as above. Prove `appOf_packBody`, `packBody_inj` (in `app` and in the ordered `rw`, rounds included), and `rowsOk_iff : rowsOk b rw = true ↔ b.body = packBody (appOf b.body) rw`. Honest `propose` (`Frame.lean:149`) selects the rows first, then builds `Block.node parent s (packBody 0 rw)`.
- [ ] **Step 2: Admission.** Use the SAME `rowsOk` in `wellFormed` (:96) and in `blockAccepted` (after `parentFG` succeeds). Prove the erasure law: `b ≠ .genesis → eraseFG P = b.parent → rowsOk b rows = true → eraseFG (fgBlock P b rows) = b` (named exception). The global law `(eraseFG B).root = B.root` follows by structural induction, because both root functions use the same outer codec (Task 7).
- [ ] **Step 3: Invariants.** `CStoreInv.rootInj` and the second conjunct of `Inv0` are filled by `FGBlock.root_injective` (fields stay). Strengthen `MetaInv.wireTree` with the full content equality (`rowsOk` for each stored proposal); admission establishes it, and the other transitions keep it because they keep the stored proposals. Prove `ContentAgree st st'` for any two stores that satisfy `CStoreInv` and `MetaInv`: equal base roots give equal blocks, hence equal bodies, and `packBody_inj` gives equal ordered signed rows. Raw and support lists stay outside its conclusion. `contentAgree_self` becomes a corollary.
- [ ] **Step 4: Proofs.** Redo the r203 §6 FG-SA list: `eraseFG_fgBlock`, `fgBlock_root` (from the erasure law, not `rfl`), `fgBlock_rows`, `fgBlock_notMem`, `blockAccepted_of_wellFormed`, `rootTest_iff_blockTest`, `blockAccepted_facts`, `accepted_base_facts`, `fg_on_block_accepts`, `admitProposal_of_accept`, `base_admitProposal_accepts`, `admitBlock_accepted_eq`, `admitProposal_base_view`, `actView_admitBlock_sameF`, `actView_admitBlock_movedF`, `admitBlock_sufficient`, `admitBlock_sufficient_absent`, the `Carrier` and `CrossNode` lemmas (including `eraseFG_root`), `Model/Store.lean`'s `activeCompatible`, `normalizeS` and their callers, and `Proofs/{Fields,Nesting,Reconcile}.lean`. The sufficiency theorems get `rowsOk` from their `wellFormed` premise; cross-node theorems keep their now-redundant `ContentAgree` premises. The lookup lemma and the no-op fact (`parentFG = none` returns `st` before any write, `Handlers.lean:62`) are proved here, in the FG-SA library; relating base membership to `parentFG` uses the store correspondence.
- [ ] **Step 5: Tests** (A07). All packed fixtures are local to FG-SA.
  - `RootCollision.lean` (r203 §8): keep `ba`, `c1`, `bb`; prove `ba.root ≠ bb.root`; replace `not_contentAgree` with a positive `ContentAgree stX stY`; show a reader holding `ba` accepts `c1` then `bb`; a repeated `bb` is refused as a duplicate.
  - `Smoke.lean`: build each literal proposal block from its own signed row list with `packBody`. Split `yB` into two blocks, because `:415` and `:534` carry different row lists. Every refusal fixture that tests another check has `rowsOk = true`. The DQ2 case at :208–210 becomes the declared duplicate test. At :374 keep a depth tie and prove the root order before `deepest`. Rebuild the expected packed proposal and root references at :432–447 and :590–607; keep the selected head and record. At :500–501 and :571–573 keep the alternative winners that detect wrong controls, witnesses or filtering, and prove their order. Rebuild `stA` and `wProp` (`:24`, `:144`) from packed content.
  - New checks (r203 §8): genesis versus a slot-0 node; same parent and slot with different bodies; a wrong row list is refused and both stores stay unchanged; a body with the right signed-row code and a wrong outer decoded-row list is refused; two row lists with the same decoded rows and different rounds give different roots.
- [ ] **Step 6: Axioms file** (F5). Regenerate `Tests/Axioms.lean` for any new or renamed public theorem; keep every existing name; keep the `--expect` command of `scripts/CheckFGSAAxioms.lean`.
- [ ] **Step 7: Checkpoint.** `lake build --wfail AvailableChainFGSA`; `bash scripts/check-fgsa.sh` exit 0 (all controls still refused); the axioms check shows only the allowed axioms. Commit `FGSA: signed content in block identity; ContentAgree proved`.

### Task 10: Documents

**Files:**
- Modify: `docs/FRAMEWORK-DESIGN.md` (§12 I9: "As implemented" note; §2 E4 note that I9 added no exclusion), `docs/CONTRACT.md` (the `RootInjective` premise is now a theorem), `docs/MAP.md`, `docs/GRIDCO-STATUS.md`, `docs/FGSA-STORE-REPORT.md` (DQ2/DQ10/I9 status), `docs/PHASE0-REPORT.md` (Roots row closed).

- [ ] **Step 1:** Dated notes only; the approved text stays. Remove no history. Name the L* obligation (DC m4): a future root-only adapter must apply the L* parent-slot test after the store lookup, because the L* handler does not repeat the `wellFormed` parent-slot test (`LStar/Model/Protocol.lean:283, 300`). State: roots are derived; the store check is the dependency lookup; the model is a resolved-block model and a root-only wire refinement is open; the regime root fields are kept and filled by `rootInjective_all`; their removal is a later plan; the relay feasibility question (Finding 7) is open for plan 1c.
- [ ] **Step 2: Checkpoint.** Commit `docs: I9 derived roots`.

### Task 11: Full build, lock, merge

**Files:** `docs/catalog.lock`, `docs/FRAMEWORK-DESIGN.md` (§8 lock log), `docs/I9-REPORT.md` (new).

- [ ] **Step 1:** `pgrep -fl lean`; `lake build --wfail` (every default target; the full-target rule applies again); `CheckFrameworkAxioms`; `check-fg.sh`; `check-fgsa.sh`; `Registry --check`; the self-test compare; the grep `sorry|admit|native_decide|^axiom` over every changed Lean file (outside `scripts/registry-selftest/`); every library root file imports its modules (import coverage).
- [ ] **Step 2: Lock** (A08). If main has moved since the branch point, first merge main into the branch and rebuild with `--wfail`; run the lock step on that merged tree (DC m6). Imported Model or Statements changes can change lock hashes too, so the trigger is any move of main, not only `docs/catalog.lock` or `AvailableChainFramework/**` (Astra R03). Then `CatalogLock --check > claude-files/i9/lock-final.out`. Before the rewrite, the documented result is exit code 1 with CHANGED lines; any other failure (a crash, an elaboration error, a missing module) stops the task. After the rewrite, `--check` must exit 0 with no differences. Stop, and do not write, unless all of these hold:
  - the CHANGED names are exactly the 91 names of `docs/plans/i9-lock-expected.tsv`;
  - no locked name is REMOVED or ADDED;
  - `git diff main -- AvailableChainFramework/` shows no source change, or only binder repairs in `Catalog/Mono.lean` that keep every declaration's type;
  - the changed definitions in the closures (`Block`, `nodeRoot`, `Block.root`, the codec) are the only new or changed definitions that the CHANGED lines reach; list them.
  Then `--write --allow-changes`, and `--check` prints nothing. Add a design §8 lock-log entry with the count, the reason (closure through `Block`) and the names.
- [ ] **Step 3: Merge.** Merge `i9-derived-roots` into main with `--ff-only` if main has not moved since Step 2, else merge main into the branch again and repeat Steps 1–2 on the exact merged tree (build, lock `--check`, closure review) before the `--ff-only` merge (Astra R03). Tell DC-simplify before the merge (FG-SA T7 and the FG-COMPOSITION entries depend on it). Remove the worktree after the merge.
- [ ] **Step 4:** The controller writes `docs/I9-REPORT.md`: tasks and commits, checks, the lock break with its names, every statement change (old and new text), every fixture whose intent changed, and decisions taken without the user.

## Risks

```text
┌────┬────────────────────────────────────────┬──────────────────────────────────────────┐
│ R  │ Risk                                   │ Response                                 │
├────┼────────────────────────────────────────┼──────────────────────────────────────────┤
│ R1 │ The codec's laws are hard to prove     │ Task 0 first; arithmetic factorisation,  │
│    │                                        │ not bit reasoning                        │
│ R2 │ FG roots too large, or kernel checks   │ Task 0 Step 3 measures the worst chains  │
│    │ do not finish                          │ (generic G02 and FG-SA stA) with `#eval` │
│    │                                        │ and `decide`; stop rule                  │
│ R3 │ A proof depended on a numeric root     │ Replace with injectivity or an index     │
│    │ (root = height)                        │ lemma; list it in the report             │
│ R4 │ Order outcomes change and a test keeps │ Review Focus 4 and 5: restate each       │
│    │ passing for a different reason         │ winner; companion fixtures for refusals  │
│ R5 │ FG-SA `fgBlock_root` stops being `rfl` │ Task 9 Step 2: the erasure law under     │
│    │ and many proofs used that              │ `rowsOk` replaces it                     │
│ R6 │ Main moves during the work (Phase 2a,  │ Phase 2a builds new libraries that do    │
│    │ T7)                                    │ not use `Block.node`'s third argument;   │
│    │                                        │ Task 11 Step 3 merges with a full build  │
│ R7 │ A lock line outside the expected set   │ Task 11 stop rule                        │
│    │ changes                                │                                          │
│ R8 │ A statement change outside the allowed │ The task stops and reports; the          │
│    │ classes                                │ controller decides with a new exception  │
└────┴────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Not in this plan

- Removal of the five regime root fields, `CStoreInv.rootInj` and the `Inv0` conjunct (a later API plan; r203 §9 step 5).
- A root-only wire and its adapter (waits for the P2P spec; Task 1 Step 3 states its extra obligations).
- An honest external input for the body (Phase 2c, I1).
- Plan 1c items: "deps never present" classification, the relay feasibility question of Finding 7, inhabitation, certificates.
- An FG-SA `ProtocolSpec` and its `excludes` (T7). A failed `rowsOk` is a permanent refusal of that wire; it needs no `excludes` clause, because with `rowsOk` in `wellFormed` such a wire cannot be delivered directly in an `ExecutionValid` run. A later completeness rule for `excludes` must state its well-formed-input scope.

## Audit disposition

r1 (24ecaaa) had two reviews: Astra `docs/audit/i9-plan-audit-report.md` (REVISE, 3 blocking, 5 major, 2 minor) and fgsa-impl `…/codex/scratch/i9-plan-fgsa-review.md` (ADOPT WITH FIXES, 0/3/3). DC-simplify's Opus review is pending; its findings go here before execution.

```text
┌─────┬──────────────────────────────────────┬──────────────────────────────────────────┐
│ Id  │ Finding                              │ Disposition in r2                        │
├─────┼──────────────────────────────────────┼──────────────────────────────────────────┤
│ A01 │ lpair doubles under nesting; Nat.log2│ D4, Finding 1–2, Task 0: `epair` codes   │
│     │ has no kernel fast path              │ the length; `#eval` AND `decide` checks  │
│ A02 │ rowsOk too weak; FG node must keep   │ D9, Task 9 Steps 1–3: full reconstruction│
│     │ the inner packed value               │ check; FG body = `packInner`             │
│ A03 │ Statement rule conflicts with needed │ Global Constraints: classes (a)–(c) and  │
│     │ changes                              │ the named exception table                │
│ A04 │ Three-case lemma false as written;   │ Task 1 Step 3 lookup lemma; per-protocol │
│     │ ExecutionValid ≠ waits forever       │ no-op facts; Finding 7; relay → 1c       │
│ A05 │ Range of nodeRoot ≠ image of root;   │ D3, Task 1 Step 3 docstring              │
│     │ wire equivalence overstated          │                                          │
│ A06 │ Missing sites (CausalCap, FGSA Store,│ Tasks 4, 8, 9 file lists; audit-only     │
│     │ Fields, Nesting, Reconcile, SAPC     │ lists in Tasks 2, 4, 9                   │
│     │ Handlers)                            │                                          │
│ A07 │ FG-SA fixtures: signed rows, yB,     │ Task 9 Step 5; Global Constraint on      │
│     │ refusal causes                       │ refusal fixtures; Review Focus 5         │
│ A08 │ Lock: 91 CHANGE, not 101; weak stop  │ Finding 5, `i9-lock-expected.tsv`, Task  │
│     │ rule                                 │ 11 Step 2                                │
│ A09 │ rootInjective_all in Statements      │ Task 1 Step 4: in the Kit                │
│ A10 │ References, paths, proof terms       │ Spec line, Task 3/4/5/9 refs, exception  │
│     │                                      │ table note                               │
│ Q6  │ Witnesses before Registry; FG-SA     │ Task 6 order; Global Constraints         │
│     │ fixtures local; build-rule exception │ (Layering, Build states)                 │
│ F1  │ rowsOk = full body equality, same fn │ D9, Task 9 Steps 1–2                     │
│     │ in wellFormed and blockAccepted      │                                          │
│ F2  │ RowCodec as a class                  │ D10, Task 7 Interfaces, class (b)        │
│ F3  │ Lemma run-free in Model; FG-SA does  │ Task 1 Step 3; Task 9 Files, Step 4      │
│     │ not import Statements                │                                          │
│ F4  │ Spike covers FG-SA packing and stA   │ Task 0 Step 3                            │
│ F5  │ Regenerate Tests/Axioms, keep        │ Task 9 Step 6                            │
│     │ --expect                             │                                          │
│ F6  │ rowsOk inside D2                     │ D9                                       │
└─────┴──────────────────────────────────────┴──────────────────────────────────────────┘
```

DC-simplify's combined verdict on r2 (Opus review `docs/audit/i9-plan-claude-review.md` with fgsa-impl): ADOPT WITH FIXES, 0 blocking, 1 major, 6 minor. r3 applies all of them: M1 (log-step `bitLen`; B4 and store-level spike; time and RSS in the stop rule; Task 0 Step 1, Step 3), m1 (`AvailableChainKit/Roots.lean` imports `Generic.Conditions`), m2 (`#eval` before "does not finish"), m3 (`decide +kernel` switches listed per task), m4 (L* obligation in Task 10), m5 (D9 is a decision without the user; I9-REPORT lists it), m6 (merge main before the lock step). Gate: one Astra pass on r3 with no blocking and no major finding.

Astra re-check of r3 (`docs/audit/i9-plan-recheck-report.md`): REVISE, 1 blocking, 1 major, 1 minor; A02, A04–A07, A09, A10 RESOLVED; the 91-name set confirmed against the compiled tree. r4 applies: R01 (total, globally correct log-step `bitLen` with input-dependent fuel and a sufficiency proof; `tz` with fuel `m + 1`; all codec laws unrestricted), R02 (`metaInv_accepted` premise, `MetaInv.wireTree`, and the collision-test replacements in the exception table), R03 (lock and closure checks on the exact merged tree; exit-code rule). Gate: an Astra pass on r4 with no blocking and no major finding.

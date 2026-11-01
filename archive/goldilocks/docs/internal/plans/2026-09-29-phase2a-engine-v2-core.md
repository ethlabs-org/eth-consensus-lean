# Phase 2a: engine v2 core — Implementation Plan (r3)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A frozen engine v2 core (design §2 E1, E2, E5, with the E4 hooks and the reserved E6 and input interfaces) and a Kit v2 port, so that the FG-SA T7 steps that do not wait for the lift (T7.0–T7.7, T7.9, T7.10; not T7.8, T7.12 or the lift parts of T7.6, as T7 §1a says) can start on v2. Dated note (2026-09-29, DC-simplify from the T7 r5 reviews, F2): T7.8 and T7.12 need only Task 5 of this plan, not the 2b lift.

**Architecture:** Everything goes into the library `AvailableChainEngineV2` (engine, conditions, laws; namespace `AvailableChain.V2`) and a new library `AvailableChainKitV2` (engine lemmas). Nothing goes into `AvailableChainFramework` except one anchor declaration at the gate, which adds lock lines only. `ProtocolSpec` takes the run-chosen input type as a parameter. One atomic `tick` function gives both the post-tick state and the released objects. Restart, `durable`, `restore` and the input are reserved now, so that 2b and 2c add declarations but never change a 2a type. Stages 2b (the lift, v2 claims) and 2c (E6, the toy protocol, I1) get their own plans after 2a is frozen.

**Tech Stack:** Lean 4 v4.30.0-rc2, Mathlib (no `lake update`), Lake libraries of this repository.

**Spec:** `docs/FRAMEWORK-DESIGN.md` §2 (E1–E6, Lift), §1, §8 ("Order after plan 1b"), §9. Order check: `docs/audit/phase2-order-check-report.md` (conditions O1–O4; §6 self-delivery). Survey: `claude-files/p2/survey.md`. FG-SA T7 plan: branch `fgsa-composition-plan` (a0f08c6), `docs/plans/2026-09-29-fgsa-composition-t7-t1.md`. I9 plan: `docs/plans/2026-09-29-i9-derived-roots.md`.

## Decisions

```text
┌────┬─────────────────────────────────────────────────┬──────────────────────────────┐
│ D  │ Decision                                        │ By                           │
├────┼─────────────────────────────────────────────────┼──────────────────────────────┤
│ D1 │ Phase 2 in stages; 2a unblocks the T7 steps     │ user (Phase 2 asap, both     │
│    │ that do not need the lift (Goal); 2b lift; 2c   │ parts); DC-simplify; Astra   │
│    │ E6, toy, I1                                     │                              │
│ D2 │ Reserve NoRestart, durable, restore and the     │ Astra O2; DC-simplify        │
│    │ input in 2a; later stages only ADD              │                              │
│ D3 │ The input is a TYPE PARAMETER                   │ controller (survey R1): a    │
│    │ `ProtocolSpec (In : Type)`, per validator and   │ field would let a protocol   │
│    │ time (`Run.input : V → Time → In`); the claim   │ set `In := Unit`. Necessary, │
│    │ domain fixes `In` (2c)                          │ not sufficient: 2c states    │
│    │                                                 │ the exact condition (DC N2)  │
│ D4 │ Self-delivery at the emission time through      │ DC-simplify (i-a); Astra §6  │
│    │ `process` is allowed, not required; 2a proves   │                              │
│    │ it admissible; an optional `SelfDelivery`       │                              │
│    │ condition exists; FG-SA regimes do not require  │                              │
│    │ it                                              │                              │
│ D5 │ No P2P forwarding rule beyond the v1 receipt    │ user; DC-simplify            │
│    │ premises; DC's receipt relay stays              │                              │
│ D6 │ 2a code outside the Framework; an anchor under  │ controller (survey §5, R4)   │
│    │ a new locked prefix `AvailableChainFramework.V2`│                              │
│    │ at the gate (ADDED lines only)                  │                              │
│ D7 │ The E4 hooks stay run-level (deviation (i)),    │ design §8 row 0; T7 plan     │
│    │ with stability on restart-free intervals of     │ T7.7                         │
│    │ ALL runs (no `NoRestart` alternative)           │                              │
│ D9 │ Kit v2 restart premises are restore premises:   │ DC-simplify N1; Astra N02    │
│    │ `hrestore` for invariants, `hrestore_now` for   │                              │
│    │ clock lemmas; `NoRestart` only where a lemma is │                              │
│    │ false after a restart                           │                              │
│ D8 │ Tasks 0–4 need no `Block` and may run before    │ controller (survey R5);      │
│    │ the I9 merge; Tasks 5–7 run after it            │ Astra A08                    │
└────┴─────────────────────────────────────────────────┴──────────────────────────────┘
```

Answered by DC-simplify (2026-09-29; survey R6): FG-SA HEAD labels (the SA base, AP duties) are in the `fresh` (CStar) family; FG labels (`.fg r`) are in the `linked` family (one FG identity across rounds, needed for client safety). FG-SA regimes do not require `SelfDelivery`; every FG-SA result holds for both self-delivery timings. `selfDelivery_admissible` shows that one such delivery is admissible; that complete regime runs with the DC timing exist is an inhabitation question (plan 1c). Claim ids for v2 (survey R7) are a 2b question for the user.

## Global Constraints

- Toolchain and Mathlib v4.30.0-rc2. Do not run `lake update`.
- No `sorry`, `admit`, `native_decide` or new axioms. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The Mac `lean` is a 3-slot throttle wrapper. Run `pgrep -fl lean` first. Use `lake env lean --run <file>` for scripts; never a `lean_exe`. When the I9 branch builds at the same time, one build at a time per worktree.
- **Worktree.** Work in `~/worktrees/available-chain-v2` on branch `v2-2a` from main. Before Task 5, merge (or rebase onto) the I9 result on main. Clone `.lake/packages` from the main checkout with `cp -c -R` (APFS clone) when the worktree is created, so that Mathlib is not rebuilt.
- **No v1 edits.** Do not edit `AvailableChainModel/**`, `AvailableChainStatements/**`, `AvailableChainFramework/**` (except Task 7's anchor), the v1 Kit, or any protocol library. v2 copies v1 text; it does not import-and-modify v1 definitions.
- **Imports** (DC N9). `AvailableChainEngineV2` imports only Mathlib, the narrow model modules `AvailableChainModel.Objects.Identifiers`, `AvailableChainModel.Objects.Time`, `AvailableChainModel.Generic.Env` (and `AvailableChainModel.Objects.Blocks` from Task 5 on), and its own modules. It does not import `AvailableChainModel.Objects.Seats`, whose v1 `Auth` and `Signed` clash with the v2 names. `AvailableChainKitV2` imports only Mathlib, those model modules and `AvailableChainEngineV2`. Consumers that open both namespaces use qualified names.
- **Freeze rule** (DC N6). After the gate (Task 7), no declaration in `docs/V2-API.md` changes its name, type or body; in particular a 2a structure never gains a field, a 2a inductive never gains a constructor, a 2a definition never gains a parameter. Kit v2 statements are frozen by this rule only (they are not locked). 2b and 2c add declarations or separate structures.
- Commit by explicit path. Commit messages end with the `Claude-Session:` line. Never stage `log.md`, `state.md`, `docs/FG-COMPOSITION.md`, `docs/audit/*.log`.
- Prose in ASD-STE100; tables in Unicode box drawing inside fenced `text` blocks. No time estimates.

## Review Focus

1. **Emission equals the actual tick** (Astra A01). `emits` and `emittedAt` are defined from the state before the tick EVENT (its index), so a restart at the same time is included. Test: Task 1 `step_tick_eq`, and a restart-then-tick test in Task 1 Step 6.
2. **An asleep node emits nothing and records nothing.** Test: Task 1 `tick_asleep`.
3. **Separation.** AP labels and the designated fresh family `F.fresh` are never self-visible; `Linked` labels may be. Test: Task 3 negative example.
4. **Self-delivery admissibility is real** (Astra A02). The hypotheses hold in a complete finite run. Test: Task 6, a finite `ExecutionValid` witness with a self-delivery at the emission time.
5. **The input type is not a protocol field.** `In` is a parameter; a protocol can still ignore its input (test (c) shows it), so the non-vacuity of the 2c floor needs the 2c condition (DC N2). Test: Task 1 Step 6.
6. **Kit stability covers `recordOwn` and restarts** (Astra A03, N02; DC N1). Every stability or invariant lemma has a `recordOwn` premise (or "factors through `base`"); every field-origin or field-prefix lemma has a field premise on `recordOwn`; every clock lemma has `hrestore_now`. Test: Task 4 counterexample checks.

## Tasks

### Task 0: Libraries and layout

**Files:**
- Modify: `lakefile.toml` (new library `AvailableChainKitV2`; globs for `AvailableChainEngineV2` `Engine/*`, `Conditions/*`, `Laws/*`, `Tests/*`).
- Create: `AvailableChainKitV2.lean` (empty root module; Task 4 extends it; Astra N01).
- Modify: `AvailableChainEngineV2.lean` (imports as the tasks add modules), `scripts/CheckFrameworkAxioms.lean` (scan `AvailableChainEngineV2` and `AvailableChainKitV2`, Astra A10).

- [ ] **Step 1:** Library entries. `Sketch.lean` stays; I9 Task 2 edits its block folds. New 2a modules must not import `Sketch.lean` or `Block` (Tasks 0–4).
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainEngineV2 AvailableChainKitV2`; the axiom check covers both. Commit `EngineV2, KitV2: library layout for 2a`.

### Task 1: Objects, spec, events, tick, runs

**Files:**
- Create: `AvailableChainEngineV2/Engine/Objects.lean`, `Engine/Spec.lean`, `Engine/Run.lean`, `Tests/Engine.lean`.

**Interfaces:**
- Produces: `Auth (L) (seats : L → Nat)` with `seat (ℓ) (i : Fin (seats ℓ)) | none`; `Signed L seats Payload`; `ProtocolSpec (In : Type)` with fields `State Label seats Payload Durable init clock actTime duties duties_spec duties_nodup act gossip process selfVisible recordOwn durable restore wellFormed depsPresent processed excludes handles carries` (`act : State → Label → In → Option Payload`); `P.Object`; `objSelfVisible`; `Event V Object` with `restart | tick | deliver`, phases 0, 1, 2; `World`; `Run V P` with `honest horizon events seatOf input`; `holder`; `tick E rho st v t : P.State × List P.Object`; `World.step`; `stateBefore E rho i`, `stateBeforeTime`, `readAt` (run function; Task 5's output reader is `outputAt`, DC N9), `final`, `emitsAt E rho i` (objects of the tick event at index `i`), `tickIdx?`, `emittedAt`, `emits`, `processes`, `handlesAt`, `acceptsAt`.

- [ ] **Step 1: Objects.** `Auth` and `Signed`, with `deriving DecidableEq` (DC N10 checked that it elaborates on the dependent `Fin`).
- [ ] **Step 2: Spec.** `ProtocolSpec (In : Type)`. `objSelfVisible o := match o.auth with | .seat ℓ _ => selfVisible ℓ | .none => false`. The `selfVisible` docstring states the agreed text (PHASE1B-REPORT :196–201; DC N8): "`selfVisible` controls the private own-signature record. A normal delivery to the emitting node may occur at the emission timestamp, after the tick phase."
- [ ] **Step 3: Tick.** Clock; if awake, the payloads of every duty `ℓ ∈ duties t` for every seat `i` with `seatOf ℓ i = v`, from the post-clock state and `rho.input v t`, in label order then seat order, then gossip; `recordOwn` folded over the self-visible released objects; release. `World.step`: `restart` ↦ `restore (durable _)`, `tick` ↦ `(tick …).1`, `deliver` ↦ `process`.
- [ ] **Step 4: Run functions** (Astra A01). As v1 (`AvailableChainModel/Generic/Run.lean`), each taking `E`. Emission is indexed by the event: `emitsAt E rho i := match rho.events[i]? with | some (.tick v t) => (tick E rho (stateBefore E rho i v) v t).2 | _ => []`. `tickIdx? rho v t := rho.events.findIdx? (fun e => match e with | .tick v' t' => decide (v' = v ∧ t' = t) | _ => false)` (the FIRST matching tick; a predicate on `V` and `Time` only, so no `BEq` on objects; Astra N03, DC N5). `emittedAt E rho v t` is `emitsAt` at `tickIdx?` (empty if none); `emits` quantifies over tick indices. Lemma `mem_emittedAt_iff_emits` under `ScheduleWellFormed` (its `nodup` excludes a second equal tick). `stateBefore E rho i` is the world before event `i`, so a restart at the same time (phase 0) is included.
- [ ] **Step 5: Laws.** `step_tick_eq` (the world after the tick event at `i` is `(tick … (stateBefore E rho i v) v t).1` at `v`, and its released objects are `emitsAt E rho i`); `tick_decomp` (post-tick state = `recordOwn` fold over the released self-visible objects, from the post-clock state); `tick_asleep`.
- [ ] **Step 6: Tests.** (a) A two-label spec with one seat each, three events; `decide` or `rfl` checks of `emitsAt`, `stateBefore`. (b) Restart-then-tick at the same time: state 1 before `t`, restart restores 0, clock keeps the state, `act` emits the state: `emittedAt` reports 0. (c) A spec that ignores its input, typed at `In := Nat` and `In := Unit`; a `#check` that `ProtocolSpec` has no input field.
- [ ] **Step 7: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: objects, spec, tick, runs`.

### Task 2: Conditions without blocks

**Files:**
- Create: `AvailableChainEngineV2/Conditions/Schedule.lean`, `Conditions/Committees.lean`.

**Interfaces:**
- Produces: `PublicTime`, `ScheduleWellFormed`, `DeliveryWellFormed`, `UnforgeableSignatures`, `ExecutionValid` (v1 text over v2 runs; `holder` through `seatOf`; emission through `emitsAt`); `NoRestart`; `restartFree rho v i j` (no restart of `v` at an index `k` with `i ≤ k < j`; restarts of other nodes do not count); `LabelFamilies P` (`ap fresh linked : P.Label → Prop`); `CStar F rho`, `Linked F rho` (one bijection `Fin N ≃ V` for all labels in `F`, `seats ℓ = N`, `Fin.cast`), `SingleSeat F`; `SelfDelivery rho`.

- [ ] **Step 1:** Copy the v1 texts from `AvailableChainStatements/Generic/Conditions.lean`; adapt to v2 runs; record each adaptation in the report.
- [ ] **Step 2:** `Linked F → CStar F` (lemma). `restartFree` endpoint lemmas: `restartFree rho v i i`; `restartFree rho v i (i+1)` fails exactly when event `i` is a restart of `v`.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: schedule, committee and restart conditions`.

### Task 3: Laws without blocks

**Files:**
- Create: `AvailableChainEngineV2/Laws/Isolation.lean`, `Laws/Hooks.lean`, `Laws/SelfDelivery.lean`.

**Interfaces:**
- Produces: `Isolation P F` (`Base`, `base`, `clockB`, `clock_base`, `processB`, `process_base`, `recordOwn_base`, `actB` with the input argument, `act_base` on `F.ap`, `gossipB`, `gossip_base`, `hooks_base` (the hooks restricted to AP objects factor through `base`; for `handles`, both object arguments are AP objects), `separation : ∀ ℓ, F.ap ℓ ∨ F.fresh ℓ → P.selfVisible ℓ = false`); `base_tick : base (tick …).1 = clockB (base st) t`; `HooksSound P` (v1 fields over v2 runs; stability on `restartFree` intervals; `recordOwn_processed` (equality), `recordOwn_deps` (equality), `recordOwn_excludes` (true stays true)); `EmitOk`; `selfDelivery_admissible`.

- [ ] **Step 1: Isolation.** Port the law shapes of `Sketch.lean` (`Isolated`, `foldl_recordOwn_base`) to the new spec. Prove `base_tick` in the stronger form above (Astra: released AP payloads are not an extra dependency). The 2c restore law will reserve both directions, `restore_base` and `durable_base` (note in the docstring).
- [ ] **Step 2: HooksSound.** Stated over v2 runs with `ScheduleWellFormed`; the stability fields take `restartFree rho v i j`.
- [ ] **Step 3: Self-delivery** (Astra A02). `EmitOk` fields: `P.wellFormed o`; `P.depsPresent` in the post-tick state; NOT `P.processed` in the POST-CLOCK state (the `recordOwn_processed` field carries it through the fold); `∀ o', P.carries o o' → False` for the object class of the lemma (or a carried-signature premise; choose one and state it). Premises of `selfDelivery_admissible` (Astra A02): a tick index `i` with `rho.events[i]? = some (.tick v t)`, `v ∈ rho.honest`, `o ∈ emitsAt E rho i` (the previous emission), `objSelfVisible o`, `HooksSound P`, a delivery index `j > i` at time `t` with `rho.events[j]? = some (.deliver v o t)`, and the receiver state unchanged on `[i+1, j)`, stated as the equation `stateBefore E rho j v = stateBefore E rho (i+1) v` (DC N4). Conclusion, at the delivery prefix: the delivery passes the wire, dependency and freshness checks of `DeliveryWellFormed`, and the outer signature has provenance for `UnforgeableSignatures`. The lemma does not claim acceptance by the handler, and it does not claim that the rest of the run stays valid.
- [ ] **Step 4: Append form** (DC N3). `ExecutionValid.snoc_selfDelivery`: if `rho` is `ExecutionValid`, `HooksSound P` holds (for `recordOwn_processed`; `ExecutionValid` does not contain it; Astra re-check 2, M3), every event has key at most `(t, 2)`, `t ≤ rho.horizon`, `v ∈ rho.honest`, the last event of `v` is its tick at `t`, `o ∈` that tick's objects, and `EmitOk` holds, then `rho` with `.deliver v o t` appended is `ExecutionValid`. (T7.10 builds its witness with this lemma.)
- [ ] **Step 5: Negative test.** A spec where an AP label is self-visible has no `Isolation` value for the obvious `LabelFamilies`. The `separation` docstring says that a one-seat label (a proposal) cannot be in `fresh` unless `|V| = 1`, because `CStar` needs `seats ℓ = |V|`; the FG-SA reference assignment is HEAD `ap` and `fresh`, FG `linked`, proposal `ap` and `SingleSeat` (DC N9).
- [ ] **Step 6: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: isolation, hooks, self-delivery`.

### Task 4: Kit v2

**Files:**
- Modify: `AvailableChainKitV2.lean` (created empty in Task 0).
- Create: `AvailableChainKitV2/{ClockLaws,Execution,EngineClock,Stable,Emission}.lean`.

**Interfaces:**
- Produces: `ClockLaws` (v1 fields plus `recordOwn_now`); the v2 forms of the lemmas that the T7 plan names (`eventIndex_lt_of_time_lt`, `readAt_eq_stateBefore`, `stateBefore_tick_eq_stateBeforeTime`, `tick_index_lt_delivery`, `delivery_now_ge_public`, `stateBefore_now_mono`, `stateBefore_now_le_event`, `stateBefore_stable`, `stateBefore_stable_clock`, `stateBefore_invariant`, `stateBefore_now_source`, `clock_field_origin`, `stateBefore_field_prefix`) with their `Execution` dependencies (all of them go into the `docs/V2-API.md` manifest as "not locked"; DC-simplify, T7 r5 review); `stateBefore_other_node` (an event at `w ≠ v` does not change `v`'s component; DC N4); and the generic emission lemmas of DC N7: `emits_bijSeat` (under a bijective seat map `e`, the label-`ℓ` objects that `v` releases are exactly `⟨.seat ℓ (e.symm v), p⟩`), `linked_index_stable` (`(i : Nat) = j → seatOf ℓ i = seatOf ℓ' j` for `ℓ ℓ'` in a `Linked` family), `ownRecord_fold` (a projection that `clock` and `process` keep and that `recordOwn` updates by `g` equals, at `stateBefore E rho i v`, the `g`-fold over the self-visible objects `v` released before `i`; premise `NoRestart`).

- [ ] **Step 1:** Port each lemma from `AvailableChainKit/Engine/{EngineClock,Execution,Stable}.lean`; names kept; namespace `AvailableChain.V2.Engine`; imports narrowed to the v2 engine.
- [ ] **Step 2: `recordOwn` premises** (Astra A03). Every stability and invariant lemma gets `∀ st o, Q st → Q (recordOwn st o)`, or the alternative premise "Q factors through `iso.base`". A field-origin lemma requires that `recordOwn` adds no field rows (`field (recordOwn st o) = field st`); a field-prefix lemma requires `field st <+: field (recordOwn st o)`. Preservation of the source predicate alone is not enough (with source predicate `False` it is vacuous).
- [ ] **Step 3: Restart premises** (D9; DC N1, Astra N02). No lemma takes `restartFree` as its only restart premise when it uses `stateBefore_now_le_event`, because that fact depends on the whole prefix. Shape:
  - `stateBefore_invariant` and every whole-run invariant lemma take `hrestore : ∀ st, Q st → Q (P.restore (P.durable st))` AND `hrestore_now` (its tick step uses `stateBefore_now_le_event` for the clock precondition);
  - `stateBefore_now_le_event` takes `hrestore_now : ∀ d, C.now (P.restore d) ≤ 0` (event times are nonnegative), so it holds across restarts;
  - the interval lemmas `stateBefore_now_mono` and `stateBefore_stable_clock` take `hrestore_now` AND `restartFree` on `[i, j)` (a restart lowers `now`, and no premise keeps `Q` through `restore`); `stateBefore_stable_clock` also gets a restore form with `hrestore` for `Q` and no `restartFree` (DC N1 check);
  - `stateBefore_stable` (interval only) takes `restartFree` on its interval;
  - `stateBefore_now_source` (Astra re-check 2, M1): its first alternative becomes `now ≤ 0` (not `now = 0`), because `Time` is `Int` and `hrestore_now` allows a negative `now`;
  - field lemmas (M2): `clock_field_origin` takes `hrestore_field : ∀ st x, x ∈ field (P.restore (P.durable st)) → x ∈ field st` (restore adds no rows; it holds when `field init = []`); `stateBefore_field_prefix` takes `restartFree` on its interval, or the restore form `∀ st, field st <+: field (P.restore (P.durable st))`;
  - `NoRestart` only for `delivery_now_ge_public` and `stateBefore_tick_eq_stateBeforeTime`, which are false after a restart at a non-public time or at the tick time; and `ownRecord_fold`;
  - `NoRestart` corollaries of the restore forms, for callers that want them.
  With `Durable := Unit` and `restore := fun _ => init`, `hrestore` holds for every `Q` with `Q init`, and `hrestore_now` holds by `ClockLaws.init`. List every lemma with its restart premise in the report; 2c ADDS lemmas for durable clocks and keeps these.
- [ ] **Step 4: Counterexample checks.** (a) A predicate on a private flag that clock and process preserve and `recordOwn` changes: `stateBefore_stable`'s premises fail for it. (b) Astra N02's run (ticks at 0 and 2, a restart at 1 that sets `now := 100`): `hrestore_now` fails for that `restore`. (c) `Q st := st.flag = true`, `restore := fun _ => init` with `init.flag = false`: `hrestore_now` holds, `Q` fails after a restart inside `[i, j)`, so `stateBefore_stable_clock` needs `restartFree` (DC N1 check). Short `example`s.
- [ ] **Step 5: Checkpoint.** `lake build --wfail AvailableChainKitV2`; axiom check. Commit `KitV2: engine lemmas`.

### Task 5: Conditions with blocks; interface; outputs (after the I9 merge)

**Files:**
- Create: `AvailableChainEngineV2/Conditions/Delivery.lean`, `Conditions/Interface.lean`, `Laws/Outputs.lean`.

**Interfaces:**
- Produces: `PartialSynchrony`, `HealthyPrefixDelivery` (v1 text with the exclusion exemption and DC's receipt relay); `Interface P` (`confirmed`, `stable`, `block`, `opening`, `propLabel : Slot → P.Label`, `propLabel_single : P.seats (propLabel s) = 1`); `proposalTime`, `proposerOf`; `outputAt` (the output reader; not `readAt`, DC N9); `BlockInRun`, `RootInjective` (post-I9) and `rootInjective_all`; `OutputsFactor I iso` (every output getter factors through `base`).

- [ ] **Step 1:** Merge or rebase onto main after the I9 merge. Copy from the post-I9 text.
- [ ] **Step 2: Checkpoint.** `lake build --wfail AvailableChainEngineV2`. Commit `EngineV2: delivery conditions, interface, outputs`.

### Task 6: Toy run and self-delivery witness (after the I9 merge)

**Files:**
- Create: `AvailableChainKitV2/Tests/Toy.lean` (moved from EngineV2 by the layer rule, 1cece1d).

- [ ] **Step 1:** A toy spec on the new engine: receipts in `base`, the own record outside `base`, a state-preserving clock, one Linked self-visible label that emits a previously unseen row and carries nothing, one-seat AP proposal labels indexed by slot (`propLabel` injective, as `Interface.propLabel_injective` requires; 2a Task 5 fix round 1). Give its `Interface`, `Isolation`, `OutputsFactor` and `HooksSound` values. Also show that a run with an honest emitter satisfies `HealthyPrefixDelivery` at a cut past `t + Δ`, and add one relay case (an accepted object that another node handles before the deadline) (Task 5 review M1).
- [ ] **Step 2:** A complete finite run with a tick, a self-delivery at the emission time, and a delivery to another node. Prove `ExecutionValid` for the whole run (Review Focus 4), and check that `selfDelivery_admissible`'s hypotheses hold at the self-delivery.
- [ ] **Step 3: Checkpoint.** `lake build --wfail AvailableChainEngineV2`; axiom check. Commit `EngineV2: toy run with a self-delivery`.

### Task 7: Gate — manifest, anchor, lock, merge

**Files:**
- Create: `docs/V2-API.md` (the frozen API manifest: every 2a declaration that T7 and 2b may use), `AvailableChainFramework/V2/Anchor.lean`.
- Modify: `scripts/CatalogLock.lean` (`lockedModulePrefixes` gains `AvailableChainFramework.V2`), `AvailableChainFramework.lean` (import), `lakefile.toml` if needed.

- [ ] **Step 1: Anchor** (Astra A07). `AvailableChainFramework` may import `AvailableChainEngineV2` (design §1: L2–L3 may depend on L0–L1). The anchor is one `def` whose VALUE references every declaration of `docs/V2-API.md` from `AvailableChainEngineV2`, as a chain `let _ := @a; let _ := @b; …; ()` (a tuple can fail across universes; DC N6), so its closure contains each one. Do not import `AvailableChainKitV2` into the Framework (L5); list the Kit v2 lemmas in the manifest as "not locked".
- [ ] **Step 2: Build the anchor** (Astra A07 re-check). `lake build --wfail AvailableChainFramework` after the anchor and the `lockedModulePrefixes` change; the checks below import built modules.
- [ ] **Step 3: Coverage check.** A small script (or `CatalogLock` option) that reads `docs/V2-API.md` and checks, with the same dependency rules as `scripts/CatalogLock.lean:132–165`, that each listed engine declaration is in the anchor's closure; exit 1 if one is missing, and exit 1 if the anchor itself is missing.
- [ ] **Step 4: Lock.** `CatalogLock --check`: ADDED lines only (under `AvailableChainFramework.V2`), against the post-I9 lock. `--write` (no `--allow-changes`). `--check` prints nothing.
- [ ] **Step 5: Full build.** `pgrep -fl lean`; `lake build --wfail` (every default target, `AvailableChainKitV2` included); `CheckFrameworkAxioms` (EngineV2 and KitV2 scanned); `Registry --check`; `check-fg.sh`; `check-fgsa.sh`; the grep for `sorry|admit|native_decide|^axiom` over the new files.
- [ ] **Step 6: Docs.** `docs/MAP.md` rows; a dated design §2 note "As implemented in Phase 2a" with the agreed `selfVisible` sentence (Task 1 Step 2); the finite checked v2 traces added to the design §8 Phase 2 acceptance row (DC N8); `docs/PHASE2A-REPORT.md` (controller).
- [ ] **Step 7: Merge.** Merge `v2-2a` into main (`--ff-only` if possible, else `--no-ff` after `merge-tree` and a full build). Tell DC-simplify: the manifest and the report. fgsa-impl then writes the v2 revision of the T7 plan against the manifest (survey R10).

## After 2a (outlines; each gets its own plan and audit)

**2b — lift and v2 claims.**
- Generic parts in `AvailableChainFramework/V2` and `Catalog/V2` (ADDED lock lines only): v2 properties and regimes (each with `NoRestart` and `CStar` on the fresh family); the v2 `Instance` (binds `LabelFamilies`, `Isolation`, `OutputsFactor`, `HooksSound`, `Interface`); `ClaimDomain.v2 In`; the 14 claims and 3 profiles under new ids (the user decides the scheme); v2 `StrongInstance`; `Simulation`, `ClaimSim`, `ClaimSim.holds`.
- Concrete parts in L4 (Registry or protocol libraries), not in the Framework (Astra A09): the lifted instances, the transported `grid_holds`, `sa_holds`, `sapc_holds_*`, Counter certificates and Sanity refutations, and the finite checked traces of lifted Grid CO, SA and SA-PC.
- Input in the context correspondence (Astra A04): legacy v2 contexts ≃ v1 contexts × (V → Time → In), or an embedding that is a section of the projection for a chosen input stream; certificate transport needs an input value (no transport at `In = Empty`); refutation transport needs the reverse conclusion implication on embedded contexts.
- Hooks for lifted instances (Astra A05): v2 `HooksSound` quantifies over runs with restarts and over non-bijective seat maps. A v1 hook proof does not give it. Prove the five facts per protocol on v2, with the legacy restart behaviour (`Durable := Unit`, `restore := fun _ => init`) and the Kit's restore premises (D9); a `NoRestart` premise cannot give the full `HooksSound` value. Do not weaken the v2 hook interface.
- AP projection hooks (2a Task 3 re-review d1): `Isolation`'s factors (`depsB`, `processedB`, `excludesB`, `handlesB`) are constrained only on `F.APObject` (AP-signed or unsigned objects). The 2b AP projection must mask them off `F.APObject` with a permissive value, or a delivery of a non-projection object (an FG row) can fail the projection's `DeliveryWellFormed`; `F.ap` is a `Prop`, so the mask needs classical or decidable `ap`.
- `n` versus `Fintype.card V` (Astra A06): prove the relation from `CStar` for protocols with a non-empty legacy label family; handle protocols with no old labels (for example `clockChain`) separately.
- Registry: v2 instance and strong-instance types; the new floor's certificate form; old ids, certificates and the I1 `KNOWN-GAP` history kept.

**2c — restart, toy protocol, I1.** The E6 restore law (`RestoreLaw` with `restore_base` and `durable_base`), epochs, rejoin conditions, `catchUp`, restart regimes; restart-aware Kit lemmas ADDED beside the frozen `NoRestart` ones (including per-node forms of `stateBefore_tick_eq_stateBeforeTime` and `delivery_now_ge_public`, for example with `restartFree rho v 0 i` and `hrestore_now`; 2a Task 4 review m4); the toy Linked, self-visible, restart protocol (a non-trivial restart, receipt loss outside the durable state, a later delivery that is fresh in the new epoch); the I1 fix, with the exact non-vacuity condition (DC N2): (i) the decoder is a FUNCTION of the output block (`decode : Block → Option In` applied to `I.block` of the honest proposal), not a relation and not a decoder on the payload; (ii) the conclusion is the equality `decode b = some (rho.input (proposerOf rho I s) (proposalTime I s))`, with no premise that assumes the binding; (iii) REVISED (DC-simplify, 2026-09-29; Opus study with Astra sub-checks, `research/async-resilient-committees/tip-stability/codex/scratch/i1-noninvacuity-opus.md`, to be copied to `docs/audit/` with the 2c plan): the old form "the regime and trigger are closed under a change of `rho.input`" fails for a protocol whose proposal reads its input (a changed input changes the honest proposal, and the same event list then breaks `UnforgeableSignatures`). The candidate form is closure up to events: `Run.reinput rho f evs := { rho with input := f, events := evs }` (the environment, the honest set, the horizon, the seat map and the point stay) and `InputClosed I W x t₀ := ∀ f, ∃ evs, SleepyRegime₂ I W x.E (x.rho.reinput f evs) t₀`, in the conclusion of a new floor claim `core.input.bound.v2` beside the (ii) binding equality; `Const := Unit`; the regime is the one of `includedConfirmed₂`; `decode` goes in a 2c facet (`InputInstance`), because the 2a `Interface` is frozen. The study rejects existence per input (a witness can put its only honest proposal within Δ of the horizon, and it accepts protocols that get stuck only under partial sleep), two inputs at one slot, and an engine-defined re-execution map (post-I9 roots hash the content, and GHOST breaks ties on the root). If plan 1c states its run-extension theorem for every skeleton and every input, `InputClosed` is one general corollary; SA and Grid CO put body 0 today and fail (ii), as they should, so they need an input-aware port. Limits L1–L3: §8 of the note (partial-participation breadth goes to 1c `Eligible`); (iv) REVISED (same study): the floor profile is stated at ONE fixed INFINITE `In` (for example `Nat`), not a family. Two elements are not enough: Astra found a protocol that passes the whole floor at `Bool` with an output that is a fixed chain with one block per input value, so the output never depends on the input; the same works for every finite `In`. `core.input.bound.v2` is never a floor on its own: it has the same regime and skeleton-only trigger as `includedConfirmed₂`, and it counts as the I1 floor only inside `core₂` together with inclusion and the shared D; a certificate or profile that has it without inclusion does not count (note V10: otherwise a protocol whose output reads only a never-honest seat passes vacuously; DC-simplify); The 2c plan audit decides the final form of (iii) and (iv); for FG-SA the decoder unpacks the post-I9 packed body; `clockChain` lifted at a non-trivial `In` and refuted, `Candidate` kept as the legacy floor (order check O1). E6's `Durable` is a protocol-chosen type that can carry a protocol's private record: FG-SA will keep at least Λ durable (its signing record, as in slashing protection) so that T7.9 client safety holds on all runs. CLOSED 2026-09-29 by the user (via DC-simplify; final form): the faithful form keeps Λ and F with F's chain state (an anchor) and prunes the history below F; it comes with the planned anchor-and-pruning feature (design §8). Until then FG-SA uses the interim form: Λ kept, store reset to its initial state, no claim reads F across a restart. 2a does not change; T7.9 holds on all runs (Λ is durable; DC-simplify, T7 r8/r9); the FG output claims that read F across a restart are for `NoRestart` runs until the anchor feature (DC-simplify). Check the lift and the finite traces again against the final 2c engine.

## Risks

```text
┌────┬────────────────────────────────────────┬──────────────────────────────────────────┐
│ R  │ Risk                                   │ Response                                 │
├────┼────────────────────────────────────────┼──────────────────────────────────────────┤
│ R1 │ `DecidableEq` on dependent `Auth`      │ Does not occur: `deriving` works (DC N10)│
│ R2 │ Every run function takes `E`; Kit      │ Accepted (survey R9); the port records   │
│    │ lemma statements change                │ each changed statement                   │
│ R3 │ A 2a type must change after T7 starts  │ Freeze rule, manifest and anchor; a      │
│    │                                        │ change is a declared lock break with     │
│    │                                        │ DC-simplify's review                     │
│ R4 │ T7 needs restart-aware hook facts      │ D9: with `Durable := Unit`, T7.5 and     │
│    │ (Astra 6: T7.5, T7.7, T7.9)            │ T7.7 hold on all runs through the restore│
│    │                                        │ premises; T7.9 needs `NoRestart` until   │
│    │                                        │ FG-SA has a durable Λ (2c)               │
│ R5 │ I9 changes a copied v1 text            │ Tasks 5–7 wait for the I9 merge (D8)     │
│ R6 │ Two worktrees build at once on 3 Lean  │ One build per worktree at a time; the    │
│    │ slots                                  │ controller orders builds                 │
└────┴────────────────────────────────────────┴──────────────────────────────────────────┘
```

## Audit disposition

Astra audit (`docs/audit/phase2a-plan-audit-report.md`): REVISE, 1 blocking, 8 major, 1 minor. All applied in this revision: A01 (emission from the tick event, Task 1 Steps 4–6), A02 (`EmitOk`, Task 3 Step 3), A03 (Kit `recordOwn` premises, Task 4 Steps 2–3), A04–A06 and A09 (2b outline), A07 (manifest, anchor value, coverage check, Task 7), A08 (task split: Tasks 0–4 before I9, 5–7 after), A10 (KitV2 in the build and axiom check, Task 0). Also from the report: separation names the designated fresh family; `actB` keeps the input; `base_tick` in the stronger form; 2c restore law reserves both directions; 2c adds restart-aware Kit lemmas and keeps the frozen ones; the I1 floor needs a specified decoding relation. DC-simplify review: pending.

Re-check of r2 (`docs/audit/phase2a-plan-recheck-report.md`, Astra): REVISE, 0 blocking, 5 major, 2 minor. DC-simplify's Claude review of r2 (`docs/audit/phase2a-plan-claude-review.md`): ADOPT WITH FIXES, 0 blocking, 1 major, 9 minor. r3 applies all of them:

```text
┌──────────────┬─────────────────────────────────────────────┬──────────────────────────┐
│ Id           │ Finding                                     │ r3                       │
├──────────────┼─────────────────────────────────────────────┼──────────────────────────┤
│ Astra A02    │ EmitOk lemma lost the emission premise      │ Task 3 Step 3 premises   │
│ Astra A03    │ recordOwn can add field rows                │ Task 4 Step 2 field      │
│              │                                             │ premises                 │
│ Astra A05    │ NoRestart cannot give full HooksSound       │ D7, R4, 2b outline       │
│ Astra A07    │ Coverage and lock before the anchor builds  │ Task 7 Steps 2–4         │
│ Astra N01    │ KitV2 root created too late                 │ Task 0 Files             │
│ Astra N02 +  │ restartFree does not give clock lemmas      │ D9, Task 4 Step 3        │
│ DC N1        │                                             │                          │
│ Astra N03 +  │ emittedAt index                             │ Task 1 Step 4 (`tickIdx?`│
│ DC N5        │                                             │ `findIdx?`, first tick)  │
│ DC N2        │ D3 necessary, not sufficient                │ D3, Review Focus 5, 2c   │
│ DC N3        │ Append form of self-delivery                │ Task 3 Step 4            │
│ DC N4        │ Locality lemma                              │ Task 3 Step 3, Task 4    │
│ DC N6        │ Freeze rule text; anchor as a let chain     │ Global Constraints,      │
│              │                                             │ Task 7 Step 1            │
│ DC N7        │ Generic emission lemmas for T7.9            │ Task 4 Interfaces        │
│ DC N8        │ Goal scope; selfVisible text; §8 traces     │ Goal, Task 1 Step 2,     │
│              │                                             │ Task 7 Step 6            │
│ DC N9        │ Narrow imports; two readAt; fresh docstring │ Imports, Tasks 1, 3, 5   │
│ DC N10       │ R1 does not occur                           │ Task 1 Step 1, R1        │
│ DC (2c)      │ E6 Durable carries a private record         │ 2c outline               │
└──────────────┴─────────────────────────────────────────────┴──────────────────────────┘
```

Re-check 2 of r3 (`docs/audit/phase2a-plan-recheck2-report.md`, Astra): REVISE, 0 blocking, 3 major, 0 minor; Tasks 0–2 may start. Applied: M1 (`stateBefore_stable_clock` restartFree, already in 204cf2e; `stateBefore_now_source` weakened to `now ≤ 0`), M2 (field restore premises), M3 (`HooksSound P` in the append form). Task 3 Step 4 and Task 4 use the corrected text.

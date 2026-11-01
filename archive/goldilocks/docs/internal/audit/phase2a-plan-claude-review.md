# Phase 2a plan — Claude review (r2)

_2026-09-29. Reviewer: Claude (Opus). Subject:
`lean/available-chain/docs/plans/2026-09-29-phase2a-engine-v2-core.md`.
First review at `d98c352` (r1). This report is on r2 at `cb33acd`
(cited "Plan:<line>"). It keeps the r1 findings only where they still
apply. This review is read-only on the repository. Context: design §1, §2, §8; PHASE1B-REPORT;
the order-check report; Astra's plan audit
(`docs/audit/phase2a-plan-audit-report.md`, REVISE 1/8/1); `Sketch.lean`;
`claude-files/p2/survey.md`; `scripts/CatalogLock.lean`; v1 `Run.lean`,
`Conditions.lean`, `Framework/Hooks.lean`, `Kit/Engine/{Stable,EngineClock,
Execution}.lean`; the I9 plan; the T7 plan at
`~/worktrees/available-chain-fgsa-plan` `d6871e4` (cited "T7:<line>")._

## Verdict

**ADOPT WITH FIXES.** On r2: 0 BLOCKING, 1 MAJOR, 9 MINOR.

The r1 BLOCKING item (emission read from `stateBeforeTime`) is fixed by
A01. It is the same defect that Astra found. The r1 MAJOR items on
self-delivery (M2) and D8 (M3) are fixed by A02 and A08. The r1 MAJOR item
on D3 (M1) is now MINOR: the 2c outline has the main constraints, but not
the exact condition that makes the floor non-vacuous. The one MAJOR item on
r2 (N1) is a statement-shape decision for the Kit v2 lemmas. The freeze makes it final, and it
decides how much restart work T7.5 and T7.7 have. Fix N1 before Task 4.

```text
┌────┬──────────┬─────────────────────────────────────────────┬───────────────┐
│ ID │ Severity │ Finding (r2)                                │ Plan lines    │
├────┼──────────┼─────────────────────────────────────────────┼───────────────┤
│ N1 │ MAJOR    │ Kit v2: "restartFree on its interval" is    │ 129, 190–192  │
│    │          │ not enough for the clock lemmas; use        │               │
│    │          │ restore premises, so that T7.5/T7.7 hold on │               │
│    │          │ all runs for restore := init                │               │
│ N2 │ MINOR    │ D3/Review Focus 5 still overclaim; give 2c  │ 23–26, 64,    │
│    │          │ the exact non-vacuity condition             │ 176           │
│ N3 │ MINOR    │ No run-level (append) form of self-delivery;│ 116, 44       │
│    │          │ T7.10 expects one                           │               │
│ N4 │ MINOR    │ EmitOk's "no change of v's state" needs a   │ 116, 126      │
│    │          │ locality lemma in the Kit                   │               │
│ N5 │ MINOR    │ emittedAt "the index": define it with a     │ 89            │
│    │          │ tick predicate; the emits link needs nodup  │               │
│ N6 │ MINOR    │ Freeze rule text is narrower than the       │ 54            │
│    │          │ manifest                                    │               │
│ N7 │ MINOR    │ Kit v2 omits generic lemmas that T7.9 needs │ 126           │
│ N8 │ MINOR    │ Goal scope vs T7 §1a; docs step omits two   │ 5, 163        │
│    │          │ agreed texts                                │               │
│ N9 │ MINOR    │ Imports and names: v1 Auth/Signed clash;    │ 53, 84, 139   │
│    │          │ two readAt; one-seat labels not fresh       │               │
│ N10│ MINOR    │ R1 does not occur (checked in Lean)         │ 184           │
└────┴──────────┴─────────────────────────────────────────────┴───────────────┘
```

## Check of the A01–A08 fixes

```text
┌─────┬──────────┬────────────────────────────────────────────────────────┐
│ ID  │ Status   │ Assessment                                             │
├─────┼──────────┼────────────────────────────────────────────────────────┤
│ A01 │ correct  │ emitsAt E rho i reads stateBefore at the tick EVENT    │
│     │          │ index (Plan:89), so a same-time restart is included.   │
│     │          │ step_tick_eq ties it to World.step (Plan:90). Test (b) │
│     │          │ (Plan:91) is the case I checked in Lean for r1: plan   │
│     │          │ r1 gave [5], the actual tick [0]. See N5 for the       │
│     │          │ emittedAt helper.                                      │
│ A02 │ correct  │ Post-clock freshness; recordOwn_processed through the  │
│     │          │ fold; carried objects excluded or a premise; the       │
│     │          │ conclusion names the three DeliveryWellFormed checks   │
│     │          │ and outer-signature provenance (Plan:116). See N3, N4. │
│ A03 │ correct, │ recordOwn premise or "factors through base" is right   │
│     │ N1       │ (Plan:129). The restart part is not: see N1.           │
│ A04 │ correct  │ Product equivalence or a section (Plan:171). It also   │
│     │          │ answers my r1 m2.                                      │
│ A05 │ correct  │ Plan:172. Per-protocol v2 hook proofs become easier    │
│     │          │ with N1.                                               │
│ A06 │ correct  │ Plan:173.                                              │
│ A07 │ correct  │ Manifest + anchor VALUE + coverage check (Plan:156,    │
│     │          │ 159–160). The lock hashes definition bodies and        │
│     │          │ theorem statements in the closure (CatalogLock:121–    │
│     │          │ 135), so the named theorems also get a tripwire. See   │
│     │          │ N6.                                                    │
│ A08 │ correct  │ Tasks 0–4 need no Block: Objects, Spec, Run, the       │
│     │          │ Block-free conditions, Isolation, HooksSound, EmitOk,  │
│     │          │ the Kit. OutputsFactor, Interface and the toy moved    │
│     │          │ after I9 (Plan:39–40, 133–151). The Kit v2 Execution   │
│     │          │ port needs only ScheduleWellFormed, not v1 Regimes.    │
└─────┴──────────┴────────────────────────────────────────────────────────┘
```

A09 (concrete lifted results in L4) and A10 (KitV2 in the build and in the
axiom check) are also applied correctly (Plan:170, 73, 162).

## Findings on r2

### N1 (MAJOR). Restart premises of the Kit v2 lemmas: decide them now, and prefer restore premises

Plan:129 says: "Each lemma that crosses a restart takes `NoRestart` (or
`restartFree` on its interval)." R4 (Plan:190–192) says that T7.7 "proves
[restart-aware hook facts] on its own spec, or states `NoRestart`".

Two problems:

1. **`restartFree` on the interval is not sufficient for the clock
   lemmas.** v1 `stateBefore_stable_clock` (`EngineClock.lean:175`) and
   `stateBefore_invariant` (`:145`) use `stateBefore_now_le_event`: at
   every event, `now` of the node is at most the event time. That fact is
   proved by induction from index 0. It depends on the WHOLE prefix, and
   so on every earlier restart. It does not depend only on the interval
   `[i, j]`. After an earlier restart, `now (restore d)` is not controlled
   by any 2a law. So a `restartFree rho v i j` premise does not give the
   `C.now st ≤ t` premise at the ticks in `[i, j]`. The interval-only
   lemma (`stateBefore_stable`, `Stable.lean:12`) is fine with
   `restartFree`.
2. **T7 cannot "state `NoRestart`" and keep the `HooksSound` shape.** The
   v2 `HooksSound` stability fields quantify over ALL runs with
   `ScheduleWellFormed`, on `restartFree` intervals (Plan:112, 115). A fact
   with a `NoRestart` premise does not have that shape. With the Kit as
   planned, T7.7's `excludes_stable` (the row window and the Grid CO
   old-label clause need `now` monotone, T7:680–684) needs its own
   restart proofs, or it waits for the 2c lemmas.

Recommended shape (premises only; no 2a type changes):
- `stateBefore_invariant` and each whole-run invariant lemma take
  `hrestore : ∀ st, Q st → Q (P.restore (P.durable st))` in place of
  `NoRestart`.
- `stateBefore_now_le_event` and the lemmas that use it take
  `hrestore_now : ∀ d, C.now (P.restore d) ≤ 0`. Event times are
  nonnegative (`in_horizon`; `Time := Int`). Then `now ≤` event time holds
  at every event, across restarts. `now` is monotone on every
  `restartFree` interval, also after an earlier restart.
- Keep `NoRestart` corollaries for callers that want them. Keep
  `NoRestart` ONLY where it is really necessary: `delivery_now_ge_public`
  and `stateBefore_tick_eq_stateBeforeTime` fail after a restart at a
  non-public time or at the tick time.

Effect on FG-SA T7 (the question in the coordinator's message): the T7 v2
value is `Durable := Unit`, `restore := fun _ => init` (survey §2.2). Then
`hrestore` holds for every `Q` with `Q init`, and `hrestore_now` holds
because `ClockLaws.init` gives `now init = 0`. So:
- **T7.5** (`Reachable` at every state, `stored_proposal_delivered`): holds
  on ALL v2 runs, because `Reachable init` is true. No `NoRestart` is
  necessary.
- **T7.7** (the five hook facts): hold in the exact `HooksSound` shape, on
  `restartFree` intervals of all runs. No 2c dependency.
- **T7.9** (client trace): needs `NoRestart`. This comes from the protocol,
  not from the Kit. With `Durable := Unit`, a restart resets Λ, so an
  honest node can sign a row after a restart that conflicts with a row
  from before the restart. Client safety then fails on restart runs. Design
  E6 puts Λ in the FG durable part for this reason. The T7 v2 revision must
  record that T7.9 and the FG claims are for `NoRestart` runs until FG-SA
  has a durable Λ (2c or Phase 4). Every 2b legacy regime has `NoRestart`,
  so this agrees with the 2b claims.

With this shape, 2c must ADD lemmas only for durable clocks. Plan:129 and
Plan:176 already require that 2c adds lemmas and does not change the 2a
statements.

### N2 (MINOR; r1 M1, reduced). D3 is necessary, not sufficient; give 2c the exact condition

r2's 2c outline (Plan:176) now has the binding in the conclusion, no
premise that assumes it, a non-trivial `In` for `clockChain`, and "a
specified decoding relation (not a protocol-supplied `binds := True`)".
Three items remain:

1. **The exact non-vacuity condition.** Let the decoder be a FUNCTION of
   the output block, for example `decode : Block → Option In` applied to
   `I.block` of the honest proposal. Let the conclusion be the equality
   `decode b = some (rho.input (proposerOf rho I s) (proposalTime I s))`.
   Let the claim's regime and trigger be closed under a change of
   `rho.input`. Then even a protocol-supplied decoder cannot trivialize
   the floor. Proof sketch: a protocol that ignores its input has the same
   block in two runs that differ only in the proposer's input. The
   conclusion then gives `decode b` equal to two different values. So
   `In` needs two distinct elements. A RELATION (`binds : In → Payload →
   Prop`) or a decoder on the PAYLOAD (a side field that never reaches the
   block) does not have this property. Write these three conditions into
   the 2c outline. They are more exact than "specified". For FG-SA the
   post-I9 body is `pack appBody rows` (I9 plan D5), so its decoder must
   unpack. That is permitted by the condition above.
2. **One fixed `In` for the floor.** `ClaimDomain.v2 In` (Plan:169) is a
   family. State the floor profile at one fixed type with two distinct
   elements. Then no instance is registered as a "floor" instance at
   `Unit` (trivial binding) or at `Empty` (no runs, so every `holds` is
   vacuous).
3. **Review Focus 5 (Plan:64)** still says "the input cannot be trivialized
   by the protocol". Test (c) (Plan:91) shows that ignoring the input is
   POSSIBLE. Only the `#check` (no input field) is a 2a fact. Change the title to "the
   input type is not a protocol field", and change D3's "By" text
   (Plan:25–26) to "necessary, not sufficient".

### N3 (MINOR; r1 M2 point 4). No run-level form of the self-delivery lemma

Plan:116 limits the conclusion to the delivery's own checks: "it does not
claim that the rest of the run stays valid". For an INSERTION into a run,
that is correct: an inserted delivery changes the states that later
deliveries read, so their `fresh` can fail. Plan:44 moves "complete regime
runs with the DC timing" to plan 1c. That is also correct.

T7.10, however, says: "this execution is built with the self-delivery lemma
below, so it is an admissible run and not only a hand-set state"
(T7:833–836). An APPEND form is local and cheap: if `rho` is
`ExecutionValid`, every event has key at most `(t, 2)`, `t ≤ rho.horizon`,
`v ∈ rho.honest`, the last event of `v` is its tick at `t`, and `EmitOk`
holds, then `rho` with `deliver v o t` appended is `ExecutionValid`. Nothing
after the new event can break. Add it as `ExecutionValid.snoc_selfDelivery`
to Task 3 or Task 4. Otherwise the T7 v2 revision must prove `ExecutionValid`
of its FG-SA witness from the start, as Task 6 does for the toy.

### N4 (MINOR). A locality lemma for the `EmitOk` position hypothesis

Plan:116: "if the events between the tick event and the delivery do not
change `v`'s state". State it as an equation,
`stateBefore E rho j v = stateBefore E rho (i+1) v`. Add to Kit v2 the lemma
that discharges it: an event at node `w ≠ v` does not change `v`'s
component (`World.step` is `Function.update` at the event's node). v1 has
this only inside proofs (the `by_cases hv` branches of `Stable.lean`). T7.10
and the Task 6 toy need it as a lemma.

### N5 (MINOR). The `emittedAt` helper

Plan:89: "`emittedAt E rho v t` is `emitsAt` at the index of the tick event
of `v` at `t` (empty if none)". Define the index with `List.findIdx?` and a
predicate that matches `.tick v t` on `V` and `Time` only. `List.idxOf`
needs `BEq` on events, so it needs `BEq` on `P.Object`, and `ProtocolSpec`
has no `DecidableEq` fields. The link `o ∈ emittedAt E rho v t ↔ emits E rho v
o t` needs `nodup` from `ScheduleWellFormed` (two equal tick events can
occur only in a malformed run). State that link as a lemma with the
`ScheduleWellFormed` premise.

### N6 (MINOR; r1 m1, mostly fixed). Freeze rule text

With the manifest, the anchor value and the coverage check (A07), the
tripwire covers what T7 uses from the engine. The freeze rule (Plan:54)
still lists only additions (field, constructor, parameter). Write it as:
"no declaration in `docs/V2-API.md` changes its name, type or body. Kit v2
statements are frozen by this rule only (not locked)." About the anchor mechanics (Plan:159):
a tuple of terms from different universes can fail to elaborate. A chain
`let _ := @a; let _ := @b; …; ()` avoids that. The coverage check (Plan:160)
detects the problem in either form.

### N7 (MINOR; r1 m5, partly fixed). Generic lemmas that T7.9 needs

r2 fixes the 2c rule (new lemmas; the frozen ones stay). These generic
engine facts are still not in the Task 4 list (Plan:126). Without them, each
protocol proves them by unfolding `tick`:
- Emission under a bijective seat map: the label-`ℓ` objects of `v` are
  exactly `⟨.seat ℓ (e.symm v), p⟩` (T7.9 row wire, T7:782–785; also the
  lift).
- `Linked` index stability: `(i : Nat) = j → seatOf ℓ i = seatOf ℓ' j`
  for `ℓ ℓ'` in the family (replaces v1 `LinkedFG`, T7:787).
- Own-record fold: for a projection that `clock` and `process` keep and
  that `recordOwn` updates by `g`, the value at `stateBefore E rho i v` is
  the `g`-fold over the self-visible objects that `v` released before `i`
  (T7.9 (i)–(iii) in v2 form; `NoRestart`, or per epoch).

### N8 (MINOR; r1 m3 and m6, open). Goal scope and two agreed texts

- Plan:5 says 2a lets "T7.0–T7.9 … start". T7 §1a (T7:110–114) says T7.8,
  T7.12 and parts of T7.6 wait for the lift. Make the two plans say the
  same thing. Name T7.10, because it needs `selfDelivery_admissible`.
- PHASE1B-REPORT (:196–201) says: "The Phase 2 plan states '`selfVisible`
  controls the private own-signature record. A normal delivery to the
  emitting node may occur at the emission timestamp, after the tick
  phase.'" r2 does not contain this sentence. Put it in the `selfVisible`
  docstring and in the dated §2 note (Plan:163).
- Design §8's Phase 2 acceptance row does not have the finite checked v2
  traces yet (PHASE1B-REPORT :201–202; Plan:170 has them). Add them in the
  Task 7 docs step.

### N9 (MINOR; r1 m7 and m8, partly open)

- v1 `Auth` and `Signed` are in namespace `AvailableChain`
  (`Objects/Seats.lean:6,16,25`). T7's decode adapter opens both
  namespaces, so the names are ambiguous. Import `Objects.Identifiers`,
  `Objects.Time`, `Generic.Env` (and `Objects.Blocks` from Task 5 on), not
  the whole `AvailableChainModel` (Plan:53). Tell T7 to use qualified
  names.
- `readAt` is produced twice: as a run function (Plan:84) and "for
  outputs" (Plan:139). Use two names.
- Separation: r2 now uses the designated `F.fresh` family (Plan:62, 112).
  Still add to the docstring that a one-seat label (a proposal) cannot be
  in `fresh` unless `|V| = 1` (`CStar` needs `seats ℓ = |V|`). The FG-SA
  reference assignment is: HEAD `ap` and `fresh`; FG `linked`; proposal `ap`
  and `SingleSeat`.

### N10 (MINOR, information). R1 does not occur

I compiled with core Lean v4.30.0-rc2, with no Mathlib. The scratch files
are removed.
- `inductive Auth (L) (seats : L → Nat) | seat (l : L) (i : Fin (seats l)) |
  none deriving DecidableEq` and `structure Signed … deriving DecidableEq`
  elaborate. `decide` works on concrete values. R1 (Plan:184) does not need
  the manual fallback.
- A payload that carries signed objects of its own protocol (a nested
  inductive through the dependent `Signed`) elaborates. With `seats`
  defined by a match on the constructor, `Fin (seats (.head s))` reduces to
  `Fin n` by `rfl`. So the frozen `Signed` shape also permits native v2
  payloads, not only the FG-SA decode adapter.

## r1 findings that r2 resolves

```text
┌───────┬──────────┬──────────────────────────────────────────┬──────────┐
│ r1 ID │ r1 sev.  │ Subject                                  │ r2       │
├───────┼──────────┼──────────────────────────────────────────┼──────────┤
│ B1    │ BLOCKING │ emittedAt from stateBeforeTime           │ fixed    │
│       │          │ (same-time restart)                      │ (A01)    │
│ M1    │ MAJOR    │ D3 not sufficient for I1                 │ partly;  │
│       │          │                                          │ now N2   │
│ M2    │ MAJOR    │ selfDelivery_admissible: fields, index,  │ fixed    │
│       │          │ clock gap, carried; run-level form       │ (A02);   │
│       │          │                                          │ N3, N4   │
│ M3    │ MAJOR    │ D8: OutputsFactor needs Interface        │ fixed    │
│       │          │                                          │ (A08)    │
│ m1    │ MINOR    │ freeze and lock coverage                 │ mostly   │
│       │          │                                          │ (A07);N6 │
│ m2    │ MINOR    │ context equivalence loses the input      │ fixed    │
│       │          │                                          │ (A04)    │
│ m3    │ MINOR    │ goal scope vs T7 §1a                     │ open, N8 │
│ m4    │ MINOR    │ decided items shown as open              │ fixed    │
│       │          │                                          │ (Pl:44)  │
│ m5    │ MINOR    │ Kit generic lemmas; 2c adds, not edits   │ partly;  │
│       │          │                                          │ N1, N7   │
│ m6    │ MINOR    │ self-delivery sentence; §8 traces        │ open, N8 │
│ m7    │ MINOR    │ import clash; two readAt                 │ open, N9 │
│ m8    │ MINOR    │ separation on the declared fresh family  │ fixed;   │
│       │          │                                          │ note N9  │
│ m9    │ info     │ R1 does not occur                        │ N10      │
└───────┴──────────┴──────────────────────────────────────────┴──────────┘
```

## Answers to the six questions (on r2)

### (1) D1–D8

```text
┌────┬──────────────┬──────────────────────────────────────────────────────┐
│ D  │ Assessment   │ Note                                                 │
├────┼──────────────┼──────────────────────────────────────────────────────┤
│ D1 │ agree        │ Staging matches the design §8 post-1b note           │
│ D2 │ agree        │ With A01, every reserved interface can stay fixed in │
│    │              │ 2c. 2c restart regimes, restore laws and epochs are  │
│    │              │ additions. N1 decides the Kit premises before the    │
│    │              │ freeze                                               │
│ D3 │ agree, N2    │ The parameter stops the protocol from choosing       │
│    │              │ In := Unit. The domain must fix one In with two      │
│    │              │ elements. The claim must use a block decoder with    │
│    │              │ equality, over an input-closed regime. Nothing in 2a │
│    │              │ stops a protocol from ignoring its input, and        │
│    │              │ nothing should: every legacy lift ignores it. Only   │
│    │              │ the 2c floor refutes an ignoring protocol.           │
│ D4 │ agree        │ A02 fixes the lemma. N3 (append form) and N4         │
│    │              │ (locality) make it usable for T7.10                  │
│ D5 │ agree        │ —                                                    │
│ D6 │ agree        │ Framework may import L0–L1; the new prefix adds      │
│    │              │ lines only (no module has it today)                  │
│ D7 │ agree        │ Run-level fields on restartFree intervals fit E6     │
│    │              │ epochs (the endpoints are correct, Plan:100, 103)    │
│ D8 │ agree        │ Tasks 0–4 are Block-free as specified                │
└────┴──────────────┴──────────────────────────────────────────────────────┘
```

### (2) E5 `Isolation`

The field list (Plan:112) is the design E5 list: `recordOwn` keeps `base`.
`process` and `clock` change `base` as a function of `base` and the object
or the time. `act` on `ap` (with the input) and all gossip factor through
`base`. The hooks on AP objects factor through `base`, with both `handles`
arguments AP. Separation applies to `ap ∪ fresh`. `base_tick` in the
stronger form is correct. `Base` is data of the law structure. That is
correct.

FG-SA's needs:
- **Own row through normal delivery.** `process_base` allows the pool
  insertion if FG-SA's `process` does not read Λ. The store `State` is
  Λ-free (T7:538, DQ4), so it does not. `recordOwn` changes only `rec`, so
  `recordOwn_base` holds. The conflict case in the order check, §6 (recordOwn
  writes the pool that `proposalRows` reads) is correctly excluded.
- **Λ while asleep.** `tick_asleep` gives no released objects, so nothing
  is recorded. That is the spec form ("sleep inserts no client input"). v1
  difference (1) was a defect, not a need. E5 does not forbid `clock` from
  writing record-only data, because `clock_base` constrains only `base`.
  The v2 FG-SA must prove that its `clock` does not change `rec`. That is a
  T7.2/T7.9 fact, not an engine guarantee.

### (3) E2 `Linked`

`Linked F rho` is a run condition in `Conditions/Committees.lean`
(Plan:100), not a protocol field, as design E2 says. `LabelFamilies` is a
separate structure, which the 2b `Instance` binds. One bijection
`Fin N ≃ V` for all labels of the family gives the fixed FG identity across
rounds. The designated `fresh` family has per-label bijections. `Linked →
CStar` is a lemma, and separation uses the designated family, so FG labels
can be self-visible. Add the index-stability lemma (N7).

### (4) Astra O1–O4 and the finite-trace item

O1: Plan:176 (`Candidate` = legacy floor, versioned floor) and
PHASE1B-REPORT item 12. O2: D2 plus A01 and the manifest/lock. A later 2a
change is a declared break, so the lift is checked again by the lock. Plan:176
also requires a final check against the 2c engine. O3 and O4:
design §8 post-1b note and PHASE1B-REPORT :188–192. Finite v2 traces:
Plan:170 (L4, per A09). They are not yet in the design §8 acceptance row
(N8). `Cert.pull` needs an equivalence: Plan:169 (`Simulation`, `ClaimSim`)
and Plan:171 (product equivalence or section).

### (5) Lock and freeze

Sound with A07: a new locked prefix, one anchor whose value names every
manifest declaration, a closure check, and a check against the post-I9
lock. The lock hashes definition types and bodies, and the statements of
the theorems in the closure. So the manifest's definitions and theorems get
a tripwire. Kit v2 stays outside, by the layer rule. Only the freeze-rule
text needs to be wider (N6).

### (6) T7.0–T7.10 on the r2 API

```text
┌────────┬──────────────────────────────────────┬─────────────────────────┐
│ Step   │ r2 supplies                          │ Gap                     │
├────────┼──────────────────────────────────────┼─────────────────────────┤
│ T7.0–3 │ core, conditions, Interface (Task 5) │ —                       │
│ T7.4   │ ClockLaws + recordOwn_now            │ —                       │
│ T7.5   │ stateBefore_stable/_invariant with   │ restore premise (N1) to │
│        │ recordOwn premise                    │ hold on all runs        │
│ T7.6   │ ScheduleWellFormed, Execution and    │ bridge lemmas need      │
│        │ EngineClock ports, step_tick_eq      │ NoRestart (correct)     │
│ T7.7   │ HooksSound shapes, record laws       │ restore-now premise (N1)│
│        │                                      │ for excludes_stable     │
│ T7.8   │ delivery conditions (Task 5)         │ scope vs T7 §1a (N8)    │
│ T7.9   │ emitsAt, emits, Unforgeable-         │ N7 lemmas; NoRestart    │
│        │ Signatures, Linked, tick_decomp      │ from Durable := Unit    │
│        │                                      │ (N1)                    │
│ T7.10  │ selfDelivery_admissible, EmitOk      │ append form (N3),       │
│        │                                      │ locality (N4)           │
└────────┴──────────────────────────────────────┴─────────────────────────┘
```

r2 adds no new problem for T7 beyond N1. N1 is the choice that sets how
much restart work T7 has. With restore premises, T7.5 and T7.7 hold on
all runs for `restore := init`. Only T7.9 needs `NoRestart`, and that
comes from the protocol (Λ not durable), not from the engine.

## Scope note

All fixes change the text of the plan. N1 changes the premises of about
four Kit lemmas. N3 and N4 add two lemmas. N7 adds three generic lemmas.
N2 adds three conditions to the 2c outline. No fix changes a 2a type, the
stage split or the decision set.

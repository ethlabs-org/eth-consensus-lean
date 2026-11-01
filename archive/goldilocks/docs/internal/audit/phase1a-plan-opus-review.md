# Phase 1a plan: independent review (Opus)

Plan: `docs/plans/2026-09-28-phase1a-gate-catalog.md` (commit `54f6e0d`).
Job: `docs/audit/phase1a-plan-audit.md`. Special emphasis: Lean
elaboration of the core declarations of Tasks 1, 2 and 4.

Scratch files (outside the repository):

- `/private/tmp/p1a-scratch/Core.lean` (447 lines). It imports only
  `AvailableChainStatements`, `AvailableChainFramework.Hooks` and
  `Mathlib.Tactic.NormNum`. It declares `Validators`, `Carrier`,
  `Instance` (with `Δ_pos`), `V1Ctx`, `Carrier.v1`, `ClaimSpec K` with
  `holds` and `inhabited`, `Cert`, `Refutation`, `RefutationFamily`,
  `Profile.Entry`, `Profile`, `ProfileCert`, `Profile.holdsAt`,
  `ProfileCert.holdsAt`, the four core claims over `Carrier.v1`,
  `includedConfirmed_trigger_late`, `core`, `Candidate`,
  `not_candidate_of_family`, a `Candidate` built with the Task 2 Step 3
  pattern, `CarrierMap`, `ClaimSpec.pull`, `holds_pull`, `inhabited_pull`,
  `Cert.pull`, `StrongInstance`, `StrongInstance.sface`, `Carrier.strong`,
  `CarrierMap.strongV1`, `testStrongSafe`, `zeroConstants`, the regime
  equivalences of Task 9, and `ac43_valid_cross`.
  Command: `cd lean/available-chain && lake env lean /private/tmp/p1a-scratch/Core.lean`.
  Result: exit 0, no error, no `sorry`. Output:
  `ClaimSpec Carrier.v1 : Type 1` and `Profile Carrier.v1 : Type 1`.
  Every proof in the file is real, including `ClaimSpec.pull.transport`,
  `holds_pull`, `inhabited_pull`, `ProfileCert.holdsAt`,
  `includedConfirmed_trigger_late` and `not_candidate_of_family`.
- `/private/tmp/p1a-scratch/Fails.lean`: `Core.lean` plus the plan's text
  in three places. It gives three expected errors (F1 `Iff.rfl`, F2
  `simp [core]`, F3 `shared := 1`).
- `/private/tmp/p1a-scratch/CarrierImport.lean`: `Validators` with the
  import list of the plan's `Carrier.lean`. Error: `Fintype` is unknown.

## Findings

```text
┌────────┬──────────┬───────┬──────────────────────────────┬──────────────────────────┬──────────────────────────────┐
│ ID     │ Severity │ Task  │ Finding                      │ Evidence                 │ Proposed fix                 │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-01 │ MAJOR    │ 1, 6; │ After the gate, `Instance`   │ plan:54, plan:56,        │ Rule now how later instance  │
│        │          │ 1b    │ is frozen. But design §3     │ plan:26-38;              │ data enters: as a facet      │
│        │          │       │ puts `deliv`, `iso` and      │ FRAMEWORK-DESIGN.md:     │ structure with its carrier   │
│        │          │       │ `pparams` in `Instance`, and │ 246-253, 265-268,        │ and a `CarrierMap` (as       │
│        │          │       │ plan 1b must add Deliverable │ 196-197;                 │ `StrongInstance`), or as a   │
│        │          │       │ and the other eligibility    │ scripts/CatalogLock.lean:│ separate structure indexed   │
│        │          │       │ facts. The plan gives them   │ 30-36, 45-57             │ by the instance (`Eligible   │
│        │          │       │ no place. The ruling "If     │                          │ (I : Instance) : Prop`) in   │
│        │          │       │ wrong: a later field, which  │                          │ its own module. Never a new  │
│        │          │       │ is an addition" is false: a  │                          │ `Instance` field. Correct    │
│        │          │       │ new field changes the hash   │                          │ the ProtocolParams ruling    │
│        │          │       │ of `Instance` and of every   │                          │ text. Add the rule to the 1b │
│        │          │       │ locked declaration that uses │                          │ "needs" column. Record the   │
│        │          │       │ it (exit 1), and every       │                          │ departure from §3's sketch   │
│        │          │       │ `Instance` value. So the     │                          │ for the user.                │
│        │          │       │ "one lock regeneration" does │                          │                              │
│        │          │       │ not hold for Phase 1.        │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-02 │ MAJOR    │ 7     │ The persistence triggers do  │ plan:642-650;            │ Add `b₀ < b₁` to the         │
│        │          │       │ not require `b₀ < b₁`. At    │ Regimes.lean:51, 53;     │ triggers of `persistOutage`  │
│        │          │       │ `budget = 0` (valid: `0 ≤    │ Properties.lean:107-111; │ and `persistOutageFast`.     │
│        │          │       │ budget`), the regime forces  │ Constants.lean:48;       │ Keep `valid` as it is, so    │
│        │          │       │ `b₁ = b₀`, the window        │ FRAMEWORK-DESIGN.md:362  │ that `ac43_iff` stays true   │
│        │          │       │ `[b₀, b₀)` is empty, and     │                          │ (the trigger is not in       │
│        │          │       │ `holds` is true for every    │                          │ `holds`). Add a test that a  │
│        │          │       │ instance. The trigger is met │                          │ certificate at budget 0 has  │
│        │          │       │ by any healthy run. So a     │                          │ no inhabitation witness.     │
│        │          │       │ `Cert` at Π = 0 is vacuous   │                          │                              │
│        │          │       │ and passes inhabitation: the │                          │                              │
│        │          │       │ same class of defect as I2.  │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-03 │ MINOR    │ 9     │ `Iff.rfl` does not prove the │ plan:755;                │ Make the fallback the main   │
│        │          │       │ regime equivalence: the      │ Fails.lean:457 (F1);     │ guide:                       │
│        │          │       │ regimes are structures, and  │ Core.lean, section Rfl   │ `⟨fun h => { h with },       │
│        │          │       │ `C` is not defeq to `{       │                          │ fun h => { h with }⟩`.       │
│        │          │       │ zeroConstants with … }`. The │                          │ Tested for StableSleepy,     │
│        │          │       │ plan's fallback works.       │                          │ Outage, FastOutage,          │
│        │          │       │ `EtaSleepy` (a def) agrees   │                          │ Recovery and RecoveredAt.    │
│        │          │       │ by `Iff.rfl`.                │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-04 │ MINOR    │ 1     │ `Carrier.lean` imports only  │ plan:100-111;            │ Add `public import           │
│        │          │       │ `Objects.Time`. `Fintype` is │ CarrierImport.lean:6     │ Mathlib.Data.Fintype.Defs`   │
│        │          │       │ then unknown in              │                          │ (or `.Card`).                │
│        │          │       │ `Validators`.                │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-05 │ MINOR    │ 2     │ `by simp [core]` does not    │ plan:312;                │ Use `List.mem_cons.1` in     │
│        │          │       │ prove membership in          │ Fails.lean:461 (F2),     │ term mode, or `show _ ∈      │
│        │          │       │ `core.entries`, and `tauto`  │ 465 (F3); Core.lean      │ ([_, _, _, _] : List         │
│        │          │       │ does not close the last      │ `testCandidate`          │ (Profile.Entry Carrier.v1    │
│        │          │       │ branch: the element type is  │                          │ Time))` before `simp`;       │
│        │          │       │ `Entry … core.Shared`, which │                          │ write `shared := (1 :        │
│        │          │       │ does not unfold at reducible │                          │ Time)`. Tested.              │
│        │          │       │ transparency. `shared := 1`  │                          │                              │
│        │          │       │ fails (`OfNat core.Shared`). │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-06 │ MINOR    │ 1     │ `armedToy`: "one more        │ plan:234;                │ Say: `regime` and            │
│        │          │       │ argument" is wrong. The      │ Tests/Pareto.lean:23-26  │ `conclusion` take 5          │
│        │          │       │ trigger keeps 6 binders (`I  │                          │ binders, `trigger` 6; the    │
│        │          │       │ k W x p H`); regime and      │                          │ `transport` intro becomes    │
│        │          │       │ conclusion go from 6 to 5.   │                          │ `… W x hΔ p _`.              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-07 │ MINOR    │ 7     │ `decide` does not reduce the │ plan:667; Core.lean      │ Make `simp [<claim>]` the    │
│        │          │       │ `le` tests on ℚ (tested).    │ `outLe` examples         │ main guide.                  │
│        │          │       │ `simp [le-def]` closes both  │                          │                              │
│        │          │       │ the `true` and the `false`   │                          │                              │
│        │          │       │ case.                        │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-08 │ MINOR    │ 8     │ `valid := True` for the      │ plan:702-714;            │ Set `refutable := .run` for  │
│        │          │       │ strong recovery claims is    │ Regimes.lean:77-82;      │ these two claims and say     │
│        │          │       │ needed for `strong1_iff` and │ Strong/Claims.lean:30-36 │ why in the docstring. Or     │
│        │          │       │ is correct. But at θrec ≥ 1  │                          │ add claim-level bounds and   │
│        │          │       │ and ρ ≥ 0 the Recovery       │                          │ state `strong1_iff` under    │
│        │          │       │ regime is empty, so `holds`  │                          │ `C.Valid`.                   │
│        │          │       │ is vacuous at a valid        │                          │                              │
│        │          │       │ constant. A RefutationFamily │                          │                              │
│        │          │       │ of these claims is then      │                          │                              │
│        │          │       │ impossible. The plan does    │                          │                              │
│        │          │       │ not give their `refutable`.  │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-09 │ MINOR    │ 1, 7, │ The late trigger is a        │ plan:175-178, 77;        │ Add a `_trigger_late` lemma  │
│        │          │ 8     │ convention per claim: the    │ Core.lean                │ for each catalog claim with  │
│        │          │       │ `ClaimSpec` shape lets a     │ `includedConfirmed_      │ a trigger that is not        │
│        │          │       │ trigger ignore `H`. Only     │ trigger_late`            │ `True` (Tasks 7, 8), as for  │
│        │          │       │ `includedConfirmed` has a    │                          │ `includedConfirmed`.         │
│        │          │       │ test.                        │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-10 │ MINOR    │ 4;    │ `CarrierMap` needs an        │ plan:53, 370-374, 413;   │ In the ruling and in the     │
│        │          │ plan 2│ `Equiv` of contexts, and the │ FRAMEWORK-DESIGN.md:     │ plan-2 row, say that the     │
│        │          │       │ `pull.transport` proof uses  │ 235-243; Core.lean       │ lift needs a second, one-way │
│        │          │       │ `.symm`. The v1→v2 lift is a │ `ClaimSpec.pull`         │ map (holds pulls back in one │
│        │          │       │ simulation (every lifted v2  │                          │ direction only) and new      │
│        │          │       │ run has a v1 run), not an    │                          │ transport proofs.            │
│        │          │       │ equivalence. So plan 2 can   │                          │                              │
│        │          │       │ not reuse `pull`.            │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-11 │ MINOR    │ 4     │ One structure, carrier and   │ plan:52, 415-441;        │ Consider one generic facet   │
│        │          │       │ map per facet COMBINATION.   │ FRAMEWORK-DESIGN.md:     │ carrier, `Inst := Σ I :      │
│        │          │       │ `counterInst` and            │ 246-256                  │ Instance, F I`, with one     │
│        │          │       │ `counterStrong` are two      │                          │ generic map to v1. Let the   │
│        │          │       │ unrelated registry           │                          │ registry show the base       │
│        │          │       │ instances.                   │                          │ instance of a facet row.     │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-12 │ MINOR    │ 6     │ The skip list does not cover │ plan:533;                │ Skip by provenance, not by   │
│        │          │       │ generated names that are in  │ docs/catalog.lock (36    │ name suffix (for example: no │
│        │          │       │ today's lock: `ctorIdx`,     │ such lines)              │ declaration range, or the    │
│        │          │       │ `toCtorIdx`, `ofNat`,        │                          │ environment's aux / no-      │
│        │          │       │ `ofNat_ctorIdx`, `ctorElim`, │                          │ confusion / ctor-aux tests). │
│        │          │       │ `ctorElimType`, `<ctor>.     │                          │ Test with a hand-written     │
│        │          │       │ elim`, `noConfusionType`,    │                          │ `X.inj` in a scratch copy.   │
│        │          │       │ `rec`. M6 is not closed. A   │                          │                              │
│        │          │       │ hand-written `foo.inj` or    │                          │                              │
│        │          │       │ `foo.eq_def` gets no line.   │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-13 │ MINOR    │ 6, 1–5│ Audit of the regeneration:   │ plan:68, 542             │ Do Task 6 Steps 1–3 first,   │
│        │          │       │ the new script, run against  │                          │ before Task 1, with a        │
│        │          │       │ the old lock, prints every   │                          │ rewrite that only drops      │
│        │          │       │ skipped generated name as    │                          │ generated lines. Then the    │
│        │          │       │ REMOVED, mixed with the real │                          │ gate diff is pure. Also      │
│        │          │       │ changes. Main has five       │                          │ record the old and new       │
│        │          │       │ commits with a failing lock. │                          │ types of the L3 claims.      │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-14 │ MINOR    │ 6–8   │ The lock hashes a def body.  │ scripts/CatalogLock.lean:│ Put each `transport` proof   │
│        │          │       │ So a claim's `transport`     │ 30-43; PHASE0-REPORT.md  │ in a named theorem and       │
│        │          │       │ proof term is in its hash: a │ §5.1 (e); plan:73        │ reference it; a theorem      │
│        │          │       │ new proof is CHANGED (exit   │                          │ enters the closure by its    │
│        │          │       │ 1), and the id rule then     │                          │ statement only.              │
│        │          │       │ asks for a new id. This      │                          │                              │
│        │          │       │ conflicts with deviation (e).│                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-15 │ MINOR    │ 6     │ Registry: the script imports │ scripts/Registry.lean:66,│ Import every module root in  │
│        │          │       │ only `AvailableChainRegistry`│ 76-78; plan:538-540;     │ `instanceLibraries`. Read    │
│        │          │       │ so `instanceLibraries` alone │ Core.lean `ClaimSpec.pull│ the pulled claim as the LAST │
│        │          │       │ adds nothing. The pulled     │ ` (`@pull K K' m c`)     │ app argument.                │
│        │          │       │ claim `c` is the last of 4   │                          │                              │
│        │          │       │ args of `ClaimSpec.pull`.    │                          │                              │
├────────┼──────────┼───────┼──────────────────────────────┼──────────────────────────┼──────────────────────────────┤
│ P1a-16 │ MINOR    │ 5     │ With `clock := fun _ t => t` │ plan:480, 512;           │ Optional: `clock := fun st t │
│        │          │       │ the read is the time of the  │ CounterRun.lean:526-547  │ => max st t`. Then the       │
│        │          │       │ LAST tick, so monotonicity   │                          │ Counter sublist argument     │
│        │          │       │ needs the sorted schedule.   │                          │ (`readAt_mono`) works for    │
│        │          │       │ It works, but it is harder.  │                          │ every run.                   │
└────────┴──────────┴───────┴──────────────────────────────┴──────────────────────────┴──────────────────────────────┘
```

## Counterexamples and scratch results for the MAJOR findings

**P1a-01.** Take the design's own §3 field `deliv : Deliverable P` and add
it to `Instance` in plan 1b. `ownHash` hashes the type of `Instance`
(`CatalogLock.lean:31`, `:35`), and `closureHash` mixes the hash of every
dependency (`:53-56`). `V1Ctx`, `Carrier.v1`, every `ClaimSpec
Carrier.v1` definition, `core`, `Candidate` and `Cert` reach `Instance`
through their closure. So `--check` prints `CHANGED` for almost every
locked line and exits 1. Every `Instance` value (`sanity`, `counterInst`,
`clockInst`) also needs the new field. That is a second lock break, but
the plan says "One lock regeneration" (plan:56) and "a later field, which
is an addition" (plan:54). The design already names the cause: "adding a
field to a frozen Lean structure changes its declaration"
(FRAMEWORK-DESIGN.md:265-268). The design also says the E4 obligations
"are proved per migrated instance; they are not silently added to the v1
hooks" (:196-197), but the §3 sketch has them as `Instance` fields. The
plan must choose now.

**P1a-02.** Let `I` be any instance with one healthy run in which some
honest stable read at a time `T ≥ H` is not genesis (every real protocol
has one). Take `k := ⟨η, θ, lag, 0⟩` with `0 ≤ η`, `1/2 ≤ θ ≤ 3/4`,
`0 ≤ lag`. Then `valid k` holds (`0 ≤ budget`, `budget ≤ η`).
`OutageRegime` gives `b₀ ≤ b₁` (`Regimes.lean:51`) and `b₁ − b₀ ≤ 0`
(`:53`), so `b₁ = b₀`. `PersistsThrough … T b₀ b₀` asks for
`b₀ ≤ t → t < b₀ → …` (`Properties.lean:111`), which is vacuous. So
`persistOutage.holds I k` is true for every `I`. The trigger ("`H ≤ T`
and a non-genesis honest stable read at `T`") holds in the healthy run
with `b₀ = b₁ = T + lag`. So `Cert persistOutage I` exists at `k` for a
protocol with no persistence at all. The same holds for
`persistOutageFast`. The bundle has the same vacuity at `budget = 0`, so
`ac43_iff` is not affected; the defect is in inhabitation, which V07 and
I2 exist to close. With `b₀ < b₁` in the trigger, the witness needs
`0 < b₁ − b₀ ≤ budget`, so no certificate exists at `budget = 0`.

## Answers to questions 1–7

**1. Lean feasibility.** Yes. All the core declarations of Tasks 1, 2
and 4 elaborate as written, in one scratch file, with no error. The
universes are as stated: `ClaimSpec Carrier.v1 : Type 1`,
`Profile Carrier.v1 : Type 1`, and the explicit `ProfileCert … : Type 1`
is accepted. `@[reducible] def Carrier.v1` makes `x.E` and `x.rho`
elaborate on `x : Carrier.v1.Ctx I W` (all four core claims use them),
and the same holds for `Carrier.strong`. `CarrierMap.strongV1`
typechecks with `Equiv.refl _`, `Iff.rfl` and `rfl`. `ClaimSpec.pull`
with a real `transport` proof, `holds_pull` and `inhabited_pull` are
routine (about 8 lines each, with `Equiv.apply_symm_apply`). The
`Candidate` pattern of Task 2 Step 3 works with `subst`, but not with
`simp [core]` or `tauto`, and the numeral needs a type (P1a-05).
`Carrier.lean` needs one more import (P1a-04).

**2. Soundness of the claims.** Every `le` direction agrees with design
§4: θ, θrec, η, A, A_f, ρ up; `full` false → true; G and Π down; f down;
exact-time D fixed. Each `transport` guide agrees with the regime
definitions. `etaSleepy_mono` needs `0 ≤ C.θ` of the stronger constant,
which `valid k` gives; the strong recovery transport needs no sign of
θrec, as the plan says. The claims restate the bundle fields with the
same strength; no claim is stronger or weaker than its field. The
late-trigger shape `trigger … H` agrees with design §5 and closes I2
for the inclusion and recovery claims, but only by convention per
claim (P1a-09). The persistence triggers are inhabitable by real
protocols, but they also admit an empty outage window, so a vacuous
certificate at Π = 0 passes (P1a-02).

**3. The equivalence theorems.** Both `ac43_iff` and `strong1_iff` are
true as stated. The regimes do NOT agree by `Iff.rfl`: the regimes are
structures, and a structure argument `C` is not defeq to
`{ zeroConstants with … }` (Fails.lean F1). The plan's fallback
`⟨fun h => { h with }, fun h => { h with }⟩` works for all five
structure regimes and for `RecoveredAt` (tested). `Δ_pos` is used
correctly: the `→` direction needs one admissible environment to get
`C.Valid` (and `SC.Valid`); `Fin 1` as the validator type is enough, and
any type works. `monotone` comes from the two `SafeFrom.monotone`
facts; `nested` comes from `prefixOrder` (regime `True`). Nothing else
is needed. `valid := True` for the strong recovery constants is
necessary for `strong1_iff`, because `StrongClaims` has no
`Constants.Valid`, and it is correct; its cost is P1a-08.

**4. The I1 witness.** `clockChain` passes the four core claims at
`D = 0`. Safety: every read is `clockBlock m`, and these blocks form one
chain, so any two reads are compatible (at any nodes and times, in
every run); per-node monotonicity follows from the sorted schedule,
because the filter `time ≤ t` of a sorted list is a prefix. Prefix: the
two outputs are equal. Inclusion at `D = 0`: admissibility gives
`E.Δ = 1`, so every slot time `s ≥ 0` is public; `tick_total` gives a
tick of the proposer at `s`; `emittedAt` then emits `⟨.proposer s, s⟩`
(awake, `slotsAt s = [s]`, `propose = some s`); every honest node ticks
at `s`, and by `nodup` and sortedness its last tick up to `s` is at
`s`, so its read at `s` is `clockBlock s`. Inhabitation: the Sanity
pattern works; `PartialSynchrony` is vacuous because `excludes` is
always true and `processed` is always false; `RootInjective` holds in
every run, because every named block is some `clockBlock k` with root
`⟨k⟩`. A simpler clock is optional (P1a-16).

**5. Design conformance.** Departures from §3's `Instance` sketch: no
`pparams`; no `FacetBundle` (the `iface` field plus facet structures
that extend `Instance`); no `deliv` and no `iso` (deferred); new `Δ` and
`Δ_pos`. Departures from §4's `ClaimSpec` sketch: `needs` becomes the
carrier parameter; `holds` and `inhabited` are definitions from
`regime` and `conclusion`, not fields (as in Phase 0); `trigger` reads a
context, a point and `H`. Profiles: a `Shared` type with `share`
projections for "shared constant names". These are representation
choices that §3 leaves open (FRAMEWORK-DESIGN.md:265-268), and the late
trigger is the fix that §12 names. Dropping `ProtocolParams` is
acceptable only as a user ruling, because §3 lists it as a field; the
reason "a later field is an addition" is false (P1a-01). The deferral of
`deliv` has no plan (P1a-01).

**6. Lock and registry.** The by-name compare, the axiom check and the
`--lock` tests close I8 and M5. M6 is not closed: the skip list misses
many generated names in today's lock, and a suffix match can skip a
hand-written declaration (P1a-12). A changed claim cannot hide behind a
skipped generated name, because the parent's own line and every user's
closure still change. The regeneration diff mixes skip removals with
real changes (P1a-13), and proof terms in def bodies make proof changes
look like statement changes (P1a-14). The registry changes fit the
type-scan design: `Candidate I` has the head `Candidate`, a
`ProfileCert` has the args `K p I`, and `KNOWN-GAP` by module prefix is
sound. Two details are wrong: the imports for `instanceLibraries`, and
the index of the pulled claim (P1a-15).

**7. Scope and ordering.** The split into 1a, 1b and 2 is sound, and the
task order is consistent: each task builds on the earlier ones, and no
FG or protocol library imports the framework, so the build stays green.
The "exit 1 until Task 6" window is five commits on main; the hardening
can come first (P1a-13). Missing interfaces: a place for eligibility and
parameters that is not an `Instance` field (P1a-01, needed by 1b), and a
one-way map for the v1→v2 lift (P1a-10, needed by plan 2).

VERDICT: ADOPT WITH FIXES

AUDIT COMPLETE: 0 blocking, 2 major, 14 minor

# Phase 1a plan review — async (FG-SA composition) session

_2026-09-28. Object: `docs/plans/2026-09-28-phase1a-gate-catalog.md` (54f6e0d).
Drafted by an independent Opus reviewer. The async session vetted it. Spot checks
by the async session: design:263-268 (the extensible-representation text),
Properties.lean:107-111 and Regimes.lean:51-53 (the M5 vacuity), and log.md:950
(user approval of plan 1a at 22:42) all agree with the findings._

**Verdict: ADOPT WITH FIXES. 0 BLOCKING, 6 MAJOR, 12 MINOR.**

The carrier design works in Lean. The reviewer compiled the core declarations in
scratch files outside the repository (`/private/tmp/p1a-fgrev/`, `lake env lean`
against the built tree). The pull-back of claims and certificates can be proved as
the plan says. No finding stops Task 1. Fold in the six MAJOR findings before
Task 1, or before the task that each one names. M4 and M6 set rules that plans 1b,
2 and the FG-SA work depend on; after the Task 6 lock regeneration, a change to
either one breaks the lock. No fix below changes an approved design section,
except the OPTIONAL part of M6 (pointwise `transport`), which needs the user.

## Scratch results

```text
┌────────────────────┬────────────────────────────────────────────┬──────────────────────────────────┐
│ File               │ Content                                    │ Result                           │
├────────────────────┼────────────────────────────────────────────┼──────────────────────────────────┤
│ Core.lean          │ Carrier, Carrier.v1, V1Ctx, ClaimSpec K,   │ All compile, no sorry.           │
│                    │ holds, inhabited, Cert, RefutationFamily,  │ Carrier : Type 2,                │
│                    │ Profile.Entry, Profile, ProfileCert,       │ ClaimSpec : Carrier → Type 1.    │
│                    │ ProfileCert.holdsAt (proved);              │ x.E, x.rho and I.P elaborate on  │
│                    │ includedConfirmed with the late trigger;   │ Carrier.v1.Ctx.                  │
│                    │ includedConfirmed_trigger_late; CarrierMap;│                                  │
│                    │ pull with transport proved; holds_pull;    │                                  │
│                    │ inhabited_pull; Cert.pull; StrongInstance; │                                  │
│                    │ Carrier.strong; strongV1; FinalInstance;   │                                  │
│                    │ a diamond StrongFinalInstance; a nesting   │                                  │
│                    │ claim "finalized ⪯ stable ∧ OutputOrder"   │                                  │
│ Builder.lean       │ Carrier.ofV1 J base; CarrierMap.ofV1       │ Compile. A map between two facet │
│                    │                                            │ carriers whose bases are only    │
│                    │                                            │ propositionally equal needs a    │
│                    │                                            │ cast (▸ fails).                  │
│ Regime.lean        │ Task 9 route                               │ Iff.rfl FAILS (OutageRegime).    │
│                    │                                            │ ⟨fun h => {h with}, …⟩ works for │
│                    │                                            │ Outage, FastOutage, Recovery.    │
│ Prof.lean          │ core profile; not_candidate_of_family;     │ Compiles. `shared := 1` fails:   │
│                    │ a Candidate by classical case split        │ "OfNat core.Shared 1".           │
│ CarrierImport.lean │ the plan's Carrier.lean header and imports │ FAILS: `Fintype` is unknown.     │
└────────────────────┴────────────────────────────────────────────┴──────────────────────────────────┘
```

No FG library imports `AvailableChainFramework` or `AvailableChainRegistry` (only
the two library roots, `scripts/CatalogLock.lean`, `scripts/Registry.lean`). Tasks
1–9 cannot break the FG build (`lakefile.toml:4-16`).

## Findings

```text
┌─────┬───────┬───────┬───────────────────────────────────────────┬────────────────────────────────┐
│ ID  │ Sev   │ Task  │ Finding                                   │ Evidence                       │
├─────┼───────┼───────┼───────────────────────────────────────────┼────────────────────────────────┤
│ M1  │ MAJOR │ 5, P2 │ I1 regression has the wrong spec: the v1  │ plan:463, :53; design:239;     │
│     │       │       │ candidate cannot "fail to elaborate"; the │ Conditions.lean:110-127        │
│     │       │       │ lift carries it into v2                   │                                │
│ M2  │ MAJOR │ 6     │ Regeneration diff not auditable: policy   │ plan:532-542; catalog.lock:26- │
│     │       │       │ and real changes mix; every L3 line       │ 30; CatalogLock.lean:15-43     │
│     │       │       │ changes; no meaning check                 │                                │
│ M3  │ MAJOR │ all   │ No axiom check on framework theorems      │ CatalogLock.lean:36,42;        │
│     │       │       │ (ac43_iff, strong1_iff, pull lemmas, Mono)│ Registry.lean:79; plan:63,:766 │
│ M4  │ MAJOR │ rul., │ "A later [Instance] field is an addition" │ plan:54, :56, :73, :26-38;     │
│     │       │ 1b    │ is false; eligibility location undecided  │ design:252, :265-268, :315-317 │
│ M5  │ MAJOR │ 7     │ Persistence certificate can be vacuous    │ plan:642-650; Properties.lean: │
│     │       │       │ (budget 0 or b₀ = b₁)                     │ 107-111; Regimes.lean:51-53;   │
│     │       │       │                                           │ Constants.lean:48              │
│ M6  │ MAJOR │ 4, P2 │ Pull works only along a context bijection;│ plan:370-374, :180-184, :381,  │
│     │       │       │ no id rule for a claim over another       │ :53; design:239, :283-284      │
│     │       │       │ carrier                                   │                                │
│ m1  │ MINOR │ 1     │ Imports: Carrier.lean lacks Fintype;      │ plan:100-101, :205             │
│     │       │       │ Profile.lean loses Instance               │                                │
│ m2  │ MINOR │ 2, 5  │ Untyped numerals `shared := 1`, `:= 0`    │ plan:312, :516                 │
│ m3  │ MINOR │ 9     │ Iff.rfl fails; make the rewrap primary    │ plan:755                       │
│ m4  │ MINOR │ 1     │ Name "carrier" collides with FG "carrier" │ FG-COMPOSITION.md (88 uses);   │
│     │       │       │                                           │ KitFG CausalCap.lean:37-38     │
│ m5  │ MINOR │ 4     │ Facet carriers restate admissible and     │ plan:429-433                   │
│     │       │       │ horizon: drift possible                   │                                │
│ m6  │ MINOR │ 1     │ Carrier has no id/name field              │ plan:119-127                   │
│ m7  │ MINOR │ 2–6   │ Registry shows clockChain as LEAN until   │ plan:68, :520, :539            │
│     │       │       │ Task 6; REGISTRY.md commits unstated;     │                                │
│     │       │       │ KNOWN-GAP keyed on module path only       │                                │
│ m8  │ MINOR │ 6     │ Pulled claim is the last argument of      │ plan:538                       │
│     │       │       │ ClaimSpec.pull, not args[1]               │                                │
│ m9  │ MINOR │ 6     │ Lock keys Lean names, not ClaimSpec.id:   │ plan:73                        │
│     │       │       │ id immutability not enforced              │                                │
│ m10 │ MINOR │ 1, 7  │ Inline transport proofs enter the def     │ CatalogLock.lean:33; plan:661  │
│     │       │       │ hash: a proof refactor forces a new id    │                                │
│ m11 │ MINOR │ 6     │ --write unguarded; no test for M6's hole; │ plan:533-536                   │
│     │       │       │ skip rule uses name suffixes              │                                │
│ m12 │ MINOR │ 10    │ No "as implemented" notes under §3–§5     │ plan:762, :765                 │
└─────┴───────┴───────┴───────────────────────────────────────────┴────────────────────────────────┘
```

### M1 — I1 regression spec (Task 5 and the handoff to plan 2)

plan:463 says that after plan 2 "this candidate must fail to elaborate; plan 2 keeps
this file as its regression test". That cannot happen: (1) plan 2 adds a new carrier
and keeps v1 (plan:53), so `clockCandidate : Candidate clockInst` stays true; (2) a
file that does not elaborate cannot stay in a `lake build --wfail` target; (3) the
lift transports v1 claims to v2 (design:239), so if the v2 floor is the lift of
`core.v1`, the lifted clockChain passes it too.

Fix: write in the plan: "Plan 2 adds `core.v2` with an input-inclusion claim (new id,
new floor profile). Its regression test is a `RefutationFamily` of that claim for the
lifted `clockInst` (or `Candidate₂ (lift clockInst) → False`). `clockCandidate` stays
a positive v1 fact: after plan 2 the v1 floor is not the floor."
The gap does not depend on `excludes := true`: with `excludes := false` the same
protocol still passes (`processed = false`, `process = id`; broadcast needs handler
calls, so the witness run needs delivery events; relay has no work). State this in
the docstring (plan:518) so that plan 2 cannot "close" I1 by an exclusion rule alone.
Pollution: the lock, no (`Gaps` is L4; the lock reads framework modules only). The
registry, briefly (m7), and permanently unless consumers filter: add a 1a contract
that MATRIX.md (1b), Pareto sets and the explorer ignore `KNOWN-GAP` rows.
clockChain probably also meets the 1b eligibility obligations (reasoned, not
compiled), so 1b can keep it as an "eligible candidate" regression.

### M2 — the regeneration diff cannot be audited (Task 6)

(a) Step 1 changes the lock policy (generated-name skip, three new locked modules) in
the same task as the regeneration: a `--check` with the new script against the old
lock prints REMOVED for generated lines (e.g. `Cert.casesOn`, `Cert.ctorIdx`,
`Cert.mk`, catalog.lock:26-30) and ADDED for new modules, mixed with real changes.
(b) `ClaimSpec`, `Instance` and the trigger arity all change, so every L3 line
changes; "no certificate conclusion changed" (plan:542) has no check behind it.

Fix: (1) a new Task 0 before Task 1 with Task 6 Steps 1–3 (hardened lock script with
`--lock <path>`, registry changes that do not need Tasks 1–5); write a baseline with
the hardened script at the Phase 0 tree to a scratch path; each checkpoint of Tasks
1–5 prints the by-name diff against it, and the task report lists it. (2) Meaning pins
in Task 1: for each of the four existing claims, theorems that state `holds` and
`inhabited` in the Phase 0 form with L1 predicates only, in a locked L3 module (e.g.
`Catalog/Pins.lean`). Example (type-checks in the scratch setting):

```lean
theorem includedConfirmed_holds_iff (I : Instance) (D : Time) :
    includedConfirmed.holds I D ↔
      ∀ (W : Validators) (E : Env W.V), E.Δ = I.Δ → ∀ (rho : Run W.V I.P) (t₀ : Time),
        SleepyRegime I.P E I.iface rho t₀ →
          IncludedFrom I.P E I.iface rho I.iface.confirmed t₀ D :=
  ⟨fun h W E hE rho t₀ hr => h W ⟨E, rho⟩ hE t₀ hr,
   fun h W x hx t₀ hr => h W x.E hx x.rho t₀ hr⟩
```

(3) Record the git blob id of the old lock in the change log. A reviewer then compares
each pin with Phase 0 `ClaimSpec.holds`/`inhabited` (Claim.lean:52-60); the only
intended difference is the `inhabited` pin of `includedConfirmed`, which gains
`H ≤ proposalTime s`.

### M3 — no axiom check on framework theorems

The lock hashes only theorem statements (CatalogLock.lean:36,42); the registry checks
axioms only on certificate rows (Registry.lean:79); `--wfail` flags `sorry` but not a
declared `axiom` or `native_decide`; Task 10 greps only `sorry` (plan:766). So
`ac43_iff`, `strong1_iff`, `holds_pull`, `inhabited_pull`, `ProfileCert.holdsAt`,
`not_candidate_of_family` and the Mono lemmas are unchecked.
Fix: extend `scripts/CheckFGAxioms.lean` with module prefixes, or add
`CheckFrameworkAxioms.lean` for `AvailableChainFramework` and `AvailableChainRegistry`
(reject `sorryAx`, the `native_decide` auxiliary axioms, project axioms); run it at
every CHECKPOINT and in Task 10; grep `sorry|admit|native_decide` and `^axiom`
(lean/AGENTS.md requires axiom checks when proof soundness is part of the change).

### M4 — `Instance` must be closed after Task 6

plan:54 ("If wrong: a later field, which is an addition") is false: after Task 6 a new
`Instance` field changes the `Instance` lock line, the closure hash of every claim over
`Carrier.v1`, and every `Instance` literal — a second regeneration, which plan:56 and
:73 rule out. The approved §3 text gives the reason (design:265-268: "because adding a
field to a frozen Lean structure changes its declaration"). The §3 sketch has
`deliv : Deliverable P` (design:252); the 1b row (plan:26-38) lists Deliverable,
RelayFeasible, WindowMargin, EmitWellFormed and HandlerCoverage but not where they go.
Fix: rewrite the ruling: "After Task 6, `Instance` is closed. Protocol parameters,
eligibility obligations and later per-instance data enter as facet structures
(`… extends Instance`) with their own carrier, which is additive (G2), or as a separate
`Eligible I` structure outside the claim closure. 1b adds no `Instance` field." This
agrees with design:315-317 ("Eligibility (hooks, deliverability, inhabitation) is
separate").

### M5 — vacuous persistence certificates (Task 7)

`PersistsThrough` quantifies over `t ∈ [b₀, b₁)` (Properties.lean:107-111); at
`budget = 0`, `withinBudget` and `interval` force `b₁ = b₀` (Regimes.lean:51-53);
`valid` allows `budget = 0` (plan:643-645; Constants.lean:48); the trigger "H ≤ T ∧ a
non-genesis read at T" (plan:646-647) does not require `b₀ < b₁`. So every instance
with late non-genesis stable reads (e.g. Counter) gets a LEAN certificate of
`std.persist.outage.v1` and the fast variant that states nothing — the same class of
hole as I2. Fix: add `b₀ < b₁` to both persistence triggers in Task 7, before the lock
records them (after that it needs new ids); inhabitation then needs `budget ≥ 1`;
`ac43_iff` does not change. Downstream relevance: the FG-SA P1 claims
(`stableResilient`, `stableResilientFast`) are in this family.

### M6 — pull scope and the id rule

`CarrierMap` requires an `Equiv` of contexts (plan:370-374); `transport` is stated for
`holds` over all contexts (plan:180-184, design:283-284). The pulled `transport` needs
`(m.ctx I W).symm`; with a plain function there is no proof (scratch). So pull works
for facets over one protocol (strong, a finalized output), not for the v1→v2 lift
(design:239 gives a one-way map) nor for a composite-to-AP projection. Plan 2 must
restate every catalog claim over `Carrier.v2` with relation lemmas; plan:53 ("It does
not change ClaimSpec") is true but suggests a reuse that does not exist, and no rule
gives the id of a restated claim.
Fix (no code change): add the ruling "Pull keeps the id and exists only along a context
equivalence that keeps admissibility (↔) and the horizon. A claim over another carrier,
or over a carrier with a stronger `admissible` (e.g. a v1 carrier with `LinkedFG`), is a
new claim with a new id and a relation lemma."
OPTIONAL, needs the user: a pointwise (per-context) `transport` would allow pull along
any admissibility-preserving function; it departs from approved design:283-284. Decide
it before Task 6 or not at all. **Async-session recommendation: do not take the
optional part now** (it changes approved text; the id rule covers the FG-SA needs).

### MINOR fixes

- **m1** `public import Mathlib.Data.Fintype.Defs` (or equal) in Carrier.lean;
  `public import AvailableChainFramework.Instance` in Profile.lean in Task 1 Step 4
  (after Step 3 `Claim` imports only `Carrier`). State the module header (`module`,
  `public import`, `@[expose] public section`) for every new file.
- **m2** Write `(1 : Time)` and `(0 : Time)` (PHASE0-REPORT §5.2, Task 4).
- **m3** Make `⟨fun h => {h with}, fun h => {h with}⟩` the primary route in Task 9.
- **m4** Rename `Carrier` before Task 6 (e.g. `ClaimDomain`); after Task 6 a rename
  breaks the lock. The FG-SA plan has its own `Proofs/Carrier.lean` (K5), and the FG
  registry uses "carrier" 88 times for row carriers.
- **m5** One builder, `Carrier.ofV1 J base`, with `CarrierMap.ofV1`. A native strong
  claim (Task 8) reads `Carrier.strong.admissible` with no map to check it. Document
  the cast trap for diamond maps.
- **m6** Add `id : Lean.Name` to `Carrier` now.
- **m7** Move KNOWN-GAP labelling before Task 5 (Task 0); state at each checkpoint
  whether `docs/REGISTRY.md` is committed; key KNOWN-GAP on the instance name too.
- **m8** Use `getAppArgs.back!` of the `ClaimSpec.pull` term (implicit carriers come
  first; the claim is at index 3).
- **m9** Check in the lock or registry that catalog id strings are unique and bound to
  one Lean name (pulled claims excepted).
- **m10** `transport := <claim>_transport` as a separate theorem, so only the statement
  enters the hash. Do it now; Task 1 rewrites every transport anyway.
- **m11** `--write` refuses when CHANGED or REMOVED names exist (or an `--add` append
  mode); test (d): change a definition body and confirm its line is CHANGED while
  `eq_def` is skipped; skip generated names with Lean's classifiers, not suffixes.
- **m12** Task 10: dated "as implemented in plan 1a" notes under §3, §4 and §5 (notes,
  not edits of approved text).

## Answers to the focus items

1. **Lean soundness of carriers.** Sound; the Core.lean row compiles, including the
   certificate pull exactly as planned (`Cert.pull` needs only the ← directions;
   `holds_pull` ← needs a function; `inhabited_pull` ← needs surjectivity, given by the
   `Equiv`). Universes as the plan claims (`Carrier : Type 2`; `ClaimSpec K`,
   `Profile K`, `ProfileCert`, `CarrierMap` : `Type 1`; `Inst : Type 1` suffices for v2,
   the FG-SA composite and §7.3's `inst T σ`). Dot notation works on a non-reducible
   carrier. Traps: numerals (m2), `Iff.rfl` for regimes (m3), diamond maps (m5).
2. **Approved sections.** Approved text: §3 sketch (design:247-253), design:265-268, §4
   sketch (design:273-288), §5 (design:359-362).

   ```text
   ┌──────────────────────────────────────┬───────────────────────────────────────────────┐
   │ Plan point                           │ Class                                         │
   ├──────────────────────────────────────┼───────────────────────────────────────────────┤
   │ Carrier index replaces needs;        │ Representation (design:265-268 leaves         │
   │ facets as extends-structures         │ FacetNeeds open; names "separate facet        │
   │                                      │ records").                                    │
   │ holds and trigger over K.Ctx         │ Representation.                               │
   │ No pparams field                     │ Representation (params live in P); drops a    │
   │                                      │ named field; user-approved; fallback text     │
   │                                      │ wrong (M4).                                   │
   │ No deliv or iso in 1a                │ Deferred; must enter as a facet (M4).         │
   │ Δ_pos                                │ Representation (a parameter invariant).       │
   │ Late trigger (H) in inhabited        │ Stricter than approved §5 text; covered by    │
   │                                      │ plan approval (plan:5 names I2); note (m12).  │
   │ Profile Shared/valid, ProfileCert    │ Matches design:311-314.                       │
   └──────────────────────────────────────┴───────────────────────────────────────────────┘
   ```

   Nothing goes beyond what the user approved (log.md:950); only the optional
   pointwise `transport` of M6 needs the user again.
3. **I1 witness.** A correct compiled witness; wrong plan-2 acceptance criterion (M1);
   no lock pollution; brief registry pollution (m7); a lasting risk unless consumers
   filter KNOWN-GAP rows (M1). clockChain passes the floor (reasoned, not compiled):
   with Δ = 1 every integer time is public, `tick_total` (Conditions.lean:46-49) gives a
   tick at s for every honest node; `readAt` includes events at times ≤ t
   (Run.lean:130-131), so the read at s is `clockBlock s`; `emittedAt` emits
   ⟨.proposer s, s⟩ (Run.lean:147-150); `PartialSynchrony` exempts excluded objects
   (Conditions.lean:113-115, 123-125); roots ⟨k⟩ are distinct, genesis has root ⟨0⟩.
4. **Lock regeneration.** Not auditable as planned (M2). Verify by the meaning pins,
   the per-task diff against a hardened-script baseline, and the source diff of the
   lambdas in Catalog/Core.lean; fix m9–m11.
5. **Forward needs.**

   ```text
   ┌──────────────────────────────────────┬───────────────────────────────────────────────┐
   │ Need                                 │ Status with 1a                                │
   ├──────────────────────────────────────┼───────────────────────────────────────────────┤
   │ FG facet (finalized output)          │ Fits: FinalInstance extends Instance with a   │
   │                                      │ carrier; map to v1 is Equiv.refl (tested).    │
   │ Nesting F ⪯ S ⪯ confirmed            │ Fits: a claim over that carrier (tested).     │
   │ Strong and FG on one instance        │ Fits: diamond structure, two maps (tested).   │
   │ Run context with an FG store         │ v1: store in P.State. v2: Carrier.v2 context. │
   │ Premises G, recurrence, a ≤ f        │ Claim constants with le; shared via           │
   │                                      │ Profile.Shared.                               │
   │ LinkedFG run premise on v1           │ Not a catalog claim. Additive: a carrier with │
   │                                      │ stronger admissible and new ids (M6 rule).    │
   │ FamilyCert (§7.3)                    │ Additive over one carrier.                    │
   │ Eligibility, protocol parameters     │ Facets or a separate structure (M4).          │
   │ Lift, v2 floor                       │ New claims over Carrier.v2 with relation      │
   │                                      │ lemmas; new core.v2 with an input claim       │
   │                                      │ (M1, M6).                                     │
   └──────────────────────────────────────┴───────────────────────────────────────────────┘
   ```

   Shapes that would force a breaking change later: new `Instance` fields (M4), pull
   along bijections only (M6), the `Carrier` name (m4), no `Carrier` id (m6), inline
   transports in the hash (m10). Each is cheap before Task 6 and breaks the lock after.
6. **Other.** Ordering: add Task 0 (M2, m7). Build commands correct (`lake build --wfail
   AvailableChainFramework AvailableChainRegistry`; scripts with `lake env lean --run`).
   Axiom checks: gap (M3). `sorry` policy: widen the grep (M3). Module headers (m1).

## Audit questions 1–7 (docs/audit/phase1a-plan-audit.md)

1. Core types feasible, after m1 and m2.
2. Every `le` direction matches design §4 (η↑, θ↑, lag↑, Π↓ weaker; θrec↑,
   recoveryFull false→true, G↓, ρ↑ weaker; exact-time D fixed; faultCap↓ weaker);
   transport guides agree with Regimes.lean; one vacuity hole (M5).
3. `ac43_iff` true as stated, via the `{h with}` rewrap (m3). `monotone` from
   `SafeFrom.monotone` (Properties.lean:34-38); `nested` matches `prefixOrder`. `Δ_pos`
   is needed only because `C.Valid` sits inside `∀ E`; harmless. For the strong claims
   `valid := True` is right (`StrongClaims` has only `SC.Valid`, Strong/Claims.lean:19;
   `SC.Valid` gives `0 ≤ strongDelay`, Strong/Constants.lean:13-14).
4. clockChain passes (focus item 3).
5. Design conformance: focus item 2.
6. Lock and registry: M2, m7–m11. The `profile-cert` row kind, the `Candidate` head,
   `KNOWN-GAP` and `--check` work with the type scan.
7. The 1a/1b/2 split is sound and each task leaves the build consistent. 1a lacks the
   eligibility location (M4), the axiom checker (M3), the KNOWN-GAP consumer contract (M1).

## Notes for the FG-SA composition work (async session)

- Plan 1a changes no library that FG-SA imports (GridCO, SA, SimplexFG, KitFG); only
  `AvailableChainRegistry/GridCOHooks.lean` (L4). FG-SA T3–T8 see no churn.
- On v1 with `LinkedFG`, FG-SA cannot certify catalog ids (core regimes have no
  `LinkedFG`). `FGSAClaims` stays outside the catalog until a `LinkedFG` carrier with
  new ids exists (additive under the M6 rule) or engine v2 with E2 `Linked`.
- After plan 2, a v1 `Candidate` is not the floor (M1); this bears on FG-SA Q1.
- Plan 1b changes Grid CO `excludes` and moves engine-generic GridCO and Counter lemmas
  into `Kit.Engine` (PHASE0-REPORT §6). FG-SA T7 reuses GridCO run lemmas: coordinate
  with 1b.

AUDIT COMPLETE: 0 blocking, 6 major, 12 minor

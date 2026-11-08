# Layout

How the code is organised: the libraries, the layers and their import rules, what `scripts/` holds, where the
proofs are, and the tests. `scripts/boundaries.toml` is the authoritative configuration; this file explains it.

## Libraries and layers

Lean module names are global. The main library is `ConsensusLean`; its layers are module
prefixes under `ConsensusLean/`. Namespaces and declarations stay unchanged.
The only default target is `ConsensusLean` (`defaultTargets = ["ConsensusLean"]`).
`ConsensusLeanTest` is the test library, selected by the lakefile's `testDriver` and built by
`lake test`; it is not a default target.
`Solution` and `Challenge` are single-module libraries for the comparator.
Reference snapshots that no target builds or checks (an earlier Goldilocks Lean model and spec, a Baseline properties sheet and the regime rows R.3–R.6) are outside the tree, at [`archive/` of `79cdddc8`](https://github.com/ethlabs-org/eth-consensus-lean/tree/79cdddc8e8e4c981211076da0ab1e7ee0bac1a25/archive), each with its `ARCHIVE.md`.
`specs/goldilocks/tex/` is the live LaTeX spec of Goldilocks, edited here; it is outside every Lake target and check and not trusted surface: fidelity is carried by the Lean statements and `docs/goldilocks-mapping.md` ([`README.md`](../specs/goldilocks/tex/README.md)).

| Layer under `ConsensusLean/` | Contents |
|---|---|
| `Init.lean` | Curated public imports: `Mathlib.Init` and `Mathlib.Tactic.Common`. |
| `Core/`, `ToMathlib/` | Trusted support; both empty for now. |
| `Spec/{Problem,Model,Blocks,Shape}/` | Trusted definitions. |
| `Statements/Review.lean` | The four review statements. |
| `Lemmas/{Problem,Model,Blocks,Shape}/` | Derived definitions, lemmas, canonical runs and witnesses. |
| `Proofs/<M>/Main.lean` | Milestones: `Behaviour`, `RegimesRealizable`, `Faithful`. |
| `Main.lean` | `ShapeObligations.correct` and `ShapeObligations.activeService`. |
| `Instances/<P>/{Spec,Statements}/` | Goldilocks (`Spec/`: what the endpoint statement reaches; `Statements/Obligations`: the endpoint). |
| `Instances/<P>/Milestones/` | Goldilocks milestone vocabulary and statements, not on the trusted surface. |
| `Examples/Shape/` | Shape examples, not on the trusted surface: Bft, Streamlet, Tendermint as contract values. |
| `Comparison/` | Comparison properties, untrusted: bound functions over environment parameters and the profiles they bound (`docs/decisions.md` §"Comparison properties"); proofs in `Proofs/Comparison/`, coverage witnesses for chain shapes in `Proofs/ComparisonCoverage/`. |

`Init.lean` is imported last by `Spec/Problem/Basic.lean` and `Spec/Model/Objects.lean`,
so every module reaches it. It is part of the trusted surface.
`scripts/boundaries.toml` is the one configuration of the import rules, checked
at source level by `scripts/check-boundaries.py` (module headers parsed by `lean --deps-json`; no build,
so no stale build output hides a violation). Every module is in exactly one `[[layer]]` (prefixes never
overlap); `allow` lists the layers it may import, written out in full:

| Layer | May also import |
|---|---|
| `Init`, `ToMathlib` (trusted) | Mathlib only |
| `Core` (trusted) | Init, ToMathlib |
| `Spec` (trusted) | the above, Core |
| `Statements` (trusted) | the above, Spec |
| `Lemmas` | the above, Statements |
| `Proofs.<M>` (one layer per milestone directory) | the above, Lemmas |
| `Main` | the above, every `Proofs.<M>` |
| `Examples` (Shape examples, untrusted) | Init, ToMathlib, Core, Spec |
| `Comparison` (untrusted) | Init, ToMathlib, Core, Spec |
| `Proofs.Comparison` | the above, Comparison |
| `Proofs.ComparisonCoverage` | Init, ToMathlib, Core, Spec, Statements, Lemmas, `Proofs.RegimesRealizable` (through its `Main`), Comparison |
| `Instances.Goldilocks.*` (one layer per component and level: `Spec.{Common,FG,Frame,Trace,FGStore,AC,SA,Node,Run}`, `AsChainShape`, `Statements.*`, `Lemmas.*`, `Proofs.<M>`, `Main`) | its row in `scripts/boundaries.toml`: no FG layer imports an AC or SA layer and no AC or SA layer an FG layer; `Statements.FG` reaches only the chain-level FG |
| `Instances.Goldilocks.Lemmas.{Simulation,Obligations}` | its row above, including `Lemmas.Healing` for finite regime consumers and healing/final adapters; Healing cannot import either, and Simulation cannot import Obligations |
| `Solution` | every generic layer and the closure of each finished instance milestone (today `Instances.Goldilocks.Proofs.FGSafety`, `Instances.Goldilocks.Proofs.ACBase`, `Instances.Goldilocks.Proofs.ACSteps`, `Instances.Goldilocks.Proofs.FGStore`, `Instances.Goldilocks.Proofs.ComposeAnyAC`, `Instances.Goldilocks.Proofs.Persist`, `Instances.Goldilocks.Proofs.Regimes`, `Instances.Goldilocks.Proofs.Service`, `Instances.Goldilocks.Proofs.Obligations` and `Instances.Goldilocks.Proofs.Healing`, with `Instances.Goldilocks.Lemmas.Healing`) |
| `Test` (`ConsensusLeanTest`) | everything above; library roots, import-only aggregates, `import all` |

The checker fails on: a missing, unparsable or mistyped config (missing or unknown keys included); a
module in no layer; a `Proofs/<M>/` directory without its own layer, or a milestone imported other than
through `Proofs.<M>.Main` (exception or not); an import outside `allow`, directly or through another
module's exception (printed with its path); allow lists that are cyclic, not downward-closed, or let a
trusted layer import an untrusted one; `import Mathlib`; an import of a library root or an import-only
aggregate, or `import all`, outside the tests; a module that does not reach `ConsensusLean.Init` through
public imports (except `ToMathlib` and the meta tool `ReviewGuard`); a fixture module or an unknown
top-level name; the attribute `expose` (a whole-file `@[expose]` section, on a declaration, or `attribute
[expose]`; comments and strings ignored) in a layer without `expose = true`, which only Core, Spec, Statements,
the instance Spec, Statements and `AsChainShape` layers, the Examples layer, the solution and the tests have (Lemmas, Proofs, Main and ToMathlib export no
bodies; the solution and the tests are leaves, so their exposure costs no rebuild), or `expose = true` on a
Lemmas, Proofs, ToMathlib or Main layer. Lean also exports the bodies of `abbrev`s and of instances of non-`Prop`
classes without the attribute; the checker does not flag those (today `Trace.Agree` and `kv`). Its self-test (`scripts/fixtures/boundaries/cases.toml`, one case per
failure kind) runs in check.sh step 2. Today's deviations from the matrix are reviewed
`[[exception]]` entries, each with its reason; today one: Goldilocks `Lemmas.Healing.ResetInv`,
`Lemmas.Healing.Recovery.Reports` and `Proofs.Healing.Main` import `Lemmas.Obligations.HealthyEffective`. An exception lets the modules under its `from` depend on the modules
under its `to` (and so on what those reach), never the importers of the `from` modules; none starts in a
trusted layer, and every `from` and `to` entry must be used.

The trusted layers' closure holds only trusted modules and the pinned base set: it cannot reach proofs,
instances, the solution, tests or fixtures (`CheckFixtures`, `CheckDeclsTest`, `Challenge`).
Every file of `ConsensusLean` and `ConsensusLeanTest` is imported by its library root. The generated
roots `ConsensusLean.lean` and `ConsensusLeanTest.lean` import every module of their library;
`check-boundaries.py` fails on an unlisted file. Regenerate them with
`lake exe mk_all --lib ConsensusLean --module` and
`lake exe mk_all --lib ConsensusLeanTest --module`.
The generated roots and other modules with descendants own no constants.
The external base set is `Init`, `Std`, `Lean`, `Lake`, `Mathlib`, `Batteries`, `Aesop`, `Qq`,
`ProofWidgets`, `Plausible`, `ImportGraph`, `LeanSearchClient`; unknown names fail.
Pins establish the provenance of those names.
The inventory configuration is cross-checked against `lakefile.toml`, including default targets
and globs. A `Proofs` component is allowed only under `ConsensusLean.Proofs` and
`ConsensusLean.Instances.Goldilocks.Proofs` (`[checks].proofs_component_prefixes`): check-decls
exempts definitions there from reaches-opaque, which is sound because no trusted layer can
reach them. `Exports` components are refused.

In `scripts/`:

- `check.sh`: the single driver, fixture self-tests and pass/fail/skip summary.
- `check-boundaries.py`, `boundaries.toml`: the layer matrix, its exceptions and the library inventory.
- `check-pins.py`, `pins.toml`: toolchain, dependency revisions, clean checkouts and resolution checks.
- `SpecSurface.lean`, `spec-extensions.txt`, `spec-theorems.txt`, `spec-snapshot.txt`, `instance-spec-snapshot.txt`: persisted-extension policy, theorem hygiene and the reviewed Spec and protected-surface snapshots.
- `CheckDecls.lean`, `check_decls_baseline.txt`: EthLib declaration checker (three local patches, see TRUST.md) and reviewed exceptions.
- `AxiomAudit.lean`, `AxiomAuditMain.lean`, `LICENSE.axiom-audit`: leanprover-community/axiom-audit v0.1.2 (verbatim; step 3b).
- `test_check_decls.sh`, `CheckDeclsTest.lean`, `CheckDeclsTest/`, `CheckDeclsForeign.lean`: verbatim EthLib fixture suite.
- `LICENSE.EthLib`, `vendor.sha256`: CC0 licence and hashes of every vendored copy.
- `fixtures/`: build (`--wfail`), boundary, `sorry` placement, axiom-audit, Spec-surface, review-pin, grep, pins, docs, comparator and Lake-check controls.
- `metrics-baseline.py`: report-only module metrics per layer of `boundaries.toml`
  (`docs/notes/metrics-baseline.md`); step 13 prints its totals.

The fixture libraries are `Challenge` (`Challenge.lean`, comparator statements
with placeholder proofs, importing exactly `ConsensusLean.Statements.Review` and the
`milestone_statements_modules`), rootless
`CheckFixtures` (under `scripts/fixtures/`, each fixture a separate target), and `CheckDeclsTest`
(EthLib fixtures under `scripts/`).
They may contain deliberately unfinished proofs or extra axioms; no checked library reaches them.
`comparator.json` connects the challenge to `Solution.lean`.

## Where the proofs are

### Responsibility and entry-point guide

Read the claim before its proof: [the definition](definition.md) explains the generic contract,
[the mapping](goldilocks-mapping.md) identifies the Goldilocks statement, and
[scenario coverage](scenario-coverage.md) distinguishes witnesses from proof packaging.
The generated library root is an inventory, not the recommended reading order.

| Question | Start here (paths under `ConsensusLean/`) | Responsibility / next layer |
|---|---|---|
| What does correctness require? | `Spec/Problem/CorrectProtocol.lean`, `Statements/Review.lean` | Generic property table and review roots; `Main.lean` composes the sufficiency proof. |
| What does an execution mean? | `Spec/Model/Run.lean`, `Lemmas/Model/View.lean`, `Lemmas/Model/Laws.lean` | Events, holdings and reads; `Proofs/Faithful/Main.lean` packages communication faithfulness. |
| How does a shape give correctness? | `Spec/Shape/Obligations.lean`, `Proofs/Behaviour/Main.lean` | Shape claims refine the generic properties; `Proofs/RegimesRealizable/Main.lean` constructs active regime witnesses. |
| What is the concrete protocol? | `Instances/Goldilocks/Spec/`, `Instances/Goldilocks/AsChainShape.lean` | Node transition rules and their engine representation; `Statements/Obligations.lean` fixes the contract and endpoint. |
| Where is a Goldilocks paper claim stated? | `Instances/Goldilocks/Milestones/Statements/` and the mapping | Milestone vocabulary outside the certified statement surface; `Proofs/<M>/Main.lean` packages proved fields. |
| Where is the endpoint assembled? | `Instances/Goldilocks/Proofs/Obligations/Main.lean`, `Instances/Goldilocks/Lemmas/Obligations/Accepted.lean` | Endpoints consume finite regime suppliers, simulation and read projections, rather than assuming open whole-run transport goals. |

The following paths are relative to `ConsensusLean/Instances/Goldilocks/Lemmas/`:

| Area | Entry points and responsibilities |
|---|---|
| `Common/`, `FG/`, `FGChain/`, `FGStore/` | `Common/Claims` states tree/digest facts; `FG/` and `FGChain/` handle chain safety and replay; `FGStore/` lifts them to node stores and effective phases. Consult the milestone's proof entry rather than importing a large hub for one helper. |
| `AC/` | `Basic` and `Trace` provide trace vocabulary; `Steps/` handles node-call preservation and locks; `FrameClaims` records frame statements. `ACBase` and `ACSteps` proof entries assemble the respective milestones. |
| `Compose/` | `Run/` relates the node to AC/FG projections; `Persist/Induction` proves C1.1 and its next-vote corollary. `Service/{Record,Inclusion,Later}` and `Sleepy/{Served,Transport,Read}` separate service, transport and observable reads. Their parent modules only re-export interfaces. |
| `Healing/` | `Assembly` packages run claims, `Service` packages phase service, `AC/Standalone` is the driven-AC endpoint, `Recovery/Assembly` packages HR.5/O.1/C1.3. `Retention/`, `Outcome/` and `Recovery/` supply preservation, outcome and finalization arguments; the corresponding milestone statements fix their contracts. |
| `Simulation/` | `Interface` states the simulation bundle. `Core`/`Provenance` tie canonical objects and trace cuts to engine holdings; `Queue` follows pool/queue inventories; `Steps` identifies event-local node transitions; `Run` assembles run laws; `Release` follows the release path; `Transport` supplies read-side adapters. |
| `Obligations/` | `ContractDefs` provides proof-side coefficient facts; `NonfinalSuppliers` supplies sleepy proposals, `HealthySuppliers` prepares bounded healthy state, `NonfinalEndpoints` projects confirmed coverage, and `OutageSuppliers` obtains armed pre-outage reads. `HealthyEffective` develops operational update/selection and report coverage; `OperationalPersistence` carries selected proposals into later parents. `NetworkTransport` distinguishes finite services from its stated open whole-run suppliers. `Accepted` assembles the obligations. |

For a report-only inventory of the current checkout, run `python3 -I scripts/metrics-baseline.py`;
`python3 -I scripts/module-cones.py --help` describes static downstream-cone reports. These are navigation
aids, not graph-size gates or measured rebuild times. Historical measurements in `docs/notes/` retain
their original scope. When a module is split, update this table by responsibility, not by line count.

Proof support outside the trusted surface: `ConsensusLean/Lemmas/Problem/Derived.lean` defines
`Agree`, `Safe`, `ReadySafeUpTo` and `FaultsBelow` with their characterising lemmas (not on the trusted surface: the
Goldilocks sheet that read them is archived), and `ConsensusLean/Lemmas/Problem/DerivedFacts.lean` defines `SendsFromZero` and
`Trace.map` with theirs (not protected); `CorrectProtocol` reads none of them. `ConsensusLean/Lemmas/Problem/Facts/` holds the derived `CorrectProtocol.*`
lemmas, including `CorrectProtocol.served`; `ConsensusLean/Lemmas/Blocks/Facts.lean` holds the block lemmas.
`ConsensusLean/Lemmas/Shape/Payload.lean` proves the payload bridges;
`ConsensusLean/Proofs/Behaviour/Main.lean`, `ConsensusLean/Proofs/RegimesRealizable/Main.lean`,
and `ConsensusLean/Main.lean` prove
refinement, coverage/witnesses, `ShapeObligations.correct` and `ShapeObligations.activeService`.
`ConsensusLean/Lemmas/Model/` and `ConsensusLean/Proofs/Faithful/Main.lean` prove
`sysOf_adequate`, `sysOf_log_faithful`,
`Run.held_iff_served`, `sysOf_nonFraming` and `sysOf_laws`, with support for canonical runs
(`canonical_run_from`), truncation (`Run.truncate_*`), views (`Run.mem_viewIdx_iff`)
and slashing protection (`honestNeverSlashed`). A node's `Run.ViewIdx` is the closure
of its engine `seen` log; the view lemma gives the event-index form.
Injective-hash lifting is checked in `ConsensusLeanTest/Model/Lift.lean`.

## Tests (`ConsensusLeanTest/`)

The [statement-to-scenario coverage map](scenario-coverage.md) records premise witnesses, reachable
events, rejection/control pairs, arithmetic checks and branch limitations, especially for Healing
and persistence. Use it before interpreting a missing-witness comment as a work queue.

`lake test` builds this library, including the review pins and citation index. The review files are at the top;
the generic tests are grouped by layer and the Goldilocks tests by component (`docs/notes/test-module-map.tsv` maps the
earlier flat names to these).

- `ReviewAxioms`, `ReviewGuard`: statement alpha-equality, completeness and axiom pins. `MilestoneAxioms`: the axiom
  pins of the other Goldilocks milestones.
- `Gaps`: the gap dispositions. `Index`: every cited name, checked to exist.
- `Problem/Properties`: every L0 property has teeth; local accountability (`local_accountability_teeth`).
- `Problem/Network`: the delivery rule (wakers served strictly before the bound, not instantly), faithfulness, silent runs and truncation.
- `Problem/Regimes`: what each regime admits and rejects; the explanatory regime lemmas of the abstract definition (L0, `docs/definition.md`).
- `Problem/CorrectProtocol`: vacuous systems are not correct; censoring progress, rotating sleepers, η-sleepy history.
- `Model/Basic`, `Blocks/Basic`, `Shape/Basic`: model mechanics, recurrence, compiled roles and poll mode.
- `Shape/Leaks`: do-nothing, fabricating and self-silencing protocols fail `ShapeClaims`; `recorder_live_testK` passes.
- `Shape/Realizable`: coverage, `allProposers_no_witness`, late-GST and late-outage witnesses.
- `Shape/Controls`: positive controls at explicit numbers.
- `Shape/Vacuity`: admissibility rejections, progress fit and tolerance, forgery, `noService_not_obligations`.
- `Model/Lift`, `Fixtures/{Support,Common}`: injective-hash lifting and fixtures; the example contract values are in `ConsensusLean/Examples/Shape/{Bft,Streamlet,Tendermint}.lean`.
- `Tactic/LinarithFrontEnd`: regressions for the `linarith` front end.
- `Goldilocks/`: one folder per component (`FG`, `FGStore`, `Frame`, `AC`, `Compose`, `Run`, `Regimes`, `Persist`,
  `Healing`, `Refinement`), with the concrete executions they share in `Runs/` and `Mirror/` (a computable mirror of
  the node), and the five-validator runs that show a premise is needed in `HalfCommittee/` and `InitialCarry/`.

### Gap dispositions

One line per gap (M1–M39 and the vacuous system), with `example`s for the
by-construction rows: `ConsensusLeanTest/Gaps.lean`.

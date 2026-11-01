# Historical API policy and exceptions

Superseded by the user decision of 2026-10-09. No checker reads this file.
Basis: e1afe9f3; inventory reference: 6c36d4810cb070655f2f4aadb3346db6c76aa0a3.

## docs/V2-API.md — prior header

# V2 API manifest

_Frozen at the Phase 2a gate (plan `docs/plans/2026-09-29-phase2a-engine-v2-core.md`,
Task 7), 2026-09-29._

This file lists the frozen v2 API: every public declaration of engine v2
(`AvailableChainEngineV2`: `Engine`, `Conditions` and `Laws`) and of
Kit v2 (`AvailableChainKitV2`, without `Tests`), by fully qualified name
and grouped by module.

ROOT-DIGEST W1 exception: user option 3, 2026-10-04 (plan r2 §2 M1).
Remove only `AvailableChain.V2.rootInjective_all` and
`AvailableChain.V2.D.rootInjective_all`. Keep both scope predicates. Remove each
proof reference from its existing Framework anchor body; keep both anchors.
This exception does not permit other engine claims or checker changes.
W3 owns the final generated entries after the interface checkpoint.

ROOT-DIGEST W1c, option-3 class addition (plan r2.1 and r2.2):
the [Gen exception list](GEN-API.md#root-digest-option-3-exception) names the no-eligible-child
and retained-transport statement/equation pairs, their exact tree premises, and kernel evidence.
No v2 walk entry changes. The v2 generated delta remains the two named M1 removals above.
The tool output is `.lake/rdw1c-v2-manifest.md`; its exact delta is
`.lake/rdw1c-v2-manifest-delta.json`. Both Framework anchors remain declared.

ROOT-DIGEST-2 option 3 permits the 64 mode-indexed generic entries and measured
representation dependencies. See the [full exception](FGSA-API.md#root-digest-2-option-3-exception).
Keep the frozen baselines and SHAs. Exact old/new hashes and causes follow at integration.

## Freeze rule

After the gate, no declaration in this file changes its name, type or body
(DC N6). A 2a structure never gains a field, a 2a inductive never gains a
constructor, and a 2a definition never gains a parameter. Later stages (2b,
2c) only ADD declarations or separate structures.

- **The module blocks are append-only.** A changed or removed line in a
  module block below is a freeze break, unless a named user decision allows
  it. A new line is an ADD. The Counts table and the date line change with
  every ADD.
- **Engine v2 entries are locked.** The values of the anchor defs
  (`AvailableChain.Framework.V2.anchor` in
  `AvailableChainFramework/V2/Anchor.lean` for the 2a entries, and one new
  anchor def per later stage; see "Anchors") reference each engine entry.
  `scripts/CatalogLock.lean` locks the module prefix
  `AvailableChainFramework.V2`, so the lock lines of the anchor defs hash
  the closure of every engine entry. A change to an engine entry gives a
  `CHANGED` anchor line. As everywhere in the lock, a theorem contributes its
  statement only: a new proof keeps the hash. A change to a model module in
  the closure (for example `AvailableChainModel.Objects.Time`) also changes
  the anchor line.
- **Every entry has its own hash.** Each line of the blocks below ends with
  an entry hash, and `V2Manifest --check` fails when it differs. Thus a
  change to one engine entry is found even in a commit that also has a
  `CHANGED` anchor line, and a change to a Kit entry is found although the
  lock does not see the Kit (L5; the Framework does not import it). The
  entry hash mixes: the own hash of the entry and of every generated or
  private constant in its closure (`deps` rules of the lock) that is in a v2
  module or in the module of the entry (matchers, equation lemmas,
  `_proof_` constants, private helpers), in `Name.lt` order; the binder
  names (without macro scopes, which depend on earlier declarations of the
  module) and binder infos of its type; its reducibility status; and whether
  it is an instance. The own hash is the `ownHash` of the lock (kind, name
  and type; for a definition also the value; for an inductive also the
  constructor names; for a theorem not the proof), after the universe
  parameters are renamed `u0`, `u1`, …. A new proof keeps the hash.
- **Frozen by rule, not checked.** The lock hash does not see binder names,
  binder infos, reducibility or attributes. The entry hash sees binder names
  and binder infos of the type, reducibility and the instance attribute, but
  not other attributes (for example `@[simp]` on
  `LabelFamilies.apObject_seat`) or an instance priority. All of them are
  frozen by rule.
- **Outside v2.** The entry hash does not see a change to a declaration
  outside the v2 libraries that the entry uses (Model, Mathlib). For an
  engine entry the lock line of its anchor sees it; a `CHANGED` anchor line
  with no `CHANGED` entry means such a change. A Model declaration that
  only Kit entries use is seen by neither the lock nor the manifest; it is
  frozen by rule only.

## Anchors

Never edit `anchor`. A later stage adds its engine entries to this file
and one new anchor def in a new module under `AvailableChainFramework/V2/`
(for example `anchor_2b` in `Anchor2b.lean`, imported by the Framework
root); `V2Manifest --anchor` prints its body (the engine entries that no
anchor covers yet). The lock change is then ADDED only. An engine entry is
anchored if it is in the closure of some non-generated declaration of a
module under `AvailableChainFramework.V2`.

Put new declarations AFTER the existing declarations of a 2a module, or in a
new module. Lean reuses a matcher of the same shape within a module, first
come first served: a declaration inserted above a 2a declaration can take
over its matcher, and the ADD then gives `CHANGED` lines.

## Scope

An entry is a declaration of a scope module that Lean did not generate, by
the rule of `scripts/CatalogLock.lean` (`generated`). Thus the list
includes structure constructors and fields (projections) and derived
instances, and excludes recursors, `casesOn`, `noConfusion`, matchers,
equation lemmas, `injEq`, `sizeOf_spec` and private declarations.

- Scope modules: `AvailableChainEngineV2.Engine.*`,
  `AvailableChainEngineV2.Conditions.*`, `AvailableChainEngineV2.Laws.*`,
  and every module `AvailableChainKitV2.*` outside `AvailableChainKitV2.Tests`.
- Not in scope: the modules `AvailableChainEngineV2.Tests.*` (namespace
  `AvailableChain.V2.Tests`) and `AvailableChainKitV2.Tests.*` (the Kit
  counterexamples, namespace `AvailableChain.V2.Engine.Tests`, and the toy
  run, namespace `AvailableChain.V2.Tests.Toy`); the library roots (imports
  only). The exclusion is by module, not by namespace.
- `AvailableChainEngineV2.Sketch` was deleted at the gate; it is not API.
- Rulings: the Task 5 helpers (`propSeat`, `eq_propSeat`,
  `holder_propLabel`, `Output`, the `OutputsFactor` lemmas) are listed
  and frozen; `Interface.propLabel_injective` is a frozen field; the run
  checks of `AvailableChainKitV2.RunCheck` (`allTicks`, `allDeliveries`,
  `emittedBy` and their `_spec` lemmas) are Kit entries. Every Kit entry is
  frozen; no group is "helpers, not frozen".

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --list` prints the module
  blocks below from the environment, in source order, with the hashes.
- `lake env lean --run scripts/V2Manifest.lean --anchor` prints the body of
  a new anchor def over the engine entries that no anchor covers yet.
- `lake env lean --run scripts/V2Manifest.lean --check` exits 1 if the
  anchor `AvailableChain.Framework.V2.anchor` is missing, if an entry does
  not exist or is not in the module of its heading, if a kind word differs,
  if a hash is missing or differs, if an engine entry is not anchored, if a
  public declaration of a scope module is not listed, or if a scope module
  has no heading. It exits 2 if the declaration ranges (`.olean.server`
  data) are missing.
- `V2Manifest --check` enforces completeness, so 2b adds a manifest line
  for each new public declaration in a 2a scope module.
- `generated`, `deps`, the closure traversal, `kindTag` and `ownHash` in
  `V2Manifest` are copies of `scripts/CatalogLock.lean`, except that
  `ownHash` renames the universe parameters first. A change to one needs
  the same change in the other.

Each block line is `<kind> <name> <hash>`. The kinds are `structure`,
`inductive`, `ctor`, `def` (fields that are data included) and
`theorem` (fields that are proofs included).

## Counts

```text
┌──────────────────────────────────────────────┬─────────┬────────────────────┐
│ Module                                       │ Entries │ Status             │
├──────────────────────────────────────────────┼─────────┼────────────────────┤
│ AvailableChainEngineV2.Engine.Objects        │      15 │ locked (anchor)    │
│ AvailableChainEngineV2.Engine.Run            │      42 │ locked (anchor)    │
│ AvailableChainEngineV2.Engine.Spec           │      28 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Committees │      10 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Delivery   │       8 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Interface  │      19 │ locked (anchor)    │
│ AvailableChainEngineV2.Conditions.Schedule   │      33 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.Hooks            │      16 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.Isolation        │      26 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.Outputs          │      10 │ locked (anchor)    │
│ AvailableChainEngineV2.Laws.SelfDelivery     │      17 │ locked (anchor)    │
│ AvailableChainKitV2.ClockLaws                │       9 │ frozen, not locked │
│ AvailableChainKitV2.Emission                 │      10 │ frozen, not locked │
│ AvailableChainKitV2.EngineClock              │      16 │ frozen, not locked │
│ AvailableChainKitV2.Execution                │      10 │ frozen, not locked │
│ AvailableChainKitV2.RunCheck                 │       6 │ frozen, not locked │
│ AvailableChainKitV2.Stable                   │       5 │ frozen, not locked │
├──────────────────────────────────────────────┼─────────┼────────────────────┤
│ Engine v2 total                              │     224 │ locked (anchor)    │
│ Kit v2 total                                 │      56 │ frozen, not locked │
│ Total                                        │     280 │                    │
└──────────────────────────────────────────────┴─────────┴────────────────────┘
```

## Engine v2 (locked through the anchor)


## docs/GEN-API.md — prior header

# Generic API manifest

_Baseline for A0 step 2 (I23, ruling D15), 2026-09-30._

This file lists every public declaration of
`AvailableChainGeneric.Statements.*` (Pure, V2 and AC), by fully qualified
name and grouped by module. Gen has no anchor rule.

ROOT-DIGEST-2 option 3 permits the 64 mode-indexed generic entries and measured
representation dependencies. See the [full exception](FGSA-API.md#root-digest-2-option-3-exception).
Keep the frozen baselines and SHAs. Exact old/new hashes and causes follow at integration.

## Baseline rule

Baseline at the A0 step-2 close. Before G-F0a a Gen Statements edit re-writes this file in the SAME commit (visible diff); from G-F0a it is append-only.

## ROOT-DIGEST option-3 exception

ROOT-DIGEST W1c, user option 3 (2026-10-04), plan r2 Addenda r2.1 and r2.2.
The class exception covers these four entries in `AvailableChain.Gen.Pure`:

- `WalkNoEligibleChildOfAnchorClosedStatement` and
  `WalkNoEligibleChildOfAnchorClosedStatement_def`: add
  `(∀ A ∈ tree, ∀ B ∈ tree, A.root = B.root → A = B)` before `AnchorClosed anchor tree`.
  Evidence: `.lake/rdw1b-walk-evidence.lean`, theorem `old_walk_claim_false`, checked against
  production objects in `.lake/rdw1c-check-walk-evidence.log`. Equal-root eligible siblings
  cause GHOST to stop at their parent.
- `WalkCoversOfRetainedTransportStatement` and
  `WalkCoversOfRetainedTransportStatement_def`: add
  `(∀ A ∈ targetTree, ∀ B ∈ targetTree, A.root = B.root → A = B)` before source coverage.
  Evidence: `.lake/rdw1c-retained-evidence.lean`, theorem `frozen_retained_claim_false`.
  Its kernel check is `.lake/rdw1c-retained-evidence-final.log`. The source returns A;
  equal-root target siblings make GHOST return genesis despite BestAncestry.

The census is `.lake/rdw1c-census.md`. No other frozen walk entry needs a new premise.
BestAncestry keeps its definition. Strict dominance and a selected source path need no new premise.
CStoreInv supplies the local tree premise through `baseBlocks_rootInj` and `erasedList_rootInj`.
Generic helpers forward their explicit tree premise. W2 caller edits remain outside W1 scope.
No FGSAClaims field or Base₂ text changes beyond plan §2 are permitted by this exception.
GHOST, its tie refusal, and the selector/window algorithm stay unchanged.

The official Gen list has 705 entries. The tool output and the exact four-entry delta are in
`.lake/rdw1c-gen-manifest.md` and `.lake/rdw1c-gen-manifest-delta.json`.
All new objects come from the production build. No caller is removed from those modules.
The full lower-library build remains blocked by W3 test migration.

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --scope gen --list` prints
  the module blocks from the environment, in source order, with hashes.
- `lake env lean --run scripts/V2Manifest.lean --scope gen --check` checks
  the names, modules, kinds, hashes and completeness. A failed check exits 1.
- `--manifest <path>` overrides this file. `--anchor` is a usage error for Gen.

Each entry hash uses the shared hash rules in `scripts/V2Manifest.lean`:
types and definition values, generated or private helpers in the closure,
type binder names and infos, reducibility, and instance status. Theorem
proofs do not affect the hash.

## Entries


## docs/FGSA-API.md — prior header

# FG-SA API manifest

_Baseline for G-F0a (D15, lead ruling DC 2026-09-30)._

This file lists every public declaration under the Statements prefixes of
`AvailableChainFGSA`, `AvailableChainFGSARun` and `AvailableChainFGSAClaims`,
by fully qualified name and grouped by library and module. FGSA has no anchor rule.

## Baseline rule

Before G-F0a, a missing doc makes the check print SKIP and exit 0. F0 writers
do not update this doc. At G-F0a, run `bash scripts/fgsa-freeze.sh` to write
this doc, copy it to `docs/FGSA-API-frozen.md`, and record the frozen SHA-256
in `scripts/fgsa-manifest-frozen.sha256`. From G-F0a the API is append-only.
Every frozen entry must keep its kind and hash; new entries pass. A changed
or removed entry needs an allow line in `scripts/fgsa-manifest-allow.txt`:
`<name>\t<reason>\t<plan revision>`, with actual tabs and no empty field.
Stale allow lines fail. Put later fields in new structures unless a named
exception below permits the exact aggregate change.

## WC plan r2.1 aggregate exception

Lead ruling 2026-10-05, WC plan r2.1, §8 Job 4; DC: SAME source witness order.
Append exactly one field after `cleanGrowth` in `AvailableChain.FGSA.Run.FGSAClaims`:
`weakContinuationLive : ∀ G : Time, WeakContinuationLiveClaim p G`.
The permitted delta is this aggregate, its constructor, every existing generated
projection, and the new field entry. Each changed frozen entry has one measured
allow line. The new field is additive and needs no frozen allowance.
Root fills the field with the complete WC proof and the closed H-time producer.
`fgsaClaims (p) : FGSAClaims p` stays hypothesis-free. The live-to-safety adapter
stays in Shared/Claims. Source non-vacuity still requires `4 * p.Δ ≤ G`.
No other frozen entry changes under this exception. Preserve the frozen file
bytes and SHA. All earlier exception records still apply.

## ROOT-DIGEST-2 option-3 exception

ROOT-DIGEST-2, option 3, 2026-10-04. Full identity means equality of recursive NamedProposal,
including each ancestor's body, signed rows, raw HEAD list, and support list. This supersedes
root-digest-plan r2's body-only limitation and its instruction to retain the old ContentAgree.
The exception permits the exact N/A/H/E/Q changes in root-digest2-plan §4.1, the 64-entry generic
mode delta in §9, and their measured representation dependencies. It permits exact named-parent
admission and root-identifier HEAD handling in the shared GridCO base, with legacy block-mode
behavior retained for the deferred protocols. The closed fgsaClaims type, all claim fields,
numerical bounds, original observation scopes, and prior named exceptions remain. Each changed
frozen entry must have an old/new type or hash and a cause. No frozen baseline or SHA is replaced.

## ROOT-DIGEST W1c class exception

The [Gen exception list](GEN-API.md#root-digest-option-3-exception) names all four frozen walk
entries and their kernel evidence under plan r2.1 and r2.2. No frozen FG-SA walk entry needs a
new premise. The non-frozen `AvailableChain.FGSA.fgsa_headInTree_reanchor_of_pivot` now takes
root uniqueness on its arbitrary `tree`. CStoreInv supplies this for each erasedList view.
The census is `.lake/rdw1c-census.md`. FGSAClaims fields and Base₂ text are unchanged by W1c.
W3 has migrated `AvailableChainFGSA.Tests.Support`. Final manifest generation waits for W2.
No generated FG-SA entry, frozen baseline, SHA, or allow policy is changed here.

## ROOT-DIGEST W2b D1 exception

Plan r2.3 permits `AvailableChain.FGSA.Run.CPPrefix` and `CPPrefix_def` to take
`RootBlockInRun p c E rho (eraseFG B)` after honest membership. EntryBelow is unchanged.
CPPrefix now quantifies over run blocks only. Evidence:
`TS/codex/reports/rdigest/w2/rdw2/cp-prefix-stop.lean`:
"counterexample to the local inference only". This is not a full-run claim counterexample.

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --scope fgsa --list` prints
the module blocks from the environment, in source order, with hashes.
- `lake env lean --run scripts/V2Manifest.lean --scope fgsa --write` writes this doc.
- `lake env lean --run scripts/V2Manifest.lean --scope fgsa --check` checks
the names, modules, kinds, hashes and completeness (D15), then the frozen
SHA-256 and append-only rule. A failed check exits 1.
- `--manifest <path>`, `--frozen <path>`, `--allow <path>` and
`--frozen-sha <path>` override the paths. `--anchor` requires v2.

Each entry hash uses the shared hash rules in `scripts/V2Manifest.lean`:
types and definition values, generated or private helpers in the closure,
type binder names and infos, reducibility, and instance status. Theorem
proofs do not affect the hash. Public `_def` theorems are entries. Each public
structure projection is a separate `field` entry beside the structure entry.

## FG-SA port r2 SWITCH exception

The single h+i+j protocol switch changes canonical readers and the final frame surface.
The [SWITCH record](reports/fgsa-port-switch.md) gives the reason, scope, and red-window limits.
The [measured diff](reports/fgsa-port-switch-diff.json) attributes all 54 changed shallow hashes.
Exact allowances preserve earlier reasons. Deep and frame baselines remain fixed.
The new exact exception maps contain 897 deep entries and five frame entries.


## `AvailableChainFGSA`



## Inventory discovery scope

Current audit inventories contain compiled public declarations, projections,
constructors with declaration ranges, and public explicit `_def` equations.
Internal/private names, auxiliary recursors, matchers, noConfusion declarations,
and other generated names are excluded by compiler metadata. The independent
axiom/used-constant auditors still inspect all compiled constants in their scopes.
The old Claims inventory explicitly named FinFormW.rec, FinFormW.recOn, and
FinFormW.casesOn. These generated names are not public inventory roots; they
remain in the unchanged compiled axiom scan. No source declaration was removed.

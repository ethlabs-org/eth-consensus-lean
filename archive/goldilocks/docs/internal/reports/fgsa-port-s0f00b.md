# S0-F / 00b — final frame surface and review fixes

Basis: `cd736e868ef710d87c326ebc220297435a3f79b9`; branch `port-s0f00b`.
Review fix basis: `0d34012a4b71d7520e7d7350f7c6f845d413a015`.
Plan: port r2 and binding addendum ruling A, 2026-10-09.

All existing protocol declarations keep their source text in Stage 0. The
canonical aggregate keeps its present field types. The changes below prepare
SWITCH; they do not execute it.

P1: `Statements/FrameNext` is the lower module. It imports Run `Statements/AC`,
FGSA `Statements/Invariants`, Claims `Statements/Channels`, Gen
`Statements/Pure/Quorum`, and Model `FrameNext`. It contains `frameRNext`,
`domainRNext`, `RFrameExactNext`, `RFrameNext`, `TStartNext`, `TWalkNext`,
`SettledPhaseFrameNext`, `TGeomNext`, `OpeningCoveredNext`, `FrameAtNext`,
`WalkBatchNext`, and their existing equations. It does not reach `ComposeStmt`.
`WalkBatchNext` copies the complete unchanged `WalkBatch` predicate so that
`TWalkNext` does not import its canonical home in `ComposeStmt`.

`Statements/ComposeNext` is above `ComposeStmt` and the lower `FrameNext`.
It contains `FGFoundationNext`. `Claims/FrameNext` is above `ComposeNext` and
`Statements/Packages/Safety`. It contains `FGFoundationClaimNext` and
`FrameClaimNext`. No Claims module imports another Claims module.

The binder structure, observation indices, bounds, and premises stay fixed.
The exact-frame copies use guarded `treeFjControlsView`, proposals retained in
`Next.tree`, voter blocks and ancestor witnesses in that tree, and cumulative
support resolution followed by retained-tree membership. Metadata and admission
clauses stay fixed. `TWalkNext` now names the identical lower `WalkBatchNext`.

Canonical-to-Next classification (comparison B is separate from SWITCH classes):

```text
┌────────────────────────────────┬────────────────────────────┬───────┐
│ Next                           │ Canonical                  │ Class │
├────────────────────────────────┼────────────────────────────┼───────┤
│ frameRNext (+ _def)            │ frameR (+ _def)            │ B     │
│ domainRNext (+ _def)           │ domainR (+ _def)           │ B     │
│ RFrameExactNext (+ _def)       │ RFrameExact (+ _def)       │ B     │
│ RFrameNext (+ _def)            │ RFrame (+ _def)            │ B     │
│ FGFoundationNext               │ FGFoundation               │ B     │
│ TStartNext                     │ TStart                     │ B     │
│ TWalkNext                      │ TWalk                      │ B     │
│ SettledPhaseFrameNext (+ _def) │ SettledPhaseFrame (+ _def) │ B     │
│ TGeomNext                      │ TGeom                      │ B     │
│ OpeningCoveredNext             │ OpeningCovered             │ B     │
│ FrameAtNext                    │ FrameAt                    │ B     │
│ FrameClaimNext                 │ FrameClaim                 │ B     │
│ FGFoundationClaimNext          │ FGFoundationClaim          │ B     │
│ WalkBatchNext                  │ WalkBatch                  │ A     │
└────────────────────────────────┴────────────────────────────┴───────┘
```

The structure has the same seven fields. Only its frame field uses
`RFrameExactNext`. Its constructor and projections inherit class B in this
canonical-to-Next comparison. `WalkBatchNext` is an identical predicate (A).

P2: Before/after SWITCH classification of the NEW entries:

```text
┌────────────────────────────────────────────────┬──────────────┬─────────────────────────┐
│ New entries (Run namespace)                    │ SWITCH class │ Deep cause              │
├────────────────────────────────────────────────┼──────────────┼─────────────────────────┤
│ frameRNext, domainRNext, SettledPhaseFrameNext │ A            │ fixed local closure     │
│ their three _def entries                       │ A            │ fixed local closure     │
│ RFrameExactNext, RFrameNext, both _def entries │ A            │ run binder              │
│ WalkBatchNext, TWalkNext, TStartNext           │ A            │ run binder              │
│ FrameAtNext, FrameClaimNext                    │ A            │ run binder              │
│ TGeomNext                                      │ B            │ run/emitted proposal    │
│ OpeningCoveredNext                             │ B            │ run/source/emitted row  │
│ FGFoundationNext, .mk, all seven fields        │ B            │ run/emitted row         │
│ FGFoundationClaimNext                          │ B            │ run/premise/emitted row │
└────────────────────────────────────────────────┴──────────────┴─────────────────────────┘
```

Transport argument: fix the events, inputs, seats, honest set, environment,
horizon, and parameters. SWITCH keeps `initial`, input handlers, `process`, and
`clock` fixed. Induct on event prefixes. A delivery or input uses the same store
handler. A tick uses the same clock; changed duties can change emitted objects
and the record, but `recordOwn` writes only `Node.record`. A restore sets
`Node.st` to the same initial store independently of the saved record. Thus
`Node.st` is equal at each index and at each pre-tick/post-clock observation.
The argument does not require equal emitted objects or equal records.

`RFrameExactNext`, `RFrameNext`, `FrameAtNext`, and `FrameClaimNext` read these
stores with fixed Next functions. `WalkBatchNext` also uses only fixed seats,
honest membership, supplied vote lists, and store resolution. `TWalkNext` adds
fixed Next tree/head reads to that predicate. `TStartNext` uses only the
`leases`, `now`, and `output` projections of `fgsaAC` in `LeaseBelowOutput`;
those project `Node.st`, although the unused `fgsaAC.head` projection changes.
All these propositions therefore transport as class A. This is a source
argument, not a new checked transport lemma.

`TGeomNext` still uses `HonestProposal -> Run.emits -> dutyAction`.
`OpeningCoveredNext` still uses canonical `actionSourceFG -> fgSource`, and
`HonestRowAt -> Run.emitsAt -> dutyAction`. `FGFoundationNext.strat` uses
`RStrat -> HonestRowBefore -> HonestRowAt -> Run.emitsAt`. These complete
entries have class B. All projections of the structure depend on its carrier
and inherit B, including `.frame`; its individual `RFrameExactNext` predicate
retains the class-A guarantee. `FGFoundationClaimNext` also has the source
premise and this B conclusion. No new premise is added.

Exact new entries that need measured SWITCH deep exceptions are listed here.
Prefix: `AvailableChain.FGSA.Run.`. Class A does not remove a deep exception:
the unchanged run binder still contains `fgsa -> dutyAction`, whose body changes.

- Class A: `RFrameExactNext`, `RFrameExactNext_def`, `RFrameNext`,
  `RFrameNext_def`, `WalkBatchNext`, `TStartNext`, `TWalkNext`, `FrameAtNext`,
  `FrameClaimNext` (nine entries).
- Class B: `TGeomNext`, `OpeningCoveredNext`, `FGFoundationClaimNext`,
  `FGFoundationNext`, `FGFoundationNext.mk`, `FGFoundationNext.store`,
  `FGFoundationNext.cumul`, `FGFoundationNext.mono`, `FGFoundationNext.frame`,
  `FGFoundationNext.geo`, `FGFoundationNext.strat`,
  `FGFoundationNext.reconcile` (12 entries).
- No expected deep exception: `frameRNext`, `frameRNext_def`, `domainRNext`,
  `domainRNext_def`, `SettledPhaseFrameNext`, `SettledPhaseFrameNext_def`.
  Their local Next reader closures stay fixed; WP00c must verify this.

The one h+i+j switch owns all changed deep causes. WP00c measures each old/new
digest and dependency path. This report is not an allowance or a deep baseline.
C-i remains contextual evidence: Clean needs the Clean invariant, not only
FaultQ; Recovery needs RXing and the local finality carrier. Neither requires
equal honest finalized roots. It does not change a complete B predicate to A.

Planned SWITCH import edges, with full module prefixes:

1. `AvailableChainFGSA.Model.Frame -> AvailableChainFGSA.Model.FrameNext`:
   canonical reader bodies can name their fixed Next targets.
2. `AvailableChainFGSARun.Model.Protocol -> AvailableChainFGSA.Model.FrameNext`:
   duty bodies can name their Next targets.
3. `AvailableChainFGSAClaims.Statements.ComposeStmt ->`
   `AvailableChainFGSAClaims.Statements.FrameNext`:
   canonical `FGFoundation.frame := RFrameExactNext`.
4. `AvailableChainFGSAClaims.Claims.Foundations ->`
   `AvailableChainFGSAClaims.Statements.FrameNext`:
   canonical `FrameAt` uses the final exact-frame conjunction.
5. `AvailableChainFGSAClaims.Claims.Foundations ->`
   `AvailableChainFGSAClaims.Statements.ComposeNext`:
   canonical `FGFoundationClaim` uses `FGFoundationNext`.
6. `AvailableChainFGSAClaims.Claims.Clean ->`
   `AvailableChainFGSAClaims.Statements.ComposeNext`:
   `CleanCutPosClaim` uses the Next foundation antecedent.
7. `AvailableChainFGSAClaims.FGSAClaims -> AvailableChainFGSAClaims.Claims.FrameNext`:
   `FGSASafetyClaims.frame` uses `FrameClaimNext` and
   `FGSASafetyInterfaces.fgFoundation` uses `FGFoundationClaimNext`.

These are the complete added edges for this frame plan, including its model
and duty routing. Existing edges remain. `ComposeNext -> ComposeStmt` and
`ComposeNext -> FrameNext` already exist in Stage 0. SWITCH must not add
`ComposeStmt -> ComposeNext` or `ComposeStmt -> Claims.FrameNext`.

Acyclicity evidence: `lake env lean --run /tmp/s0f-fix-graph-repro.lean` imports the
compiled FGSA, Run, Claims, and Proofs facades with `loadExts := false`, then reads every module's
`env.header.moduleData[i].imports`. It forms the full direct-import graph,
checks both lower closures for `ComposeStmt`, and inserts the seven edges in
order. Before each insertion it rejects a path from the target to the source.
Thus a cycle formed by more than one new edge is also rejected. The current
compiled graph is acyclic because Lean built it. Results are recorded below.

Reproducible import query: save this block to a temporary `.lean` file and run
`LEAN_SLOTS=2 lake env lean --run <file>` from the built repository.

```lean
import Lean
open Lean

def planned : Array (Name × Name) := #[
  (`AvailableChainFGSA.Model.Frame, `AvailableChainFGSA.Model.FrameNext),
  (`AvailableChainFGSARun.Model.Protocol, `AvailableChainFGSA.Model.FrameNext),
  (`AvailableChainFGSAClaims.Statements.ComposeStmt,
   `AvailableChainFGSAClaims.Statements.FrameNext),
  (`AvailableChainFGSAClaims.Claims.Foundations,
   `AvailableChainFGSAClaims.Statements.FrameNext),
  (`AvailableChainFGSAClaims.Claims.Foundations,
   `AvailableChainFGSAClaims.Statements.ComposeNext),
  (`AvailableChainFGSAClaims.Claims.Clean,
   `AvailableChainFGSAClaims.Statements.ComposeNext),
  (`AvailableChainFGSAClaims.FGSAClaims, `AvailableChainFGSAClaims.Claims.FrameNext)]

partial def closure (g : Std.HashMap Name (Array Name)) (todo : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match todo with
  | [] => seen
  | n :: ns => if seen.contains n then closure g ns seen
    else closure g ((g[n]?.getD #[]).toList ++ ns) (seen.insert n)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `AvailableChainFGSAClaims },
    { module := `AvailableChainFGSARun }, { module := `AvailableChainFGSAProofs },
    { module := `AvailableChainFGSA }] {} (loadExts := false)
  let mut g : Std.HashMap Name (Array Name) := {}
  let mut count := 0
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    let deps := env.header.moduleData[i]!.imports.map (·.module)
    count := count + deps.size
    g := g.insert m deps
  IO.println s!"CURRENT: {g.size} modules, {count} direct import edges"
  for root in #[`AvailableChainFGSAClaims.Statements.FrameNext,
      `AvailableChainFGSA.Model.FrameNext] do
    let c := closure g [root]
    if c.contains `AvailableChainFGSAClaims.Statements.ComposeStmt then
      throw <| IO.userError s!"lower target reaches ComposeStmt: {root}"
    IO.println s!"LOWER: {root}: {c.size} modules; ComposeStmt absent"
  for (src, dst) in planned do
    if (closure g [dst]).contains src then throw <| IO.userError s!"cycle from {src} -> {dst}"
    let edgePresent := (g[src]?.getD #[]).contains dst
    IO.println s!"SWITCH: {src} -> {dst}; already present={edgePresent}; reverse path=false"
    g := g.insert src ((g[src]?.getD #[]).push dst)
  -- Sequential insertion tests each new edge against all preceding new edges.
  IO.println "PLANNED SWITCH GRAPH: PASS (acyclic)"
  return 0
```

P2: Complete SWITCH reader-consumer map. `K` means the declaration keeps its
text and gets the new meaning through the stated canonical reader path. It
needs no further Next copy. `N` means its final text/type must change; the
reviewed Next target supplies that surface. `L` means legacy text retained.
All B causes below belong to the same h+i+j switch. Each equation inherits
its predicate's decision and class. A structure cause includes its constructor
and all projections; aggregate extensions also inherit the changed parent.

The direct scan covers Model reader calls in FGSA, Run, and Claims Statements
and Claims. It also checks Proofs Statements. The compiled dependency map
below checks indirect API consumers without treating the run binder alone as
a reader use.

Compiled scan: 25 direct and 129 indirect source declarations from the
369-source census have a reader path. The census classes are preserved.
The scan uses declaration types and definition values; theorem proofs are not
reader meanings. It omits the `fgsa` constant edge during path search, then
records that separate run cause below. It excludes the 27 new entries, whose
classes and exact causes are listed above. Every current non-Next API source
root outside the census was also checked; none adds another reader path.

`C` is the census class. `Deep` is `H` for the listed canonical reader change,
plus `D` when the closure reaches `fgsa` and its changed duties. Every row has
one exact current dependency path; constructor nodes are retained. Names without
`FGSA.` use the prefix `AvailableChain.FGSA.Run.`; `FGSA.` means
`AvailableChain.FGSA.`. The module path above each table gives the source home.

The N rows are retargeted at SWITCH as described in the seven import edges.
All downstream K rows then follow those canonical declarations to the final
Next surface. K does not require a new import: its current reader import is
sufficient. Existing Stage 0 copies of K predicates remain the fixed Next
comparison targets; no additional copy is needed.

`fgsaOutputs` is A despite its syntactic path through `fgsaIso -> actS`:
its `output`/`headOutput` projections reduce to stored stable output/F. Its
meaning transports with `Node.st`; only its deep closure changes (D).
Likewise, unused fields of `fgsaAC` do not make `TStartNext` class B.

Direct readers:

`AvailableChainFGSARun/Statements/AC.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ fgsaAC                       │ B │ K │ H+D  │ fgsaAC -> FGSA.headVote                           │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSARun/Statements/Client.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ fgClientEvent                │ B │ K │ H+D  │ fgClientEvent -> FGSA.fgInputs                    │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSARun/Statements/Emission.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ HeadTargetAtEmission         │ B │ K │ H+D  │ HeadTargetAtEmission -> FGSA.headVote             │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSARun/Statements/ReceiptCoverage.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ ReceiptCoverageStatement     │ B │ K │ H+D  │ ReceiptCoverageStatement -> FGSA.fgHead,          │
│                              │   │   │      │ FGSA.getHead, FGSA.headVote                       │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Clean.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ CleanTruncAt                 │ B │ K │ H+D  │ CleanTruncAt -> FGSA.controls, FGSA.fullTree      │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Healing.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ RowPermissionAt              │ B │ K │ H+D  │ RowPermissionAt -> FGSA.controls, FGSA.fullTree   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Outage.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ ExactProposalAt              │ B │ K │ H+D  │ ExactProposalAt -> FGSA.headVote                  │
│ LeaseOrFFrom                 │ B │ K │ H+D  │ LeaseOrFFrom -> FGSA.controls, FGSA.fullTree      │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Shared.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ HeadReachesLoAt              │ B │ K │ H    │ HeadReachesLoAt -> FGSA.controls, FGSA.eligible,  │
│                              │   │   │      │ FGSA.headInTree, FGSA.liveRoot                    │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/ChannelProps.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ RFrameExact                  │ B │ L │ H+D  │ RFrameExact -> FGSA.controls, FGSA.fullTree       │
│ RFrame                       │ B │ L │ H+D  │ RFrame -> FGSA.controls, FGSA.headSupport,        │
│                              │   │   │      │ FGSA.headVotes, FGSA.proposalRows,                │
│                              │   │   │      │ FGSA.proposalsAt, FGSA.voterBlocks                │
│ TGeom                        │ B │ K │ H+D  │ TGeom -> FGSA.fullTree                            │
│ OpeningCovered               │ B │ K │ H+D  │ OpeningCovered -> FGSA.fullTree                   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Channels.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ frameR                       │ B │ K │ H    │ frameR -> FGSA.controls                           │
│ proposerHead                 │ B │ K │ H    │ proposerHead -> FGSA.getHead,                     │
│                              │   │   │      │ FGSA.proposerSupport                              │
│ actionHead                   │ B │ K │ H+D  │ actionHead -> FGSA.fgHead                         │
│ actionTriple                 │ B │ K │ H+D  │ actionTriple -> FGSA.fgInputs                     │
│ headAtLabel                  │ B │ K │ H+D  │ headAtLabel -> FGSA.headVote                      │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/ComposeStmt.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ TStart                       │ B │ K │ H+D  │ TStart -> FGSA.controls, FGSA.fullTree,           │
│                              │   │   │      │ FGSA.liveRoot                                     │
│ TWalk                        │ B │ K │ H+D  │ TWalk -> FGSA.controls, FGSA.fullTree,            │
│                              │   │   │      │ FGSA.getHead, FGSA.liveRoot                       │
│ SettledPhaseFrame            │ B │ K │ H    │ SettledPhaseFrame -> FGSA.controls                │
│ RPhase                       │ B │ K │ H+D  │ RPhase -> FGSA.voterBlocks                        │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Reads.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ headAtIdx                    │ B │ K │ H+D  │ headAtIdx -> FGSA.headVote                        │
│ vHead                        │ B │ K │ H+D  │ vHead -> FGSA.headVote                            │
│ actionSourceFG               │ B │ K │ H+D  │ actionSourceFG -> FGSA.fgSource                   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

Indirect readers:

`AvailableChainFGSARun/Statements/Client.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ fgClientEvents               │ B │ K │ H+D  │ fgClientEvents -> fgClientEvent -> FGSA.fgInputs  │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSARun/Statements/Interface.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ fgsaOutputs                  │ A │ K │ D    │ fgsaOutputs -> fgsaIso -> actS -> FGSA.headVote   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Clean.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ CleanHistoryAt               │ B │ K │ H+D  │ CleanHistoryAt -> actionSourceFG -> FGSA.fgSource │
│ CleanCutClaim                │ B │ K │ H+D  │ CleanCutClaim -> CleanTruncAt -> FGSA.fullTree    │
│ CleanCutZeroClaim            │ B │ K │ H+D  │ CleanCutZeroClaim -> CleanTruncAt ->              │
│                              │   │   │      │ FGSA.fullTree                                     │
│ CleanHistoryClaim            │ B │ K │ H+D  │ CleanHistoryClaim -> CleanHistoryAt ->            │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ CleanPrefixTruncationClaim   │ B │ K │ H+D  │ CleanPrefixTruncationClaim -> CleanTruncAt ->     │
│                              │   │   │      │ FGSA.fullTree                                     │
│ CleanCutPosClaim             │ B │ N │ H+D  │ CleanCutPosClaim -> CleanTruncAt -> FGSA.fullTree │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Finality.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ FinalityKernelClaim_W        │ B │ K │ H+D  │ FinalityKernelClaim_W -> KernelPrem_W ->          │
│                              │   │   │      │ KernelPrem_W.mk -> CoreServices ->                │
│                              │   │   │      │ CoreServices.mk -> TWalk -> FGSA.liveRoot         │
│ KernelACSideClaim_W          │ B │ K │ H+D  │ KernelACSideClaim_W -> CoreServices ->            │
│                              │   │   │      │ CoreServices.mk -> TWalk -> FGSA.liveRoot         │
│ FinalityKernelJoinedClaim_W  │ B │ K │ H+D  │ FinalityKernelJoinedClaim_W -> KernelJoinedPrem   │
│                              │   │   │      │ -> KernelJoinedPrem.mk -> HealingInput ->         │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ TailKernelClaim_W            │ B │ K │ H+D  │ TailKernelClaim_W -> TailKernelPrem_W ->          │
│                              │   │   │      │ TailKernelPrem_W.mk -> HealingInput ->            │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ FirstFinalityConcl_W         │ B │ K │ H+D  │ FirstFinalityConcl_W -> HealingInput ->           │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ FirstFinalityRecFEClaim_W    │ B │ K │ H+D  │ FirstFinalityRecFEClaim_W -> FirstFinalityConcl_W │
│                              │   │   │      │ -> HealingInput -> HealingInput.mk -> HealT ->    │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ FirstFinalityRecF4Claim_W    │ B │ K │ H+D  │ FirstFinalityRecF4Claim_W -> FirstFinalityConcl_W │
│                              │   │   │      │ -> HealingInput -> HealingInput.mk -> HealT ->    │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ FinalityLivenessRecFEClaim_W │ B │ K │ H+D  │ FinalityLivenessRecFEClaim_W ->                   │
│                              │   │   │      │ FinalityLivenessPrem_W ->                         │
│                              │   │   │      │ FinalityLivenessPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ FinalityLivenessRecF4Claim_W │ B │ K │ H+D  │ FinalityLivenessRecF4Claim_W ->                   │
│                              │   │   │      │ FinalityLivenessPrem_W ->                         │
│                              │   │   │      │ FinalityLivenessPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ ProposalFinalRecFEClaim_W    │ B │ K │ H+D  │ ProposalFinalRecFEClaim_W -> ProposalFinalPrem_W  │
│                              │   │   │      │ -> ProposalFinalPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ ProposalFinalRecF4Claim_W    │ B │ K │ H+D  │ ProposalFinalRecF4Claim_W -> ProposalFinalPrem_W  │
│                              │   │   │      │ -> ProposalFinalPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ AboveFrontierRecFEClaim_W    │ B │ K │ H+D  │ AboveFrontierRecFEClaim_W -> AboveFrontierPrem_W  │
│                              │   │   │      │ -> AboveFrontierPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ AboveFrontierRecF4Claim_W    │ B │ K │ H+D  │ AboveFrontierRecF4Claim_W -> AboveFrontierPrem_W  │
│                              │   │   │      │ -> AboveFrontierPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ FinalityLivenessGSTClaim_W   │ B │ K │ H+D  │ FinalityLivenessGSTClaim_W -> HealingInput ->     │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ ProposalFinalGSTClaim_W      │ B │ K │ H+D  │ ProposalFinalGSTClaim_W -> HealingInput ->        │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ AboveFrontierGSTClaim_W      │ B │ K │ H+D  │ AboveFrontierGSTClaim_W -> HealingInput ->        │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Foundations.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ FGFoundationClaim            │ B │ N │ H+D  │ FGFoundationClaim -> FGFoundation ->              │
│                              │   │   │      │ FGFoundation.mk -> RFrameExact -> FGSA.fullTree   │
│ SrcFrameAboveClaim           │ B │ K │ H+D  │ SrcFrameAboveClaim -> SrcFrameAboveStmt ->        │
│                              │   │   │      │ SrcFrameAbove -> R_at -> frameR -> FGSA.controls  │
│ SourceDisciplineBaseAt       │ B │ K │ H+D  │ SourceDisciplineBaseAt -> actionSourceFG ->       │
│                              │   │   │      │ FGSA.fgSource                                     │
│ SourceDisciplineAt           │ B │ K │ H+D  │ SourceDisciplineAt -> SourceDisciplineBaseAt ->   │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ FrameAt                      │ B │ N │ H+D  │ FrameAt -> RFrame -> FGSA.voterBlocks             │
│ FrameClaim                   │ B │ N │ H+D  │ FrameClaim -> FrameAt -> RFrame ->                │
│                              │   │   │      │ FGSA.voterBlocks                                  │
│ SourceDisciplineBaseClaim    │ B │ K │ H+D  │ SourceDisciplineBaseClaim ->                      │
│                              │   │   │      │ SourceDisciplineBaseAt -> actionSourceFG ->       │
│                              │   │   │      │ FGSA.fgSource                                     │
│ SourceDisciplineClaim        │ B │ K │ H+D  │ SourceDisciplineClaim -> SourceDisciplineAt ->    │
│                              │   │   │      │ SourceDisciplineBaseAt -> actionSourceFG ->       │
│                              │   │   │      │ FGSA.fgSource                                     │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Healing.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ RowPermissionClaim           │ B │ K │ H+D  │ RowPermissionClaim -> RowPermissionAt ->          │
│                              │   │   │      │ FGSA.fullTree                                     │
│ HealingInputClaim            │ B │ K │ H+D  │ HealingInputClaim -> HealingInput ->              │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ HTimeConcl                   │ B │ K │ H+D  │ HTimeConcl -> HealingInput -> HealingInput.mk ->  │
│                              │   │   │      │ HealT -> HealT.mk -> TCarrier -> actionSourceFG   │
│                              │   │   │      │ -> FGSA.fgSource                                  │
│ HTimeClaim                   │ B │ K │ H+D  │ HTimeClaim -> HTimeConcl -> HealingInput ->       │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ ResetArrivalConcl            │ B │ K │ H+D  │ ResetArrivalConcl -> H0Reset -> H0Reset.mk ->     │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ ResetArrivalClaim            │ B │ K │ H+D  │ ResetArrivalClaim -> ResetArrivalConcl -> H0Reset │
│                              │   │   │      │ -> H0Reset.mk -> actionSourceFG -> FGSA.fgSource  │
│ RenewedPromotionConcl        │ B │ K │ H+D  │ RenewedPromotionConcl -> OpeningCovered ->        │
│                              │   │   │      │ FGSA.fullTree                                     │
│ RenewedPromotionClaim        │ B │ K │ H+D  │ RenewedPromotionClaim -> RenewedPromotionConcl -> │
│                              │   │   │      │ OpeningCovered -> FGSA.fullTree                   │
│ HTimeBestClaim               │ B │ K │ H+D  │ HTimeBestClaim -> HTimeBestConcl -> HealingInput  │
│                              │   │   │      │ -> HealingInput.mk -> HealT -> HealT.mk ->        │
│                              │   │   │      │ TCarrier -> actionSourceFG -> FGSA.fgSource       │
│ HTimeSearchClaim             │ B │ K │ H+D  │ HTimeSearchClaim -> HTimeBestConcl ->             │
│                              │   │   │      │ HealingInput -> HealingInput.mk -> HealT ->       │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Outage.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ ExactProposalClaim           │ B │ K │ H+D  │ ExactProposalClaim -> ExactProposalAt ->          │
│                              │   │   │      │ FGSA.headVote                                     │
│ DutiesExtendOn               │ B │ K │ H+D  │ DutiesExtendOn -> HeadTargetAtEmission ->         │
│                              │   │   │      │ FGSA.headVote                                     │
│ P1Concl                      │ B │ K │ H+D  │ P1Concl -> DutiesExtendOn -> HeadTargetAtEmission │
│                              │   │   │      │ -> FGSA.headVote                                  │
│ OutageCompatAt               │ B │ K │ H+D  │ OutageCompatAt -> LeaseOrFFrom -> FGSA.fullTree   │
│ OutageCompatClaim            │ B │ K │ H+D  │ OutageCompatClaim -> OutageCompatAt ->            │
│                              │   │   │      │ LeaseOrFFrom -> FGSA.fullTree                     │
│ FastP1Claim                  │ B │ K │ H+D  │ FastP1Claim -> P1Concl -> DutiesExtendOn ->       │
│                              │   │   │      │ HeadTargetAtEmission -> FGSA.headVote             │
│ SlowP1Claim                  │ B │ K │ H+D  │ SlowP1Claim -> OutageCompatAt -> LeaseOrFFrom ->  │
│                              │   │   │      │ FGSA.fullTree                                     │
│ AvailableGSTClaim            │ B │ K │ H+D  │ AvailableGSTClaim -> HealingInput ->              │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ AvailableGrowthGSTClaim      │ B │ K │ H+D  │ AvailableGrowthGSTClaim -> HealingInput ->        │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Claims/Shared.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ HeadReachesLoClaim           │ B │ K │ H    │ HeadReachesLoClaim -> HeadReachesLoAt ->          │
│                              │   │   │      │ FGSA.liveRoot                                     │
│ ReleaseAt                    │ B │ K │ H+D  │ ReleaseAt -> HeadTargetAtEmission ->              │
│                              │   │   │      │ FGSA.headVote                                     │
│ ReleaseClaim                 │ B │ K │ H+D  │ ReleaseClaim -> ReleaseAt -> HeadTargetAtEmission │
│                              │   │   │      │ -> FGSA.headVote                                  │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/FGSAClaims.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ FGSASafetyClaims             │ B │ N │ H+D  │ FGSASafetyClaims -> FGSASafetyClaims.mk ->        │
│                              │   │   │      │ CleanPrefixTruncationClaim -> CleanTruncAt ->     │
│                              │   │   │      │ FGSA.fullTree                                     │
│ FGSASafetyInterfaces         │ B │ N │ H+D  │ FGSASafetyInterfaces -> FGSASafetyInterfaces.mk   │
│                              │   │   │      │ -> CPPrefix -> R_at -> frameR -> FGSA.controls    │
│ FGSAClaims                   │ B │ K │ H+D  │ FGSAClaims -> FGSAClaims.mk -> ExactProposalClaim │
│                              │   │   │      │ -> ExactProposalAt -> FGSA.headVote               │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/ChannelProps.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ TSrc                         │ B │ K │ H+D  │ TSrc -> actionSource -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ TCompat                      │ B │ K │ H+D  │ TCompat -> actionSource -> actionSourceFG ->      │
│                              │   │   │      │ FGSA.fgSource                                     │
│ RQCOrigin                    │ B │ K │ H+D  │ RQCOrigin -> actionSourceFG -> FGSA.fgSource      │
│ SrcFrameAbove                │ B │ K │ H+D  │ SrcFrameAbove -> R_at -> frameR -> FGSA.controls  │
│ SrcFrame                     │ B │ K │ H+D  │ SrcFrame -> SrcFrameAbove -> R_at -> frameR ->    │
│                              │   │   │      │ FGSA.controls                                     │
│ SrcFrameAboveStmt            │ B │ K │ H+D  │ SrcFrameAboveStmt -> SrcFrameAbove -> R_at ->     │
│                              │   │   │      │ frameR -> FGSA.controls                           │
│ CPPrefix                     │ B │ K │ H+D  │ CPPrefix -> R_at -> frameR -> FGSA.controls       │
│ CPCompat                     │ B │ K │ H+D  │ CPCompat -> domainR -> frameR -> FGSA.controls    │
│ THigh                        │ B │ K │ H+D  │ THigh -> actionSourceFG -> FGSA.fgSource          │
│ TCarrier                     │ B │ K │ H+D  │ TCarrier -> actionSourceFG -> FGSA.fgSource       │
│ SourceBefore                 │ B │ K │ H+D  │ SourceBefore -> actionSourceFG -> FGSA.fgSource   │
│ Kept                         │ B │ K │ H+D  │ Kept -> R_at -> frameR -> FGSA.controls           │
│ KeepOrCause                  │ B │ K │ H+D  │ KeepOrCause -> SourceBefore -> actionSourceFG ->  │
│                              │   │   │      │ FGSA.fgSource                                     │
│ RExcl                        │ B │ K │ H+D  │ RExcl -> SourceBefore -> actionSourceFG ->        │
│                              │   │   │      │ FGSA.fgSource                                     │
│ RKeep                        │ B │ K │ H+D  │ RKeep -> R_at -> frameR -> FGSA.controls          │
│ RFProv                       │ B │ K │ H+D  │ RFProv -> SourceBefore -> actionSourceFG ->       │
│                              │   │   │      │ FGSA.fgSource                                     │
│ TDel                         │ B │ K │ H+D  │ TDel -> actionSourceFG -> FGSA.fgSource           │
│ TDelReset                    │ B │ K │ H+D  │ TDelReset -> H0 -> H0.mk -> H0Reset -> H0Reset.mk │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ ExactService                 │ B │ K │ H+D  │ ExactService -> headAtLabel -> FGSA.headVote      │
│ PhaseInterval                │ B │ K │ H+D  │ PhaseInterval -> R_at -> frameR -> FGSA.controls  │
│ Transfers                    │ B │ K │ H+D  │ Transfers -> headAtLabel -> FGSA.headVote         │
│ TPerm                        │ B │ K │ H+D  │ TPerm -> Transfers -> headAtLabel ->              │
│                              │   │   │      │ FGSA.headVote                                     │
│ RepairAfter                  │ B │ K │ H+D  │ RepairAfter -> ExactService -> headAtLabel ->     │
│                              │   │   │      │ FGSA.headVote                                     │
│ TRepair                      │ B │ K │ H+D  │ TRepair -> ExactService -> headAtLabel ->         │
│                              │   │   │      │ FGSA.headVote                                     │
│ OpeningEntry                 │ B │ K │ H+D  │ OpeningEntry -> actionSourceFG -> FGSA.fgSource   │
│ TCommon                      │ B │ K │ H+D  │ TCommon -> OpeningCovered -> FGSA.fullTree        │
│ TFrontier                    │ B │ K │ H+D  │ TFrontier -> OpeningCovered -> FGSA.fullTree      │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Channels.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ domainR                      │ B │ K │ H    │ domainR -> frameR -> FGSA.controls                │
│ jointSource                  │ B │ K │ H    │ jointSource -> domainR -> frameR -> FGSA.controls │
│ R_at                         │ B │ K │ H+D  │ R_at -> frameR -> FGSA.controls                   │
│ D_at                         │ B │ K │ H+D  │ D_at -> domainR -> frameR -> FGSA.controls        │
│ proposalHeadAt               │ B │ K │ H+D  │ proposalHeadAt -> proposerHead ->                 │
│                              │   │   │      │ FGSA.proposerSupport                              │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/ComposeStmt.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ FGFoundation                 │ B │ N │ H+D  │ FGFoundation -> FGFoundation.mk -> RFrameExact -> │
│                              │   │   │      │ FGSA.fullTree                                     │
│ CoreServices                 │ B │ K │ H+D  │ CoreServices -> CoreServices.mk -> TWalk ->       │
│                              │   │   │      │ FGSA.liveRoot                                     │
│ ResetArrivalStatement        │ B │ K │ H+D  │ ResetArrivalStatement -> H0Reset -> H0Reset.mk -> │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ ResetArrivalFullStatement    │ B │ K │ H+D  │ ResetArrivalFullStatement -> H0 -> H0.mk ->       │
│                              │   │   │      │ H0Reset -> H0Reset.mk -> actionSourceFG ->        │
│                              │   │   │      │ FGSA.fgSource                                     │
│ kernelStart                  │ B │ K │ H+D  │ kernelStart -> tstarOf -> H0 -> H0.mk -> H0Reset  │
│                              │   │   │      │ -> H0Reset.mk -> actionSourceFG -> FGSA.fgSource  │
│ KernelPrem_W                 │ B │ K │ H+D  │ KernelPrem_W -> KernelPrem_W.mk -> CoreServices   │
│                              │   │   │      │ -> CoreServices.mk -> TWalk -> FGSA.liveRoot      │
│ TailKernelPrem_W             │ B │ K │ H+D  │ TailKernelPrem_W -> TailKernelPrem_W.mk ->        │
│                              │   │   │      │ HealingInput -> HealingInput.mk -> HealT ->       │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ HealTContract                │ B │ K │ H+D  │ HealTContract -> HealTContract.mk -> TGeom ->     │
│                              │   │   │      │ FGSA.fullTree                                     │
│ ContestEvidence              │ B │ K │ H+D  │ ContestEvidence -> R_at -> frameR ->              │
│                              │   │   │      │ FGSA.controls                                     │
│ EffectiveEvent               │ B │ K │ H+D  │ EffectiveEvent -> ContestEvidence -> R_at ->      │
│                              │   │   │      │ frameR -> FGSA.controls                           │
│ AttemptPhaseAt               │ B │ K │ H+D  │ AttemptPhaseAt -> ContestEvidence -> R_at ->      │
│                              │   │   │      │ frameR -> FGSA.controls                           │
│ ServedFrontier               │ B │ K │ H+D  │ ServedFrontier -> ExactService -> headAtLabel ->  │
│                              │   │   │      │ FGSA.headVote                                     │
│ AttemptValid                 │ B │ K │ H+D  │ AttemptValid -> ServedFrontier -> ExactService -> │
│                              │   │   │      │ headAtLabel -> FGSA.headVote                      │
│ AttemptEndsBy                │ B │ K │ H+D  │ AttemptEndsBy -> EffectiveEvent ->                │
│                              │   │   │      │ ContestEvidence -> R_at -> frameR ->              │
│                              │   │   │      │ FGSA.controls                                     │
│ HealRContract                │ B │ K │ H+D  │ HealRContract -> HealRContract.mk -> RPhase ->    │
│                              │   │   │      │ FGSA.voterBlocks                                  │
│ ProgressAttemptStatement     │ B │ K │ H+D  │ ProgressAttemptStatement -> AttemptValid ->       │
│                              │   │   │      │ ServedFrontier -> ExactService -> headAtLabel ->  │
│                              │   │   │      │ FGSA.headVote                                     │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Healed.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ H2A                          │ B │ K │ H+D  │ H2A -> actionSourceFG -> FGSA.fgSource            │
│ H2Prime                      │ B │ K │ H+D  │ H2Prime -> headAtLabel -> FGSA.headVote           │
│ H3                           │ B │ K │ H+D  │ H3 -> ExactService -> headAtLabel ->              │
│                              │   │   │      │ FGSA.headVote                                     │
│ H5RawTransfer                │ B │ K │ H+D  │ H5RawTransfer -> headAtLabel -> FGSA.headVote     │
│ H6GateService                │ B │ K │ H+D  │ H6GateService -> headAtLabel -> FGSA.headVote     │
│ HealT                        │ B │ K │ H+D  │ HealT -> HealT.mk -> TCarrier -> actionSourceFG   │
│                              │   │   │      │ -> FGSA.fgSource                                  │
│ HealAC                       │ B │ K │ H+D  │ HealAC -> HealAC.mk -> H2Prime -> headAtLabel ->  │
│                              │   │   │      │ FGSA.headVote                                     │
│ HealingInput                 │ B │ K │ H+D  │ HealingInput -> HealingInput.mk -> HealT ->       │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ HTimeStatement               │ B │ K │ H+D  │ HTimeStatement -> HealingInput -> HealingInput.mk │
│                              │   │   │      │ -> HealT -> HealT.mk -> TCarrier ->               │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/HealedBest.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ HTimeBestConcl               │ B │ K │ H+D  │ HTimeBestConcl -> HealingInput -> HealingInput.mk │
│                              │   │   │      │ -> HealT -> HealT.mk -> TCarrier ->               │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Packages/Finality.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ FinalityLivenessPrem_W       │ B │ K │ H+D  │ FinalityLivenessPrem_W ->                         │
│                              │   │   │      │ FinalityLivenessPrem_W.mk -> HealingInput ->      │
│                              │   │   │      │ HealingInput.mk -> HealT -> HealT.mk -> TCarrier  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ ProposalFinalPrem_W          │ B │ K │ H+D  │ ProposalFinalPrem_W -> ProposalFinalPrem_W.mk ->  │
│                              │   │   │      │ HealingInput -> HealingInput.mk -> HealT ->       │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ AboveFrontierPrem_W          │ B │ K │ H+D  │ AboveFrontierPrem_W -> AboveFrontierPrem_W.mk ->  │
│                              │   │   │      │ HealingInput -> HealingInput.mk -> HealT ->       │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Packages/Healing.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ HealingWitnessPrem           │ B │ K │ H+D  │ HealingWitnessPrem -> HealingWitnessPrem.mk -> H0 │
│                              │   │   │      │ -> H0.mk -> H0Reset -> H0Reset.mk ->              │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ KernelJoinedPrem             │ B │ K │ H+D  │ KernelJoinedPrem -> KernelJoinedPrem.mk ->        │
│                              │   │   │      │ HealingInput -> HealingInput.mk -> HealT ->       │
│                              │   │   │      │ HealT.mk -> TCarrier -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ HealingAttemptPrem           │ B │ K │ H+D  │ HealingAttemptPrem -> HealingAttemptPrem.mk ->    │
│                              │   │   │      │ AttemptValid -> ServedFrontier -> ExactService -> │
│                              │   │   │      │ headAtLabel -> FGSA.headVote                      │
│ HealingInputPrem             │ B │ K │ H+D  │ HealingInputPrem -> HealingInputPrem.mk ->        │
│                              │   │   │      │ HealingWitnessPrem -> HealingWitnessPrem.mk -> H0 │
│                              │   │   │      │ -> H0.mk -> H0Reset -> H0Reset.mk ->              │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Phases.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ FreshFinalityRows_W          │ B │ K │ H+D  │ FreshFinalityRows_W -> actionSourceFG ->          │
│                              │   │   │      │ FGSA.fgSource                                     │
│ TerminalCarriagePrem_W       │ B │ K │ H+D  │ TerminalCarriagePrem_W ->                         │
│                              │   │   │      │ TerminalCarriagePrem_W.mk -> FreshFinalityRows_W  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ TerminalCarriage_W           │ B │ K │ H+D  │ TerminalCarriage_W -> TerminalCarriagePrem_W ->   │
│                              │   │   │      │ TerminalCarriagePrem_W.mk -> FreshFinalityRows_W  │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Reads.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ actionSource                 │ B │ K │ H+D  │ actionSource -> actionSourceFG -> FGSA.fgSource   │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAClaims/Statements/Witness.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ H0Reset                      │ B │ K │ H+D  │ H0Reset -> H0Reset.mk -> actionSourceFG ->        │
│                              │   │   │      │ FGSA.fgSource                                     │
│ H0                           │ B │ K │ H+D  │ H0 -> H0.mk -> H0Reset -> H0Reset.mk ->           │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ tstarOf                      │ B │ K │ H+D  │ tstarOf -> H0 -> H0.mk -> H0Reset -> H0Reset.mk   │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

The compiled scan also checks Proofs Statements outside the API census.
The following 53 source entries (including equations) keep their text (K) and
follow canonical readers. They have B meaning attribution by the same rule;
they are not new rows in the 369-source API census. Their deep causes are H/D
as defined above. Each structure cause includes its constructor and all fields.
In particular, the WC duty view, live frame, and proposal pivot acquire the
new meaning through canonical voter/tree/live-root readers. Clean statement
arguments still name canonical `FGFoundation`, whose frame field is retargeted.
No new copy or statement import is needed for these consumers.

`AvailableChainFGSAProofs/Statements/WeakContinuation.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ WCHeadRead                   │ B │ K │ H+D  │ WCHeadRead -> WCHeadRead.mk -> headAtIdx ->       │
│                              │   │   │      │ FGSA.headVote                                     │
│ WCTargetOrigin               │ B │ K │ H+D  │ WCTargetOrigin -> WCTargetOrigin.mk ->            │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ WCFiniteFacts                │ B │ K │ H+D  │ WCFiniteFacts -> WCFiniteFacts.mk ->              │
│                              │   │   │      │ WCTargetOrigin -> WCTargetOrigin.mk ->            │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ WCSeed                       │ B │ K │ H+D  │ WCSeed -> WCSeed.mk -> actionSourceFG ->          │
│                              │   │   │      │ FGSA.fgSource                                     │
│ WCInv                        │ B │ K │ H+D  │ WCInv -> WCInv.mk -> actionSourceFG ->            │
│                              │   │   │      │ FGSA.fgSource                                     │
│ WCUsableHighSourcesBelow     │ B │ K │ H+D  │ WCUsableHighSourcesBelow ->                       │
│                              │   │   │      │ WCUsableHighSourcesBelow.mk -> actionSourceFG ->  │
│                              │   │   │      │ FGSA.fgSource                                     │
│ WCFrameBelow                 │ B │ K │ H    │ WCFrameBelow -> WCFrameBelow.mk -> frameR ->      │
│                              │   │   │      │ FGSA.controls                                     │
│ WCDutyView                   │ B │ K │ H    │ WCDutyView -> WCDutyView.mk -> FGSA.voterBlocks   │
│ WCFrameLiveBelow             │ B │ K │ H    │ WCFrameLiveBelow -> WCFrameLiveBelow.mk ->        │
│                              │   │   │      │ FGSA.liveRoot                                     │
│ WCFramePathBelow             │ B │ K │ H    │ WCFramePathBelow -> WCFramePathBelow.mk -> frameR │
│                              │   │   │      │ -> FGSA.controls                                  │
│ WCProposalPivot              │ B │ K │ H+D  │ WCProposalPivot -> WCProposalPivot.mk ->          │
│                              │   │   │      │ FGSA.liveRoot                                     │
│ WCFinalityTargetEarlier      │ B │ K │ H+D  │ WCFinalityTargetEarlier ->                        │
│                              │   │   │      │ WCFinalityTargetEarlier.mk -> actionSourceFG ->   │
│                              │   │   │      │ FGSA.fgSource                                     │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

`AvailableChainFGSAProofs/Statements/CleanInvariant.lean`:

```text
┌──────────────────────────────┬───┬───┬──────┬───────────────────────────────────────────────────┐
│ Consumer                     │ C │ Do │ Deep │ Dependency path (current closure)                 │
├──────────────────────────────┼───┼───┼──────┼───────────────────────────────────────────────────┤
│ CleanHist                    │ B │ K │ H+D  │ CleanHist -> CleanHist.mk -> headAtIdx ->         │
│                              │   │   │      │ FGSA.headVote                                     │
│ CleanRowSources              │ B │ K │ H+D  │ CleanRowSources -> actionSourceFG ->              │
│                              │   │   │      │ FGSA.fgSource                                     │
│ CleanRowSources_def          │ B │ K │ H+D  │ CleanRowSources_def -> actionSourceFG ->          │
│                              │   │   │      │ FGSA.fgSource                                     │
│ CleanCertSources             │ B │ K │ H+D  │ CleanCertSources -> actionSourceFG ->             │
│                              │   │   │      │ FGSA.fgSource                                     │
│ CleanCertSources_def         │ B │ K │ H+D  │ CleanCertSources_def -> actionSourceFG ->         │
│                              │   │   │      │ FGSA.fgSource                                     │
│ CleanState                   │ B │ K │ H+D  │ CleanState -> CleanState.mk -> FGSA.controls      │
│ FGPart                       │ B │ K │ H+D  │ FGPart -> FGPart.mk -> CleanCertSources ->        │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ GT                           │ B │ K │ H+D  │ GT -> CleanHist -> CleanHist.mk -> headAtIdx ->   │
│                              │   │   │      │ FGSA.headVote                                     │
│ GT_def                       │ B │ K │ H+D  │ GT_def -> CleanHist -> CleanHist.mk -> headAtIdx  │
│                              │   │   │      │ -> FGSA.headVote                                  │
│ GR                           │ B │ K │ H+D  │ GR -> FGPart -> FGPart.mk -> CleanCertSources ->  │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ GR_def                       │ B │ K │ H+D  │ GR_def -> FGPart -> FGPart.mk -> CleanCertSources │
│                              │   │   │      │ -> actionSourceFG -> FGSA.fgSource                │
│ CleanGateOutputStmt          │ B │ K │ H+D  │ CleanGateOutputStmt -> FGFoundation ->            │
│                              │   │   │      │ FGFoundation.mk -> RFrameExact -> FGSA.fullTree   │
│ CleanGateOutputStmt_def      │ B │ K │ H+D  │ CleanGateOutputStmt_def -> FGFoundation ->        │
│                              │   │   │      │ FGFoundation.mk -> RFrameExact -> FGSA.fullTree   │
│ CleanActionSourcesStmt       │ B │ K │ H+D  │ CleanActionSourcesStmt -> actionSource ->         │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ CleanActionSourcesStmt_def   │ B │ K │ H+D  │ CleanActionSourcesStmt_def -> actionSource ->     │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ CleanFrameStmt               │ B │ K │ H+D  │ CleanFrameStmt -> FGSA.fullTree                   │
│ CleanFrameStmt_def           │ B │ K │ H+D  │ CleanFrameStmt_def -> FGSA.controls               │
│ CleanAGStmt                  │ B │ K │ H+D  │ CleanAGStmt -> FGFoundation -> FGFoundation.mk -> │
│                              │   │   │      │ RFrameExact -> FGSA.fullTree                      │
│ CleanAGStmt_def              │ B │ K │ H+D  │ CleanAGStmt_def -> FGFoundation ->                │
│                              │   │   │      │ FGFoundation.mk -> RFrameExact -> FGSA.fullTree   │
│ CleanStateStep               │ B │ K │ H+D  │ CleanStateStep -> CleanState -> CleanState.mk ->  │
│                              │   │   │      │ FGSA.controls                                     │
│ CleanStateStep_def           │ B │ K │ H+D  │ CleanStateStep_def -> CleanState -> CleanState.mk │
│                              │   │   │      │ -> FGSA.controls                                  │
│ CleanHistStep                │ B │ K │ H+D  │ CleanHistStep -> CleanState -> CleanState.mk ->   │
│                              │   │   │      │ FGSA.controls                                     │
│ CleanHistStep_def            │ B │ K │ H+D  │ CleanHistStep_def -> CleanState -> CleanState.mk  │
│                              │   │   │      │ -> FGSA.controls                                  │
│ CleanDeliveryStateStep       │ B │ K │ H+D  │ CleanDeliveryStateStep -> CleanStateStep ->       │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanDeliveryStateStep_def   │ B │ K │ H+D  │ CleanDeliveryStateStep_def -> CleanStateStep ->   │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanDeliveryHistStep        │ B │ K │ H+D  │ CleanDeliveryHistStep -> CleanHistStep ->         │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanDeliveryHistStep_def    │ B │ K │ H+D  │ CleanDeliveryHistStep_def -> CleanHistStep ->     │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanBlockStateStep          │ B │ K │ H+D  │ CleanBlockStateStep -> CleanStateStep ->          │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanBlockStateStep_def      │ B │ K │ H+D  │ CleanBlockStateStep_def -> CleanStateStep ->      │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanBlockHistStep           │ B │ K │ H+D  │ CleanBlockHistStep -> CleanHistStep -> CleanState │
│                              │   │   │      │ -> CleanState.mk -> FGSA.controls                 │
│ CleanBlockHistStep_def       │ B │ K │ H+D  │ CleanBlockHistStep_def -> CleanHistStep ->        │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanNoGateStateStep         │ B │ K │ H+D  │ CleanNoGateStateStep -> CleanStateStep ->         │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanNoGateStateStep_def     │ B │ K │ H+D  │ CleanNoGateStateStep_def -> CleanStateStep ->     │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanNoGateHistStep          │ B │ K │ H+D  │ CleanNoGateHistStep -> CleanHistStep ->           │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanNoGateHistStep_def      │ B │ K │ H+D  │ CleanNoGateHistStep_def -> CleanHistStep ->       │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanGateStateStep           │ B │ K │ H+D  │ CleanGateStateStep -> CleanStateStep ->           │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanGateStateStep_def       │ B │ K │ H+D  │ CleanGateStateStep_def -> CleanStateStep ->       │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanGateHistStep            │ B │ K │ H+D  │ CleanGateHistStep -> CleanHistStep -> CleanState  │
│                              │   │   │      │ -> CleanState.mk -> FGSA.controls                 │
│ CleanGateHistStep_def        │ B │ K │ H+D  │ CleanGateHistStep_def -> CleanHistStep ->         │
│                              │   │   │      │ CleanState -> CleanState.mk -> FGSA.controls      │
│ CleanActionStep              │ B │ K │ H+D  │ CleanActionStep -> CleanRowSources ->             │
│                              │   │   │      │ actionSourceFG -> FGSA.fgSource                   │
│ CleanActionStep_def          │ B │ K │ H+D  │ CleanActionStep_def -> CleanState ->              │
│                              │   │   │      │ CleanState.mk -> FGSA.controls                    │
└──────────────────────────────┴───┴───┴──────┴───────────────────────────────────────────────────┘
```

Explicit SWITCH text changes and canonical deep exceptions:

- `RFrameExact`, `RFrame`, and both `_def` entries: L; keep their source text.
  They have census B and H+D attribution. Active `FrameAt` and foundation
  fields stop using these legacy exact-frame predicates.
- `FGFoundation.frame` becomes `RFrameExactNext`; `FGFoundationClaim` names
  `FGFoundationNext`. `FrameAt` uses `RFrameExactNext` and `RFrameNext`;
  `FrameClaim` follows it. These are N/B changes to the final frame surface.
- `FGSASafetyClaims.frame` becomes `FrameClaimNext`;
  `FGSASafetyInterfaces.fgFoundation` becomes `FGFoundationClaimNext`.
  `FGSAClaims` keeps its text and inherits the changed safety parent.
- `CleanCutPosClaim` changes only its foundation antecedent to
  `FGFoundationNext`. Its conclusion follows canonical controls through
  `CleanTruncAt`. Other Clean text stays fixed.
- `CoreServices` keeps its text: `.start -> TStart -> liveRoot/controls/fullTree`,
  `.walk -> TWalk -> getHead/liveRoot/controls/fullTree`, and `.vote -> TVote ->
  FullVoteService -> Run.emits`. It has B and H+D attribution. Its complete
  carrier, constructor, and projections have the same cause. No Next aggregate
  copy is needed. `KernelACSideClaim_W`, `TVote`, and `FullVoteService` keep
  their text and follow that path.
- `CPCompat` keeps its text: `R_at -> frameR -> controls` and
  `domainR -> frameR -> controls`; its contest/root/domain clauses acquire the
  new guarded meaning. The table gives the domain path; its census class is B.
- Every aggregate cause applies to the structure, constructor, and all
  projections, including projections with an unchanged displayed field type.
  WP00c must measure this full closure and the 154 reader paths above, plus
  roots with only a changed run dependency. Source class and deep change are
  separate records.

Registration: the facade imports `ComposeNext`; Claims imports remain layered.
The statement order puts `FrameNext` before `ComposeStmt`, then `ComposeNext`.
The audit inventory moves `FrameAtNext` to the lower module and the foundation
family to `ComposeNext`; it adds `WalkBatchNext`. Expected names and axiom
commands include that helper. The new module has an exact WP00b owner path.
The lower imports name its
actual state, channel, and batch dependencies directly.
`ComposeNext` keeps its `ComposeStmt` import with
`shake: keep (foundation layer)`: the review requires this module above
`ComposeStmt`, even though those field predicates have lower declaration homes.
No V2Manifest or deep-checker code is changed.

Manifest: the tool generated 1,242 entries in 57 modules. All 1,215 entries at
`cd736e86` keep their kind and hash. The package adds 27 entries in three
modules. Compared with the review tip, only the new `TWalkNext` hash changes: it now
names the identical lower batch helper. `FrameAtNext` keeps its original binder
order and hash after relocation; `FrameClaimNext` also keeps its hash.
The foundation family keeps its kind/hash while its owner module
moves. The tool's header reset was followed by restoration of the existing
exception prose. Frozen bytes, SHA, and existing allow lines stay unchanged.
No added entry needs an allow line.

Review-fix checks and results follow. Earlier validation is superseded by these
runs; the FULL landing gate and compiled Claims negative controls remain outside
this job's reported results.

- Planned import graph: PASS on 5,314 compiled modules and 27,007 direct edges.
  Both lower closures exclude `ComposeStmt` (2,474 and 2,430 modules).
  All seven planned edges have no reverse path, checked after each insertion.
- Exact precheck command, with this worktree and `91735679`: PASS;
  `/tmp/s0f-fix-precheck-final.log` prints `PRECHECK PASS`.
- `LEAN_SLOTS=2 lake build --wfail` for `Statements.FrameNext`,
  `Statements.ComposeNext`, `Claims.FrameNext`, `Tests.Axioms`, and the Claims
  facade: PASS (1,113 jobs); `/tmp/s0f-fix-build-final.log`.
- Compiled signature checks: PASS for all 14 Next source declarations.
  `WalkBatchNext = WalkBatch` is proved by `rfl` in the temporary check.
  `FrameAtNext` keeps the original instance/codec binder order.
  `/tmp/s0f-fix-signatures.log` and `/tmp/s0f-fix-copy-check-final.log`.
- Prior manifest preservation: PASS; all 1,215 kind/hash pairs match `cd736e86`.
- Owners: PASS (746 exact paths; 72 new; 99 proof tests).
- Census recount: PASS (369 sources; 876 entries; 799 frozen; 77 later).
- Audit registration owners: PASS; all 27 new/moved entries match their compiled
  modules and the exact inventory. Source name/layer guards pass in precheck.
- Source equality for the batch copy, lines of at most 100 characters in changed
  modules/report, and `git diff --check`: PASS.
- `LEAN_SLOTS=2 bash scripts/check-fgsa-manifest.sh`: PASS; all 1,242 entries
  match, EOF/copy/hash controls pass, and C1–C13 pass.
  `/tmp/s0f-fix-manifest-check-complete.log`.
- Compiled Claims axiom/import/used-constant audit: PASS (rc 0), recorded in
  `/tmp/s0f-fix-claims-audit-complete.log`. Its later lease step overlapped the
  final Axioms rebuild and stopped on a transient missing object file.
- After the final build, resume the original guard at lease with no source
  changes: lease, equation, unused-import, and W1 checks all PASS. W1 uses only
  standard axioms. `/tmp/s0f-fix-claims-resume.log`.
  The temporary resume script copies the repository guard and skips only the
  already-passing axiom call. No repository auditor or baseline is weakened.
  This is separate validation of all guard steps, not a one-pass guard result.
- New-module unused-import check: PASS; three modules, zero suggestions.
  `/tmp/s0f-fix-shake-final.log`. The foundation layer import is retained by the
  explicit policy note; the lower module imports its actual dependencies.
- Final import graph log: `/tmp/s0f-fix-graph-final.log`. All seven reverse-path
  checks are false; the final planned graph is acyclic.

Not run: the FULL landing gate, compiled Claims negative controls (`NEG=0`),
and WP00c's future measured frame/deep baseline checks. No review, agent,
Codex/Claude child process, push, or rebase was started.

Files changed by this review fix:

- `AvailableChainFGSAClaims/Statements/FrameNext.lean`
- `AvailableChainFGSAClaims/Statements/ComposeNext.lean` (new upper module)
- `AvailableChainFGSAClaims/Claims/FrameNext.lean`
- `AvailableChainFGSAClaims.lean`
- `AvailableChainFGSAClaims/Tests/Axioms.lean`
- `docs/FGSA-API.md`
- `docs/FGSA-PORT-OWNERS.json`
- `docs/reports/fgsa-port-s0f00b.md`
- `scripts/check-fgsa-claims.sh`
- `scripts/fgsa-claims-expected.txt`
- `scripts/proof-audit-coverage.txt`

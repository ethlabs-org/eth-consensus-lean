import Lean.CoreM
import Lean.Util.CollectAxioms
open Lean

/-! FG axiom check. Every compiled constant of the modules of
`AvailableChainSimplexFG` and `AvailableChainKitFG` may depend only on
`propext`, `Classical.choice` and `Quot.sound`. This rejects `sorryAx`, the
auxiliary `_native` axiom of `native_decide` or `decide +native` (for example
`t._native.native_decide.ax_1_1` on v4.30.0-rc2; older toolchains:
`Lean.ofReduceBool`) and project axioms.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainSimplexFG
AvailableChainKitFG` first, or use `bash scripts/check-fg.sh`, which builds and
then runs every FG check.

It also checks the import closure of the two FG roots (the compiled import
data): the root of every module in it is on `closureRoots` (Lean, its
standard libraries, Mathlib and its dependencies, `AvailableChainModel` and the
two FG libraries, and `AvailableChainGeneric` for the Pure weights bridge).
So no FG module, `AvailableChainKitFG/Pins.lean` included,
imports `AvailableChainFGSA` or another library above the FG libraries.

Run: `lake env lean --run scripts/CheckFGAxioms.lean [--root M] [--expect N …]`.
`--root M` imports one more root module (negative controls only).
With `--expect`, each named constant must be a checked constant (a short
name matches a qualified one by suffix).
Exit codes: 0 clean; 1 a bad axiom or a module outside `closureRoots`; 2 nothing found, a usage error (an
unknown argument, or `--expect` without a name), or an expected name missing.
Each missing expected name forces exit 2, also after a bad axiom or after
other expected names that are present. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def inFG (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      (`AvailableChainSimplexFG).isPrefixOf m || (`AvailableChainKitFG).isPrefixOf m
  | none => false

/-- The axioms `n` transitively depends on. Uses the `Core.CoreM.toIO'`
pattern of `scripts/Registry.lean`: the toolchain's `CollectAxioms` API is
called through `Lean.Util.CollectAxioms`'s `collectAxioms` in `CoreM`. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFGAxioms", fileMap := .ofString "" } { env := env }

/-- The libraries that the import closure of the two FG roots may contain
(module roots; a literal list, fail closed). -/
def closureRoots : List Name :=
  [`Init, `Lean, `Std, `Lake, `Batteries, `Mathlib, `ImportGraph, `Aesop, `Qq,
    `Plausible, `LeanSearchClient, `ProofWidgets, `AvailableChainModel,
    `AvailableChainSimplexFG, `AvailableChainKitFG, `AvailableChainGeneric]

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

def composeSources (scope : String) : IO (Array Name) := do
  return (← layoutOutput #["modules", scope]).map String.toName

def pureMain (args : List String) (useAxiomData := false) : IO UInt32 := do
  let usage := "USAGE: lake env lean --run scripts/CheckFGAxioms.lean [--root M] [--expect N …]"
  let (extra, args) := match args with
    | "--root" :: m :: r => (#[m.toName], r)
    | _ => (#[], args)
  -- Reject an unknown argument: a typo must not skip the `--expect` test.
  unless args.isEmpty || (args.head? == some "--expect" && args.length ≥ 2) do
    IO.eprintln usage
    return 2
  let expected := args.drop 1
  initSearchPath (← findSysroot)
  if useAxiomData then unsafe enableInitializersExecution
  -- Match the generated inventory, including modules absent from the facades.
  let sources := (← composeSources "AvailableChainSimplexFG") ++
    (← composeSources "AvailableChainKitFG")
  let env ← importModules ((sources ++ extra).map ({ module := · })) {}
    (loadExts := useAxiomData) (level := .private)
  let mut badClosure := false
  for m in env.header.moduleNames do
    if extra.contains m then continue
    unless closureRoots.contains m.getRoot do
      IO.println s!"FORBIDDEN LIBRARY IN THE FG IMPORT CLOSURE: {m}"
      badClosure := true
  let cs := env.constants.toList.filter (fun (n, _) => inFG env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let thms := cs.filterMap fun (n, ci) => if ci matches .thmInfo _ then some n else none
  let mut badAxioms := false
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
  -- Count the missing names; no later name can clear an earlier miss.
  let mut missing := 0
  for s in expected do
    unless cs.any (fun (n, _) => s.toName.isSuffixOf n) do
      IO.println s!"NOT CHECKED: {s}"
      missing := missing + 1
  IO.println s!"checked {cs.length} constants, {thms.length} theorems"
  if missing > 0 then
    IO.println s!"{missing} expected names not checked"
    return 2
  return if badAxioms || badClosure then 1 else 0

-- Keep the pure audit in its own environment. Compose has a separate closure.
def composeStatements (m : Name) : Bool :=
  (`AvailableChainFGCompose.Statements).isPrefixOf m

def composeImportAllowed (m dep : Name) : Bool :=
  let under (p : Name) := p.isPrefixOf dep
  let foundation := [`Init, `Lean, `Std, `Mathlib].any under
  let ownStatements := under `AvailableChainFGCompose.Statements
  let ownProofs := under `AvailableChainFGCompose.Proofs
  let base := foundation || under `AvailableChainModel.Objects ||
    [`AvailableChainEngineV2.Engine, `AvailableChainEngineV2.Conditions,
     `AvailableChainEngineV2.Laws.Duty, `AvailableChainGeneric.Statements.V2.Duty].any under ||
    (under `AvailableChainGeneric.Statements.Pure &&
      !under `AvailableChainGeneric.Statements.Pure.Walk) ||
    [`AvailableChainSimplexFG.Store, `AvailableChainKitFG.HeightLawsDef].contains dep
  let safety := [(`AvailableChainFGCompose.Statements.SafetyReads, `AvailableChainKitFG.ClientOnce),
    (`AvailableChainFGCompose.Statements.FinalityKernel,
     `AvailableChainKitFG.WindowEntriesDef),
    (`AvailableChainFGCompose.Statements.FinalityRows,
     `AvailableChainKitFG.WindowViewsDef),
    (`AvailableChainFGCompose.Statements.ExecutionAcceptance,
     `AvailableChainKitFG.WindowViewsDef),
    (`AvailableChainFGCompose.Statements.FinalityReceipts,
     `AvailableChainSimplexFG.WindowStore),
    (`AvailableChainFGCompose.Statements.FinalityRecords,
     `AvailableChainKitFG.ProvenanceCoreDef),
    (`AvailableChainFGCompose.Statements.FinalityHistory, `AvailableChainKitFG.WindowEntriesDef),
    (`AvailableChainFGCompose.Statements.Observations, `AvailableChainKitFG.TreeFrameDef),
    (`AvailableChainFGCompose.Statements.Observations, `AvailableChainKitFG.CertificateCoreDef),
    (`AvailableChainFGCompose.Statements.SafetyReads, `AvailableChainSimplexFG.Evidence),
    (`AvailableChainFGCompose.Statements.SafetyReads, `AvailableChainKitFG.CertificateCoreDef),
    (`AvailableChainFGCompose.Statements.SafetyReads, `AvailableChainGeneric.Statements.V2.Duty.Slashing),
    (`AvailableChainFGCompose.Statements.SafetyStore, `AvailableChainKitFG.StoreSafetyDef),
    (`AvailableChainFGCompose.Statements.SafetyClient, `AvailableChainGeneric.Statements.Pure.Quorum),
       (`AvailableChainFGCompose.Statements.FinalityHistory,
        `AvailableChainKitFG.WindowEntriesDef)].contains (m, dep)
  if dep == `Init then true
  else if m == `AvailableChainFGCompose then
    [`AvailableChainFGCompose.Statements.EventReads, `AvailableChainFGCompose.Statements.CoreReads,
     `AvailableChainFGCompose.Statements.ExecutionObs,
     `AvailableChainFGCompose.Statements.ExecutionBridges,
     `AvailableChainFGCompose.Statements.ExecutionRecords,
     `AvailableChainFGCompose.Proofs.ExecutionObs,
     `AvailableChainFGCompose.Proofs.ExecutionHistory,
     `AvailableChainFGCompose.Statements.HolderClient,
     `AvailableChainFGCompose.Proofs.HolderClient,
     `AvailableChainFGCompose.Proofs.OrdinaryHolderClient,
     `AvailableChainFGCompose.Statements.FrontierSearch,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchBudget,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop,
     `AvailableChainFGCompose.Statements.FrontierMaturity,
     `AvailableChainFGCompose.Proofs.Healing.PromotionSource,
     `AvailableChainFGCompose.Proofs.Healing.PromotionAge,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchAge,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchHG2a,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchTail,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchRise,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchCompose,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchTasks,
     `AvailableChainFGCompose.Proofs.Healing.FrontierSearchFull,
     `AvailableChainFGCompose.Proofs.Healing.Reset,
     `AvailableChainFGCompose.Statements.Attempt,
     `AvailableChainFGCompose.Proofs.Healing.AttemptStop,
     `AvailableChainFGCompose.Proofs.Healing.AttemptSettle,
     `AvailableChainFGCompose.Proofs.Healing.AttemptRows,
     `AvailableChainFGCompose.Proofs.Healing.Attempt,
     `AvailableChainFGCompose.Statements.Phase,
     `AvailableChainFGCompose.Statements.PhaseReceipts,
     `AvailableChainFGCompose.Proofs.Healing.PhaseFrame,
     `AvailableChainFGCompose.Proofs.Healing.PhaseOrder,
     `AvailableChainFGCompose.Proofs.Healing.PhaseSettle,
     `AvailableChainFGCompose.Statements.FinalityRows,
     `AvailableChainFGCompose.Proofs.Finality.Rows,
     `AvailableChainFGCompose.Proofs.Finality.RowsRecords,
     `AvailableChainFGCompose.Proofs.Finality.RowsPrem,
     `AvailableChainFGCompose.Proofs.Finality.Batch,
     `AvailableChainFGCompose.Proofs.Finality.Carry,
     `AvailableChainFGCompose.Proofs.Finality.RestoreReads,
     `AvailableChainFGCompose.Proofs.Finality.Receipt,
     `AvailableChainFGCompose.Proofs.Finality.Accept,
     `AvailableChainFGCompose.Proofs.Finality.Kernel,
     `AvailableChainFGCompose.Proofs.Finality.Joined,
     `AvailableChainFGCompose.Proofs.Finality.Forward,
     `AvailableChainFGCompose.Proofs.Finality.Local,
     `AvailableChainFGCompose.Statements.SafetyOrigin,
     `AvailableChainFGCompose.Proofs.SafetyOrigin,
     `AvailableChainFGCompose.Statements.ResetCut,
     `AvailableChainFGCompose.Statements.FinalityKernel,
     `AvailableChainFGCompose.Proofs.Finality.MiddleSupport,
     `AvailableChainFGCompose.Proofs.Finality.Middle,
     `AvailableChainFGCompose.Statements.FinalityRecords,
     `AvailableChainFGCompose.Proofs.Finality.RecordInv,
     `AvailableChainFGCompose.Statements.FinalityHistory,
     `AvailableChainFGCompose.Proofs.Finality.History,
     `AvailableChainFGCompose.Proofs.Healing.ResetCut,
     `AvailableChainFGCompose.Statements.ResetHistory,
     `AvailableChainFGCompose.Statements.Service,
     `AvailableChainFGCompose.Statements.Bounds,
     `AvailableChainFGCompose.Statements.Finality,
     `AvailableChainFGCompose.Statements.FinalityReceipts,
     `AvailableChainFGCompose.Proofs.ServiceTransport,
     `AvailableChainFGCompose.Statements.Dependency,
     `AvailableChainFGCompose.Statements.DependencyTrace,
     `AvailableChainFGCompose.Proofs.Dependency,
     `AvailableChainFGCompose.Statements.HistoricalReads,
     `AvailableChainFGCompose.Proofs.HistoricalReads,
     `AvailableChainFGCompose.Statements.Promotion,
     `AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic,
     `AvailableChainFGCompose.Proofs.Healing.CommonEntry,
     `AvailableChainFGCompose.Proofs.Healing.Promotion,
     `AvailableChainFGCompose.Proofs.Healing.PromotionRows,
     `AvailableChainFGCompose.Statements.HistoricalReads,
     `AvailableChainFGCompose.Proofs.HistoricalReads,
     `AvailableChainFGCompose.Statements.RowPermission,
     `AvailableChainFGCompose.Proofs.RowPermission,
     `AvailableChainFGCompose.Statements.Observations,
     `AvailableChainFGCompose.Statements.Selection,
     `AvailableChainFGCompose.Statements.Timing,
     `AvailableChainFGCompose.Statements.Channels,
     `AvailableChainFGCompose.Statements.ChannelLaws,
     `AvailableChainFGCompose.Proofs.ObservationTransport,
     `AvailableChainFGCompose.Proofs.Timing,
     `AvailableChainFGCompose.Proofs.SourceHead,
     `AvailableChainFGCompose.Statements.Restart, `AvailableChainFGCompose.Proofs.Restart,
     `AvailableChainFGCompose.Statements.SafetyReads, `AvailableChainFGCompose.Statements.SafetyStore,
     `AvailableChainFGCompose.Statements.SafetyClient, `AvailableChainFGCompose.Statements.SafetyClaims,
     `AvailableChainFGCompose.Proofs.SafetyStore,
     `AvailableChainFGCompose.Proofs.SafetyAccountable,
     `AvailableChainFGCompose.Proofs.SafetyClient, `AvailableChainFGCompose.Proofs.SafetyCount,
     `AvailableChainFGCompose.Proofs.SafetyMonotone,
     `AvailableChainFGCompose.Proofs.SafetySlashing,
     `AvailableChainFGCompose.Statements.Phase,
     `AvailableChainFGCompose.Statements.PhaseReceipts,
     `AvailableChainFGCompose.Proofs.Healing.PhaseFrame,
     `AvailableChainFGCompose.Proofs.Healing.PhaseOrder,
     `AvailableChainFGCompose.Proofs.Healing.PhaseSettle,
     `AvailableChainFGCompose.Statements.ResetCut,
     `AvailableChainFGCompose.Statements.FinalityHistory,
     `AvailableChainFGCompose.Proofs.Finality.History,
     `AvailableChainFGCompose.Proofs.Healing.ResetCut].contains dep
  else if composeStatements m then base || ownStatements || safety
  else if [(`AvailableChainFGCompose.Tests.P0d3,
      `AvailableChainKitFG.WindowHeightBridge)].contains (m, dep) then true
  else if (`AvailableChainFGCompose.Tests).isPrefixOf m then
    foundation || ownStatements || ownProofs
  else if (`AvailableChainFGCompose.Proofs).isPrefixOf m then
    base || ownStatements || ownProofs ||
      [`AvailableChainKitV2.DutyStable, `AvailableChainKitFG.Correspondence].contains dep ||
      -- Lead ruling 2026-10-07 (s2-plan P1): the exact pair of check-layers.py.
      -- Lead ruling 2026-10-07 (P2, S3a): the two exact SafetyClient pairs.
      [(`AvailableChainFGCompose.Proofs.SafetyAccountable,
        `AvailableChainKitFG.AccountableCore),
       (`AvailableChainFGCompose.Proofs.ExecutionHistory,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Healing.PhaseFrame,
        `AvailableChainKitFG.StoreBounds),
       (`AvailableChainFGCompose.Proofs.Healing.PhaseFrame,
        `AvailableChainKitFG.FrameGeometry),
       (`AvailableChainFGCompose.Proofs.Healing.PhaseSettle,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Healing.CommonEntry,
        `AvailableChainKitFG.Ancestry),
       (`AvailableChainFGCompose.Proofs.Healing.PromotionRows,
        `AvailableChainKitFG.Ancestry),
       (`AvailableChainFGCompose.Proofs.Healing.PhaseFrame,
        `AvailableChainKitFG.FrameGeometry),
       (`AvailableChainFGCompose.Proofs.Healing.PhaseFrame,
        `AvailableChainKitFG.StoreBounds),
       (`AvailableChainFGCompose.Proofs.Healing.PhaseSettle,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Finality.Rows,
        `AvailableChainKitFG.HeightHistoryTransfer),
       (`AvailableChainFGCompose.Proofs.Finality.Rows,
        `AvailableChainKitFG.WindowTerminal),
       (`AvailableChainFGCompose.Proofs.Finality.Batch,
        `AvailableChainKitFG.WindowRetention),
       (`AvailableChainFGCompose.Proofs.Finality.Carry,
        `AvailableChainKitFG.WindowValidity),
       (`AvailableChainFGCompose.Proofs.Finality.Carry,
        `AvailableChainKitFG.WindowHeightBridge),
       (`AvailableChainFGCompose.Proofs.Finality.RestoreReads,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Finality.Forward,
        `AvailableChainGeneric.Proofs.Pure.ScheduleW),
       (`AvailableChainFGCompose.Proofs.Finality.Local,
        `AvailableChainGeneric.Proofs.Pure.BlockOrder),
       (`AvailableChainFGCompose.Proofs.Finality.RestoreReads,
        `AvailableChainKitFG.Ancestry),
       (`AvailableChainFGCompose.Proofs.Finality.Receipt,
        `AvailableChainKitFG.FrameGeometry),
       (`AvailableChainFGCompose.Proofs.Finality.Receipt,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Finality.Accept,
        `AvailableChainKitFG.FrameGeometry),
       (`AvailableChainFGCompose.Proofs.Finality.Accept,
        `AvailableChainKitFG.WindowStore),
       (`AvailableChainFGCompose.Proofs.Population.HolderBaseHighTarget,
        `AvailableChainSimplexFG.Client),
       (`AvailableChainFGCompose.Proofs.Population.HolderBaseTop,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Finality.RecordInv,
        `AvailableChainKitFG.ProvenanceCore),
       (`AvailableChainFGCompose.Proofs.Finality.RecordInv,
        `AvailableChainKitFG.StoreSafetyDef),
       (`AvailableChainFGCompose.Proofs.Finality.RecordInv,
        `AvailableChainGeneric.Proofs.V2.Duty.Fields),
       (`AvailableChainFGCompose.Proofs.Finality.History, `AvailableChainKitFG.CausalCapCore),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainKitFG.HeightHistoryTransfer),
       (`AvailableChainFGCompose.Proofs.Finality.History, `AvailableChainKitFG.WindowRetention),
       (`AvailableChainFGCompose.Proofs.Finality.History, `AvailableChainKitFG.WindowSelection),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.HistoricalReads,
        `AvailableChainGeneric.Proofs.Pure.CommonAncestor),
       (`AvailableChainFGCompose.Proofs.Healing.PromotionRows,
        `AvailableChainSimplexFG.Window),
       (`AvailableChainFGCompose.Proofs.RowPermission, `AvailableChainKitFG.ClientOnceSafety),
       (`AvailableChainFGCompose.Proofs.SafetyClient, `AvailableChainKitFG.ClientOnceSafety),
       (`AvailableChainFGCompose.Proofs.SafetyClient,
        `AvailableChainGeneric.Proofs.V2.Duty.Fields),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainKitFG.CausalCapCore),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainKitFG.HeightHistoryTransfer),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainKitFG.WindowRetention),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainKitFG.WindowSelection),
       (`AvailableChainFGCompose.Proofs.Finality.History,
        `AvailableChainGeneric.Proofs.V2.Duty.Reads),
       (`AvailableChainFGCompose.Proofs.Healing.ResetCut,
        `AvailableChainKitFG.StoreBounds)].contains (m, dep)
  else false

def composeMain (args : List String) : IO UInt32 := do
  let (extra, rest) := match args with
    | "--root" :: m :: r => (#[m.toName], r)
    | _ => (#[], args)
  unless rest.isEmpty || (rest.head? == some "--expect" && rest.length ≥ 2) do
    IO.eprintln "USAGE: CheckFGAxioms --compose [--root M] [--expect N …]"
    return 2
  let expected := rest.drop 1
  let facade := (← layoutOutput #["path", "AvailableChainFGCompose"])[0]!
  unless ← System.FilePath.pathExists facade do
    IO.eprintln "MISSING COMPOSE ROOT"
    return 2
  let directory := (← layoutOutput #["dir", "AvailableChainFGCompose"])[0]!
  unless ← System.FilePath.isDir directory do
    IO.eprintln "MISSING COMPOSE DIRECTORY"
    return 2
  let sources := (← composeSources "AvailableChainFGCompose")
  if sources.size ≤ 1 then
    IO.eprintln "EMPTY COMPOSE SOURCE SCOPE"
    return 2
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules ((sources ++ extra).map ({ module := · })) {}
    (loadExts := true) (level := .private)
  let mut bad := false
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if !extra.contains m && !(closureRoots ++
        [`AvailableChainEngineV2, `AvailableChainKitV2, `AvailableChainFGCompose]).contains m.getRoot then
      IO.println s!"FORBIDDEN LIBRARY IN THE COMPOSE IMPORT CLOSURE: {m}"
      bad := true
    if (`AvailableChainFGCompose).isPrefixOf m then
      for imp in env.header.moduleData[i]!.imports do
        unless composeImportAllowed m imp.module do
          IO.println s!"COMPILED IMPORT NOT ALLOWED: {m} imports {imp.module}"
          bad := true
  for m in sources do
    unless env.header.moduleNames.contains m do
      IO.eprintln s!"MISSING COMPILED SOURCE: {m}"
      return 2
  let cs := env.constants.toList.filter fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some idx => (`AvailableChainFGCompose).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let forbidden := axs.filter (fun a => !allowed.contains a)
    unless forbidden.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {forbidden}"
      bad := true
  let mut missing := 0
  for s in expected do
    unless cs.any (fun (n, _) => s.toName.isSuffixOf n) do
      IO.println s!"NOT CHECKED: {s}"
      missing := missing + 1
  IO.println s!"Compose checked {cs.length} constants in {sources.size} source modules"
  if missing > 0 then return 2
  return if bad then 1 else 0

def main (args : List String) : IO UInt32 := do
  match args with
  | "--compose" :: rest =>
      let pureArgs := match rest with
        | "--root" :: m :: _ =>
            if (`AvailableChainKitFG).isPrefixOf m.toName ||
                (`AvailableChainSimplexFG).isPrefixOf m.toName then ["--root", m] else []
        | _ => []
      let rc ← pureMain pureArgs true
      if rc != 0 then return rc
      try composeMain rest catch e =>
        IO.eprintln s!"COMPOSE INPUT ERROR: {e}"
        return 2
  | _ => pureMain args

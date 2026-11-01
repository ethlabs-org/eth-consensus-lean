module
public import Lean -- shake: keep (re-export)

public section
namespace AvailableChainCheckSupport.ImportPolicy
open Lean

/-- Generated from scripts/import-policy.json. Do not edit. -/
def accepts (rows : List (Name × Bool × Bool)) (name : Name) : Bool :=
  rows.any fun (baseName, descendants, self) =>
    (self && name == baseName) ||
    (descendants && baseName.isPrefixOf name && name != baseName)

def fgsaAllowedImport (mod imp : Name) : Bool :=
  imp == `Init ||
  let parts := mod.components.map (·.toString)
  let layer := if mod == `AvailableChainFGSA then "root"
    else if parts.head? == some "AvailableChainFGSA" && parts.length >= 3
    then parts[1]! else ""
  accepts (match layer with
    | "root" => [
      (`AvailableChainFGSA, true, false)]
    | "Tests" => [
      (`AvailableChainFGSA, true, false),
      (`AvailableChainModel, true, false),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainSA.Model.Protocol, false, true),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false)]
    | "Model" => [
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainModel, true, false),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainSA.Model.Protocol, false, true),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainKitFG.ClientOnce, false, true),
      (`AvailableChainKitFG.FrameBridgeDef, false, true),
      (`AvailableChainKitFG.TreeFrameDef, false, true)]
    | "Statements" => [
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainFGSA.Statements, true, false),
      (`AvailableChainModel, true, false),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainSA.Model.Protocol, false, true),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainKitFG, true, false)]
    | "Proofs" => [
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainFGSA.Statements, true, false),
      (`AvailableChainFGSA.Proofs, true, false),
      (`AvailableChainModel, true, false),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainSA.Model.Protocol, false, true),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainGridCO.Proofs, true, false),
      (`AvailableChainKitFG, true, false),
      (`AvailableChainGeneric.Proofs, true, false)]
    | _ => []) imp

def runAllowedImport (mod imp : Name) : Bool :=
  imp == `Init ||
  let parts := mod.components.map (·.toString)
  let layer := if mod == `AvailableChainFGSARun then "root"
    else if parts.head? == some "AvailableChainFGSARun" && parts.length >= 3
    then parts[1]! else ""
  accepts (match layer with
    | "root" => [
      (`AvailableChainFGSARun, true, false)]
    | "Tests" => [
      (`AvailableChainFGSARun, true, false),
      (`AvailableChainEngineV2, true, false),
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainFGSA.Statements, true, false),
      (`AvailableChainGeneric.Statements, true, false),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainModel.Objects.Identifiers, false, true),
      (`AvailableChainModel.Objects.Time, false, true),
      (`AvailableChainModel.Objects.Blocks, false, true),
      (`AvailableChainModel.Objects.Codec, false, true),
      (`AvailableChainModel.Generic.Env, false, true),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainGridCO.Model.Walk, false, true),
      (`AvailableChainSA.Model.Protocol, false, true),
      (`AvailableChainKitV2, true, false),
      (`AvailableChainFGSA.Proofs, true, false),
      (`AvailableChainKitFG, true, false),
      (`AvailableChainGeneric.Proofs, true, false),
      (`AvailableChainFGSA.Tests.Support, false, true)]
    | "Model" => [
      (`AvailableChainFGSARun.Model, true, false),
      (`AvailableChainEngineV2, true, false),
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainFGSA.Statements, true, false),
      (`AvailableChainGeneric.Statements, true, false),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainModel.Objects.Identifiers, false, true),
      (`AvailableChainModel.Objects.Time, false, true),
      (`AvailableChainModel.Objects.Blocks, false, true),
      (`AvailableChainModel.Objects.Codec, false, true),
      (`AvailableChainModel.Generic.Env, false, true),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainGridCO.Model.Walk, false, true),
      (`AvailableChainSA.Model.Protocol, false, true)]
    | "Statements" => [
      (`AvailableChainFGSARun.Model, true, false),
      (`AvailableChainFGSARun.Statements, true, false),
      (`AvailableChainEngineV2, true, false),
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainFGSA.Statements, true, false),
      (`AvailableChainGeneric.Statements, true, false),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainModel.Objects.Identifiers, false, true),
      (`AvailableChainModel.Objects.Time, false, true),
      (`AvailableChainModel.Objects.Blocks, false, true),
      (`AvailableChainModel.Objects.Codec, false, true),
      (`AvailableChainModel.Generic.Env, false, true),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainGridCO.Model.Walk, false, true),
      (`AvailableChainSA.Model.Protocol, false, true)]
    | "Proofs" => [
      (`AvailableChainFGSARun.Model, true, false),
      (`AvailableChainFGSARun.Statements, true, false),
      (`AvailableChainFGSARun.Proofs, true, false),
      (`AvailableChainEngineV2, true, false),
      (`AvailableChainFGSA.Model, true, false),
      (`AvailableChainFGSA.Statements, true, false),
      (`AvailableChainGeneric.Statements, true, false),
      (`AvailableChainSimplexFG, true, false),
      (`Mathlib, true, false),
      (`AvailableChainModel.Objects.Identifiers, false, true),
      (`AvailableChainModel.Objects.Time, false, true),
      (`AvailableChainModel.Objects.Blocks, false, true),
      (`AvailableChainModel.Objects.Codec, false, true),
      (`AvailableChainModel.Generic.Env, false, true),
      (`AvailableChainGridCO.Model.Protocol, false, true),
      (`AvailableChainGridCO.Model.Walk, false, true),
      (`AvailableChainSA.Model.Protocol, false, true),
      (`AvailableChainKitV2, true, false),
      (`AvailableChainFGSA.Proofs, true, false),
      (`AvailableChainKitFG, true, false),
      (`AvailableChainGeneric.Proofs, true, false)]
    | _ => []) imp

end AvailableChainCheckSupport.ImportPolicy
end

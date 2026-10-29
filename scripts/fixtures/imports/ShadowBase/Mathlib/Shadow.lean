module
public import Lean
open Lean Elab Command in
run_cmd liftCoreM <| withOptions (debug.skipKernelTC.set · true) <|
  addDecl (.axiomDecl { name := `bogus, levelParams := [], type := .const ``False [], isUnsafe := false })

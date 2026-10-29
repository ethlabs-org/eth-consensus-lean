module
public meta import Lean.Elab.Command

@[expose] public section

/-! A metaprogram that adds a theorem of `False` without the kernel's check (`debug.skipKernelTC`, set
through `withOptions`, so no `set_option` appears in the source). `#print axioms` and the `axioms`
command see no axiom; only the kernel replay rejects it. -/

open Lean Elab Command in
run_cmd liftCoreM <| withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
  addDecl (.thmDecl { name := `CheckFixtures.BadSkipKernel.bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })

theorem CheckFixtures.BadSkipKernel.uses_bogus : 1 = 2 := CheckFixtures.BadSkipKernel.bogus.elim

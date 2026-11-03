module -- shake: keep-downstream, shake: keep-all

public import Mathlib.Init
public import Mathlib.Tactic.Common

/-!
# ConsensusLean initialization

Every module of `ConsensusLean` reaches this file by public imports (directly from the modules that
import no other project module, for example `Spec/Problem/Basic.lean` and
`Spec/Model/Objects.lean`), so its imports are curated: the linters of `Mathlib.Init` and the
tactics of `Mathlib.Tactic.Common` (pattern of CSLib `Cslib/Init.lean`). It is part of the trusted
surface, because the Spec modules elaborate under it. It holds no options: a `set_option` does not
travel through imports; shared options are in `lakefile.toml`.
-/

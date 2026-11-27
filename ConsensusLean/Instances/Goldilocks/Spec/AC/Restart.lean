module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions

@[expose] public section

/-! # Goldilocks AC: restart

goldilocks-spec.tex §"Joining and restart" (Figure "Goldilocks: restart"): a restart keeps the locks
and `latest_confirmed` and the installed voting permission, resets every other field, and
sets `restart_time` to the time of the restart. Genesis is stamped `⊥`, every other root in
`Φ.tree` is stamped with that time, and roots outside the tree are stamped `⊤`. No votes
are admitted or emitted. -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} (sp : ACParams)

set_option linter.unusedVariables false in
/-- `ac_restart(𝒜, Φ, t)`: bulk stamp the held non-genesis roots and emit nothing.
The retained `self` parameter does not affect the result. -/
noncomputable def acRestart (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n × List (Em sp FGP) := by
  classical
  exact ({ ACState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time)
    mayVote := A.mayVote,
    blockStamp := fun q => if q = sp.genesisRoot then ⊥
      else if InTree Φ q then ETime.of t else ⊤ }, [])

end Consensus.Goldilocks.AC

end

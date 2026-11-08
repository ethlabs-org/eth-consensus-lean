module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace

@[expose] public section

/-! # The parent's unlock oracle at a write mode

Beside the parent's unlock and its oracle (`parentUnlock`, `parentOracle`, `RelTrace`): the
parent's unlock of the call's input at a write mode `m` (`callInputM`, `callViewM`), and the
oracle that gives it at each labelled cut of a trace. A run of the parent's stage at mode `m` is
`ACLocalRunU m (parentOracleM sp m tr)`; at the parent's mode it is `parentOracle`
(`Lemmas/AC/ParentOracleM`). Definitions only. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

variable (sp) in
/-- The parent's locks after the unlock of the call `c` at mode `m`. -/
noncomputable abbrev parentUnlockM {ro : ReplayOrder sp FGP} (m : WriteMode) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) : Set Lock :=
  unlock sp (callInputM sp m A Φ t c).locks Φ t ((sp.slot t : Int) - 1) (callViewM sp m A Φ t c)

variable (sp) in
/-- The parent's unlock oracle of a trace at mode `m`: at each labelled cut, the parent's locks
after the unlock of the call at mode `m` at the pre-state. -/
noncomputable abbrev parentOracleM {ro : ReplayOrder sp FGP} (m : WriteMode)
    (tr : SATrace sp FGP ro) (i : Nat) : Set Lock :=
  match tr.label i with
  | some ℓ => parentUnlockM sp m (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call
  | none => ∅

end Consensus.Goldilocks.SA

end

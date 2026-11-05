module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Confirmation

@[expose] public section

/-! # Goldilocks milestone vocabulary: fast-confirmation helpers

The part of `Spec/SA/Confirmation` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

`fastSelect` and `fastCounted`: the block the fast test of an update selects, and the votes it
counts. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} (sp : SAParams)

/-- The block `D` that the fast test of the update of slot `s` selects on the path of the result
`C`: the deepest block of the path that passes it (whether or not a lock vetoes the result). -/
noncomputable def fastSelect (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (C : Blk sp.n FGP) :
    Option (Blk sp.n FGP) :=
  deepest Φ {B | B ∈ confirmationPath sp Φ C ∧ FastTest sp A Φ s B}

/-- The validators the fast test counts for `B` in slot `s`, with their counted votes: the
votes of the slot-`s` pool resolved before `t_s + 2Δ`, of validators with no second vote, whose
head extends `B`. -/
noncomputable def fastCounted (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (B : Blk sp.n FGP) :
    Set (Vote sp.n) :=
  {v | v ∈ A.pool s ∧ v.val ∉ equivocators {x | x ∈ A.pool s} ∧
    resolutionTime A Φ v < ETime.of (sp.ts s + 2 * sp.Δ) ∧ AncR Φ B v.head}

end Consensus.Goldilocks.SA

end

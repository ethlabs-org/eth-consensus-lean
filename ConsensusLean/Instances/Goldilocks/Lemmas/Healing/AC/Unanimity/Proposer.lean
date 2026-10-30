module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd

public section

/-! # Goldilocks Healing: the canonical walk from the proposal's anchor ends at `P` (T1 §6)

The proposer's walk from `d.start` has one step per block of its tree, so it stops, at
`d.head = parent(P)`: no child of `d.head` in the proposer's tree is eligible, and `P` is not
in that tree (it would be an eligible child, of the current slot). With `P` added, the walk
takes the same steps up to `d.head` (`P` is a child of `d.head` only), then `P`, the only
eligible child there, and stops (no block of the tree has a slot above `p`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n}

/-- **The canonical walk from the proposal's anchor ends at `P`**, through `d.head`. -/
theorem proposal_walkEnd (hs : UnanimitySetting tr H U g p P k ℓp d pay) :
    WalkEnd (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)) d.start P ∧
      P ∈ U ∧ ℓp.frame.tree ⊆ U ∧ Anc U d.start d.head ∧ Anc U d.head P := by
  sorry

end Consensus.Goldilocks.SA

end

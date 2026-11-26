module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks AC: an honest validator does not equivocate in an honest pool

* `honest_pool_not_equivocator`: under the honest-object facts, a validator honest at a pool of
  an honest node has at most one vote per slot there (its pool votes were cast, one per slot by
  A0.8, and the pool of a slot holds only votes of that slot), so it is no equivocator of it. -/

namespace Consensus.Goldilocks.AC

variable {wm : WriteMode} {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro}
  {ini : Fin sp.n → ACState sp.n} {proposer : Nat → Fin sp.n}

/-- **An honest validator is not an equivocator in an honest node's pool**, with the unlock
given, from starts up to the vote permission. -/
theorem honest_pool_not_equivocator {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) (hho : HonestObjects proposer tr H)
    {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) {w : Fin sp.n} (hw : w ∈ H) :
    w ∉ equivocators {v | v ∈ (tr.state y i).pool σ} := by
  rintro ⟨a, ha, b, hb, hab, rfl, hbw⟩
  obtain ⟨ja, -, ea, hva, rfl⟩ := hho.pool_vote y hy i σ _ ha hw
  obtain ⟨jb, -, eb, hvb, rfl⟩ := hho.pool_vote y hy i σ _ hb (hbw ▸ hw)
  rw [hbw] at hvb
  obtain ⟨-, rfl⟩ := one_vote_per_slotU sp FGP ro H U tr hr _ hw ja jb ea eb hva hvb
    ((state_pool_slotU sp hr hini hy i σ _ ha).trans (state_pool_slotU sp hr hini hy i σ _ hb).symm)
  exact hab rfl

end Consensus.Goldilocks.AC

end

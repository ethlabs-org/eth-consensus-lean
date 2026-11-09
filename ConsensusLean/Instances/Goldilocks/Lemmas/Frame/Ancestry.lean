module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Ancestry restricted to a rooted frame

Coherence identifies parent edges in the universe with those in the frame. This geometry
is shared by AC and node-run proofs and needs neither execution nor source premises. -/

namespace Consensus.Goldilocks.Frame

/-- Ancestry in a coherent universe restricts to a rooted frame containing both endpoints,
for arbitrary FG and AC payloads. -/
theorem anc_tree_of_anc_U {n : Nat} {FGP ACP : Type} {U : Set (Block n FGP ACP)}
    (hU : Coherent U) {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {B C : Block n FGP ACP} (hB : B ∈ Φ.tree) (h : Goldilocks.Anc U B C) :
    C ∈ Φ.tree → Φ.Anc B C := by
  induction h with
  | refl => exact fun _ => Relation.ReflTransGen.refl
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      have := Goldilocks.Anc.antisymm hU (hBc.tail e) ((hΦ.rooted.2 B hB).mono hΦU)
      exact this ▸ Relation.ReflTransGen.refl
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some.inj (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact (ih hp.1).tail hp

end Consensus.Goldilocks.Frame

end

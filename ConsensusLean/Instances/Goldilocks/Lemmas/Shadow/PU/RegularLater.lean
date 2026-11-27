module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Views
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # P-U regular-later investigation

The run-level `regular_later_heads_at'` is unresolved. No reachable counterexample is
claimed. The stock proof's viable-head branch used `fcRoot = J` twice: to compare the
origin D with J, and to put D above the reader's fork-choice root. Neither use transfers
to a top contest. In particular, leaf 9 concerns reports, not arbitrary lock origins D.

The existing early-witness argument admits a different geometric route. At each reader,
keep Q viable and establish F ⪯ Q. Totality of D ⪯ Q and F ⪯ Q then puts D below F,
or puts D on the viable path rooted at F. The second case is precisely the input used
by `WitnessUnanimity.witness_frame_at`; no ancestry J ⪯ D is required.

The theorem below proves that geometric step. Its coherent ambient tree is an explicit
premise, not inferred from a stock run. Instantiation over a shadow run still requires
the shadow cache/coherence and relay/early-witness suppliers. It does not certify V-B8.

There is also a signature constraint: the stock early-witness supplier assumes only a
height floor for Q, not source viability. Removing its `hJ` premise literally does not
supply the P-U J clause at height M−1. The regular-later viable-head branch does supply
source viability. Any shadow instantiation must use that evidence rather than quietly
assume that a height bound makes every held Q viable in a top contest.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (Blk Frm)

/-- The frame-level step of the existing witness argument when the root is F.
The ambient coherence premise must come from the shadow run, not a stock-run cast. -/
theorem regular_witness_frame_of_root_F
    {n : Nat} {FGP : Type} {U : Set (Blk n FGP)} {Φ : Frm n FGP}
    (hU : Coherent U) (hΦ : FrameOK Φ) (hsub : Φ.tree ⊆ U)
    (hroot : Φ.fcRoot = Φ.F) {D Q : Blk n FGP}
    (hvQ : Q ∈ Φ.viableHeads) (hDQ : Anc U D Q) :
    Anc U D Φ.F ∨
      (Anc U Φ.F D ∧ D ∈ Φ.tree ∧ Φ.Anc Φ.fcRoot D ∧
        Q ∈ Φ.tree ∧ Q ∈ Φ.viableHeads ∧ Φ.Anc D Q) := by
  have hQt := hΦ.viableHeads_subset hvQ
  have hFQ := (hΦ.rooted.2 Q hQt).mono hsub
  rcases AC.anc_total hU hFQ hDQ with hFD | hDF
  · have hmiddle : ∀ {W}, Φ.Anc Φ.F W → Anc U D W → D ∈ Φ.tree := by
      intro W hpath
      induction hpath with
      | refl =>
        intro hDF
        have he := Anc.antisymm hU hFD hDF
        exact he ▸ hΦ.rooted.1
      | @tail A B hFA hAB ih =>
        intro hDB
        rcases Relation.ReflTransGen.cases_tail hDB with he | ⟨C, hDC, hCB⟩
        · exact he ▸ hAB.2.1
        · have he : C = A := hU.1 hCB.1 (hsub hAB.1)
            (Option.some.inj (hCB.2.2.symm.trans hAB.2.2))
          subst C
          exact ih hDC
    have hDframe := hmiddle (hΦ.rooted.2 Q hQt) hDQ
    have hFDf := AC.anc_tree_of_anc_U hU hΦ hsub hΦ.rooted.1 hFD hDframe
    exact Or.inr ⟨hFD, hDframe, hroot ▸ hFDf, hQt, hvQ,
      AC.anc_tree_of_anc_U hU hΦ hsub hDframe hDQ hQt⟩
  · exact Or.inl hDF

end Consensus.Goldilocks.Healing.PU

end

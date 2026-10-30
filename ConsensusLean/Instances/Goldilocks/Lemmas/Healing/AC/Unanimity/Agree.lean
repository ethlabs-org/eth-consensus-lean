module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd

public section

/-! # Goldilocks Healing: every honest slot-`p` walk is the canonical walk (T1 §6)

At every honest vote of slot `p`, the voter walks the canonical walk: at every block, its
eligible children (in the viable voter block tree, with the merged view) are the eligible
children of the proposer's tree with `P` added (with the proposal's view at `t_p`), with the
same scores. The voter holds `P` (its `vote_ready`, or acceptance relay by `t_p + Δ`), and `P`
is the only slot-`p` block of the honest frames (`one_block`). A child of slot below `p` of the
voter block tree was accepted before the vote freeze, so it reached the proposer by `t_p`; an
eligible child of slot below `p` of the proposer's tree has a strict majority of the voters,
all honest validators among them (`Healthy`), so an honest supporter, and reached the voter
before the freeze (`trivial_viable`); the scores and eligibility agree by `view_agree`. `P` has
no supporters in either view. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n}

/-- **An honest voter of slot `p` holds `P`**, and `P` is in `U`. -/
theorem vote_holds_proposal (hs : UnanimitySetting tr H U g p P k ℓp d pay) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = p) : P ∈ ℓ.frame.tree ∧ P ∈ U := by
  sorry

/-- **The voter's walk is the canonical walk**: at an honest vote of slot `p`, the eligible
children of every block, and their scores, are those of the proposer's tree with `P` added. -/
theorem vote_children_eq (hs : UnanimitySetting tr H U g p P k ℓp d pay) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = p) (X : Blk sp.n FGP) :
    eligibleChildren (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
        (goldfishEligible sp ℓ.frame (tr.time j) (mergedVoteView sp e.readPoint ℓ.frame p)
          ((p : Int) - 1)) X =
      eligibleChildren (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)) X ∧
    ∀ B ∈ eligibleChildren (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
        (goldfishEligible sp ℓ.frame (tr.time j) (mergedVoteView sp e.readPoint ℓ.frame p)
          ((p : Int) - 1)) X,
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1) B =
        goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1) B := by
  sorry

end Consensus.Goldilocks.SA

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild

public section

/-! # Goldilocks Healing: the parent and the old children at the proposal parent

Two frame steps of stopping a voter's walk at the parent `Q` of an actual proposal `P`. They read
the frames, the proposal call and the agreement of the two vote views only, not the run or its
fault model:

* `parent_mem_frame_of_children`: in a coherent universe holding a well-formed frame, a block with
  two distinct children in the frame tree, both above `fc_root`, is in the tree above `fc_root`;
* `old_child_ineligible_of_views`: when the proposer's view and the voter's merged view agree
  (equivocators, voters, and supporters of the common blocks), a child of the duty head older
  than the proposal slot and viable in the proposer's frame is not eligible at the voter, since
  the proposer's walk stopped at the duty head. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}

/-- **The parent of two viable children.** In a coherent `U` holding the well-formed frame `Φ`,
a block `Q ∈ U` with two distinct children `P ≠ B` in `Φ.tree`, both above `fc_root`, is in
`Φ.tree` above `fc_root`: a common ancestor of `B` and `P` in `U` is an ancestor of `Q`. -/
theorem parent_mem_frame_of_children {U : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {Φ : AC.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {Q P B : AC.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ U)
    (hPQ : P.parent = some Q.root) (hBQ : B.parent = some Q.root) (hBP : B ≠ P)
    (hP : P ∈ Φ.tree) (hPr : Φ.Anc Φ.fcRoot P) (hB : B ∈ Φ.tree) (hBr : Φ.Anc Φ.fcRoot B) :
    Q ∈ Φ.tree ∧ Φ.Anc Φ.fcRoot Q := by
  have hQP : Anc U Q P := .single ⟨hQU, hΦU hP, hPQ⟩
  have hnBP : ¬ Anc U B P := by
    intro h
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hBY, hY⟩
    · exact hBP heq.symm
    obtain rfl : Y = Q := hU.1 hY.1 hQU
      (Option.some_injective _ (hY.2.2.symm.trans hPQ))
    have h1 := (Anc.slot_le hU hBY).1
    have h2 := hU.2 Y hQU B (hΦU hB) hBQ
    omega
  have below : ∀ X, Anc U X B → Anc U X P → Anc U X Q := by
    intro X hXB hXP
    rcases Relation.ReflTransGen.cases_tail hXB with heq | ⟨Y, hXY, hY⟩
    · exact False.elim (hnBP (heq ▸ hXP))
    obtain rfl : Y = Q := hU.1 hY.1 hQU
      (Option.some_injective _ (hY.2.2.symm.trans hBQ))
    exact hXY
  have hfQ := below _ (hBr.mono hΦU) (hPr.mono hΦU)
  have hQt := AC.frame_mem_of_between sp hU hΦ hΦU hP hQP ((hΦ.F_anc_fcRoot.mono hΦU).trans hfQ)
  exact ⟨hQt, AC.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfQ hQt⟩

/-- **An old child stays ineligible.** Let the proposal call at `t_i` (slot `s + 1`) in the
well-formed frame `Φp` return the duty head `d.head` with the payload `pay`, and let the voter's
view `V` at `t_j` (slot `s + 1`) agree with `pay` on equivocators, voters and the supporters of
every block of both frames. A child `B` of `d.head` viable in `Φp`, in the voter's frame `Φy`,
with `d.head` viable at the voter and `B.slot < s + 1`, is not eligible at the voter: its strict
majority would give the proposer's stopped walk a best child at `d.head`. -/
theorem old_child_ineligible_of_views {Φp Φy : AC.Frm sp.n (List (FG.Att sp.n))}
    (hΦ : FrameOK Φp) {st : AC.ACState sp.n} {ti tj : Time} {s : Nat}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp st Φp ti).2 = some (d, pay)) (hslot : sp.slot ti = s + 1)
    {V : AC.View sp.n}
    (heq : AC.equivocators (AC.View.ofLists pay).votes = AC.equivocators V.votes)
    (hvot : AC.voters (AC.View.ofLists pay).votes = AC.voters V.votes)
    (hsup : ∀ X ∈ Φp.tree, X ∈ Φy.tree →
      AC.supporters Φp (AC.View.ofLists pay) s X = AC.supporters Φy V s X)
    (hsj : sp.slot tj = s + 1) (hQvy : d.head ∈ Φy.viableHeads)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hBv : B ∈ Φp.viableTree Φp.tree)
    (hBy : B ∈ Φy.tree) (hBQ : B.parent = some d.head.root) (hBs : B.slot < s + 1) :
    ¬ AC.headEligible sp Φy tj V s B := by
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  set T := Φp.viableTree Φp.tree
  have hT : T ⊆ Φp.tree := fun _ h => h.1
  have hhead : d.head = AC.ghost sp T
      (AC.headScore sp Φp (AC.View.ofLists pay) s)
      (AC.headEligible sp Φp ti (AC.View.ofLists pay) s)
      Φp.tree.ncard d.start := by
    unfold AC.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot, hcast]
    rfl
  have hstop := AC.ghost_stopped hΦ.coherent hT (hΦ.finite.subset hT)
    (sc := AC.headScore sp Φp (AC.View.ofLists pay) s)
    (el := AC.headEligible sp Φp ti (AC.View.ofLists pay) s)
    (Set.ncard_le_ncard hT hΦ.finite) d.start
  rw [← hhead] at hstop
  rintro (h | h | h)
  · exact h ⟨d.head, hQvy, hBQ⟩
  · omega
  · have hmaj : (AC.voters (AC.View.ofLists pay).votes).ncard <
        2 * AC.headScore sp Φp (AC.View.ofLists pay) s B := by
      simpa only [AC.headScore, hvot, heq, hsup B hBv.1 hBy] using h
    exact hstop (AC.exists_isBest hΦ
      (S := {X | X ∈ T ∧ X.parent = some d.head.root ∧
        AC.headEligible sp Φp ti (AC.View.ofLists pay) s X})
      (fun X hX => hT hX.1) ⟨B, hBv, hBQ, Or.inr (Or.inr hmaj)⟩ _)

end Consensus.Goldilocks.Healing

end

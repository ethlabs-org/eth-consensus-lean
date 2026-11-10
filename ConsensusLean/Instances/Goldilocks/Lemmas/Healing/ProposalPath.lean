module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks Healing: a voter's walk along an actual proposal's walk

The proposer's walk of a slot-`s + 1` proposal call in its frame `Φp` runs from the duty start
`d.start` and stops at the duty head `d.head`, the parent of the actual proposal `P`. A voter of
slot `s + 1` with frame `Φy`, holding `P` viable, follows that walk. These steps read the two
frames, the proposer's walk and the agreement of the two vote views only, not the run or its
fault model; the suppliers of the run are premises:

* `suffix_best_of_proposal_walk`: above the voter's anchor, a best child of a block strictly on the
  proposer's walk stays the voter's best child, given competitor reflection into the proposer's
  viable tree and the transfer of viable heads from the voter's frame to the proposer's;
* `getHead_eq_of_proposal_path`: a voter whose walk passes a block of the proposer's walk, given
  that step and the stop at `d.head` with `P` as its only eligible child, ends at `P`;
* `anchor_on_proposal_path`: a voter anchor below `P` either is `P` or reaches, through the walk,
  a block of the proposer's walk, given that an anchor below `d.start` walks through `d.start`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams Payload)

variable {sp : SAParams}

/-- **A best child on the proposer's walk stays the voter's best child.** The proposer's walk in
`Φp` (call at `t_i`, slot `s + 1`, payload `pay`) runs from `d.start` and stops at `d.head`, the
parent of `P` (slot `s + 1`, viable in the voter's tree of `Φy`); both frames lie in a coherent
`U`, and the voter's merged view agrees with `pay` on equivocators, voters and the supporters of
every common block. For `X` on the walk strictly below `d.head`, above the voter's anchor, the
best eligible child `C` of `X` in `Φp` is the best eligible child of `X` in the voter's tree,
given

* `hrefl`: a child other than `P`, in the voter's tree, of a block of `Φp` above `Φp.fcRoot` is in
  `Φp`'s viable tree;
* `hviable`: a block of `Φp.tree` that is a viable head of `Φy` is a viable head of `Φp`.

`C` is below `d.head`, so it is in the voter's tree through `P`; when `X` is viable in `Φp` its
eligibility is a strict majority (`SA.isBest_transfer`), otherwise `X` is viable in neither frame
(`SA.isBest_transfer_low`). -/
theorem suffix_best_of_proposal_walk {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {Φp Φy : SA.Frm sp.n (List (FG.Att sp.n))} (hΦp : FrameOK Φp)
    (hΦpU : Φp.tree ⊆ U) (hΦy : FrameOK Φy) (hΦyU : Φy.tree ⊆ U) {R : SA.SAState sp.n}
    {ti tj : Time} {s : Nat} (hslot : sp.slot ti = s + 1)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hwalk : d.start ∈ Φp.tree ∧ Φp.Anc Φp.fcRoot d.start ∧
      SA.WalkEnd (sp := sp) (Φp.viableTree Φp.tree)
        (SA.goldfishScore sp Φp (SA.View.ofLists pay) ((sp.slot ti : Int) - 1))
        (SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) ((sp.slot ti : Int) - 1))
        d.start d.head)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = s + 1)
    (hparent : P.parent = some d.head.root)
    (hPv : P ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
    (hv : SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp R Φy (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp R Φy (s + 1)).votes ∧
      ∀ X ∈ Φp.tree, X ∈ Φy.tree →
        SA.supporters Φp (SA.View.ofLists pay) s X =
          SA.supporters Φy (SA.mergedVoteView sp R Φy (s + 1)) s X)
    (hrefl : ∀ X B, X ∈ Φp.tree → Φp.Anc Φp.fcRoot X → B.parent = some X.root → B ≠ P →
      B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) → B ∈ Φp.viableTree Φp.tree)
    (hviable : ∀ X ∈ Φp.tree, X ∈ Φy.viableHeads → X ∈ Φp.viableHeads)
    {X C : SA.Blk sp.n (List (FG.Att sp.n))} (hstartX : Φp.Anc d.start X)
    (hXQ : Φp.Anc X d.head) (hne : X ≠ d.head)
    (hanchorX : Anc U (SA.getAnchor sp R Φy tj) X)
    (hC : SA.IsBest sp (SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
      {B | B ∈ Φp.viableTree Φp.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s B} C) :
    SA.IsBest sp (SA.goldfishScore sp Φy (SA.mergedVoteView sp R Φy (s + 1)) s)
      {B | B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp Φy tj (SA.mergedVoteView sp R Φy (s + 1)) s B} C := by
  obtain ⟨hst, hroot, hw⟩ := hwalk
  simp only [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hw
  have hT : Φp.viableTree Φp.tree ⊆ Φp.tree := fun _ h => h.1
  have hQt : d.head ∈ Φp.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc hT hst) he).2
  have hXt := SA.mem_of_anc hXQ hQt
  have hCQ : Φp.Anc C d.head := by
    obtain ⟨f, hgh, _⟩ := SA.walkEnd_iff.1 (hw.of_anc hΦp.coherent hT hstartX hXQ)
    cases f with
    | zero => exact (hne hgh).elim
    | succ f =>
      rw [show f + 1 = 1 + f from Nat.add_comm f 1, SA.ghost_add,
        SA.ghost_succ_of_best 0 X hC] at hgh
      exact hgh ▸ SA.anc_ghost hT f (hT hC.1.1)
  have hCP : Anc U C P := (hCQ.mono hΦpU).tail ⟨hΦpU hQt, hΦyU hPv.1.1, hparent⟩
  have hXC : Anc U X C := .single ⟨hΦpU hXt, hΦpU hC.1.1.1, hC.1.2.1⟩
  have hfX := ((SA.fcRoot_anc_getAnchor hΦy R tj).mono hΦyU).trans hanchorX
  have hfC := hfX.trans hXC
  have hCt := SA.frame_mem_of_between sp hU hΦy hΦyU hPv.1.1 hCP
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfC)
  have hCPy := SA.anc_tree_of_anc_U hU hΦy hΦyU hCt hCP hPv.1.1
  have hCy : C ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) :=
    ⟨⟨hCt, Or.inr ⟨P, hPv.1.1, hPs, hCPy⟩⟩,
      SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem hfC hCt,
      hPv.2.2.choose, hPv.2.2.choose_spec.1, hPv.2.2.choose_spec.2.1,
      hCPy.trans hPv.2.2.choose_spec.2.2⟩
  have hXy := SA.frame_mem_of_between sp hU hΦy hΦyU hCt hXC
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfX)
  have hsc : ∀ B ∈ Φp.tree, B ∈ Φy.tree →
      SA.goldfishScore sp Φy (SA.mergedVoteView sp R Φy (s + 1)) s B =
        SA.goldfishScore sp Φp (SA.View.ofLists pay) s B := by
    intro B hBp hBy
    simp only [SA.goldfishScore, hv.1, hv.2.2 B hBp hBy]
  have hreflX : ∀ B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)),
      B.parent = some X.root → B ∈ Φp.viableTree Φp.tree := by
    intro B hB hBX
    refine hrefl X B hXt (hroot.trans hstartX) hBX ?_ hB
    rintro rfl
    exact hne (hΦp.coherent.1 hXt hQt (Option.some.inj (hBX.symm.trans hparent)))
  by_cases hXv : X ∈ Φp.viableHeads
  · have hCs : C.slot ≠ sp.slot ti := by
      have hle := (Anc.slot_le hΦp.coherent hCQ).1
      have hlt := hU.2 d.head (hΦpU hQt) P (hΦyU hPv.1.1) hparent
      clear * - hle hlt hslot hPs; omega
    exact SA.isBest_transfer hXv hCs hv.2.1 hsc hT (fun _ h => h.1.1) hCy hreflX hC
  · refine SA.isBest_transfer_low (fun W hW hr => hXv ?_)
      (fun W hW hr => hXv (hviable X hXt ?_)) hsc hT (fun _ h => h.1.1) hCy hreflX hC
    · rwa [hΦp.coherent.1 (hΦp.viableHeads_subset hW) hXt hr] at hW
    · rwa [hΦy.coherent.1 (hΦy.viableHeads_subset hW) hXy hr] at hW

/-- **A voter on the proposer's walk ends at the proposal.** The proposer's walk in `Φp` (call at
`t_i`, slot `s + 1`) runs from `d.start` and stops at `d.head`. Let `X` be on it, with the voter's
walk in `Φy` passing `X` between its anchor and its head. If every best child on the proposer's
walk strictly below `d.head` and above the voter's anchor is the voter's best child (`hsuffix`),
and at `d.head` the voter's only eligible child is `P`, which has no best eligible child
(`hstep`, `hstop`), then the voter's head is `P` (`SA.ghost_follow`). -/
theorem getHead_eq_of_proposal_path {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {Φp Φy : SA.Frm sp.n (List (FG.Att sp.n))} (hΦp : FrameOK Φp) (hΦpU : Φp.tree ⊆ U)
    (hΦy : FrameOK Φy) (hΦyU : Φy.tree ⊆ U) {R : SA.SAState sp.n} {ti tj : Time} {s : Nat}
    (hslot : sp.slot ti = s + 1)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hwalk : d.start ∈ Φp.tree ∧ Φp.Anc Φp.fcRoot d.start ∧
      SA.WalkEnd (sp := sp) (Φp.viableTree Φp.tree)
        (SA.goldfishScore sp Φp (SA.View.ofLists pay) ((sp.slot ti : Int) - 1))
        (SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) ((sp.slot ti : Int) - 1))
        d.start d.head)
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsuffix : ∀ X C, Φp.Anc d.start X → Φp.Anc X d.head → X ≠ d.head →
      Anc U (SA.getAnchor sp R Φy tj) X →
      SA.IsBest sp (SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
        {B | B ∈ Φp.viableTree Φp.tree ∧ B.parent = some X.root ∧
          SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s B} C →
      SA.IsBest sp (SA.goldfishScore sp Φy (SA.mergedVoteView sp R Φy (s + 1)) s)
        {B | B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) ∧ B.parent = some X.root ∧
          SA.goldfishEligible sp Φy tj (SA.mergedVoteView sp R Φy (s + 1)) s B} C)
    (hstep : P ∈ {B | B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp Φy tj
          (SA.mergedVoteView sp R Φy (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp Φy tj
          (SA.mergedVoteView sp R Φy (s + 1)) s B}, B = P)
    (hstop : ¬ ∃ C, SA.IsBest sp
      (SA.goldfishScore sp Φy (SA.mergedVoteView sp R Φy (s + 1)) s)
      {B | B ∈ Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp Φy tj
          (SA.mergedVoteView sp R Φy (s + 1)) s B} C)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hstartX : Φp.Anc d.start X)
    (hXQ : Φp.Anc X d.head) (haX : Φy.Anc (SA.getAnchor sp R Φy tj) X)
    (hXE : Φy.Anc X (SA.getHead sp R Φy tj
      (Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
      (SA.mergedVoteView sp R Φy (s + 1)) s)) :
    SA.getHead sp R Φy tj (Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
      (SA.mergedVoteView sp R Φy (s + 1)) s = P := by
  obtain ⟨hst, -, hw⟩ := hwalk
  simp only [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hw
  have hTp : Φp.viableTree Φp.tree ⊆ Φp.tree := fun _ h => h.1
  have hTy : Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)) ⊆ Φy.tree := fun _ h => h.1.1
  have hQt : d.head ∈ Φp.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc hTp hst) he).2
  have hXt := SA.mem_of_anc hXQ hQt
  obtain ⟨f, hgh, hstopQ⟩ := SA.walkEnd_iff.1 (hw.of_anc hΦp.coherent hTp hstartX hXQ)
  have hfollow := SA.ghost_follow f X hgh hstopQ (fun m hm' hne C hC => by
    have hXm := SA.anc_ghost (score := SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
      (eligible := SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s) hTp m hXt
    have hmt : SA.ghost sp (Φp.viableTree Φp.tree)
        (SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
        (SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s) m X ∈ Φp.tree := by
      rcases eq_or_ne X (SA.ghost sp (Φp.viableTree Φp.tree)
        (SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
        (SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s) m X) with he | he
      · exact he ▸ hXt
      · exact (Anc.mem hXm he).2
    have hmQ : Φp.Anc
        (SA.ghost sp (Φp.viableTree Φp.tree)
          (SA.goldfishScore sp Φp (SA.View.ofLists pay) s)
          (SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) s) m X) d.head := by
      have hend := hgh
      rw [show f = m + (f - m) by omega, SA.ghost_add] at hend
      exact hend ▸ SA.anc_ghost hTp (f - m) hmt
    exact hsuffix _ C (hstartX.trans hXm) hmQ hne ((haX.mono hΦyU).trans (hXm.mono hΦpU)) hC)
    hstep hstop
  have hvoter : SA.WalkEnd (sp := sp) (Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
      (SA.goldfishScore sp Φy (SA.mergedVoteView sp R Φy (s + 1)) s)
      (SA.goldfishEligible sp Φy tj (SA.mergedVoteView sp R Φy (s + 1)) s)
      (SA.getAnchor sp R Φy tj)
      (SA.getHead sp R Φy tj (Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
        (SA.mergedVoteView sp R Φy (s + 1)) s) :=
    SA.walkEnd_ghost hΦy.coherent hTy (hΦy.finite.subset hTy)
      (Set.ncard_le_ncard hTy hΦy.finite) _
  exact (hvoter.of_anc hΦy.coherent hTy haX hXE).unique
    (SA.walkEnd_iff.2 ⟨f + 1, hfollow, hstop⟩)

/-- **A voter anchor below the proposal reaches the proposer's walk.** The proposer's walk in
`Φp` runs from `d.start` (above `Φp.fcRoot`) to `d.head`, the parent of `P ∈ Φy.tree`; both frames
lie in a coherent `U`. If the voter's anchor is below `P` in `U`, then either it is `P`, or some
`X` on the proposer's walk lies on the voter's walk between its anchor and its head: `d.start`
when the anchor is below it (given `hprefix`), the anchor itself otherwise. -/
theorem anchor_on_proposal_path {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hU : Coherent U) {Φp Φy : SA.Frm sp.n (List (FG.Att sp.n))} (hΦp : FrameOK Φp)
    (hΦpU : Φp.tree ⊆ U) (hΦy : FrameOK Φy) (hΦyU : Φy.tree ⊆ U) {R : SA.SAState sp.n}
    {ti tj : Time} {s : Nat}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hwalk : d.start ∈ Φp.tree ∧ Φp.Anc Φp.fcRoot d.start ∧
      SA.WalkEnd (sp := sp) (Φp.viableTree Φp.tree)
        (SA.goldfishScore sp Φp (SA.View.ofLists pay) ((sp.slot ti : Int) - 1))
        (SA.goldfishEligible sp Φp ti (SA.View.ofLists pay) ((sp.slot ti : Int) - 1))
        d.start d.head)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPy : P ∈ Φy.tree)
    (hparent : P.parent = some d.head.root) (haP : Anc U (SA.getAnchor sp R Φy tj) P)
    (hprefix : Φy.Anc (SA.getAnchor sp R Φy tj) d.start →
      Φy.Anc d.start (SA.getHead sp R Φy tj (Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
        (SA.mergedVoteView sp R Φy (s + 1)) s)) :
    SA.getAnchor sp R Φy tj = P ∨ ∃ X, Φp.Anc d.start X ∧ Φp.Anc X d.head ∧
      Φy.Anc (SA.getAnchor sp R Φy tj) X ∧
      Φy.Anc X (SA.getHead sp R Φy tj (Φy.viableTree (SA.voterBlockTree sp R Φy (s + 1)))
        (SA.mergedVoteView sp R Φy (s + 1)) s) := by
  obtain ⟨hst, hroot, hw⟩ := hwalk
  have hstartQ := hw.anc (fun X hX => hX.1) hst
  have hQt : d.head ∈ Φp.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hstartQ he).2
  have hQP : Anc U d.head P := .single ⟨hΦpU hQt, hΦyU hPy, hparent⟩
  let A := SA.getAnchor sp R Φy tj
  have hAt : A ∈ Φy.tree := by
    by_cases he : Φy.fcRoot = A
    · exact he ▸ hΦy.fcRoot_mem
    · exact (Anc.mem (SA.fcRoot_anc_getAnchor hΦy R tj) he).2
  by_cases he : A = P
  · exact Or.inl he
  right
  have hAQ : Anc U A d.head := by
    rcases Relation.ReflTransGen.cases_tail haP with heq | ⟨Y, hAY, hYP⟩
    · exact (he heq.symm).elim
    have hYQ : Y = d.head := hU.1 hYP.1 (hΦpU hQt)
      (Option.some.inj (hYP.2.2.symm.trans hparent))
    exact hYQ ▸ hAY
  rcases Anc.total hU hAQ (Anc.mono hΦpU hstartQ) with hAS | hSA
  · have hSt := SA.frame_mem_of_between sp hU hΦy hΦyU hPy
      ((Anc.mono hΦpU hstartQ).trans hQP)
      ((Anc.mono hΦyU (hΦy.F_anc_fcRoot.trans (SA.fcRoot_anc_getAnchor hΦy R tj))).trans hAS)
    have hASf := SA.anc_tree_of_anc_U hU hΦy hΦyU hAt hAS hSt
    exact ⟨d.start, .refl, hstartQ, hASf, hprefix hASf⟩
  · have hApt := SA.frame_mem_of_between sp hU hΦp hΦpU hQt hAQ
      ((Anc.mono hΦpU (hΦp.F_anc_fcRoot.trans hroot)).trans hSA)
    refine ⟨A, SA.anc_tree_of_anc_U hU hΦp hΦpU hst hSA hApt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hApt hAQ hQt, .refl, ?_⟩
    unfold SA.getHead
    exact SA.anc_ghost (fun X hX => hX.1.1) _ hAt

end Consensus.Goldilocks.Healing

end

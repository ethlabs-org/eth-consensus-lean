module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeFrozen
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd

public section

/-! # Goldilocks Healing, HS.3: the suffix of the proposal walk and the stop at `Q`

`hs234-exact-interface.md` §4 (workbench#12 §3, as `Compose.suffix_agree` and
`Compose.stop_at_parent`), in the settled phase of `AgreeSetting`: at every block `X ≠ Q` of the
proposal walk at or above an honest slot-`s` voter's anchor, the proposer's best child is the
voter's best child (`proposal_suffix`); and `P` is the voter's only eligible child of
`Q = P.parent` (`proposal_only_child`). Their pieces:

* `winner_voter_tree` (proved): the proposer's best child `C` at `X` is on the walk below `Q`,
  so an ancestor of `P`, in the voter's viable voter block tree (`P` is,
  `proposal_frozen_viable`, and `fc_root ⪯ anchor ⪯ X ⪯ C`);
* `suffix_reflect` (open): a child `B ≠ P` of a block of the walk in the voter's viable voter
  block tree is in the proposer's viable tree (received before the freeze and relayed to the
  proposer by `t_s`, or below `Q`; a viable head at or above it at the proposer, aligned readers);
* `suffix_viable_iff` (open): a block of both trees is a viable head of the voter exactly when it
  is one of the proposer (aligned readers, `viableHeads_iff`, `effAllowed_transfer`);
* `suffix_views_agree` (open): the proposal's view and the voter's merged view have the same
  equivocators and voters, and the same supporters for every block of both trees;
* `proposal_head_viableHead` (open): `Q` is a viable head of the proposer
  (`proposal_head_viable`, as in `proposal_frozen_viable`).

When `X` is a proposer viable head, `C` (of a slot below `s`) is eligible there by a strict
majority only, so the best child carries over (`SA.isBest_transfer`); otherwise `X` is a viable
head of neither frame and every child of `X` is eligible in both (`SA.isBest_transfer_low`). At
`Q`, an old child eligible at the voter would be eligible at the proposer (`Q` a viable head of
both, the same majorities), whose walk stopped at `Q`; then `SA.stop_core`. Model check of the
literal statements and of the routes: sa-fg-model b843308 (`hs3_leaf_checks`), 244,689 and
352,012 checks, no failure. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF w : Time} {i₀ i m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))} {p : Fin sp.n} {kP s : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {iP : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}

/-! ### The proposal walk -/

/-- The duty head of a proposal is the walk of the full viable tree from its start, with the
payload's view; the start is the anchor of the unlocked state. -/
private theorem acProposal_spec {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    (∃ A₁ : SA.SAState sp.n, d.start = SA.getAnchor sp A₁ Φ t) ∧
      d.head = SA.ghost sp (Φ.viableTree Φ.tree)
        (SA.goldfishScore sp Φ (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
        (SA.goldfishEligible sp Φ t (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
        Φ.tree.ncard d.start := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨⟨_, rfl⟩, rfl⟩

/-- **The proposal walk stops at `Q`**: the walk of the proposer's viable tree from `d.start`
ends at `d.head`, and `d.start` is in the frame tree. -/
private theorem proposal_walkEnd (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay) :
    d.start ∈ ℓp.frame.tree ∧
      SA.WalkEnd (sp := sp) (ℓp.frame.viableTree ℓp.frame.tree)
        (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        (SA.goldfishEligible sp ℓp.frame (tr.time iP) (SA.View.ofLists pay) ((s : Int) - 1))
        d.start d.head := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hS.run hS.shared.noColl).localRun
  have hΦ := (SA.frameIn_of_callAt hr hS.ready.1 hS.call).1
  have hslot : sp.slot (tr.time iP) = s := by
    rw [hS.time]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  obtain ⟨⟨A₁, hst⟩, hhd⟩ := acProposal_spec hS.payload
  rw [hslot] at hhd
  have hT : ℓp.frame.viableTree ℓp.frame.tree ⊆ ℓp.frame.tree := fun _ h => h.1
  have hst' : d.start ∈ ℓp.frame.tree := by
    have h := SA.fcRoot_anc_getAnchor hΦ A₁ (tr.time iP)
    rw [← hst] at h
    rcases eq_or_ne ℓp.frame.fcRoot d.start with he | he
    · exact he ▸ hΦ.fcRoot_mem
    · exact (Anc.mem h he).2
  refine ⟨hst', ?_⟩
  rw [hhd]
  exact SA.walkEnd_ghost hΦ.coherent hT (hΦ.finite.subset hT) (Set.ncard_le_ncard hT hΦ.finite) _

/-! ### The leaves -/

section Leaves

variable (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
  {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)

include hS

/-- **`Q` is a viable head of the proposer** (`proposal_head_viable`: the proposal walk starts
in the viable tree; as in `proposal_frozen_viable`; open). -/
private theorem proposal_head_viableHead : d.head ∈ ℓp.frame.viableHeads := by
  sorry

include hy hcy hes

/-- **Viable heads agree** on the blocks of both trees (aligned readers in the settled phase,
`viableHeads_iff`, `effAllowed_transfer`; open). -/
private theorem suffix_viable_iff {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXp : X ∈ ℓp.frame.tree) (hXy : X ∈ ℓy.frame.tree) :
    X ∈ ℓy.frame.viableHeads ↔ X ∈ ℓp.frame.viableHeads := by
  sorry

/-- **Competitors reflect**: a child `B ≠ P` of a block `X ⪯ Q` of the proposer's tree in the
voter's viable voter block tree is in the proposer's viable tree (open). -/
private theorem suffix_reflect {X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hXQ : ℓp.frame.Anc X d.head) (hBX : B.parent = some X.root) (hBP : B ≠ P)
    (hB : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s)) :
    B ∈ ℓp.frame.viableTree ℓp.frame.tree := by
  sorry

/-- **The views agree**: the proposal's view and the voter's merged view have the same
equivocators and voters, and the same supporters for every block of both trees (open). -/
private theorem suffix_views_agree :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint ℓy.frame s).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓy.frame.tree →
        SA.supporters ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) X =
          SA.supporters ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)
            X := by
  sorry

/-- The scores of the blocks of both trees agree. -/
private theorem suffix_scores {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBp : B ∈ ℓp.frame.tree) (hBy : B ∈ ℓy.frame.tree) :
    SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B =
      SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) B := by
  obtain ⟨heq, -, hsup⟩ := suffix_views_agree hS hy hcy hes
  simp only [SA.goldfishScore, heq, hsup B hBp hBy]

end Leaves

/-! ### The suffix and the stop -/

/-- **The suffix** (`hs234-exact-interface.md` §4, "restrict score comparison to a branching
vertex `A` on `P`'s parent path above both roots"; workbench#12 §3, as `Compose.suffix_agree`):
at every block `X` from `D` (on the proposal walk) to `Q`, `Q` excluded, at or above the
voter's anchor (so above both roots), the proposer's best child is the voter's best child: the
votes admitted in the voter view are the carried proposer view up to cap alternatives (the
payload carries the proposer's pool; the voter's pre-freeze votes and support heads relay to the
proposer by `t_s`), and a competing child viable at the voter has a pre-freeze allowed witness,
at the proposer too (aligned readers, HS.1). Only the winner is compared (a voter-eligible
competitor need not be proposer-eligible in reachable runs, sa-fg-model 7f7e660). -/
theorem proposal_suffix (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (_hDQ : ℓp.frame.Anc D d.head) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ≠ d.head →
      Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time iP) (SA.View.ofLists pay)
              ((s : Int) - 1) B} C →
        SA.IsBest sp (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
            ((s : Int) - 1))
          {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
            B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
              (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  intro X hDX hXQ hne hanc C hC
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hS.run hS.shared.noColl).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hS.ready.1 hS.call
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  obtain ⟨hst, hw⟩ := proposal_walkEnd hS
  have hT : ℓp.frame.viableTree ℓp.frame.tree ⊆ ℓp.frame.tree := fun _ h => h.1
  have hQt : d.head ∈ ℓp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc hT hst) he).2
  have hXt : X ∈ ℓp.frame.tree := SA.mem_of_anc hXQ hQt
  -- the winner is the walk's next step, below `Q`
  have hCQ : ℓp.frame.Anc C d.head := by
    obtain ⟨f, hf, -⟩ := SA.walkEnd_iff.1 (hw.of_anc hΦp.coherent hT (hsD.trans hDX) hXQ)
    cases f with
    | zero => exact absurd hf hne
    | succ f =>
      rw [show f + 1 = 1 + f by omega, SA.ghost_add, SA.ghost_succ_of_best 0 X hC] at hf
      exact hf ▸ SA.anc_ghost hT f (hT hC.1.1)
  obtain ⟨⟨hCp, -⟩, hCX, -⟩ := hC.1
  have hPv := proposal_frozen_viable hS hy hcy hes
  have hPU : P ∈ tr.HonestBlocks H := hΦyU hPv.1.1
  have hQP : Anc (tr.HonestBlocks H) d.head P := .single ⟨hΦpU hQt, hPU, hS.parent⟩
  have hCs : C.slot < s := by
    have h1 := (Anc.slot_le hΦp.coherent hCQ).1
    have h2 := hU.2 d.head (hΦpU hQt) P hPU hS.parent
    omega
  -- the winner is in the voter's viable voter block tree
  have hCP : Anc (tr.HonestBlocks H) C P := (hCQ.mono hΦpU).trans hQP
  have hXC : Anc (tr.HonestBlocks H) X C := .single ⟨hΦpU hXt, hΦpU hCp, hCX⟩
  have hfC : Anc (tr.HonestBlocks H) ℓy.frame.fcRoot C :=
    ((SA.fcRoot_anc_getAnchor hΦy e.readPoint (tr.time j)).mono hΦyU).trans (hanc.trans hXC)
  have hCt : C ∈ ℓy.frame.tree := SA.frame_mem_of_between sp hU hΦy hΦyU hPv.1.1 hCP
    ((hΦy.F_anc_fcRoot.mono hΦyU).trans hfC)
  have hCPy : ℓy.frame.Anc C P := SA.anc_tree_of_anc_U hU hΦy hΦyU hCt hCP hPv.1.1
  obtain ⟨⟨-, hPvt⟩, -, W, hW, hWv, hPW⟩ := hPv
  have hCy : C ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
    refine ⟨⟨hCt, Or.inr ?_⟩, SA.anc_tree_of_anc_U hU hΦy hΦyU hΦy.fcRoot_mem hfC hCt, W, hW,
      hWv, hCPy.trans hPW⟩
    rcases hPvt with h | ⟨P', hP', hP's, hPP'⟩
    · exact ⟨P, (proposal_frozen_viable hS hy hcy hes).1.1, hPs, hCPy⟩
    · exact ⟨P', hP', hP's, hCPy.trans hPP'⟩
  have hXy : X ∈ ℓy.frame.tree := SA.mem_of_anc
    (SA.anc_tree_of_anc_U hU hΦy hΦyU
      (SA.frame_mem_of_between sp hU hΦy hΦyU hCt hXC
        ((hΦy.F_anc_fcRoot.mono hΦyU).trans
          (((SA.fcRoot_anc_getAnchor hΦy e.readPoint (tr.time j)).mono hΦyU).trans hanc)))
      hXC hCt) hCt
  -- competitors reflect; scores and voters agree
  have hrefl : ∀ B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s),
      B.parent = some X.root → B ∈ ℓp.frame.viableTree ℓp.frame.tree := fun B hB hBX =>
    suffix_reflect hS hy hcy hes hXQ hBX (by
      rintro rfl
      exact hne (hΦp.coherent.1 hXt hQt (Option.some_injective _ (hBX.symm.trans hS.parent))))
      hB
  have hsc := fun B hBp hBy => suffix_scores hS hy hcy hes (B := B) hBp hBy
  by_cases hXv : X ∈ ℓp.frame.viableHeads
  · have hslot : sp.slot (tr.time iP) = s := by
      rw [hS.time]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
    exact SA.isBest_transfer hXv (by omega) (suffix_views_agree hS hy hcy hes).2.1 hsc hT
      (fun B hB => hB.1.1) hCy hrefl hC
  · have hXv' : X ∉ ℓy.frame.viableHeads := fun h =>
      hXv ((suffix_viable_iff hS hy hcy hes hXt hXy).1 h)
    refine SA.isBest_transfer_low (fun W hW hr => hXv ?_) (fun W hW hr => hXv' ?_) hsc hT
      (fun B hB => hB.1.1) hCy hrefl hC
    · rwa [hΦp.coherent.1 (hΦp.viableHeads_subset hW) hXt hr] at hW
    · rwa [hΦy.coherent.1 (hΦy.viableHeads_subset hW) hXy hr] at hW

/-- **`P` is the voter's only eligible child of `Q`** (`hs234-exact-interface.md` §4, "`P` is the
unique honest current-slot child"; workbench#12 §3): another child of `Q` in the viable voter
block tree is of an earlier slot (one block per honest proposer and slot, `SA.stop_core`), in the
proposer's viable tree (`suffix_reflect`); its voter eligibility (no current-slot arm, `Q` a
viable head of both frames, the same majorities) would make it eligible at the proposer, whose
walk stopped at `Q`. -/
theorem proposal_only_child (hS : AgreeSetting dg H tr g ΔF w i₀ i m c p kP s P iP ℓp d pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = s) :
    ∀ B ∈ {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B}, B = P := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr hS.run hS.shared.noColl
  have hr := hac.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hS.ready.1 hS.call
  obtain ⟨hΦy, hΦyU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hPs : P.slot = s := hS.ready.2.2.2.2.1
  have hpH : P.proposer ∈ H := hS.ready.2.2.2.1.2.1 ▸ hS.ready.1
  have hPv := proposal_frozen_viable hS hy hcy hes
  obtain ⟨hst, hw⟩ := proposal_walkEnd hS
  have hT : ℓp.frame.viableTree ℓp.frame.tree ⊆ ℓp.frame.tree := fun _ h => h.1
  have hQt : d.head ∈ ℓp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc hT hst) he).2
  have hPU : P ∈ tr.HonestBlocks H := hΦyU hPv.1.1
  obtain ⟨-, hstop⟩ := SA.walkEnd_iff.1 hw |>.choose_spec
  have hng : ∀ B ∈ ℓy.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hBp hg
    rw [Compose.honest_eq_genesis hS.run hU (hΦyU hB) hg] at hBp
    exact hBp rfl
  refine (SA.stop_core hac hy hcy hes hPs hS.parent hpH hng hPv ?_).1.2
  intro B hB hBQ hBs hel
  have hBP : B ≠ P := fun h => by rw [h] at hBs; omega
  have hBt : B ∈ ℓy.frame.tree := hB.1.1
  -- `Q` is in the voter's tree (the parent of `B`, which is not `Φ.F`), a viable head there
  have hQy : d.head ∈ ℓy.frame.tree := by
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦy.rooted.2 B hBt) with hFB | ⟨q, -, hq⟩
    · exfalso
      have hBPy : ℓy.frame.Anc B P := hFB ▸ hΦy.rooted.2 P hPv.1.1
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hBPy with h | ⟨q, hBq, hq⟩
      · exact hBP h.symm
      · obtain rfl : q = d.head := hU.1 (hΦyU hq.1) (hΦpU hQt)
          (Option.some_injective _ (hq.2.2.symm.trans hS.parent))
        have h1 := (Anc.slot_le hΦy.coherent hBq).1
        have h2 := hΦy.coherent.2 _ hq.1 B hBt hBQ
        omega
    · obtain rfl : q = d.head := hU.1 (hΦyU hq.1) (hΦpU hQt)
        (Option.some_injective _ (hq.2.2.symm.trans hBQ))
      exact hq.1
  have hQvy : d.head ∈ ℓy.frame.viableHeads :=
    (suffix_viable_iff hS hy hcy hes hQt hQy).2 (proposal_head_viableHead hS)
  have hBp := suffix_reflect hS hy hcy hes .refl hBQ hBP hB
  have hsc := suffix_scores hS hy hcy hes hBp.1 hBt
  have hsj : sp.slot (tr.time j) = s := (SA.castAt_spec hr hy hcy).2.1.symm.trans hes
  have help : SA.goldfishEligible sp ℓp.frame (tr.time iP) (SA.View.ofLists pay)
      ((s : Int) - 1) B := by
    rcases hel with h | h | h
    · exact absurd ⟨d.head, hQvy, hBQ⟩ h
    · have h' : B.slot = s := by rw [← hsj]; exact h
      omega
    · refine Or.inr (Or.inr ?_)
      rw [(suffix_views_agree hS hy hcy hes).2.1, ← hsc]
      exact h
  exact hstop (SA.exists_isBest hΦp (S := {C | C ∈ ℓp.frame.viableTree ℓp.frame.tree ∧
    C.parent = some d.head.root ∧ SA.goldfishEligible sp ℓp.frame (tr.time iP)
      (SA.View.ofLists pay) ((s : Int) - 1) C}) (fun C hC => hT hC.1) ⟨B, hBp, hBQ, help⟩ _)

end Consensus.Goldilocks.Healing

end

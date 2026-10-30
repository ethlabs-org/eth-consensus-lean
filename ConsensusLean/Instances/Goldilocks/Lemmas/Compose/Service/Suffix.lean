module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks under `Sleepy`: the suffix of the proposal walk (open)

workbench#12 §3: on the proposal walk from the pivot `D` to `Q = P.parent`, at every block at or
above a voter's anchor, the proposer's best child is the voter's best child. Its pieces:

* `winner_on_path` (proved): the proposer's best child `C` at a block `X ≠ Q` of the walk is on
  the walk, below `Q`;
* `winner_voter_tree` (open): `C`, an ancestor of `P`, is in the voter's viable voter block tree;
* `competitor_reflect` (open): every child of `X` in the voter's viable voter block tree is in
  the proposer's viable tree (frozen before the vote freeze, so relayed to the proposer by `t_s`,
  and viable there: heights do not decrease along ancestry and `X` is a proposer viable head);
* `proposal_views_agree` (open, `Service/SuffixViews`): the two views have the same
  equivocators and voters, and the same supporters for every block of both trees (`view_agree`,
  with the Sleepy relay).

With `X` a proposer viable head (`hviab`) and `C` of a slot below `s`, `C` is proposer-eligible
only by a strict majority, so it is voter-eligible by the same majority
(`proposal_views_agree`); a competitor the proposer does not count has no majority, so its score
is below `C`'s. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

section Leaves

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
  (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
  {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
  (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
  {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
  {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
  {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
  (hDQ : ℓp.frame.Anc D d.head)
  (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s)

include hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hviab hy hcy hes

/-- **The winner is in the voter's tree**: a child `C` of a block `X` of the suffix that is an
ancestor of `Q` (so of `P`) is in the voter's viable voter block tree. -/
private theorem winner_voter_tree {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDX : ℓp.frame.Anc D X) (hXQ : ℓp.frame.Anc X d.head)
    (hanc : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X)
    (hCX : C.parent = some X.root) (hCp : C ∈ ℓp.frame.tree) (hCQ : ℓp.frame.Anc C d.head) :
    C ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) := by
  sorry

/-- **Competitors reflect**: a child of a block `X` of the suffix in the voter's viable voter
block tree is in the proposer's viable tree. -/
private theorem competitor_reflect {X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDX : ℓp.frame.Anc D X) (hXQ : ℓp.frame.Anc X d.head)
    (hanc : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X)
    (hBX : B.parent = some X.root)
    (hB : B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s)) :
    B ∈ ℓp.frame.viableTree ℓp.frame.tree := by
  sorry

omit hsl hP hPs hpj hcall hy hcy hes in
/-- **The winner is on the walk**: the proposer's best child at a block `X ≠ Q` of the suffix
is an ancestor of `Q`. -/
private theorem winner_on_path {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDX : ℓp.frame.Anc D X) (hXQ : ℓp.frame.Anc X d.head) (hne : X ≠ d.head)
    (hC : SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
      {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1) B} C) :
    ℓp.frame.Anc C d.head := by
  obtain ⟨hΦ, -⟩ := SA.frameIn_of_callAt
    (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun hp hc
  have hslot : sp.slot (tr.time i) = s := by
    rw [hti]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  set T := ℓp.frame.viableTree ℓp.frame.tree
  have hT : T ⊆ ℓp.frame.tree := fun B hB => hB.1
  have hhead : d.head = SA.ghost sp T
      (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
      (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1))
      ℓp.frame.tree.ncard d.start := by
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot]
    rfl
  have hw := SA.walkEnd_ghost (sc := SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay)
      ((s : Int) - 1)) (el := SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
      ((s : Int) - 1)) hΦ.coherent hT (hΦ.finite.subset hT) (Set.ncard_le_ncard hT hΦ.finite)
    d.start
  rw [← hhead] at hw
  obtain ⟨f, hf, -⟩ := SA.walkEnd_iff.1 (hw.of_anc hΦ.coherent hT (hsD.trans hDX) hXQ)
  cases f with
  | zero => exact absurd hf hne
  | succ f =>
    have h1 : SA.ghost sp T (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
        (SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay) ((s : Int) - 1)) 1
        X = C := SA.ghost_succ_of_best 0 X hC
    rw [show f + 1 = 1 + f by omega, SA.ghost_add, h1] at hf
    exact hf ▸ SA.anc_ghost hT f (hT hC.1.1)

end Leaves

/-- **The suffix** (workbench#12 §3; over the leaves above): at every block `X` from the pivot `D`
to `Q` (in the proposer's tree) at or above the voter's anchor, the proposer's best child is the
voter's best child. Only the winner is compared: in reachable runs (sa-fg-model 7f7e660) a
voter-eligible competitor need not be proposer-eligible (the frame moves between the proposal read
and the vote, e.g. `Σ.F` rises to `X` when the node accepts `P`, and every child of `X` becomes
eligible), and competitor scores differ between the views; below the voter's anchor the proposer's
best child can be outside the voter's viable tree. The model finds the voter's winner score strictly
above every competitor's in all of these cases. -/
theorem suffix_agree {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : ℓp.frame.Anc d.start D)
    (hDQ : ℓp.frame.Anc D d.head)
    (hviab : ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = s) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head →
      Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X →
      X ≠ d.head →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ ℓp.frame.viableTree ℓp.frame.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
              ((s : Int) - 1) B} C →
        SA.IsBest sp (SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
            ((s : Int) - 1))
          {B | B ∈ ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame s) ∧
            B.parent = some X.root ∧ SA.goldfishEligible sp ℓy.frame (tr.time j)
              (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1) B} C := by
  intro X hDX hXQ hanc hne C hC
  obtain ⟨heq, hvot, hsup⟩ :=
    proposal_views_agree hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hy hcy hes
  have hCQ := winner_on_path hrun hnc hp hc hd hti hPQ hsD hDQ hviab hDX hXQ hne hC
  obtain ⟨⟨hCp, -⟩, hCX, hCel⟩ := hC.1
  have hCy := winner_voter_tree hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hviab hy
    hcy hes hDX hXQ hanc hCX hCp hCQ
  -- the scores of the blocks of both trees agree
  have hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓy.frame.tree →
      SA.goldfishScore sp ℓy.frame (SA.mergedVoteView sp e.readPoint ℓy.frame s)
          ((s : Int) - 1) B =
        SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) B := by
    intro B hBp hBy
    simp only [SA.goldfishScore, heq, hsup B hBp hBy]
  -- `C` is proposer-eligible by a strict majority only
  have hCs : C.slot < s := by
    have hle := (Anc.slot_le (SA.frameIn_of_callAt
      (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun hp hc).1.coherent hCQ).1
    have := proposal_head_slot_lt hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ
    omega
  have hslot : sp.slot (tr.time i) = s := by
    rw [hti]; exact SA.slot_of_mem sp s le_rfl ((SA.ts_lt_iff sp).2 (by push_cast; omega))
  have hmaj : (SA.voters (SA.View.ofLists pay).votes).ncard <
      2 * SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) C := by
    rcases hCel with h | h | h
    · exact absurd ⟨X, hviab X hDX hXQ, hCX⟩ h
    · rw [hslot] at h; omega
    · exact h
  have hCyt : C ∈ ℓy.frame.tree := hCy.1.1
  refine ⟨⟨hCy, hCX, Or.inr (Or.inr ?_)⟩, fun B hB hBC => ?_⟩
  · rw [← hvot, hsc C hCp hCyt]; exact hmaj
  have hBp := competitor_reflect hrun hnc hsl hp hP hPs hpj hc hcall hd hti hPQ hsD hDQ hviab hy hcy
    hes hDX hXQ hanc hB.2.1 hB.1
  rw [hsc B hBp.1 hB.1.1.1, hsc C hCp hCyt]
  by_cases hel : SA.goldfishEligible sp ℓp.frame (tr.time i) (SA.View.ofLists pay)
    ((s : Int) - 1) B
  · exact hC.2 B ⟨hBp, hB.2.1, hel⟩ hBC
  · left
    have : ¬ (SA.voters (SA.View.ofLists pay).votes).ncard <
        2 * SA.goldfishScore sp ℓp.frame (SA.View.ofLists pay) ((s : Int) - 1) B :=
      fun h => hel (Or.inr (Or.inr h))
    omega

end Consensus.Goldilocks.Compose

end

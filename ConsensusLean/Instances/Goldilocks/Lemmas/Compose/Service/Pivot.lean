module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the pivot of an honest proposal

For the honest proposal `P` of slot `s`, made from `ac_proposal`'s duty
head `Q = P.parent`, a block `D` on the proposal walk (between its start and `Q`) such that every
honest slot-`s` voter whose earlier honest slot-`s` votes are `P` (the caller's strong induction on
the cut) has a walk that passes a block `X` of the path from `D` through `Q` to `P`: `X` is `P`,
or between `D` and `Q` in the proposer's tree.

`D` is the deepest block of the proposal walk among its start and the *old origins* (`OldOrigin`:
the regular origins of labels at most `s − 2` and the optimistic origins of labels at most
`s − 1`, the events before `t_s`); it is genesis or an old origin, and every old origin is below
it. At a voter, the anchor is `fc_root` or a live lock block. `fc_root` and a lock of a slot other
than `s` sit below an old origin (`lock_origin`, the slot of an origin before the vote), hence
below `D`; a lock of slot `s` sits below an optimistic selection with an honest supporter among
the earlier slot-`s` votes, which are `P`. So the anchor is below `D` (then `X = D`, which the
vote extends by S2, `SleepyInvariantUpTo.vote_extends`), or on `P`'s chain above `D` (then `X` is
the anchor).

The proposal walk passes every old origin (`proposal_walk_passes_old_before`, `SA.anc_getHead`): the
proposer holds it or has it below `Σ.F` (`proposal_holds_old`: an honest supporting head is
relayed to the proposer, `proposer_relay_before`), and the children towards it win the walk
(`proposal_best_toward_old_before`, the counts: the honest slot-`(s−1)` batch, or the `3n/4`
votes of an optimistic origin of label `s − 1`, relayed into the proposer's pool and resolved).
Its anchor is below one (`proposal_anchor_old_of`): no honest optimistic check of slot `s` precedes
the proposal (`proposal_no_optimistic`, so the proposer's stored locks are of slots below `s`),
and `fc_root` is below an old origin at the proposal and at a vote (`proposal_fcRoot_old_of`,
`vote_fcRoot_old_of`: the source labels of the honest attestations held before `t_s`). The path
from `D` to `Q` is through viable heads of the proposal's frame (`proposal_suffix_viable_of`:
the head height floor is at most the height of `D`, and `fc_root` is below `D`).

The steps are in `Compose/Service/PivotSteps`, imported privately, which the growing-fault pivot
shares; the old origins and the facts below them are in `Compose/Service/PivotBase`, imported
publicly. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ### Over a run -/

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The proposer holds every old origin, or it is below its `Σ.F`**: an
old origin has an honest supporting vote of a slot before `s` (`honest_supporter`), whose head
reaches the proposer when `Σ.F` is below the origin (`proposer_accepts_head_before`); otherwise
`Σ.F`, on the origin chain, is compatible with it (S1) and above it. -/
theorem proposal_holds_old_before (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ O, OldOrigin tr H s O → O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocks H) O ℓp.frame.F := by
  intro O hO
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨m, hm, hOm⟩ := hO.within hrun (hti ▸ hb)
  obtain ⟨x, hx, j, e, hv, _, hes, Hd, hHd, hHdr, hOHd⟩ :=
    honest_supporter_before hrun hnc hb0 hsync hfb hOm
  have hOU : O ∈ tr.HonestBlocks H := by
    by_cases h : O = Hd
    · exact h ▸ hHd
    · exact (Anc.mem hOHd h).1
  have hFc : OnOriginChainWithin tr H ℓp.frame.F b := by
    rw [frame_of_projAC hrun hp hc]
    exact (hinv.caches p hp i (fun k hk => (hrun.time_mono hk.le).trans hb)).1
  rcases OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible
      (hΦU hΦ.rooted.1) hOU hFc
      (onOriginChainWithin_iff.2 (Or.inr ⟨O, m, hOm, .refl⟩)) with hFO | hOF
  · left
    have hHdt := (proposer_accepts_head_before hrun hnc
      hsync.ac hp hc hcall hd hti hb hx hv
      (by omega) hHd hHdr (hFO.trans hOHd)).1
    exact mem_between hU hΦ hΦU hΦ.rooted.1 hHdt hFO hOHd
  · exact Or.inr hOF

/-- **The proposal walk passes every old origin**: the origin is held by the
proposer (or below its `Σ.F`, below the walk's start), so viable or at or below `fc_root`
(`held_origin_viable`); the proposer's live locks sit below origins, compatible with it (S1);
and the children towards it win (`SA.anc_getHead`). -/
theorem proposal_walk_passes_old_before (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hb : tr.time i ≤ b) :
    ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O d.head := by
  intro O hO
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb0)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at hzero
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hib : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hb
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hp hc
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦ hd
  obtain ⟨A₁, hA₁, -, hhd⟩ := acProposal_walk hd
  obtain ⟨m, _, hOm⟩ := hO.within hrun (hti ▸ hb)
  rcases proposal_holds_old_before hrun hnc hb0 hsync hfb hinv hp hc hcall hd hti hb O hO with
    hOt | hOF
  swap
  · exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hfr := frame_of_projAC hrun hp hc
  have hviab := held_origin_viable_before hrun hnc hf
    (fun _ => originsBelowUpTo_iff.2 (fun C l D n _ _ hC hD =>
      hinv.origins_compatible C l D n hC hD)) hp i hib
    (fun C m' hC => hinv.origins_compatible O m C m' hOm (hC.within hib)) (hfr ▸ hOt)
  rw [← hfr] at hviab
  have hsl_i : sp.slot (tr.time i) = s := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
  have hbest := proposal_best_toward_old_before hrun hnc hb0 hsync hfb hinv
    hp hc hcall hd hti hb O hO hOt
  rw [← hsl_i] at hbest
  rw [hhd]
  refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A₁ (tr.time i) _ _ (fun _ h => h)
    (fun B hB X hXB => SA.mem_of_anc hXB hB) hviab.symm ?_ hbest)
  intro L hL
  obtain ⟨l, -, O', hO', hLO'⟩ := proposal_lock_below hrun hnc hp hΦ hΦU hA₁ L hL
  rcases hinv.origins_compatible O' l.slot O m (hO'.within hib) hOm with h | h
  · exact Or.inl (hLO'.trans h)
  · exact SA.anc_total hU hLO' h

/-- **The pivot**. For a voter, the earlier honest slot-`s` votes are
assumed to be `P` (the caller's strong induction on the cut: a current-slot optimistic lock of the
voter sits below one of them). -/
theorem pivot_before {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ΔF : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (_hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hc : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts s) (hPQ : P.parent = some d.head.root) (hib : tr.time i ≤ b) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
      ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → tr.time j ≤ b → e.msg.slot = s →
        (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = s →
          e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
            (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have hzero := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb0)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at hzero
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hp hc
  have hs0 : 0 < s := by
    obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, -, -⟩ := hP
    rcases blockCall_cases hrun.toLocalRun hp hcB with hg | ⟨j, x, rfl, -, hPr, d', pay', -, hB, -⟩
    · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
    rw [← hPs, hB]
    exact hPr.1
  -- the proposal walk, from its start to `Q`
  obtain ⟨hstart, hsQ⟩ := acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hpass := proposal_walk_passes_old_before hrun hnc hb0 hsync hfb hinv hp hc hcall hd hti hib
  have hanch := proposal_anchor_old_of hrun hnc hf hp hc hcall hd hti
  -- `D`: the deepest of the start and the old origins on the proposal walk
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦp (S := {X | X ∈ ℓp.frame.tree ∧
      ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head ∧ (X = d.start ∨ OldOrigin tr H s X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦp (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦp.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, OldOrigin tr H s O → Anc (tr.HonestBlocks H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦpU hsQ) with h | h
    · exact h.trans (Anc.mono hΦpU hsD)
    have hOt := mem_between hU hΦp hΦpU hstart hQt h hOQ
    exact Anc.mono hΦpU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦp hΦpU hstart h hOt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hOt hOQ hQt, Or.inr hO⟩)
  -- `D` is genesis or an old origin
  have hDkind : D.root = sp.genesisRoot ∨ OldOrigin tr H s D := by
    rcases hDk with rfl | h
    · rcases hanch with h | ⟨O, hO, hsO⟩
      · exact Or.inl h
      · rw [Anc.antisymm hU hsO (hDold O hO)]
        exact Or.inr hO
    · exact Or.inr h
  refine ⟨D, hsD, hDQ, proposal_suffix_viable_of hrun hnc hf hp hc hcall hd hti hDt hDold,
    fun y hy j ℓy e hcy hjb hes hE => ?_⟩
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hhead
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have hah : ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
        (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) :=
    SA.anc_ghost (fun B hB => (SA.voteDomain_subset_tree hB.1)) _ hat
  have hht := mem_of_anc_left hah hat
  -- the vote's head extends `D` (S2, or genesis)
  have hDh : Anc (tr.HonestBlocks H) D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voteDomain sp e.readPoint ℓy.frame s))
      (SA.mergedVoteView sp e.readPoint ℓy.frame s) ((s : Int) - 1)) := by
    rcases hDkind with hg | hO
    · exact honest_genesis_root_anc hrun hU (hΦpU hDt) hg (hΦU hht)
    obtain ⟨m, hm, hO⟩ := hO.within hrun (hti ▸ hib)
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ :=
      hinv.vote_extends D m hO y hy j e ⟨ℓy, hcy.1, hcy.2⟩ hjb (by omega)
    rwa [hU.1 hHd (hΦU hht) (hHdr.trans hhead)] at hDHd
  rcases vote_anchor_cases_of_old hrun hnc hf hp hP hs0 hPQ
      (hΦpU hQt) (Anc.mono hΦpU hDQ) (hΦpU hDt)
      hDold hy hcy hes hE with haD | ⟨hDa, haP, hPU⟩
  · have hDt' := mem_between hU hΦ hΦU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΦ hΦU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΦ hΦU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := anc_parent hU haP haPe hPQ (hΦpU hQt)
  have hat' := mem_between hU hΦp hΦpU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦp hΦpU hat' haQ hQt⟩, .refl, hah⟩

end Consensus.Goldilocks.Compose

end

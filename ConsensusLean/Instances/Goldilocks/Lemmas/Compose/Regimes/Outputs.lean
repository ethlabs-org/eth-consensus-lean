module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Always
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest

public section

/-! # Goldilocks milestone Regimes: R.8 (the outputs of an honest node)

The three R.8 rows of `Statements/Regimes/Always`, in every Goldilocks run (no `NoColl`):

* `outputs_nested` (C0.1 at every cut): `Σ.F ⪯ ac_confirmed ⪯ ac_head` in the node's tree. The
  frame `fg_to_ac(Σ)` of a reachable FG state is well formed, and at a well-formed frame the
  SA's confirmed tip is the deepest common ancestor of the record and the head, or `Φ.F`.
* `finalized_monotone` (C0.2 over the run): every cut moves `Σ.F` to a descendant in the grown
  tree (`chain_fg`), also at restarts, which keep `Σ`.
* `outputs_valid` (F.2 with the node's checks): every block of an honest tree other than genesis
  was accepted by the node at an earlier cut, so it has its digest as root and its slot's
  proposer, and its parent is held with a smaller slot. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)
open Compose

/-- At a well-formed frame, the SA's confirmed tip and head are blocks of the tree, and the
confirmed tip is an ancestor of the head. -/
theorem sa_tips {sp : SAParams} {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    (hΦ : FrameOK Φ) (t : Time) :
    SA.acConfirmed sp A Φ t ∈ Φ.tree ∧ Φ.Anc (SA.acConfirmed sp A Φ t) (SA.acHead sp A Φ t) := by
  have hH : SA.acHead sp A Φ t ∈ Φ.tree := SA.getHead_mem hΦ (fun _ h => h.1) _ _ _ _
  unfold SA.acConfirmed
  dsimp only
  cases hd : SA.deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X ((SA.lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (SA.acHead sp A Φ t)} with
  | none => exact ⟨hΦ.rooted.1, hΦ.rooted.2 _ hH⟩
  | some D =>
    obtain ⟨hD, -⟩ := SA.deepest_mem hd
    exact ⟨hD.1, hD.2.2⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- The frame of an honest node before a cut is well formed, and its tree is in the node's. -/
private theorem frame_ok (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    FrameOK (Node.frame (tr.state y i)) ∧
      (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree :=
  ⟨(Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1, fun _ hX => hX.1⟩

/-- **R.8, `nested`.** -/
theorem outputs_nested : OutputsNested := by
  intro sp ro dg H tr hrun y hy i
  obtain ⟨hΦ, hsub⟩ := frame_ok hrun hy i
  obtain ⟨hC, hCH⟩ := sa_tips (A := (tr.state y i).ac) hΦ (tr.time i)
  exact ⟨Anc.mono hsub (hΦ.rooted.2 _ hC), Anc.mono hsub hCH⟩

/-- **R.8, `finalMonotone`.** -/
theorem finalized_monotone : FinalizedMonotone := by
  intro sp ro dg H tr hrun y hy i j hij
  induction j, hij using Nat.le_induction with
  | base => exact .refl
  | succ j _ ih =>
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      obtain ⟨-, hT, hF⟩ := chain_fg y (.cons (hrun.cutLaw y hy j c hc) (.nil _))
        (fg_reachable hrun.toLocalRun hy j)
      change (tr.state y (j + 1)).fg.Anc (tr.state y i).fg.F (tr.state y (j + 1)).fg.F
      rw [tr.state_succ_of_call hc]
      exact (Anc.mono hT ih).trans hF
    · change (tr.state y (j + 1)).fg.Anc (tr.state y i).fg.F (tr.state y (j + 1)).fg.F
      rw [tr.state_succ_of_not fun c h => hc ⟨c, h⟩]
      exact ih

/-- Every block of an honest node's tree is a valid output. -/
theorem validOutput_of_mem (hrun : GoldilocksRun dg H tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree) :
    ValidOutput tr dg y i X := by
  have h := hrun.toLocalRun
  refine ⟨hX, fun Z hZX hZg => ?_⟩
  have hZ : Z ∈ (tr.state y i).fg.tree := by
    by_cases he : Z = X
    · exact he ▸ hX
    · exact (Anc.mem hZX he).1
  rcases tree_cases h hy hZ with rfl | ⟨k, hk, hacc⟩
  · exact absurd rfl hZg
  obtain ⟨hro, hpr, -, -⟩ := accept_facts h hy hacc
  obtain ⟨pr, -, hpar, -, hheld, -⟩ := Store.onBlock_eq_some (h.cutLaw y hy k _ hacc).2.1
  obtain ⟨Pz, hPz⟩ := Option.isSome_iff_exists.1 hheld
  have hPzr := (fg_reachable h hy k).blocks_root hPz
  have hPzt : Pz ∈ (tr.state y k).fg.tree := by
    change _ = _
    rw [hPzr, hPz]
  have hPzi := tree_mono h hy hk.le hPzt
  have hp : Z.parent = some Pz.root := by rw [hpar, hPzr]
  exact ⟨hro, ⟨k, hk, hacc⟩, hpr, Pz, hPzi, hp,
    (Store.accepted_tree _ _ _ _ (fg_reachable h hy i)).2.1.2 Pz hPzi Z hZ hp⟩

/-- **R.8, `outputValid`.** -/
theorem outputs_valid : OutputsValid := by
  intro sp ro dg H tr hrun y hy i
  obtain ⟨hΦ, hsub⟩ := frame_ok hrun hy i
  exact ⟨validOutput_of_mem hrun hy
      (Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1,
    validOutput_of_mem hrun hy (hsub (sa_tips (A := (tr.state y i).ac) hΦ (tr.time i)).1)⟩

end Consensus.Goldilocks.Regimes

end

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Always
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest

public section

/-! # Goldilocks Regimes: the outputs of an honest node (R.8 over a fixed honest set)

The run-level facts behind the R.8 rows, in every Goldilocks run (no `NoColl`); the growing rows
(`Lemmas/Growing/Compose/Outputs`) apply them on a retained prefix:

* `outputs_nested_at` (C0.1 at every cut): `Σ.F ⪯ ac_confirmed ⪯ ac_head` in the node's tree. The
  frame `fg_to_ac(Σ)` of a reachable FG state is well formed, and at a well-formed frame the
  AC's confirmed tip is the deepest common ancestor of the record and the head, or `Φ.F`.
* `finalized_monotone_from` (C0.2 over the run): every cut moves `Σ.F` to a descendant in the
  grown tree (`chain_fg`), also at restarts, which keep `Σ`.
* `outputs_valid_at` (F.2 with the node's checks): every block of an honest tree other than
  genesis was accepted by the node at an earlier cut, so it has its digest as root and its slot's
  proposer, and its parent is held with a smaller slot (`validOutput_of_mem`). -/

namespace Consensus.Goldilocks.Regimes

open AC (ACParams Payload)
open Compose

/-- At a well-formed frame, the AC's confirmed tip and head are blocks of the tree, and the
confirmed tip is an ancestor of the head. -/
theorem ac_tips {sp : ACParams} {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    (hΦ : FrameOK Φ) (t : Time) :
    AC.acConfirmed sp A Φ t ∈ Φ.tree ∧ Φ.Anc (AC.acConfirmed sp A Φ t) (AC.acHead sp A Φ t) := by
  have hH : AC.acHead sp A Φ t ∈ Φ.tree := AC.getHead_mem hΦ (fun _ h => h.1) _ _ _ _
  unfold AC.acConfirmed
  dsimp only
  cases hd : AC.deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X ((AC.lookup Φ A.latestConfirmed).getD Φ.F) ∧
      Φ.Anc X (AC.acHead sp A Φ t)} with
  | none => exact ⟨hΦ.rooted.1, hΦ.rooted.2 _ hH⟩
  | some D =>
    obtain ⟨hD, -⟩ := AC.deepest_mem hd
    exact ⟨hD.1, hD.2.2⟩

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- The frame of an honest node before a cut is well formed, and its tree is in the node's. -/
private theorem frame_ok (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    FrameOK (Node.frame (tr.state y i)) ∧
      (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree :=
  ⟨(Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1, fun _ hX => hX.1⟩

/-- **R.8, `nested`**, at a cut of an honest node: the finalized tip is an ancestor of the
confirmed tip, and the confirmed tip of the head, in the node's tree. -/
theorem outputs_nested_at (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) :
    (tr.state y i).fg.Anc (tr.finalizedAt y i) (tr.confirmedAt y i) ∧
      (tr.state y i).fg.Anc (tr.confirmedAt y i) (tr.headAt y i) := by
  obtain ⟨hΦ, hsub⟩ := frame_ok hrun hy i
  obtain ⟨hC, hCH⟩ := ac_tips (A := (tr.state y i).ac) hΦ (tr.time i)
  exact ⟨Anc.mono hsub (hΦ.rooted.2 _ hC), Anc.mono hsub hCH⟩

/-- C0.2 from any start: the proof reads only the cut law and FG reachability. -/
theorem finalized_monotone_from {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H) {i j : Nat}
    (hij : i ≤ j) : (tr.state y j).fg.Anc (tr.finalizedAt y i) (tr.finalizedAt y j) := by
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

/-- Every block of an honest node's tree is a valid output, from any start. -/
theorem validOutput_of_mem {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat}
    {X : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree) :
    ValidOutput tr proposer dg y i X := by
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

/-- **R.8, `outputValid`**, at a cut of an honest node: the finalized and confirmed outputs are
valid outputs of its tree. -/
theorem outputs_valid_at (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) :
    ValidOutput tr proposer dg y i (tr.finalizedAt y i) ∧
      ValidOutput tr proposer dg y i (tr.confirmedAt y i) := by
  obtain ⟨hΦ, hsub⟩ := frame_ok hrun hy i
  exact ⟨validOutput_of_mem hrun hy
      (Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1,
    validOutput_of_mem hrun hy (hsub (ac_tips (A := (tr.state y i).ac) hΦ (tr.time i)).1)⟩

end Consensus.Goldilocks.Regimes

end

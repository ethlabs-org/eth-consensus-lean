module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.SourceLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: source labels and frame viability

The source labels at a vote (`SourceLabels`) bound the origins used by the frame argument.
`Frame` supplies the honest-store geometry and `FrameFrozen` supplies the frozen witness; together
they establish full-read and vote-frame viability (S3 of `SleepyInvariant`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **S3 at full reads, over sources `G`**: with `f < n/2`, the honest attestations at heights
`≥ h_j` sourced by `G`, the sources pairwise compatible and compatible with `B`, a held block `B` is
at or below `fc_root` or in the full viable tree. -/
private theorem held_viable_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  -- the frame
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `fc_root` (`Σ.J` or `Σ.F`) is compatible with `B`
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact J_compatible hrun hnc hf hy hsrc hGB (hsU hBt.1)
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt.1 with hle | ⟨-, E, X, -, -, -, hBE,
    -, hX, hEX, hXv⟩
  · exact ⟨hBt, hΦfB, B, hBt, ⟨hBt.1, hBt.2, Anc.mono hΦs hΦfB, hle⟩, .refl⟩
  · have hBX := hBE.trans hEX
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      SA.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩

/-- `held_origin_viable` with `f < n/2` and the origins whose event precedes the cut pairwise
compatible. -/
private theorem held_origin_viable_of (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (hP : ∀ C s C' s', OriginBefore tr H C s i → OriginBefore tr H C' s' i →
      Compatible (tr.HonestBlocks H) C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ l, OriginBefore tr H C l i) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨m, hm, -, k, hk, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
    obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
    obtain ⟨z, hz, k', hk', CV, h⟩ := originBefore_iff.1 hC
    exact ⟨D, ⟨C, ⟨l, originBefore_iff.2 ⟨z, hz, k', by omega, CV, h⟩⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU (Q := fun C => ∃ l, OriginBefore tr H C l i)
    (fun C C' ⟨l, hC⟩ ⟨l', hC'⟩ => hP C l C' l' hC hC') (fun C ⟨l, hC⟩ => hBc C l hC)
  exact held_viable_of hrun hnc hf hy i (hsrc.above _) hGG hGB hBt

/-- **S3 at full reads**: once all origins compare, a block `B` that an honest node holds before
cut `i` and that is compatible with every origin whose event precedes the cut (an origin itself;
a protected proposal before its update, S3P) is at or below its `fc_root` or in
its full viable tree. -/
theorem held_origin_viable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (hP : ∀ s, OriginsBelow tr H s) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc (two_faults_lt_of_sleepy hsl) hy i
    (fun C l C' l' hC hC' => originsBelow_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) hC.origin hC'.origin) hBc hBt

/-- **S3 at full reads up to `b`**: at a cut within `b`, once the origins within `b` compare, a
block `B` that an honest node holds before the cut and that is compatible with every origin whose
event precedes the cut is at or below its `fc_root` or in its full viable tree. -/
theorem held_origin_viable_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc (two_faults_lt_of_prefix hpre) hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

/-- Full-read viability uses the finite frontier and fault bound, with no service premise. -/
theorem held_origin_viable_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc hf hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

/-- **S3 at votes, over sources `G`, on a window**: at an honest slot-`(s+1)` vote at a time
`≤ b`, with the honest attestations at heights `≥ h_j` sourced by `G` (sources pairwise compatible,
compatible with `B`, each extended by an honest vote of a slot `≤ s`) and the heads accepted
before `t_{s₀}` caught up (`hold`), a block `B` that an honest slot-`s` vote extends is in the
viable tree of the voter block tree, or at or below `fc_root`. -/
private theorem vote_frame_of {s₀ : Nat} {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hservice : SleepyWindow tr H ΔF s₀ b ∨ SleepyServiceBefore tr H ΔF b)
    (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hold : ∀ x ∈ H, ∀ m B, tr.AcceptAt x m B → tr.time m < sp.ts s₀ →
      Anc (tr.HonestBlocks H) ℓ.frame.F B → SA.AcceptedBefore tr.projAC y B (sp.ts s + 3 * sp.Δ))
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    (hGW : ∀ D, G D → ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot ≤ s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg D)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  refine vote_frame_of_witnesses hrun hnc hf hy hc hs hsrc hGG (fun D hD hFD => ?_) hB hGB
    fun hFB => ?_
  · -- the relayed honest head of a vote extending a crossing source
    obtain ⟨x, hx, k, e', hve, hs', hext⟩ := hGW D hD
    exact honest_head_frozen hrun hnc hservice hy hc hs hib hold hx hve hs' hext hFD
  · -- the relayed honest slot-`s` head extending `B`
    obtain ⟨x, hx, k, e', hve, hs', hext⟩ := hw
    exact honest_head_frozen hrun hnc hservice hy hc hs hib hold hx hve hs'.le hext hFB

/-- **S3 at votes up to `b` (the frozen witness)**: at an honest slot-`(s+1)` vote at a time
`≤ b`, a block `B` of the honest blocks that is compatible with every origin within `b` of label
at most `s` and that some honest slot-`s` vote extends is in the viable tree of the voter block
tree, or at or below `fc_root` (inside the honest blocks). -/
theorem vote_frame_upTo {b : Time} (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hpre : SleepyPrefix tr H ΔF b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hf := two_faults_lt_of_prefix hpre
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ j, OriginWithin tr H C j b ∧ j ≤ s) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc hf hy hc hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within hib', hj⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU
    (Q := fun C => ∃ j, OriginWithin tr H C j b ∧ j ≤ s)
    (fun C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩ =>
      originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
    (fun C ⟨j, hC, hj⟩ => hBc C j hC hj)
  refine vote_frame_of hrun hnc (Or.inl hpre.window) hf hy hc hs hib
    (fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m)))
    (hsrc.above _) hGG (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ => ?_) hB hGB
    (let ⟨x, hx, k, e', hv, hs', hext⟩ := hw; ⟨x, hx, k, e', hv, hs', hext⟩)
  obtain ⟨x', hx', k', e'', hve', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
    honest_supporter_upTo hrun hnc hpre hC
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

/-- The frozen witness at a vote needs only recipient service within its finite horizon. -/
theorem vote_frame_before {b : Time} (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hfb : ∀ s : Nat, ∀ d ∈ ({0, sp.Δ, 2 * sp.Δ} : Set Time), sp.ts s + d ≤ b →
      tr.FaultBound H (sp.ts s + d))
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have h := hfb 0 0 (by simp) (by simpa [SAParams.ts] using hb)
    change Hᶜ.ncard < tr.honestAwakeJoined H (sp.ts 0 + 0) at h
    have hle : tr.honestAwakeJoined H (sp.ts 0 + 0) ≤ H.ncard :=
      Set.ncard_le_ncard fun x hx => hx.1
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hib' : ∀ k < i, tr.time k ≤ b := fun k hk => (hrun.time_mono hk.le).trans hib
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ j, OriginWithin tr H C j b ∧ j ≤ s) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc hf hy hc hs hX ha hav
    exact ⟨D, ⟨C, ⟨j, hC.within hib', hj⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU
    (Q := fun C => ∃ j, OriginWithin tr H C j b ∧ j ≤ s)
    (fun C C' ⟨j, hC, hj⟩ ⟨j', hC', hj'⟩ =>
      originsBelowUpTo_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
    (fun C ⟨j, hC, hj⟩ => hBc C j hC hj)
  refine vote_frame_of (s₀ := 0) hrun hnc (Or.inr hsync) hf hy hc hs hib
    (fun _ _ m _ _ hm _ => absurd hm (by rw [ts_natCast_zero]; exact not_lt.2 (hrun.time_nonneg m)))
    (hsrc.above _) hGG (fun D ⟨C, ⟨j, hC, hj⟩, hDC⟩ => ?_) hB hGB hw
  obtain ⟨x', hx', k', e'', hve', -, hs'', Hd, hHd, hHdr, hCHd⟩ :=
    honest_supporter_before hrun hnc hb hsync hfb hC
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.SourceLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: source labels and frame viability

The source labels at a vote (`SourceLabels`) bound the origins used by the frame argument.
`Frame` supplies the honest-store geometry and `FrameFrozen` supplies the frozen witness; together
they establish full-read and vote-frame viability (S3 of `SleepyInvariantUpTo`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **S3 at full reads, over sources `G`**: with `f < n/2`, the honest attestations at heights
`≥ h_j` sourced by `G`, the sources pairwise compatible and compatible with `B`, a held block `B` is
at or below `fc_root` or in the full viable tree. -/
private theorem held_viable_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  exact FrameGeometry.held_viable_of hrun.toLocalRun (projFG_localRun hrun hnc)
    hf hy hsrc.toFrameGeometry hGG hGB hBt

/-- Full-read viability of a held origin, with `f < n/2` and the origins whose event precedes the
cut pairwise compatible. -/
private theorem held_origin_viable_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
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

/-- Full-read viability uses the finite frontier and fault bound, with no service premise. -/
theorem held_origin_viable_before {b : Time} {ini} (hrun : GoldilocksRun proposer dg H tr ini)
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

/-- The frozen witness at a vote needs only recipient service within its finite horizon
(for population-sized committees, `hstock`). -/
theorem vote_frame_before
    {b : Time} (hrun : GoldilocksRun proposer dg H tr)
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
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) (hstock : sp.committeeSize = sp.n) :
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
    obtain ⟨D, -, hDs, C, j, hC, hj, hDC⟩ := vote_row_source hrun hnc _ SA.CommitteeP.full
      (SA.size_binding_full hstock) (SA.cs2_full hstock hf) hy (SA.mem_full _ _) hc hs
      hX ha hav
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
    honest_supporter_before hrun hnc hb hsync hfb hC hstock
  exact ⟨x', hx', k', e'', hve', hs''.trans_le hj, Hd, hHd, hHdr, hDC.trans hCHd⟩

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs

public section

/-! # Frozen optimistic cast prefix supplier -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A viable prefix of an optimistic write is reached at the next-slot cast. -/
theorem optimistic_prefix_before_at
    {g ΔF b : Time} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) {s : Nat} (hm : gbar g ≤ sp.ts s)
    {x y : Fin sp.n} {c i : Nat} (hx : x ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    {D B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hBD : Anc (tr.HonestBlocksAt H) B D)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  sorry

/-- A warm honest proposal is viable at every honest cast of its slot. -/
theorem FrameWindow.proposal_viable_at_cast_at
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame p) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

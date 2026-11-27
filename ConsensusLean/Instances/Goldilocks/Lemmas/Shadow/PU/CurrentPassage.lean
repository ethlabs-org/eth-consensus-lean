module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FollowCast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LockLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.CurrentLock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Current lock passage over the stock window: unresolved interface

The endpoint keeps the stock conclusion. Cast viability and the current-slot provenance
alternative are proved. Older-lock prefix transfer is unresolved: its regular branch awaits
the stock regular-later supplier, and its optimistic branch awaits the shared optimistic
contest residue. The geometric contest-gap dichotomy alone does not prove this transfer.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

section Passage

variable
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    {l : AC.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) (hK : CommitteeHalfUpTo tr H K g b)

include hframe hrun hnc hsvc hawake hf hcatch hnr hm hsp hp0 hpb hz hdes hP hPs
  hy hc hes hmargin hl hlive hB hBr hK

/-- Unresolved older-lock transfer, including the older-optimistic contest residue.
This is not a proved consequence of `contest_gap_residue'`. The regular and optimistic
origin cases must be separated when their shared suppliers become available. -/
theorem older_lock_prefix_transfer_unresolved' (holder : l.slot < p) :
    Anc (tr.HonestBlocksAt H) B P := by
  sorry

/-- Exact stock passage conclusion over the shadow run and stock window.
Unresolved through `older_lock_prefix_transfer_unresolved'`, not a completed proof. -/
theorem current_lock_passage_of_regular_base_at' :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame p) ∧
      (Anc (tr.HonestBlocksAt H) B P ∨
        (l.slot = p ∧ ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
          AC.OptimisticLockAt tr.projAC y a p D CV ∧ sp.ts p ≤ tr.time a ∧
          Anc (tr.HonestBlocksAt H) B D)) := by
  have hm₀ : gbar g ≤ sp.ts s₀ := by linarith [sp.toParams.hΔ]
  obtain ⟨hvP, hdomP⟩ := proposal_viable_at_cast_at' hframe hrun hnc hsvc hf hnr hm₀ hsp hp0
    hpb hz hdes hP hPs hy hc hes
  refine ⟨hvP, hdomP, ?_⟩
  by_cases hcurrent : p ≤ l.slot
  · obtain ⟨hs, a, hai, D, CV, hya, hop, ht, C, hC, hCr, hCD⟩ :=
      Core.current_lock_write_readPoint_at hrun.toCore hnc hy hc (hes ▸ hp0) hl
        (hes ▸ hcurrent)
    have hPhi := hrun.toCore.frameIn_at hnc hy hc.1
    have hcoh := hrun.toCore.coherent hnc
    obtain rfl : C = B := hcoh.1 hC (hPhi.2 hB) (hCr.trans hBr.symm)
    rw [hes] at hs hop ht
    exact Or.inr ⟨hs, a, hai, D, CV, hya, hop, ht, hCD⟩
  · exact Or.inl (older_lock_prefix_transfer_unresolved' hframe hrun hnc hsvc hawake hf
      hcatch hnr hm hsp hp0 hpb hz hdes hP hPs hy hc hes hmargin hl hlive hB hBr hK
      (Nat.lt_of_not_ge hcurrent))

end Passage

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

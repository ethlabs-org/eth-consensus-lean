module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs

public section

/-! # Frozen warm-unanimity and adjacent fresh-lock suppliers

Each voter and update reader is honest at its own cut. The original proposer need only
remain honest through its vote deadline. These are implementation boundaries, not new premises.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Warm frame unanimity at individual honest cast cuts. -/
theorem FrameWindow.honest_vote_heads_eq_at
    {g ΔF b : Time} {s₀ u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts u + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts u + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = u →
      e.msg.head = P.root := by
  sorry

/-- The actual adjacent update and to-FG call retain the proposal's fresh fast lock. -/
theorem fresh_fast_lock_update_toFG_at
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ y, y ∈ H (sp.ts u + sp.Δ) →
      SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ)
      floor kindJ J)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ)) :
    ∃ k ell ell', SA.UpdateAt tr.projAC y k u ell ∧
      tr.projAC.CallAt y (k + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (k + 1) = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P ∧
      SA.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell'.frame.viableAncestor P = P ∧
      P ∈ ell'.frame.viableTree ell'.frame.tree ∧
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post k).locks ∧
        (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.state y (k + 1)).locks := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

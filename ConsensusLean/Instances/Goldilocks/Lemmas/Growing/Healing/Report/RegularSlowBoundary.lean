module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSlow

public section

/-! # The regular slow next-vote supplier

Forwarded to its proof, `KernelProof.regular_slow_next_votes_at` in `Report/RegularSlow`. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The regular slow selection constrains next-slot votes at independently honest cuts. -/
theorem FrameWindow.regular_slow_next_votes_at {s₀ s floor : Nat}
    {kindJ : Prop} {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (hsl : SA.SlowLockAt tr.projAC x c s D) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
  exact KernelProof.regular_slow_next_votes_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hx hsl

end Consensus.Goldilocks.Healing.Growing

end

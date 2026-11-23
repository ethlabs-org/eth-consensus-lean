module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularLater

public section

/-! # Regular-lock following across independently honest cuts

Forwarded to its proof, `KernelProof.regular_later_heads_at` in `Report/RegularLater`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A regular write constrains later votes and actual proposal heads at their own cuts. -/
theorem FrameWindow.regular_later_heads_at
    {g ΔF b : Time} {s₀ s N floor : Nat} {kindJ : Prop}
    {J D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsN : s + 2 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (horigin : (∃ CV, AC.FastUpdateAt tr.projAC x c s D CV) ∨
      AC.SlowLockAt tr.projAC x c s D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) D d.head) := by
  exact KernelProof.regular_later_heads_at hframe hrun hnc hsvc hawake hf hcatch hnr hwarm hpos
    hs₀ hm hsN hmb hx horigin hK

end Consensus.Goldilocks.Healing.Growing

end

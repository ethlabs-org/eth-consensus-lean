module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs

public section

/-! # Frozen regular-lock following across independently honest cuts -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A regular write constrains later votes and actual proposal heads at their own cuts. -/
theorem FrameWindow.regular_later_heads_at
    {g ΔF b : Time} {s₀ s N floor : Nat} {kindJ : Prop}
    {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsN : s + 2 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (horigin : (∃ CV, SA.FastUpdateAt tr.projAC x c s D CV) ∨
      SA.SlowLockAt tr.projAC x c s D) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) D d.head) := by
  sorry

/-- The regular residue of a cast's live lock is below the proposal; only a current
optimistic write remains as a causal alternative. -/
theorem FrameWindow.current_lock_passage_of_regular_base_at
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame p) ∧
      (Anc (tr.HonestBlocksAt H) B P ∨
        (l.slot = p ∧ ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
          SA.OptimisticLockAt tr.projAC y a p D CV ∧ sp.ts p ≤ tr.time a ∧
          Anc (tr.HonestBlocksAt H) B D)) := by
  sorry

/-- A proposal's warm live lock is below its root, followed by prior-slot votes,
or retained from a current optimistic write. -/
theorem FrameWindow.proposal_lock_prefix_cases_at
    {g ΔF b : Time} {s₀ s floor : Nat} {kindJ : Prop}
    {J X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} {i : Nat} (hz : z ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z i ell)
    (hti : tr.time i = sp.ts (s + 1 : Nat))
    {l : SA.Lock} (hl : l ∈ SA.liveLocks sp (tr.projAC.state z i).locks ell.frame (tr.time i))
    (hwarm : s₀ + sp.k ≤ l.slot) (hpos : 0 < l.slot)
    (hpred : s₀ ≤ l.slot - 1) (hold : l.slot < s + 1)
    (hB : B ∈ ell.frame.tree) (hBr : B.root = l.block) (hXB : ell.frame.Anc X B) :
    Anc (tr.HonestBlocksAt H) X ell.frame.fcRoot ∨
      (∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∨
      ∃ a < i, ∃ D CV, z ∈ H (tr.time a) ∧ SA.OptimisticLockAt tr.projAC z a s D CV ∧
        Anc (tr.HonestBlocksAt H) X D := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

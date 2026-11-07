module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs

public section

/-! # Frozen common witness and supporter steps for regular propagation -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Common early-witness induction with the lock-specific transfer supplied by the caller. -/
theorem next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) hi floor kindJ J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      SA.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → SA.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  sorry

/-- Supporter classification separates viable, common-root and optimistic-anchor cases. -/
theorem FrameWindow.next_votes_of_supporter_at {s₀ s floor : Nat}
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {z : Fin sp.n} {q : Nat} (hz : z ∈ H (tr.time q))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC z q ell e) (hes : e.msg.slot = s)
    (hQU : Q ∈ tr.HonestBlocksAt H) (hQr : Q.root = e.msg.head)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : Q ∈ ell.frame.tree → floor ≤ ((tr.state z q).fg.σ Q.root).h →
      (kindJ → Anc (tr.HonestBlocksAt H) J X) →
      ∀ y i ev, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hoptimistic : Q = SA.getAnchor sp e.readPoint ell.frame (tr.time q) →
      ∀ a D CV, z ∈ H (tr.time a) → SA.OptimisticLockAt tr.projAC z a s D CV →
      Anc (tr.HonestBlocksAt H) Q D →
      ∀ y i ev, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocksAt H) ev.msg Q) :
    ∀ y i ev, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) ev.msg X := by
  sorry

/-- An optimistic anchor at an honest supporter propagates to independently honest later calls. -/
theorem FrameWindow.optimistic_supporter_later_heads_at {s₀ s N floor : Nat}
    {kindJ : Prop} {J L D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {i a : Nat} (hx : x ∈ H (tr.time i)) (hxa : x ∈ H (tr.time a))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = SA.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (SA.Vote sp.n)} (hop : SA.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocksAt H) L D) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y j ev, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocksAt H) ev.msg L) ∧
      (∀ y j ell', y ∈ H (tr.time j) → tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) L d.head) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

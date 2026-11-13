module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.WitnessUnanimity

public section

/-! # Arbitrary-prefix unanimity suppliers

Forwarded to their proofs in `WitnessUnanimity`.

The prefix X need not be a proposal or have slot m. A separately held descendant Q
supplies viability; prior votes need only extend X, not agree on a single head.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Prior votes extending an arbitrary prefix propagate through a frozen viable witness. -/
theorem unanimous_next_votes_of_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m floor : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hheld : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → Q ∈ (tr.state y i).fg.tree ∧
        e.readPoint.blockStamp Q.root < SA.ETime.of (SA.freeze sp (m + 1)))
    (hG : ∀ x i e, x ∈ H (tr.time i) → SA.VoteAt tr.projAC x i e →
      e.msg.slot = m → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    (hstock : sp.committeeSize = sp.n) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = m + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  exact KernelProof.unanimous_next_votes_of_witness_at hrun hnc hsvc hawake hf hcatch
    hnr hm hmb hframe hz hQ hh hJ hXQ hheld hG hstock

/-- The same arbitrary prefix reaches an actual next-slot proposal head. -/
theorem unanimous_next_proposal_of_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {m floor : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m)
    (hmb : sp.ts (m + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts m) (sp.ts (m + 1 : Nat) + sp.Δ) floor kindJ J)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    (hQ : Q ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hG : ∀ x j e, x ∈ H (tr.time j) → SA.VoteAt tr.projAC x j e →
      e.msg.slot = m → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts (m + 1 : Nat))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hQy : Q ∈ (tr.state y i).fg.tree) (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocksAt H) X d.head := by
  exact KernelProof.unanimous_next_proposal_of_witness_at hrun hnc hsvc hawake hf hcatch
    hnr hm hmb hframe hz hQ hh hJ hXQ hG hy hc hcall hti hd hQy hstock

end Consensus.Goldilocks.Healing.Growing

end

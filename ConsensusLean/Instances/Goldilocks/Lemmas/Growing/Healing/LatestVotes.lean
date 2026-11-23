module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize

public section

/-! # The latest votes after a recent result, under growing faults

The latest votes of a recent result under growing faults: the finite
result-prefix boundary `late_result_prefix_votes_before_at` read at one vote of a node honest at
it, by `t ≤ b`, with a label past the result's. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- A recent result of a node honest at its cut, whose later honest casts keep it in their
domain and whose next-slot casts hold no conflicting stored lock, is extended by every vote of
label `L > s`, by `t ≤ b`, of a node honest at its vote. -/
theorem ResetPremisesUpTo.latest_votes_of_recent_result_at {b t : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {x : Fin sp.n} {r s L : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
        s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B)
    (htb : t ≤ b) (hsL : s < L) :
    ∀ z q e, Compose.Growing.HVoteAt tr H z q e → tr.time q ≤ t →
      e.msg.slot = L → AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  intro z q e hv hqt he
  obtain ⟨hz, ell, hcast⟩ := Compose.Growing.hVoteAt_iff.mp hv
  exact hp.late_result_prefix_votes_before_at hx hres hBC hrb hts hdomain hstored q
    (hqt.trans htb) z hz ell e hcast (he ▸ hsL)

end Consensus.Goldilocks.Healing.Growing

end

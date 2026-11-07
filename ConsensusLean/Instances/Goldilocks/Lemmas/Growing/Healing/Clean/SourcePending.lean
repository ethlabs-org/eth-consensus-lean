module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts

public section

/-! # Pending interface of the clean source votes

The growing result-prefix vote domain that the clean source votes read, under its agreed name,
owned by the pivot ports: `ProposalImpl.result_prefix_vote_domain_before_at`, a result prefix is
below the frame root of a later vote, or viable in its voter block tree. Each node is honest at
its own cut, and ancestry is over `HonestBlocksAt`.

The kernel lemmas the clean source votes also read (`late_result_prefix_votes_before_at`,
`held_target_vote_domain_before_at`, `target_compatible_older_origin_at`,
`target_compatible_later_origin_before_at`) are proved in `Kernel/ResetFacts`, re-exported here.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A clean result prefix, written by a node honest at its write, is below the frame root of a
later vote of a node honest at it, or viable in its voter block tree, given the earlier votes. -/
theorem ProposalImpl.result_prefix_vote_domain_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

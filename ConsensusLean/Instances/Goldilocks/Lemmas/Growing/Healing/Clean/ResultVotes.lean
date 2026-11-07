module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResultLocks

public section

/-! # Clean result-prefix retention

This assembly supplies the domain and stored-lock inputs of the finite latest-result induction.
The domain and induction are read through the clean line's shared supplier interface.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean raw result retains every prefix in later honest votes through the horizon. -/
theorem clean_result_prefix_votes_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      SA.CastAt tr.projAC y i ell e → s < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by
    have := sp.two_le_k
    omega
  apply hp.late_result_prefix_votes_before_at hc hx hres hBC hrb
    (hp.clean_window_timing_at hclean s (by have := sp.two_le_k; omega))
  · intro y i ell e hy hcast hib hsi hprior
    exact ProposalImpl.result_prefix_vote_domain_before_at hp hc hx hy hres hBC hclean hrb
      hcast hsi hib fun z q hz hqi e' hv hse =>
        hprior z q e' hqi (Compose.Growing.hVoteAt_iff.mpr ⟨hz, hv⟩) hse
  · intro y i ell e hy hcast hib hfirst
    obtain ⟨-, -, hsl⟩ := KernelProof.castAt_facts_at hp.run hp.noColl hy hcast
    exact hp.result_prefix_stored_locks_at hc hx hy hres hBC hs hrb hib (by
      change e.msg.slot = sp.slot (tr.time i) at hsl
      rw [← hsl, hfirst])

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

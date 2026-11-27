module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResultLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers

public section

/-! # Clean result-prefix retention

This assembly supplies the domain and stored-lock inputs of the finite latest-result induction.
The domain and induction are read through the clean line's shared supplier interface.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- A clean raw result retains every prefix in later honest votes through the horizon. -/
theorem clean_result_prefix_votes_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      AC.CastAt tr.projAC y i ell e → s < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by
    have := sp.two_le_k
    omega
  have hcase : (∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
    cases hdd : sp.deepDepth with
    | none => exact Or.inl fun D hD => by cases hD
    | some D =>
      rcases hp.deepCover D hdd with hb | hc
      · exact Or.inl fun D' hD' => by cases hD'; exact hb
      · exact Or.inr hc
  rcases hcase with hpre | hc
  swap
  · -- under the high-source cover: S2, the result past the origin floor being a member
    intro i hib y hy ell e hcast hsi
    exact Compose.Growing.healed_source_votes_at hc.s2
      (Compose.Growing.HealedOrigin.of_origin (rL := healedLockFloor sp a)
        (rO := healedOriginFloor sp a) (by simp only [healedOriginFloor, healedLockFloor]; omega)
        (Compose.Growing.originWithin_iff.2 ⟨x, r, CV, hx, hrb, Or.inl hres⟩)) hBC
      (Compose.Growing.hVoteAt_iff.2 ⟨hy, ell, hcast⟩) hib hsi
  apply hp.late_result_prefix_votes_before_at hx hres hBC hrb
    (hp.clean_window_timing_at hclean s (by have := sp.two_le_k; omega))
  · intro y i ell e hy hcast hib hsi hprior
    exact ProposalImpl.result_prefix_vote_domain_before_of_quarantine_at hp hx hy hres hBC
      hclean hrb hcast hsi hib (fun z q hz hqi e' hv hse =>
        hprior z q e' hqi (Compose.Growing.hVoteAt_iff.mpr ⟨hz, hv⟩) hse) hpre
  · intro y i ell e hy hcast hib hfirst
    obtain ⟨-, -, hsl⟩ := KernelProof.castAt_facts_at hp.run hp.noColl hy hcast
    exact hp.result_prefix_stored_locks_at hx hy hres hBC hs hrb hib (by
      change e.msg.slot = sp.slot (tr.time i) at hsl
      rw [← hsl, hfirst])

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

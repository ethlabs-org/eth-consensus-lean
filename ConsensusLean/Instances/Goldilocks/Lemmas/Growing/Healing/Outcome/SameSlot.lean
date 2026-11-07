module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Compatibility
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Same-label raw sources below a unanimous head

An actual supporter is honest through the raw write and hence at its own vote.
No successful later update is assumed.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Every bounded same-label raw source is below the actual unanimous head. -/
theorem same_slot_source_below_unanimous_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r u : Nat} (hx : x ∈ H (tr.time r))
    {B P : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r u B CV) ∨ SA.SlowLockAt tr.projAC x r u B)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts u)
    (hPU : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root) : Anc (tr.HonestBlocksAt H) B P := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have below : ∀ z q, z ∈ H (tr.time r) → q ≤ r → ∀ e,
      SA.VoteAt tr.projAC z q e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B → Anc (tr.HonestBlocksAt H) B P := by
    rintro z q hz hqr e hv hes ⟨D, hD, hDr, hBD⟩
    obtain rfl : D = P := hac.localRun.coherent.1 hD hPU
      (hDr.trans (hun z q e (hp.run.antitone (hp.run.time_mono hqr) hz) hv
        ((hp.run.time_mono hqr).trans hrb) hes))
    exact hBD
  rcases horig with ⟨CV, ⟨ell, C, hupd, hC, hD, _⟩ | hop⟩ | ⟨ell, C, hupd, hC, hD⟩
  · have hr := hac.localRun.upTo (hp.run.time_nonneg r)
    have hcu := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hupd.1)
    obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := ProposalImpl.result_supporter_at hp hc hx
      ⟨ell, hupd, hC, rfl⟩ ((SA.deepest_mem hD).1.1.2.2.mono
        (SA.frameIn_of_callAt hr hx hcu).2) hrb hts
    exact below z q hz hqr.le e hv hes he
  · obtain ⟨_, z, q, hz, hqr, e, hv, hes, he⟩ := hp.optimistic_supporter_at hx hrb hop
    exact below z q hz hqr e hv hes he
  · have hr := hac.localRun.upTo (hp.run.time_nonneg r)
    have hcu := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hupd.1)
    obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := ProposalImpl.result_supporter_at hp hc hx
      ⟨ell, hupd, hC, rfl⟩ ((SA.deepest_mem hD).1.1.2.2.mono
        (SA.frameIn_of_callAt hr hx hcu).2) hrb hts
    exact below z q hz hqr.le e hv hes he

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

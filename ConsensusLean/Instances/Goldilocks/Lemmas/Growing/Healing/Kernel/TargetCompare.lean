module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Comparing a prospective target with a later historical origin

Only the origin writer's finite prefix is needed. Every supporting voter is
honest at its actual cast; no global retention induction is used here.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Prior honest head support compares a target with a later bounded controlling origin. -/
theorem target_compatible_later_origin_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r m i l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hrb : tr.time r ≤ b) (hlm : l < m)
    (hsupport : ∀ z q e, q < i → Compose.Growing.HVoteAt tr H z q e →
      l < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hm := hp.run.time_mono
  have ht := hp.run.time_nonneg r
  have hr := hac.upTo ht
  have hf : 2 * (H (tr.time r))ᶜ.ncard < sp.n := by
    have := hp.faults _ ht hrb
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  obtain ⟨hx, _, ⟨CV, ell, D, hcall, hfl, rfl⟩, _⟩ := ho
  obtain ⟨ell', hcall', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hcall'.2)
  obtain ⟨hPhi, htree⟩ := frame_tree_subset_at hp.run hp.noColl hx hcall
  have hsub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨x, r, tr.time r, ht, fun _ hq => hm hq.le, hx, htree h⟩
  have hOD := (SA.anc_viableAncestor ell.frame D).mono hsub
  have hcomp := SA.fastLock_compatible_of_votes hr _ SA.CommitteeP.full hx hri
    ((SA.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩) (SA.cs2_full hp.stock hf) (B := B) (by
      intro z hz q hq e hv hs
      obtain ⟨hqt, hv⟩ := SA.upTo_voteAt.mp hv
      exact hsupport z q e hq
        (Compose.Growing.hVoteAt_iff.mpr ⟨hp.run.antitone hqt hz, hv⟩) (by omega))
  rcases hcomp with hDB | hBD
  · exact Or.inr (hOD.trans hDB)
  · exact SA.anc_total hac.localRun.coherent hBD hOD

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Comparing a prospective target with a later historical origin

Only the origin writer's finite prefix is needed. Every supporting voter is
honest at its actual cast; no global retention induction is used here.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- Prior honest head support compares a target with a later bounded controlling origin. -/
theorem target_compatible_later_origin_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r m i l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hrb : tr.time r ≤ b) (hlm : l < m)
    (hsupport : ∀ z q e, q < i → Compose.Growing.HVoteAt tr H z q e →
      l < e.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hm := hp.run.time_mono
  have ht := hp.run.time_nonneg r
  have hr := hac.upTo ht
  have hcut := hp.cutZ_le_ts_of_highOrigin_at ho
  obtain ⟨hxz, _, ⟨CV, ell, D, hcall, hfl, rfl⟩, _⟩ := ho
  -- the lock of label `m` is written at or after `t_m`, so its committee is bounded at `t_r`
  have hmr : sp.ts m ≤ tr.time r := by
    rcases hfl with ⟨ℓ, C, hu, -⟩ | ⟨ℓ, A, -, hslot, -⟩
    · have hu' : tr.time r = sp.ts m + 6 * sp.Δ := hu.2.2.1
      linarith [sp.toParams.hΔ]
    · exact (AC.ts_le_iff_le_slot sp ht (m : Int)).2
        (by rw [show sp.slot (tr.time r) = m from hslot])
  have hf := hp.committee_cs2_at (s := m) (by have := lt_cutZ sp g; linarith [sp.toParams.hΔ])
    (hmr.trans hrb) ht hrb
  have hx := hp.run.antitone (le_max_right _ _) hxz
  obtain ⟨ell', hcall', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hcall'.2)
  obtain ⟨hPhi, htree⟩ := frame_tree_subset_at hp.run hp.noColl hx hcall
  have hsub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨x, r, tr.time r, ht, fun _ hq => hm hq.le, hx, htree h⟩
  have hOD := (AC.anc_viableAncestor ell.frame D).mono hsub
  have hcomp := AC.fastLock_compatible_of_votes hr _
    (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP (tr.time r)) hx hri
    ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩) hf (B := B) (by
      intro z hz q hq e hv hs
      obtain ⟨hqt, hv⟩ := AC.upTo_voteAt.mp hv
      exact hsupport z q e hq
        (Compose.Growing.hVoteAt_iff.mpr ⟨hp.run.antitone hqt hz, hv⟩) (by omega))
  rcases hcomp with hDB | hBD
  · exact Or.inr (hOD.trans hDB)
  · exact AC.anc_total hac.localRun.coherent hBD hOD

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

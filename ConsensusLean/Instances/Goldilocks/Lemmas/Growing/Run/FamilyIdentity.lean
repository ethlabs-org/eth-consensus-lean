module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection

/-! # Goldilocks identity observation under time-indexed honesty -/

public section

namespace Consensus.Goldilocks.Growing

open SA (SAParams ReplayOrder Payload goldilocksFamily goldilocksSA)

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

theorem goldilocksObservation {H : Time → Set (Fin sp.n)} {U : Set (SA.Blk sp.n FGP)}
    {o : SA.SATrace sp FGP ro} (hr : ACLocalRun (goldilocksSA sp FGP ro) H U o) :
    ACObsRun (goldilocksSA sp FGP ro) H U ((goldilocksFamily sp FGP ro).proj o) := by
  rw [SA.proj_goldilocks]
  exact ⟨hr.antitone, hr.coherent, hr.init, hr.frameLaw, hr.time_nonneg, hr.time_mono,
    hr.awake_of_call, hr.restart_of_sleep, hr.restart_at_wake, hr.sleep_of_restart⟩

variable {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {R : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

theorem goldilocksFamilyRun (hr : GoldilocksRun proposer dg H R) (hnc : Compose.NoCollRun dg R) :
    FamilyRun (goldilocksFamily sp (List (FG.Att sp.n)) ro) proposer dg H R := by
  refine ⟨hr.toLocalRun, hr.genesis_root_ok, ?_, ?_,
    goldilocksObservation
      (Compose.Growing.goldilocks_ac_projection sp ro dg H R proposer hr hnc).localRun⟩
  · intro y i B hy hc v hv hh
    obtain ⟨j, hj, he⟩ := hr.carried_vote_unforgeable y i B hy hc v hv hh
    change ∃ j < i, ∃ e, SA.VoteAt
      ((goldilocksFamily sp (List (FG.Att sp.n)) ro).proj R.projAC) v.val j e ∧ e.msg = v
    rw [SA.proj_goldilocks]
    obtain ⟨ℓ, hc, e, he, rfl⟩ := he
    exact ⟨j, hj, e, ⟨ℓ, Compose.projAC_callAt.mpr hc, he⟩, rfl⟩
  · constructor
    · intro y i hy
      exact congrArg (fun o : SA.SATrace sp (List (FG.Att sp.n)) ro => o.state y i)
        (SA.proj_goldilocks R.projAC)
    · intro y i ℓ hy hc he
      have h := SA.projCall_goldilocks (sp := sp) (ro := ro) ℓ.call
      exact False.elim (Option.some_ne_none _ (h.symm.trans he))
    · intro y i ℓ hy hc he
      have h := SA.projCall_goldilocks (sp := sp) (ro := ro) ℓ.call
      exact False.elim (Option.some_ne_none _ (h.symm.trans he))

end Consensus.Goldilocks.Growing

end

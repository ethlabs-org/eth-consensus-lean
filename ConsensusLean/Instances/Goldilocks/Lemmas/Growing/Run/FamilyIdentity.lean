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

open AC (ACParams ReplayOrder Payload goldilocksFamily goldilocksAC)

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}

theorem goldilocksObservation {H : Time → Set (Fin sp.n)} {U : Set (AC.Blk sp.n FGP)}
    {o : AC.GTrace sp FGP ro} (hr : ACLocalRun (goldilocksAC sp FGP ro) H U o) :
    ACObsRun (goldilocksAC sp FGP ro) H U ((goldilocksFamily sp FGP ro).proj o) := by
  rw [AC.proj_goldilocks]
  exact ⟨hr.antitone, hr.coherent, hr.init, hr.frameLaw, hr.time_nonneg, hr.time_mono,
    hr.awake_of_call, hr.restart_of_sleep, hr.restart_at_wake, hr.sleep_of_restart⟩

variable {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {R : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

end Consensus.Goldilocks.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare

public section

/-! # Joined calls and honest participants

The canonical comparison lemmas supply honest votes and participants.
-/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- At a non-restart call, joinedness agrees with the AC state's joined test. -/
theorem joined_at_call {ini} (h : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {t : Time} (i : Nat) (hi : tr.IsCall y i)
    (hnr : ¬ tr.RestartAt y i) (hit : tr.time i = t) :
    tr.JoinedAt y t ↔ AC.joined sp (tr.state y i).ac t :=
  (joined_projection_from h hy t).2.1 i hi hnr hit

end Consensus.Goldilocks.Compose

end

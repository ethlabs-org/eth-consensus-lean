module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # Historical height advances and the finite pre-reset range

The quorum budget is read at the current honest observer. Historical rows recovered
from that observer's store keep honesty at their own signing cuts.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A height advance by a signer honest at it and at `c_z` produces a growing reset no later than
its signing. The quorum budget is read at `max c_z t_k`, so the advance's honest supporter is
honest at `c_z` too. -/
theorem reset_of_height_advance_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {g : Time} {y : Fin sp.n} {k : Nat}
    (hq : (H (max (cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q)
    (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ a, IsReset tr H g a ∧ a ≤ tr.time k :=
  Generic.reset_of_height_advance_at_from hrun.toLocalRun hq hyz hs hh

/-- Before any advance by a signer honest at it and at `c_z`, an honest reader's height is at most
HZ plus one. The quorum budget is read at `max c_z t_i`. -/
theorem hmax_le_of_noAdvance_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {g T : Time}
    (hna : ∀ v k att, v ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hq : (H (max (cutZ sp.toParams g) (tr.time i)))ᶜ.ncard < sp.toParams.fg.q)
    (hiT : tr.time i < T) :
    (tr.state y i).fg.hmax ≤ HZ tr H g + 1 :=
  Generic.hmax_le_of_noAdvance_at_from hrun.toLocalRun hna hy hq hiT

end Consensus.Goldilocks.Healing.Growing

end

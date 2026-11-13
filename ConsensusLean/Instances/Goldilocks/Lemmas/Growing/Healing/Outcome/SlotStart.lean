module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps

public section

/-! # Optimistic writes before signing at a slot start

The signer's tick has received no current-slot vote from another validator.
An optimistic write at that time therefore has a single-validator committee.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- A local optimistic write before a slot-start signing can count only the signer. -/
theorem slot_start_optimistic
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att)
    {m : Nat} (hdt : tr.time d = sp.ts m) {r : Nat} (hrd : r < d)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC v r m D CV) (hstock : sp.committeeSize = sp.n) :
    sp.n = 1 ∧ ∃ j' ≤ r, ∃ e', SA.VoteAt tr.projAC v j' e' ∧ e'.msg.slot = m :=
  Healing.slot_start_optimistic hrun hnc hv hs hdt hrd hopt hstock

end Consensus.Goldilocks.Healing.Growing.Outcome

end

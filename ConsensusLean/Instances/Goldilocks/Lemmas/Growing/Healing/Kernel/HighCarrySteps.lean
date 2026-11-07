module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs

public section

/-! # Frozen no-Catch carry steps for retained high-origin votes

These steps are independent of retained-vote induction. The later step consumes
strictly earlier votes explicitly; neither step may import Kernel.ResetFacts.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A high origin's counted votes reach a next-slot honest cast without Catch. -/
theorem first_carry_of_finalized_anc_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hfl : Compose.StoredFastLockAt tr x i j B CV)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e j CV := by
  sorry

/-- Earlier honest votes extending a high origin reach a later cast without Catch. -/
theorem later_carry_of_finalized_anc_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hkb : tr.time k ≤ b)
    (hs : e.msg.slot = m + 1) (hjm : j < m)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B)
    (hprior : ∀ z q e', q < k → Compose.Growing.HVoteAt tr H z q e' →
      e'.msg.slot = m → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    SA.CarryAt tr.projAC (tr.HonestBlocksAt H) y k e m
      {v | ∃ z q e', Compose.Growing.HVoteAt tr H z q e' ∧ e'.msg = v ∧ v.slot = m} := by
  sorry

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

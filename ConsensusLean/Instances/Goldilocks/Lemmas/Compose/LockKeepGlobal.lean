module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepHonest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks

public section

/-! # Goldilocks: honest locks on `B` kept by every honest node over an interval

consensus-lean#135 (WI-16), r14 s1 L1.2: the read-point premise `UnlockKeeps` of an induction
over time in which each honest node keeps a lock on `B`. The votes that `unlock` reads at cut `j`
are of slot `slot(t_j) − 1`, so their honest casts are at earlier cuts (`cast_lt_of_slot`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The unlock premise of `lock_keep_run_view` at node `y`, cut `j`: `unlock` at the view of the
AC call at `j` does not move `B` (for the slot-`(slot(t_j) − 1)` votes). -/
abbrev UnlockKeeps (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (j : Nat)
    (B : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∀ ℓ, tr.CallAt y j (.ac ℓ) → SA.unlockTarget sp (Node.frame (tr.state y j))
    (SA.unlockView (ro := ro) (tr.state y j).ac (Node.frame (tr.state y j)) (tr.time j) ℓ.call)
    ((sp.slot (tr.time j) : Int) - 1) B = B

/-- An honest cast of a vote of slot `slot(t_j) − 1` is at a cut before `j`. -/
theorem cast_lt_of_slot (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {k j : Nat}
    {ℓ' : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)} {e}
    (hc : SA.CastAt tr.projAC x k ℓ' e)
    (hs : (e.msg.slot : Int) = (sp.slot (tr.time j) : Int) - 1) : k < j := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hsk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hx hc).2.1
  by_contra hkj
  have := SA.slot_mono sp (hrun.time_nonneg j) (hrun.time_mono (Nat.le_of_not_lt hkj))
  omega

end Consensus.Goldilocks.Compose

end

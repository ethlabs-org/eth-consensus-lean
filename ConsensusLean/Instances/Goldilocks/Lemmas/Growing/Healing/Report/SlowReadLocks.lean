module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SlowStored
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Read-point lock passage after a historical slow selection -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Stored-lock comparison and earlier honest votes discharge every live read lock. -/
theorem slow_live_locks_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {x : Fin sp.n} {c s : Nat} (hx : x ∈ H (tr.time c))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsl : SA.SlowLockAt tr.projAC x c s D)
    (hm : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hs : e.msg.slot = s + 1)
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hE : ∀ z k ev, k < i → z ∈ H (tr.time k) → SA.VoteAt tr.projAC z k ev →
      ev.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) ev.msg D)
    (hstock : sp.committeeSize = sp.n) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L D := by
  have hg := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hg.upTo (hrun.time_nonneg i)
  have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : sp.slot (tr.time i) = s + 1 :=
    ((SA.castAt_spec hr.localRun hy hc').2.1).symm.trans hs
  apply SA.live_locks_of_stored_before hr hf hy hc' hs ?_ ?_ hstock
  · intro l hl hlive hle Y hY hYr
    rw [projAC_upTo_state hrun le_rfl] at hl
    exact slow_stored_locks_service_at hrun hnc hsvc hx hsl hm hy
      (by rw [hslot]) hstock l hl hlive hle Y hY hYr
  · intro z hz k hki ev he hes
    obtain ⟨hkt, he⟩ := SA.upTo_voteAt.mp he
    exact hE z k ev hki (hrun.antitone hkt hz) he hes

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

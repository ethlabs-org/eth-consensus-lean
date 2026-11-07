module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.LockLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

/-! # Current-label read locks were written while their reader was honest -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A current-label lock in the read point comes from an optimistic write no later than the cast. -/
theorem current_lock_write_readPoint_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ell e)
    (hpos : 0 < e.msg.slot) {l : SA.Lock} (hl : l ∈ e.readPoint.locks)
    (hs : e.msg.slot ≤ l.slot) :
    l.slot = e.msg.slot ∧ ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
      SA.OptimisticLockAt tr.projAC y a e.msg.slot D CV ∧
      sp.ts e.msg.slot ≤ tr.time a ∧
      ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧ Anc (tr.HonestBlocksAt H) L D := by
  have hd := hrun.time_nonneg i
  have hc' := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  obtain ⟨hslot, a, hai, D, CV, ho, ht, L, hL, hLr, hLD⟩ :=
    SA.current_lock_write_readPoint (acRun_upTo hrun hnc hd).localRun hy hc' hpos hl hs
  obtain ⟨hat, ho⟩ := (SA.upTo_optimisticLockAt hrun.time_mono).mp ho
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  exact ⟨hslot, a, hai, D, CV, hrun.antitone hat hy, ho, ht, L, hsub hL, hLr, hLD.mono hsub⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

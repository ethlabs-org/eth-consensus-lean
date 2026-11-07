module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.WalkInputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC

public section

/-! # Growing proposal high-lock compatibility

The provenance of a stored high lock is read on the proposer's finite prefix
(`proposal_high_lock_source_at`); the protected-source comparison
(`WalkInputs.protected_source_compatible_high_origin_at`) is charged separately at the source
and origin writes.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Stored proposal high locks compare with every high origin in the finite horizon. -/
theorem proposal_stored_locks_compatible_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {q j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x q j O) (hqb : tr.time q ≤ b) :
    SA.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state p i)
      (tr.time i) (u - 1) O := by
  have hU := (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer
    hp.run hp.noColl).localRun.coherent
  rw [SA.highLocksCompatible_iff]
  intro l hl _ hlabel L hL hLr
  obtain ⟨r, D, CV, hri, hslot, hpr, hop, L', hL', hL'r, hLD⟩ :=
    proposal_high_lock_source_at hp hpH hci hcall hti hib hl hlabel
  obtain rfl : L' = L := hU.1 hL' hL (hL'r.trans hLr.symm)
  have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    have := sp.two_le_k
    rw [Healing.cleanLabel_eq]
    omega
  rcases WalkInputs.protected_source_compatible_high_origin_at hp hc hpr
      (Or.inl ⟨CV, Or.inr hop⟩) hclean ((hp.run.time_mono hri.le).trans hib) ho hqb with h | h
  · exact Or.inl (hLD.trans h)
  · exact Anc.total hU hLD h

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end

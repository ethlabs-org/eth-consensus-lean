module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionCompatibility

public section

/-! # Frozen finality ancestry at the unanimous update -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- At the exact update cut, strict finalization orients compatibility below the proposal. -/
theorem finalized_below_unanimous_at_update_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocksAt H) (hPs : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) (ha : a ≤ tr.time j) :
    Anc (tr.HonestBlocksAt H) ell.frame.F P := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

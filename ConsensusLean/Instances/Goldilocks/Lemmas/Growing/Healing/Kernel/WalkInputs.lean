module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed

public section

/-! # Frozen source comparison input for the proposal walk

The row-source owner supplies this historical-write contract. It remains an
explicit stand-in here until the independent RowSources implementation arrives.
-/

namespace Consensus.Goldilocks.Healing.Growing.WalkInputs

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The protected source writer and the high-origin writer are honest at their own writes. -/
theorem protected_source_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) B D := by
  sorry

end Consensus.Goldilocks.Healing.Growing.WalkInputs

end

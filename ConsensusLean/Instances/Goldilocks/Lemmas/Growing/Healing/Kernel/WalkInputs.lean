module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RowSources

public section

/-! # Frozen source comparison input for the proposal walk

The historical-write comparison that the proposal walk reads, forwarded to its proof
`ProposalImpl.protected_source_compatible_high_origin_at` in `Pivot/RowSources`.
-/

namespace Consensus.Goldilocks.Healing.Growing.WalkInputs

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}

/-- The protected source writer and the high-origin writer are honest at their own writes. -/
theorem protected_source_compatible_high_origin_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, AC.FastLockAt tr.projAC x r s B CV) ∨ AC.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) B D := by
  exact ProposalImpl.protected_source_compatible_high_origin_at hp hx hsource hs hrb ho hqb

end Consensus.Goldilocks.Healing.Growing.WalkInputs

end

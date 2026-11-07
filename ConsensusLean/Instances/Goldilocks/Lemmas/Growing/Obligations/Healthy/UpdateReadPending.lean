module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending interface of the read after an operational update

The growing reset-kernel facts that `UpdateReadAfter` consumes whose home modules are not on this
branch yet, in their agreed t-form: the reader is honest at an observation `t ≤ b` after its
state's cuts, the clean source's writer at its write.

* `ResetPremisesUpTo.finalized_compatible_clean_source_at`: the reader's finalized block is
  compatible with a clean raw source (static `Healing/Outcome/FiniteSources`);
* `ResetPremisesUpTo.clean_source_stored_lock_compatible_at`: a clean raw source is compatible
  with every block of a protected stored lock of the reader (same module).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Finalization at a read compares with a clean raw source. -/
theorem finalized_compatible_clean_source_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s n : Nat} {t : Time} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    (ht : 0 ≤ t) (hle : ∀ q < n, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b) :
    Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F C := by
  sorry

/-- A clean raw source compares with the protected stored locks of a reader. -/
theorem clean_source_stored_lock_compatible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} {t : Time} (hx : x ∈ H (tr.time r))
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hB : SA.ResultAt tr.projAC x r s B CV ∨ SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) {l : SA.Lock}
    (hl : l ∈ (tr.projAC.state y i).locks) (hls : cleanLabel sp a + sp.k + 2 ≤ l.slot)
    (hC : C ∈ tr.HonestBlocksAt H) (hCr : C.root = l.block) :
    Compatible (tr.HonestBlocksAt H) B C := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

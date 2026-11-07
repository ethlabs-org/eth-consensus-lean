module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending reset-kernel interface of the current-record sources

The growing forms of two reset-kernel comparisons the current-record geometry
(`CurrentSources`) consumes, under their agreed names, whose home is the growing outcome cone:

* `ResetPremisesUpTo.finalized_compatible_clean_source_at`
  (`Healing.ResetPremisesUpTo.finalized_compatible_clean_source`): a finalized block of a reader
  honest at an observation `t ≤ b`, every earlier cut at a time `≤ t`, compares with a clean
  source of a writer honest at its write;
* `ResetPremisesUpTo.clean_sources_compatible_at`
  (`Healing.ResetPremisesUpTo.clean_sources_compatible`): two clean sources, each of a writer
  honest at its write, compare.

Each theorem here is an open `sorry`; this module is deleted when the home module lands. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Finalization of a reader honest at `t ≤ b` compares with a clean raw source. -/
theorem finalized_compatible_clean_source_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s n : Nat} {t : Time} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    (ht : 0 ≤ t) (hle : ∀ q < n, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b) :
    Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F C := by
  sorry

/-- Two clean raw sources, each of a writer honest at its write, compare. -/
theorem clean_sources_compatible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r q s t : Nat} {C D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV DV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time q))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hD : SA.ResultAt tr.projAC y q t D DV ∨ SA.OptimisticLockAt tr.projAC y q t D DV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (ht : cleanLabel sp a + 2 * sp.k + 1 ≤ t)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) C D := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

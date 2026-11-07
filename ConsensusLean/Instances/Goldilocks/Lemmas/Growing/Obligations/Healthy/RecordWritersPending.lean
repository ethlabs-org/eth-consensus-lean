module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending reset-kernel facts of the record writers

The growing reset-kernel facts that `RecordWriters` consumes and that no branch has yet, in the
own-cut form agreed with the kernel owner: writers honest at their own cut, the caller at its
call, ancestry over the blocks held while honest; otherwise the static statements.

* `ResetPremisesUpTo.reset_seed_held_at_call_at` (static `Healing/Outcome/Supplier`);
* `ResetPremisesUpTo.clean_source_compatible_high_origin_at` (static
  `Healing/Outcome/FiniteSources`);
* `optimistic_next_result_of_floor_at` (static `Healing/OperationalReports`).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A bounded high seed, held at every later call above it from `a + Δ` on. -/
theorem ResetPremisesUpTo.reset_seed_held_at_call_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ)) :
    ∃ v r l S, HighOrigin tr H g v r l S ∧ tr.time r ≤ a ∧ tr.time r ≤ b ∧
      ∀ y c (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time c) →
        tr.projAC.CallAt y c ell → a + sp.Δ ≤ tr.time c → tr.time c ≤ b →
        Anc (tr.HonestBlocksAt H) ell.frame.F S → S ∈ ell.frame.tree := by
  sorry

/-- A clean raw source is compatible with every bounded high origin. -/
theorem ResetPremisesUpTo.clean_source_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hx : x ∈ H (tr.time r))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) C D := by
  sorry

/-- A clean optimistic source above the next update's finalized block is extended by that
update's result. -/
theorem optimistic_next_result_of_floor_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time j))
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y j (s + 1) ell)
    (hjb : tr.time j ≤ b) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hR : drainTime sp a ≤ sp.ts (s + 1 + 1 : Nat))
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ D DV, SA.ResultAt tr.projAC y j (s + 1) D DV ∧ Anc (tr.HonestBlocksAt H) B D := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

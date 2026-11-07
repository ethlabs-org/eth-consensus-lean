module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending pivot interface of the clean proposal domain

The growing forms of two `Outcome/PivotRowSources` lemmas that the clean proposal domain reads,
under their agreed names (static name + `_at`), owned by the pivot ports. Each node is honest at
its own cut, and ancestry and compatibility are over `HonestBlocksAt`:

* `ResetPremisesUpTo.raw_writer_held_at_slot_start_at`: a raw writer's ancestor is held by a later
  slot-start reader;
* `ResetPremisesUpTo.protected_source_compatible_high_origin_at`: a clean protected source is
  compatible with every high origin written by the horizon.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A raw writer's ancestor is held by a later slot-start reader honest at its call. -/
theorem raw_writer_held_at_slot_start_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} {r s i u : Nat} (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocksAt H) B C) (hs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) : B ∈ ell.frame.tree := by
  sorry

/-- A clean protected source, written by a node honest at its write, is compatible with every
high origin written by the horizon. -/
theorem protected_source_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r))
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) B D := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

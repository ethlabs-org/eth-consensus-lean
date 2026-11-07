module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.RowSources

public section

/-! # Pending pivot interface of the clean proposal domain

The growing form of the `Outcome/PivotRowSources` lemma that the clean proposal domain still reads
from a stand-in, under its final name (static name + `_at`, in `ProposalImpl`), owned by the pivot
ports: `ProposalImpl.raw_writer_held_at_slot_start_at` (home `Pivot/RawReceipt`), a raw writer's
ancestor is held by a later slot-start reader. Each node is honest at its own cut, and ancestry is
over `HonestBlocksAt`. `ProposalImpl.protected_source_compatible_high_origin_at` is proved in
`Pivot/RowSources`, re-exported here.

The theorem here is an open `sorry`; this module is deleted when its home module lands. -/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

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

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end

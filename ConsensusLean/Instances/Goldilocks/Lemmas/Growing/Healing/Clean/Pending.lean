module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Domain

public section

/-! # Pending interface of the clean-source proposal parent

Stated under their final names and signatures so that the clean-source proposal parent compiles
before they are proved.

The restart bound and the healthy AC base on a read prefix are imported from their homes
(`Growing/Healing/Restart`, `Healthy/PrefixBase`).

Owned by this cluster, and still open:

* `ResetPremisesUpTo.fast_source_votes_before_at`, `ResetPremisesUpTo.slow_source_votes_before_at`
  (the static clean-source vote retention of `Outcome/FiniteSources`).

Each source's writer is honest at its own write, each proposer, voter or caller at its own cut.
Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

namespace ResetPremisesUpTo

variable {b : Time}

/-- A clean fast source, written by a node honest at its write, is extended by every later vote
of a node honest at it, through the horizon. -/
theorem fast_source_votes_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfast : SA.FastLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

/-- A clean slow source, written by a node honest at its write, is extended by every later vote
of a node honest at it, through the horizon. -/
theorem slow_source_votes_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hslow : SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e, SA.CastAt tr.projAC y i ell e →
      s < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end

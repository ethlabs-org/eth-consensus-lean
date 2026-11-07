module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs

public section

/-! # Pending growing retention interface

Stated under its owner's final name and signature, so that the row services compile before it
lands: `Healing.Growing.ResetPremisesUpTo.origins_compatible_at`, the comparability of any two
bounded high origins (R1), the growing form of `Healing.ResetPremisesUpTo.origins_compatible`.
Each origin's writer is honest at its own write, which `HighOrigin` already records.

The theorem here is an open `sorry`; this module is deleted when the home module lands. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- The blocks of any two bounded high origins are comparable in the blocks held while honest. -/
theorem ResetPremisesUpTo.origins_compatible_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

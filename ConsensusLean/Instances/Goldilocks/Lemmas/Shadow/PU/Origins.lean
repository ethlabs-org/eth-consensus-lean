module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore

public section

/-! # P-U shadow: the run-level origin family over `Growing.GoldilocksRun'`

The high-origin facts that the S1/S2 inputs (`Shadow/PU/Frontier`) and the report cover read,
restated over the shadow run and the shadow reset premises `ResetPremisesUpTo'`.

* `Outcome.high_origin_mem_at'` and `Outcome.high_of_anc_at'` are the stock proofs, with Run's
  `σ_eq_honest_at'`, Coherence's `honestBlocksAt_coherent'` and `held_anc_at'`, and the shadow AC
  projection (`Compose.goldilocks_ac_projection_from'`).
* `CoveredUpTo.compatible_highOrigin'` is the stock proof (S1 of the cover, generic in the run).
* R1 (`ResetPremisesUpTo'.origins_compatible_at'`) and
  `ProposalImpl.finalized_compatible_high_origin_at'` are in `Shadow/PU/Kernel`, above the P-U
  vote domain (`Shadow/PU/VoteDomain`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The stored block of a high origin is held at its actual honest write
(`Outcome.high_origin_mem_at`). -/
theorem Outcome.high_origin_mem_at' {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    B ∈ (tr.state x i).fg.tree :=
  hrun.toCore.highOrigin_mem_at hnc ho

/-- A held descendant of a high origin is high (`Outcome.high_of_anc_at`). -/
theorem Outcome.high_of_anc_at' {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} {i j k : Nat} {t : Time}
    {B W : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hz : z ∈ H t)
    (hW : W ∈ (tr.state z k).fg.tree) (hBW : Anc (tr.HonestBlocksAt H) B W) :
    HZ tr H g + 1 ≤ ((tr.state z k).fg.σ W.root).h :=
  hrun.toCore.high_of_anc_at hnc ho ht hle hz hW hBW

/-- **A covered block is compatible with every high origin written by `b`**
(`CoveredUpTo.compatible_highOrigin`; S1 of the cover, the origin being a healed member). -/
theorem CoveredUpTo.compatible_highOrigin' {ini : Fin sp.n → (goldilocksNode' sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {m : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hib : tr.time i ≤ b)
    (ho : HighOrigin tr H g x i j B) : Compatible (tr.HonestBlocksAt H) E B :=
  hrun.toCore.compatible_highOrigin_of_covered hnc h hib ho

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # A voter's pre-freeze block reaches the proposer's frame, under growing faults

`reset_frozen_frame_at`, the growing form of `Healing.ResetPremisesUpTo.reset_frozen_frame`
(`Healing/Outcome/SupplierFrames`): a bounded pre-freeze block of a voter honest at its cast,
above the `Σ.F` of a proposer honest at its proposal call, is in the proposer's frame. The
block's stamp is an acceptance of the voter, honest then, relayed to the proposer. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A bounded pre-freeze block of a voter honest at its cast, above the `Σ.F` of a proposer
honest at its proposal call, is in the proposer's frame. -/
theorem reset_frozen_frame_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {i j s : Nat} (hpH : p ∈ H (tr.time i)) (hy : y ∈ H (tr.time j))
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : SA.CastAt tr.projAC y j elly e) (hib : tr.time i ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < SA.ETime.of (SA.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocksAt H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

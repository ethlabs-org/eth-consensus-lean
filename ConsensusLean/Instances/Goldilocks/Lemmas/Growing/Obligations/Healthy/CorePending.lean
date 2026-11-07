module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.StopAtParent
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixBest
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.CallLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Pivot

public section

/-! # Pending growing Healing Outcome core of the unanimity and report lemmas

Draft growing forms (static name + `_at`, `Healing.Growing.ResetPremisesUpTo`) of the nine Outcome
core lemmas that `operational_unanimous_at` and `report_cover_of_unanimous_at` consume, for the
kernel owner to accept or replace. The slot-`u` proposer is honest through `t_u + hold`, every
voter or caller at its own cut, unanimity and votes are quantified over voters honest at their
cast, and ancestry is over `HonestBlocksAt`. Timing and margins are the static ones.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- (`Healing.ResetPremisesUpTo.clean_window_timing`, Outcome/FiniteSources.) -/
theorem clean_window_timing_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {s : Nat}
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) :
    ∀ j : Nat, (s : Int) - sp.k < j → cutZ sp.toParams g ≤ sp.ts j := by
  sorry

/-- (`Healing.ResetPremisesUpTo.update_toFG_calls`, Outcome/Supplier.) The updater is honest at the
update time `t_u + 6Δ`. -/
theorem update_toFG_calls_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {u : Nat} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    (hu : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u)
    (hub : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ j ell ell', SA.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  sorry

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

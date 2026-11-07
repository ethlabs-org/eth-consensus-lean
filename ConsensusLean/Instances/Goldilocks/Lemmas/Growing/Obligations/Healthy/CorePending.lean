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

/-- (`Healing.ResetPremisesUpTo.reset_pivot`, Outcome/Pivot.) -/
theorem reset_pivot_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + hold sp))
    (hactual : tr.ProposesAt p k P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root) :
    ∃ D, ellp.frame.Anc d.start D ∧ ellp.frame.Anc D d.head ∧
      (∀ X, ellp.frame.Anc D X → ellp.frame.Anc X d.head → X ∈ ellp.frame.viableHeads) ∧
      ∀ y j elly e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j elly e → e.msg.slot = u →
        tr.time j ≤ b →
        (∀ x j' e', x ∈ H (tr.time j') → j' < j → SA.VoteAt tr.projAC x j' e' →
          e'.msg.slot = u → e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ellp.frame.Anc D X ∧ ellp.frame.Anc X d.head)) ∧
          elly.frame.Anc (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X ∧
          elly.frame.Anc X (SA.getHead sp e.readPoint elly.frame (tr.time j)
            (elly.frame.viableTree (SA.voteDomain sp e.readPoint elly.frame u))
            (SA.mergedVoteView sp e.readPoint elly.frame u) ((u : Int) - 1)) := by
  sorry

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

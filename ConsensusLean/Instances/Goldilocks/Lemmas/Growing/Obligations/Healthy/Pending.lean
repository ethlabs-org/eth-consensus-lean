module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs

public section

/-! # Stand-ins for the healed-safety port (open)

Statements published by their owners' modules, stated here under their final names and
signatures so the port compiles before they land:

* `Healing.Growing.operational_update_selection_at`: the operational selection at a bounded
  update after the drain, the counterpart of `Obligations.UpTo.operational_update_selection`;
* `Healing.Growing.cutZ_lt_reset_at`: under health the reset is after the cut, the counterpart of
  `Healing.cutZ_lt_reset_of_snapshot` (from the reset signing's counted voters, not a snapshot);
* `Healing.Growing.ResetPremisesUpTo.update_toFG_calls_at`: the joined update and to-FG call of
  a node honest at their time, the counterpart of `Healing.ResetPremisesUpTo.update_toFG_calls`;
* `Obligations.Growing.healthy_preparation_initialize_at`: the base timing and finite preparation
  schedule of a healed-safety query, the counterpart of
  `Obligations.healthy_preparation_initialize`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- An honest post-drain proposal, by a proposer honest through its slot's votes, is selected at
every bounded update of a node honest at it. -/
theorem operational_update_selection_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    P ∈ ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  sorry

/-- Health supplies a snapshot-honest counted voter behind every reset signing. -/
theorem cutZ_lt_reset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hh : tr.HealthyRunAt H ΔF g)
    (hR : IsReset tr H g a) :
    cutZ sp.toParams g < a := by
  sorry

/-- A node honest at `t_u + 6Δ` executes the joined update of label `u` and the to-FG call right
after it, at that time. -/
theorem ResetPremisesUpTo.update_toFG_calls_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {u : Nat} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    (hu : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ sp.ts u)
    (hub : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ j ell ell', SA.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A healed-safety query with progress on `[ready, heal]` has a base timing and a finite
preparation schedule. -/
theorem healthy_preparation_initialize_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTimingAt S A V Q, Nonempty (HealthyPreparationScheduleAt S A V Q W) := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end

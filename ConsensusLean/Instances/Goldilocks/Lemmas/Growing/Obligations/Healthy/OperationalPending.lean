module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending growing Healing interface of operational persistence

The growing forms of the Healing lemmas that `operational_proposal_below_later_parent` consumes,
under their agreed names (static name + `_at`). Each node is honest at its own cut, a reader of a
held state at an observation time after the state's cuts, and the slot-`u` proposer through
`t_u + hold`:

* `cutZ_lt_reset_of_snapshot_at` (`Healing.cutZ_lt_reset_of_snapshot`);
* `ResetPremisesUpTo.operational_unanimous_at`, `ResetPremisesUpTo.reset_seed_before_slot_at`,
  `ResetPremisesUpTo.reset_proposal_passes_at`;
* `old_origin_below_unanimous_at`, `report_cover_of_unanimous_at`
  (`Obligations.UpTo.old_origin_below_unanimous`, `Obligations.UpTo.report_cover_of_unanimous`).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-- The snapshot cut `c_z` is strictly before the reset. -/
theorem cutZ_lt_reset_of_snapshot_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hsnapshot : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g)) (hR : IsReset tr H g a) :
    cutZ sp.toParams g < a := by
  sorry

namespace ResetPremisesUpTo

variable {b : Time}

/-- Every vote of slot `u` by a node honest at its cut, by `b`, is for the post-drain operational
proposal `P` of slot `u`, whose proposer is honest through `t_u + hold`. -/
theorem operational_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hub : sp.ts u ≤ b) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = u →
      tr.time j ≤ b → e.msg.head = P.root := by
  sorry

/-- A high origin before every post-drain slot. -/
theorem reset_seed_before_slot_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ b ∧ l < u ∧ tr.time r < sp.ts u := by
  sorry

/-- A post-drain proposal call of a node honest at it extends every high origin before its slot. -/
theorem reset_proposal_passes_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ∀ O, (∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u) →
      Anc (tr.HonestBlocksAt H) O d.head := by
  sorry

end ResetPremisesUpTo

variable {b : Time}

/-- A high origin before a unanimous post-drain slot `u` is below its proposal `P`. -/
theorem old_origin_below_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {x : Fin sp.n} {r m : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m B) (ht : tr.time r < sp.ts u) :
    Anc (tr.HonestBlocksAt H) B P := by
  sorry

/-- Reports above a unanimous post-drain proposal `P` of slot `u` by `t_u + 6Δ`: every node
honest at `t_u + 6Δ` reports a descendant of `P`, or a node honest at its report reports a strict
height increase above `P`. -/
theorem report_cover_of_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ) → ∃ r e R, SA.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

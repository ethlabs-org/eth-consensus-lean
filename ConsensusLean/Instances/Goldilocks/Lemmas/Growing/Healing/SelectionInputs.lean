module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Explicit supplier stand-ins for the operational selection port

These exact interfaces are owned by the healthy-route and operational-report suppliers.
Integration deletes this module and imports their proofs; it is not a finished milestone.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Supplier: A4-engine's healthy AC base on the reader prefix. -/
theorem healthy_base_of_reset_catch_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    SA.HealthyBaseUpTo (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  sorry

/-- Supplier: A8's own-cut restart bound. -/
theorem restart_before_unanimous_slot_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} {r : Nat} (hy : y ∈ H (tr.time r)) (hr : tr.RestartAt y r)
    (hrb : tr.time r ≤ b) : tr.time r ≤ sp.ts ((u : Int) - 1) := by
  sorry

/-- Supplier: A8's actual votes from the honest cohort at the vote deadline. -/
theorem honest_votes_in_slot_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {u : Nat} (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) (hub : sp.ts u + sp.Δ ≤ b) :
    ∀ y, y ∈ H (sp.ts u + sp.Δ) → ∃ j e, SA.VoteAt tr.projAC y j e ∧ e.msg.slot = u ∧
      tr.time j ≤ sp.ts u + sp.Δ := by
  sorry

/-- Outcome supplier: a next-slot frozen root lies below the common bound on old origins. -/
theorem ResetPremisesUpTo.reset_vote_root_below_bound_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hbound : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r < sp.ts u →
      tr.time r ≤ b → Anc (tr.HonestBlocksAt H) B P)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hs : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P := by
  sorry

/-- Outcome supplier: a held bound on old origins is above the next-slot floor. -/
theorem ResetPremisesUpTo.reset_vote_floor_above_old_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u →
      tr.time r ≤ b → Anc (tr.HonestBlocksAt H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor

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

/-- Kernel supplier: the bounded high origin's label is after the snapshot. -/
theorem ResetPremisesUpTo.cutZ_le_ts_of_highOrigin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b) :
    cutZ sp.toParams g ≤ sp.ts j := by
  sorry

/-- Outcome supplier: a same-label source is below the unanimous head. -/
theorem ResetPremisesUpTo.same_slot_source_below_unanimous_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r u : Nat} (hx : x ∈ H (tr.time r))
    {B P : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r u B CV) ∨ SA.SlowLockAt tr.projAC x r u B)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts u)
    (hPU : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root) : Anc (tr.HonestBlocksAt H) B P := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

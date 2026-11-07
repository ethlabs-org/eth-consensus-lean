module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs

public section

/-! # Reset-source boundary for downstream kernel consumers

The reset lower bound uses health and counted fast-lock voters, not Catch service.
The seed is extracted from the reset signing itself. The finite result-prefix boundary
reads every writer, cast and vote at its own cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Health supplies a snapshot-honest counted voter behind every reset signing. -/
theorem cutZ_lt_reset_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hh : tr.HealthyRunAt H ΔF g)
    (hR : IsReset tr H g a) :
    cutZ sp.toParams g < a := by
  sorry

/-- Step 6 source supplier: an honestly signed reset has an earlier bounded high-origin seed. -/
theorem ResetPremisesUpTo.reset_seed_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ a ∧ l ≤ sp.slot a := by
  sorry

/-- Step 6 timing wrapper: the seed precedes every slot after the unchanged drain deadline. -/
theorem ResetPremisesUpTo.reset_seed_before_slot_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ b ∧ l < u ∧
      tr.time r < sp.ts u := by
  sorry

/-- Step 6 finite result induction, consumed by the latest-votes wrapper.
The explicit domain and stored-lock inputs are unchanged from the static boundary. -/
theorem ResetPremisesUpTo.late_result_prefix_votes_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
        s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      SA.CastAt tr.projAC y i ell e → s < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

/-- R2: every later-label honest cast extends each high origin within the finite horizon.
The origin write need not precede the cast; its writer's honesty is carried by HighOrigin. -/
theorem ResetPremisesUpTo.high_origin_votes_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → SA.CastAt tr.projAC y k ell e → j < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

/-- R1: high origins within the horizon are comparable, with each writer honest at its write. -/
theorem ResetPremisesUpTo.origins_compatible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

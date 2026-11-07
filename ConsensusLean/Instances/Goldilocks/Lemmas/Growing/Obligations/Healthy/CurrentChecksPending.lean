module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy

public section

/-! # Pending reset-kernel interface of the current-read checks

The growing forms of the reset-kernel facts the current-read checks (`CurrentChecks`) consume,
under their agreed names, whose homes are the growing reset kernel and its clean cluster:

* `ResetPremisesUpTo.reset_seed_held_at_read_at` (`reset_seed_held_at_read`): a bounded high seed
  before a post-drain slot, held at a later read whenever it is above the reader's finalization;
* `ResetPremisesUpTo.clean_stored_locks_compatible_at` (`clean_stored_locks_compatible`): two clean
  stored locks of a reader honest at its read compare;
* `ResetPremisesUpTo.clean_source_compatible_high_origin_at`: a clean source compares with every
  bounded high origin;
* `ResetPremisesUpTo.clean_source_stored_lock_compatible_at`: a clean source compares with the
  clean stored locks of a reader honest at its read;
* `ResetPremisesUpTo.result_prefix_stored_locks_at`: the time-live stored locks at a successor
  cast compare with an actual result's prefix;
* `ProposalImpl.result_prefix_vote_domain_before_at`: an actual result's prefix is in the vote
  domain of every later cast.

Each source's writer is honest at its own write, each reader at its read time.
Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

namespace ResetPremisesUpTo

/-- A bounded high seed before a post-drain slot, held at a later read of a reader honest at it
whenever it is above the reader's finalization. -/
theorem reset_seed_held_at_read_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} {n u : Nat} {t : Time}
    (hrp : Regimes.ReadPoint tr n t) (htb : t ≤ b) (hy : y ∈ H t)
    (hdrain : drainTime sp a ≤ sp.ts u) (hgst : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hbefore : sp.ts u + 6 * sp.Δ < t) :
    ∃ v r l S, HighOrigin tr H g v r l S ∧ tr.time r ≤ b ∧ l < u ∧
      tr.time r < sp.ts u ∧
      (Anc (tr.HonestBlocksAt H) (tr.state y n).fg.F S → S ∈ (tr.state y n).fg.tree) := by
  sorry

/-- Two clean stored locks of a reader honest at its read time compare. -/
theorem clean_stored_locks_compatible_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b)
    {l m : SA.Lock} (hl : l ∈ (tr.projAC.state y i).locks)
    (hm : m ∈ (tr.projAC.state y i).locks)
    (hls : cleanLabel sp a + sp.k + 2 ≤ l.slot)
    (hms : cleanLabel sp a + sp.k + 2 ≤ m.slot)
    {B C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hBr : B.root = l.block)
    (hC : C ∈ tr.HonestBlocksAt H) (hCr : C.root = m.block) :
    Compatible (tr.HonestBlocksAt H) B C := by
  sorry

/-- A clean source compares with every bounded high origin. -/
theorem clean_source_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) C D := by
  sorry

/-- A clean source compares with the clean stored locks of a reader honest at its read time. -/
theorem clean_source_stored_lock_compatible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} {t : Time} (hx : x ∈ H (tr.time r))
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hB : SA.ResultAt tr.projAC x r s B CV ∨ SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) {l : SA.Lock}
    (hl : l ∈ (tr.projAC.state y i).locks) (hls : cleanLabel sp a + sp.k + 2 ≤ l.slot)
    (hC : C ∈ tr.HonestBlocksAt H) (hCr : C.root = l.block) :
    Compatible (tr.HonestBlocksAt H) B C := by
  sorry

/-- The time-live stored locks at a successor cast compare with an actual result's prefix. -/
theorem result_prefix_stored_locks_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B := by
  sorry

end ResetPremisesUpTo

namespace ProposalImpl

/-- An actual result's prefix is in the vote domain of every later cast of a node honest at it. -/
theorem result_prefix_vote_domain_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  sorry

end ProposalImpl

end Consensus.Goldilocks.Healing.Growing

end

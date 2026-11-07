module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending interface of the clean source votes

The growing forms of the two result-prefix lemmas that the clean source votes read, under
their agreed names, owned by the kernel and pivot ports. Each node is honest at its own cut, and
ancestry is over `HonestBlocksAt`:

* `ResetPremisesUpTo.late_result_prefix_votes_before_at` (`Kernel/ResetFacts`): the finite
  latest-result induction;
* `ProposalImpl.result_prefix_vote_domain_before_at`: a result prefix is below the frame root of a
  later vote, or viable in its voter block tree;
* `ResetPremisesUpTo.held_target_vote_domain_before_at`,
  `ResetPremisesUpTo.target_compatible_older_origin_at` and
  `ResetPremisesUpTo.target_compatible_later_origin_before_at` (`Kernel/ResetFacts`): the
  held-target vote domain and its comparisons with older and later high origins.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

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

/-- A clean result prefix, written by a node honest at its write, is below the frame root of a
later vote of a node honest at it, or viable in its voter block tree, given the earlier votes. -/
theorem ProposalImpl.result_prefix_vote_domain_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hsi : s < e.msg.slot) (hib : tr.time i ≤ b)
    (hprior : ∀ z q, z ∈ H (tr.time q) → q < i → ∀ e', SA.VoteAt tr.projAC z q e' →
      s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  sorry

/-- Finite domain reduction with independently honest source and cast observations. -/
theorem ResetPremisesUpTo.held_target_vote_domain_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b) (hm : m < e.msg.slot)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hseedCompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) S O)
    (hpair : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
      Compatible (tr.HonestBlocksAt H) O O') :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  sorry

/-- An actual bounded supporter compares its target with an older bounded high origin. -/
theorem ResetPremisesUpTo.target_compatible_older_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x z : Fin sp.n} {r m q l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    {e : SA.Em sp (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hrb : tr.time r ≤ b)
    (hz : z ∈ H (tr.time q)) (hv : SA.VoteAt tr.projAC z q e) (hqb : tr.time q ≤ b)
    (hs : e.msg.slot = l) (hml : m < l)
    (hB : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  sorry

/-- Prior honest head support compares a target with a later bounded controlling origin. -/
theorem ResetPremisesUpTo.target_compatible_later_origin_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {r m i l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hrb : tr.time r ≤ b) (hlm : l < m)
    (hsupport : ∀ z q e, q < i → Compose.Growing.HVoteAt tr H z q e →
      l < e.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

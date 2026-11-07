module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation

public section

/-! # Pending interface of the conditional healed-safety port

Stated under their owners' final names and signatures so that the port compiles before they land:

* `Simulation.noCollRun_simTraceAt`: collision freedom of the canonical growing trace;
* `Healing.Growing.ResetPremisesUpTo.latest_votes_of_recent_result_at`: the growing form of
  `Healing.ResetPremisesUpTo.latest_votes_of_recent_result`. The result's writer is honest at its
  cut, every cast and vote is by a node honest at its own cut, and ancestry is read in the blocks
  held while honest.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The canonical growing trace of a collision-free valid run has no block collision. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  sorry

end Consensus.Goldilocks.Simulation

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- A recent result of a node honest at its cut, whose later honest casts keep it in their
domain and whose next-slot casts hold no conflicting stored lock, is extended by every vote of
label `L > s`, by `t ≤ b`, of a node honest at its vote. -/
theorem ResetPremisesUpTo.latest_votes_of_recent_result_at {b t : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x : Fin sp.n} {r s L : Nat}
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
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B)
    (htb : t ≤ b) (hsL : s < L) :
    ∀ z q e, Compose.Growing.HVoteAt tr H z q e → tr.time q ≤ t →
      e.msg.slot = L → SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end

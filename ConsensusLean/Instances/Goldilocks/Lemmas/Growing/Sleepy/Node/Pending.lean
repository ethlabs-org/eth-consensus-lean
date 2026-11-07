module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # Pending node interface of the sleepy layer

Node-level statements the node, service and engine files consume whose home modules are not on
this branch yet, under their final names and statements:

* `sleepy_invariant_at` (home `Lemmas/Growing/Sleepy/Node/Induction`): the dynamic invariant
  through `b` from the finite service and the two count shapes;
* `ready_read_record_at` (home `Lemmas/Growing/Sleepy/Node/Read`): the ready read is the
  effective record;
* `later_transfer_step_at` (home `Lemmas/Growing/Sleepy/Node/Transfer`): the later transfer step
  for a protected block.

Each is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The Sleepy record invariant under growing faults** through `b ≥ 0`. -/
theorem sleepy_invariant_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) : SleepyInvariantUpTo tr H b := by
  sorry

/-- **The ready read up to `b` is the effective record** under growing faults. -/
theorem ready_read_record_at {b : Time} (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hinv : SleepyInvariantUpTo tr H b)
    (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBounds tr H b) {y : Fin sp.n} {j : Nat}
    {t : Time} (hrp : Regimes.ReadPoint tr j t) (ht0 : 0 ≤ t)
    (hready : Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y t) (htb : t ≤ b) :
    (∃ R ∈ (Node.frame (tr.state y j)).tree,
        R.root = (tr.state y j).ac.latestConfirmed ∧ Regimes.readAfter tr y j t = R) ∨
      ((¬ ∃ R ∈ (Node.frame (tr.state y j)).tree,
          R.root = (tr.state y j).ac.latestConfirmed) ∧
        Regimes.readAfter tr y j t = (tr.state y j).fg.F) := by
  sorry

/-- **The later transfer step for a protected block** under growing faults. -/
theorem later_transfer_step_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hall : ∀ x k e', HVoteAt tr H x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end

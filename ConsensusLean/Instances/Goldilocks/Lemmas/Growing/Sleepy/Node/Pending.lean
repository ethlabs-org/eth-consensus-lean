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
* `ready_read_record_at`, `SleepyInvariantUpTo.read_compatible_at`,
  `SleepyInvariantUpTo.effective_record_mono_at` (home `Lemmas/Growing/Sleepy/Node/Read`): the
  ready read is the effective record; reads of nodes honest at their read times are compatible;
  the effective record only extends;
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

/-- **Reads of nodes honest at their read times are compatible** up to `b`. -/
theorem SleepyInvariantUpTo.read_compatible_at {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y y' : Fin sp.n}
    {i i' : Nat} {t t' : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (ht0' : 0 ≤ t') (hi' : ∀ k < i', tr.time k ≤ t') (htb' : t' ≤ b)
    (hy' : y' ∈ H t') (u u' : Time) :
    Compatible (tr.HonestBlocksAt H)
      ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) u)
      ((goldilocksNode sp ro).confirmed (tr.state y' i').ac (Node.frame (tr.state y' i')) u') := by
  sorry

/-- **The effective record only extends** up to `b`, for a node honest at a time `t' ≤ b` at or
after every cut before `j`. -/
theorem SleepyInvariantUpTo.effective_record_mono_at {b : Time}
    (hinv : SleepyInvariantUpTo tr H b) (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {i j : Nat} {t' : Time} (hij : i ≤ j)
    (ht0 : 0 ≤ t') (hj : ∀ k < j, tr.time k ≤ t') (ht'b : t' ≤ b) (hy : y ∈ H t') :
    Anc (tr.HonestBlocksAt H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (Node.frame (tr.state y i)).F)
      ((SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (Node.frame (tr.state y j)).F) := by
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

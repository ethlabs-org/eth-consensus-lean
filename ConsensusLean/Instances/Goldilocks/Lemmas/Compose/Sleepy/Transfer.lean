module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: the next vote batch (extending `V_s` to `V_{s+1}`)

workbench#11 §2.3, §2.4 and §4 "Extend the vote frontier, simultaneously". Fix an honest
slot-`(s+1)` vote, and assume `P_{s+1}`, `V_s` and that the honest slot-`(s+1)` votes at earlier
cuts extend the block in question (the first-bad-vote argument). The lock and later-batch steps
are stated for a block `B` with the hypotheses they use, so that the proposal-adoption bootstrap
(workbench#12 §4) applies them to the protected proposal; for an origin `C` of label `j ≤ s`:

* **Locks** (`vote_locks_compatible`): every live lock block after the unlocking is compatible
  with `C`: a lock of slot at most `s` sits below an origin of its slot, compared with `C` by
  `P_{s+1}`; one of slot `s + 1` is optimistic and was selected over earlier honest
  slot-`(s+1)` votes, which extend `C` (`SA.locks_compatible`).
* **First transfer** (`first_transfer_step`, `j = s`): `C` at or below `fc_root` (the vote's head
  extends `fc_root`), or, with `vote_frame` and the transport (`result_carry`,
  `optimistic_carry`, `result_writer_pool`), A1.8 for a result and A1.4 (a) for an optimistic
  selection.
* **Later batch** (`later_transfer_step`, `j < s`): the slot-`s` honest votes all extend `C`
  (`V_s`); the more than `f` of them cast by the validators awake and joined at `t_s + Δ` are held
  and resolved at the vote freeze, and only faulty seats oppose or equivocate, so `C`'s children
  towards the vote win the walk (`SA.isBest_of_majority`, `SA.anc_getHead`).
* `votes_below_succ`: strong induction on the cut index over the slot-`(s+1)` votes. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **The live locks at a slot-`(s+1)` vote are compatible with `B`**, a block compatible with
every origin of label at most `s` that the earlier honest slot-`(s+1)` votes extend. -/
theorem vote_locks_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, Origin tr H C j → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L B := by
  sorry

/-- **First transfer** (§2.3): an honest slot-`(s+1)` vote extends an origin `C` of label `s`
that the earlier honest slot-`(s+1)` votes extend. -/
theorem first_transfer_step (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hC : Origin tr H C s)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) C) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  sorry

/-- **Later batch** (§2.4): an honest slot-`(s+1)` vote extends a block `B` that every honest
slot-`s` vote extends, compatible with every origin of label at most `s`, and extended by the
earlier honest slot-`(s+1)` votes (an origin of label `j < s` by `V_s` and `P_{s+1}`; a protected
proposal by its common batch, workbench#12 §4, S2P). -/
theorem later_transfer_step (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, Origin tr H C j → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hall : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hE : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  sorry

/-- **Extending the vote frontier**: `P_{s+1}` and `V_s` give `V_{s+1}`. -/
theorem votes_below_succ (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) : VotesBelow tr H (s + 1) := by
  sorry

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: the next vote batch (extending `V_s` to `V_{s+1}`)

workbench#11 §2.3, §2.4 and §4 "Extend the vote frontier, simultaneously". Fix an honest
slot-`(s+1)` vote, and assume `P_{s+1}`, `V_s` and that the honest slot-`(s+1)` votes at earlier
cuts extend every origin of label at most `s` (the first-bad-vote argument). For every origin `C`
of label `j ≤ s`:

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

/-- The honest slot-`σ` votes at cuts before `i` extend every origin of label at most `s`. -/
def EarlierExtendAll (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (i σ s : Nat) : Prop :=
  ∀ C j, Origin tr H C j → j ≤ s → SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) i σ C

/-- **The live locks at a slot-`(s+1)` vote are compatible with the origins of labels at most
`s`.** -/
theorem vote_locks_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) (hE : EarlierExtendAll tr H i (s + 1) s)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} (hC : Origin tr H C j) (hj : j ≤ s) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L C := by
  sorry

/-- **First transfer** (§2.3): an honest slot-`(s+1)` vote extends every origin of label `s`. -/
theorem first_transfer_step (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hE : EarlierExtendAll tr H i (s + 1) s) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : Origin tr H C s) : SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  sorry

/-- **Later batch** (§2.4): an honest slot-`(s+1)` vote extends every origin of label `j < s`. -/
theorem later_transfer_step (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hE : EarlierExtendAll tr H i (s + 1) s) {C : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hC : Origin tr H C j) (hj : j < s) : SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
  sorry

/-- **Extending the vote frontier**: `P_{s+1}` and `V_s` give `V_{s+1}`. -/
theorem votes_below_succ (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1))
    (hV : VotesBelow tr H s) : VotesBelow tr H (s + 1) := by
  sorry

end Consensus.Goldilocks.Compose

end

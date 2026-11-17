module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Retained-record provenance under growing faults

The node-local record facts of `Lemmas/Obligations/HealthyRecordGeometry` for a node honest at a
read time `t`, every earlier cut at a time `≤ t`: each holds on the prefix through `t`, where the
node is honest throughout, and is read back on the run. -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- **An unchanged record keeps its lookup back to an earlier cut**: for a node honest at `t`,
every cut before `j` at a time `≤ t`, a record looked up before `j` and unchanged since `i ≤ j` is
already looked up before `i` (advancing finalization cannot bring it back into the frame). -/
theorem record_lookup_of_later_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i j : Nat} {t : Time} (ht : 0 ≤ t)
    (hjt : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t) (hij : i ≤ j)
    (heq : (tr.state y j).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed = some R) :
    SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed = some R := by
  have hj := Trace.upTo_state tr y hjt
  have hi := Trace.upTo_state tr y fun k hk => hjt k (hk.trans_le hij)
  have h := record_lookup_of_later (hrun.upTo ht) (hnc.upTo t) hy hij
    (by rw [hi, hj]; exact heq) (by rw [hj]; exact hR)
  rwa [hi] at h

/-- **One step of a node's record**, for a node honest at the step: the record is unchanged, or
it names a block of its tree with a result or optimistic-lock source of its own at the step. -/
theorem record_step_origin_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    (tr.state y (i + 1)).ac.latestConfirmed = (tr.state y i).ac.latestConfirmed ∨
      ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y (i + 1)).ac.latestConfirmed ∧
        ∃ s CV, SA.ResultAt tr.projAC y i s C CV ∨
          SA.OptimisticLockAt tr.projAC y i s C CV := by
  have hle : ∀ k < i + 1, tr.time k ≤ tr.time i :=
    fun k hk => hrun.time_mono (Nat.le_of_lt_succ hk)
  have h1 := Trace.upTo_state tr y hle
  have h0 := Trace.upTo_state tr y fun k hk => hle k (hk.trans (Nat.lt_succ_self i))
  rcases Compose.record_step_origin (hrun.upTo (hrun.time_nonneg i)) hy i with
    h | ⟨C, hC, hCr, s, CV, hs⟩
  · rw [h1, h0] at h
    exact Or.inl h
  · rw [h0] at hC
    rw [h1] at hCr
    rw [RunTrace.upTo_projAC] at hs
    refine Or.inr ⟨C, hC, hCr, s, CV, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl ((Compose.Growing.sa_resultAt_upTo hrun.time_mono).mp hs).2
    · exact Or.inr ((Compose.Growing.sa_optimisticLockAt_upTo hrun.time_mono).mp hs).2

end Consensus.Goldilocks.Obligations.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyEffective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # The effective record under growing faults

The trace part of `Lemmas/Obligations/HealthyEffective` for a node honest at a read time `t`,
every earlier cut at a time `≤ t`; the frame and write lemmas there are generic in the block set
and are used with the blocks held while honest. The node's own steps are read on the prefix
through `t`, where it is honest throughout; ancestry and compatibility are in the blocks held
while honest.

* `EffectiveRecordIntervalAt`: the interval contract of one earlier output, each step a guarded
  write with candidates compatible with the output and a compatible floor, or a replacement
  record extending it;
* `effective_record_frame_of_run_at`: a fixed record survives a floor change of the node;
* `effectiveRecordInterval_of_candidates_before_at`: the node's results and optimistic
  selections in the interval, compatible with the output, and compatible floors give the
  interval;
* `effective_record_of_interval_at`: the interval preserves the effective record;
* `effective_record_after_ac_call_at`: an AC call's effective post-record is the node's next
  effective record (a node honest at its call). -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}

/-- **The interval contract of one earlier output** under growing faults: each transition of the
node from `i` to `j` is a guarded write in the old frame with candidates compatible with `O`
followed by a compatible floor, or a replacement effective record extending `O`. -/
structure EffectiveRecordIntervalAt (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n))
    (y : Fin sp.n) (i j : Nat) (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  step : ∀ q, i ≤ q → q < j →
    (∃ New : SA.Blk sp.n (List (FG.Att sp.n)) → Prop,
      Compose.Writes (Node.frame (tr.state y q)) New
        (tr.state y q).ac.latestConfirmed (tr.state y (q + 1)).ac.latestConfirmed ∧
      (∀ D, New D → Compatible (tr.HonestBlocksAt H) O D) ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y (q + 1)).fg.F O) ∨
    Anc (tr.HonestBlocksAt H) O
      ((SA.lookup (Node.frame (tr.state y (q + 1)))
        (tr.state y (q + 1)).ac.latestConfirmed).getD (tr.state y (q + 1)).fg.F)

/-- **A fixed record survives the node's floor change**, for a node honest at `t`, every cut
before `j` at a time `≤ t`: a record looked up at `i ≤ j` that extends `O` still extends it at
`j` when the new floor is compatible with `O`. -/
theorem effective_record_frame_of_run_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i j r : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hjt : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t) (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hFO : Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.F O)
    (hO : Anc (tr.HonestBlocksAt H) O
      ((SA.lookup (Node.frame (tr.state y i)) r).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocksAt H) O
      ((SA.lookup (Node.frame (tr.state y j)) r).getD (tr.state y j).fg.F) := by
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hit : ∀ k < i, tr.time k ≤ t := fun k hk => hjt k (by omega)
  have hsti := Trace.upTo_state tr y hit
  have hstj := Trace.upTo_state tr y hjt
  have hr := hrun.upTo ht0
  have hreach := Compose.Growing.fg_reachable_at hrun ht0 hjt hy
  have hΨ := (Store.frame_realization _ _ _ _ hreach).1
  have hFF : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y j).fg.F := by
    have h := Healing.run_F_mono hr.toLocalRun hy hij
    rw [hsti, hstj] at h
    exact h.mono (Compose.Growing.upTo_subset hrun ht0)
  apply effective_record_frame_of_compatible hU (Φ := Node.frame (tr.state y i)) hΨ
    (fun X hX => Compose.Growing.tree_subset_at ht0 hit hy hX.1)
    (fun X hX => Compose.Growing.tree_subset_at ht0 hjt hy hX.1) hFF hFO ?_ hO
  intro C hC hFC
  have hCj : C ∈ (tr.state y j).fg.tree := by
    have h := Compose.tree_mono hr.toLocalRun hy hij
    rw [hsti, hstj] at h
    exact h hC.1
  obtain ⟨hfin, htc, hgm, hgen⟩ := Store.accepted_tree _ _ _ _ hreach
  have hfull : FrameOK (⟨(tr.state y j).fg.tree, _, _, ∅⟩ :
      Frame sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)) :=
    { finite := hfin, coherent := htc, rooted := ⟨hgm, hgen⟩, fcRoot_mem := hgm
      F_anc_fcRoot := .refl, viableHeads_subset := Set.empty_subset _
      fcRoot_anc_viableHeads := fun _ h => h.elim }
  exact ⟨hCj, SA.anc_tree_of_anc_U hU hfull
    (fun X hX => Compose.Growing.tree_subset_at ht0 hjt hy hX) hΨ.rooted.1.1 hFC hCj⟩

/-- **The node's own candidates supply the interval**, for a node honest at `t`, every cut
before `j` at a time `≤ t`: when its results and optimistic selections at the cuts of `[i, j)`
are compatible with `O`, and so are its floors after them, each step is a guarded write of those
candidates (the static call-write decomposition on the prefix through `t`). -/
theorem effectiveRecordInterval_of_candidates_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i j : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hjt : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t) {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcandidates : ∀ q, i ≤ q → q < j → ∀ D s CV,
      SA.ResultAt tr.projAC y q s D CV ∨ SA.OptimisticLockAt tr.projAC y q s D CV →
      Compatible (tr.HonestBlocksAt H) O D)
    (hframes : ∀ q, i ≤ q → q < j →
      Compatible (tr.HonestBlocksAt H) (tr.state y (q + 1)).fg.F O) :
    EffectiveRecordIntervalAt tr H y i j O := by
  have hr := hrun.upTo ht0
  have hnc' := hnc.upTo t
  have hac := Compose.goldilocks_ac_projection sp ro dg (H t) (tr.upTo t) proposer hr hnc'
  have hst := Compose.projAC_state hr.toLocalRun hy
  refine ⟨fun q hiq hqj => Or.inl ?_⟩
  have hq0 : ∀ k < q, tr.time k ≤ t := fun k hk => hjt k (by omega)
  have hq1 : ∀ k < q + 1, tr.time k ≤ t := fun k hk => hjt k (by omega)
  refine ⟨(fun D => ∃ s CV, SA.ResultAt tr.projAC y q s D CV ∨
    SA.OptimisticLockAt tr.projAC y q s D CV), ?_,
    fun D ⟨s, CV, hD⟩ => hcandidates q hiq hqj D s CV hD, hframes q hiq hqj⟩
  have hw : Compose.Writes (Node.frame ((tr.upTo t).state y q))
      (fun D => ∃ s CV, SA.ResultAt (tr.upTo t).projAC y q s D CV ∨
        SA.OptimisticLockAt (tr.upTo t).projAC y q s D CV)
      ((tr.upTo t).state y q).ac.latestConfirmed
      ((tr.upTo t).state y (q + 1)).ac.latestConfirmed := by
    by_cases hcall : ∃ ell, (tr.upTo t).projAC.CallAt y q ell
    · obtain ⟨ell, hcall⟩ := hcall
      have hw := Compose.call_writes hac.localRun hy hcall
      rw [← (tr.upTo t).projAC.state_succ_of_call hcall, hst, hst,
        Compose.frame_of_projAC hr hy hcall] at hw
      exact hw
    · have he : ((tr.upTo t).state y (q + 1)).ac.latestConfirmed =
          ((tr.upTo t).state y q).ac.latestConfirmed := by
        rw [← hst, (tr.upTo t).projAC.state_succ_of_not (fun ell h => hcall ⟨ell, h⟩), hst]
      rw [he]
      exact Compose.writes_iff.mpr .refl
  rw [Trace.upTo_state tr y hq0, Trace.upTo_state tr y hq1] at hw
  refine hw.mono ?_
  rintro D ⟨s, CV, h | h⟩
  · rw [RunTrace.upTo_projAC] at h
    exact ⟨s, CV, Or.inl ((Compose.Growing.sa_resultAt_upTo hrun.time_mono).mp h).2⟩
  · rw [RunTrace.upTo_projAC] at h
    exact ⟨s, CV, Or.inr ((Compose.Growing.sa_optimisticLockAt_upTo hrun.time_mono).mp h).2⟩

/-- **The interval preserves the effective record**, for a node honest at `t`, every cut before
`j` at a time `≤ t`. -/
theorem effective_record_of_interval_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i j : Nat} {t : Time} (ht0 : 0 ≤ t)
    (hjt : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t) (hij : i ≤ j)
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hint : EffectiveRecordIntervalAt tr H y i j O)
    (hO : Anc (tr.HonestBlocksAt H) O ((SA.lookup (Node.frame (tr.state y i))
      (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F)) :
    Anc (tr.HonestBlocksAt H) O ((SA.lookup (Node.frame (tr.state y j))
      (tr.state y j).ac.latestConfirmed).getD (tr.state y j).fg.F) := by
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hr := hrun.upTo ht0
  have step : ∀ q, i ≤ q → q ≤ j → Anc (tr.HonestBlocksAt H) O
      ((SA.lookup (Node.frame (tr.state y q)) (tr.state y q).ac.latestConfirmed).getD
        (tr.state y q).fg.F) := by
    intro q hiq
    induction q, hiq using Nat.le_induction with
    | base => exact fun _ => hO
    | succ q hiq ih =>
      intro hqj
      have hq0 : ∀ k < q, tr.time k ≤ t := fun k hk => hjt k (by omega)
      have hq1 : ∀ k < q + 1, tr.time k ≤ t := fun k hk => hjt k (by omega)
      rcases hint.step q hiq (by omega) with ⟨New, hw, hnew, hF⟩ | hreset
      · have hΦ : FrameOK (Node.frame (tr.state y q)) := by
          have h := Compose.frameOK_state hr.toLocalRun hy q
          rwa [Trace.upTo_state tr y hq0] at h
        have hwritten := effective_record_writes_of_compatible hU hΦ
          (fun X hX => Compose.Growing.tree_subset_at ht0 hq0 hy hX.1) hw hnew (ih (by omega))
        exact effective_record_frame_of_run_at hrun hnc ht0 hq1 hy (Nat.le_succ q) hF hwritten
      · exact hreset
  exact step j hij le_rfl

/-- **An AC call's effective post-record is the node's next effective record**, for a node
honest at its call: AC execution changes neither FG nor its frame. -/
theorem effective_record_after_ac_call_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell) {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Anc (tr.HonestBlocksAt H) P
      ((SA.lookup ell.frame (tr.projAC.post j).latestConfirmed).getD ell.frame.F)) :
    Anc (tr.HonestBlocksAt H) P
      ((SA.lookup (Node.frame (tr.state y (j + 1)))
        (tr.state y (j + 1)).ac.latestConfirmed).getD (tr.state y (j + 1)).fg.F) := by
  have hd := hrun.time_nonneg j
  have hle : ∀ k < j + 1, tr.time k ≤ tr.time j := fun k hk => hrun.time_mono (by omega)
  have hc' := Compose.projAC_callAt.mp hc
  have hlaw := hrun.cutLaw y j _ hc' hy
  have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
    rw [tr.state_succ_of_call hc', hlaw.1]
    exact congrArg Store.toFrame hlaw.2.2.1
  have hstate : tr.projAC.post j = (tr.state y (j + 1)).ac := by
    have h := Compose.projAC_state (hrun.upTo hd).toLocalRun hy (j + 1)
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y hle, Trace.upTo_state tr y hle,
      tr.projAC.state_succ_of_call hc] at h
    exact h
  change Anc (tr.HonestBlocksAt H) P
    ((SA.lookup (Node.frame (tr.state y (j + 1)))
      (tr.state y (j + 1)).ac.latestConfirmed).getD (Node.frame (tr.state y (j + 1))).F)
  rw [hframe, ← hstate]
  exact hP

end Consensus.Goldilocks.Obligations.Growing

end

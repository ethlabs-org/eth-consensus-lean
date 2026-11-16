module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read

public section

/-! # Goldilocks local supplier fields

Fields of the intended Goldilocks local supplier (`goldilocksACCorrectLocal`) at its data
equations (`GoldilocksLocalData`), over the shared run interface `goldilocksRunInterface`:

* `served_of_delivered`: `goldilocks_served_of_delivered`, fresh delivery is the first disjunct
  of the retained-evidence service `SA.FamilyFacts.MessageServedBefore` on the AC projection;
* `tipsValid`: `goldilocks_tips_at` at the reader's own cut time. It holds at every read of a
  reader honest at some time `t ≥ 0` after its earlier cuts, at every evaluation time;
* `goldilocks_localReadPoint`: the `LocalReadPoint` row, `goldilocks_tips_at` at an honest read
  point for every supplier whose runs are those of `goldilocksRunInterface`.

The durations, the recovery bound and the payload are the data equations themselves. The
healing field is the committee-indexed healing supplier (`goldilocksACHealing`).
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- `served_of_delivered`: a message processed before its recipient deadline is served. -/
theorem goldilocks_served_of_delivered {tr : GoldilocksTrace sp ro} {y : Fin sp.n} {j : Nat}
    {τ : Time} {m : (goldilocksNode sp ro).Msg} (h : tr.MsgDeliveredBy y j τ τ m) :
    SA.FamilyFacts.MessageServedBefore tr.projAC y j τ m := by
  obtain ⟨k, hkj, htk, hp, hlt⟩ := h
  refine Or.inl ⟨k, hkj, htk, ?_, by rw [Compose.projAC_deadline]; exact hlt⟩
  rcases hp with ⟨ℓ, hc, hm⟩ | ⟨ℓ, hc, hm⟩
  exacts [⟨ℓ, Compose.projAC_callAt.2 hc, Or.inl hm⟩, ⟨ℓ, Compose.projAC_callAt.2 hc, Or.inr hm⟩]

/-- The confirmed tip of a reader honest at `t ≥ 0`, before a cut whose earlier cuts are at or
before `t`, is held in its frame between the finalized root and the head, at every evaluation
time: the reader's store is reachable (`fg_reachable_at`), so its frame is well formed
(`Store.frame_realization`) and the SA's tips lie in it (`Regimes.sa_tips`). -/
theorem goldilocks_tips_at {cm : Time → Finset (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} (hrun : (goldilocksRunInterface sp ro).Run cm proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ k < i, tr.time k ≤ t)
    (hy : y ∈ H t) (s : Time) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) s ∈
        (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (tr.finalizedAt y i)
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) s) ∧
      (Node.frame (tr.state y i)).Anc
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) s)
        ((goldilocksNode sp ro).head (tr.state y i).ac (Node.frame (tr.state y i)) s) := by
  have hr := Compose.Growing.fg_reachable_at ((goldilocksRunInterface_run_iff cm).mp hrun).1
    ht0 hle hy
  have hΦ := (Store.frame_realization _ _ _ _ hr).1
  obtain ⟨hC, hCH⟩ := Regimes.sa_tips (A := (tr.state y i).ac) hΦ s
  exact ⟨hC, hΦ.rooted.2 _ hC, hCH⟩

/-- The local read-point row: at an honest read point, the confirmed read is held in the frame
between the finalized root and the head (`goldilocks_tips_at`), hence in the FG tree. -/
theorem goldilocks_localReadPoint (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val))
    (hrun : GoldilocksRunData sp ro C.run) : LocalReadPoint C where
  tips cm proposer dg H tr h b y i t hr := by
    rw [hrun.1] at h
    exact goldilocks_tips_at (cm := cm) ((goldilocksRunInterface_run_iff cm).mpr h) hr.2.2.1
      hr.2.1.1 hr.1 t
  held cm proposer dg H tr h b y i t hr := by
    rw [hrun.1] at h
    exact (goldilocks_tips_at (cm := cm) ((goldilocksRunInterface_run_iff cm).mpr h) hr.2.2.1
      hr.2.1.1 hr.1 t).1.1

end Consensus.Goldilocks.Generic

end

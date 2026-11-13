module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FreshLock

public section

/-! # Older locks after an honest next-slot unlock

Only the receiver's execution through the receiving cut is retained. The supporting
committee belongs to the unlock frame, rather than a run-wide honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A supporting half-committee clears old incompatible labels for a receiver that
is still honest at the later observation. -/
theorem older_locks_compatible_after_unlock_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {j k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hs : e.msg.slot = u + 1) (hjk : j < k)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    {S : Set (Fin sp.n)}
    (hS : ∀ x ∈ S,
      x ∈ SA.equivocators (SA.mergedVoteView sp e.readPoint ell.frame (u + 1)).votes ∨
        ∃ v ∈ (SA.mergedVoteView sp e.readPoint ell.frame (u + 1)).support,
          v.val = x ∧ (v.slot : Int) = u ∧ SA.AncR ell.frame P v.head)
    (hhalf : sp.n ≤ 2 * S.ncard) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P := by
  have hd := hrun.time_nonneg k
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer (hrun.upTo hd) (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time k)) y j ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨hrun.time_mono hjk.le, hc.1⟩, hc.2⟩
  have hstate := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  intro l hl hls L hL hLr
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state y k).locks := by
    rwa [hstate]
  obtain ⟨_, _, _, _, R, hR, hRr, _⟩ := SA.lock_provenance hr hy k l hl'
  have hLR : L = R := (Compose.Growing.honest_blocks_coherent hrun hnc).1
    hL (hsub hR) (hLr.trans hRr.symm)
  subst L
  exact (SA.older_locks_compatible_after_unlock hr hy hc' hs hjk hPt hS
    (by simpa only [hrun.stock] using hhalf)
    l hl' hls R hR hRr).imp (Anc.mono hsub) (Anc.mono hsub)

end Consensus.Goldilocks.Healing.Growing

end

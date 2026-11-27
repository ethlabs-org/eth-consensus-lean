module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FreshLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts

public section

/-! # Older locks after an honest next-slot unlock

Only the receiver's execution through the receiving cut is retained. The supporting
committee belongs to the unlock frame, rather than a run-wide honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- A vote branch of the prefix through `d` is a vote branch of the run at a time `≤ d`. -/
theorem voteBranchAt_upTo_iff (hm : Monotone tr.time) {d : Time} {y : Fin sp.n} {j : Nat}
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n} :
    AC.VoteBranchAt (tr.projAC.upTo d) y j ell R ↔
      tr.time j ≤ d ∧ AC.VoteBranchAt tr.projAC y j ell R := by
  have hs (ht : tr.time j ≤ d) := Trace.upTo_state tr.projAC y (d := d) (i := j)
    fun _ hk => (hm hk.le).trans ht
  rw [AC.voteBranchAt_iff, AC.voteBranchAt_iff]
  constructor
  · rintro ⟨hc, hrest⟩
    have ht := ((Trace.upTo_callAt _).mp hc).1
    rw [hs ht] at hrest
    exact ⟨ht, ((Trace.upTo_callAt _).mp hc).2, hrest⟩
  · rintro ⟨ht, hc, hrest⟩
    refine ⟨(Trace.upTo_callAt _).mpr ⟨ht, hc⟩, ?_⟩
    rw [hs ht]
    exact hrest

namespace Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- `older_locks_compatible_after_unlock_at` over a run bundle `GoldilocksRunCore`. -/
theorem older_locks_compatible_after_unlock_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {j k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n}
    (hb : AC.VoteBranchAt tr.projAC y j ell R) (hs : sp.slot (tr.time j) = u + 1) (hjk : j < k)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    {S : Set (Fin sp.n)}
    (hS : ∀ x ∈ S,
      x ∈ AC.equivocators (AC.mergedVoteView sp R ell.frame (u + 1)).votes ∨
        ∃ v ∈ (AC.mergedVoteView sp R ell.frame (u + 1)).support,
          v.val = x ∧ (v.slot : Int) = u ∧ AC.AncR ell.frame P v.head)
    (hhalf : sp.committeeSize ≤ 2 * S.ncard) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P := by
  have hd := hrun.time_nonneg k
  have hr := (hrun.acRun_upTo hnc hd).localRun
  have hb' : AC.VoteBranchAt (tr.projAC.upTo (tr.time k)) y j ell R :=
    (voteBranchAt_upTo_iff hrun.time_mono).2 ⟨hrun.time_mono hjk.le, hb⟩
  have hstate := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hsub := hrun.upTo_subset hd
  intro l hl hls L hL hLr
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state y k).locks := by
    rwa [hstate]
  obtain ⟨_, _, _, _, B, hB, hBr, _⟩ :=
    AC.lock_provenanceU (hr := hr.toU) hrun.vstart hy k l hl'
  have hLB : L = B := (hrun.coherent hnc).1
    hL (hsub hB) (hLr.trans hBr.symm)
  subst L
  exact (AC.older_locks_compatible_after_unlock_branch hr hy hb' hs hjk hPt hS hhalf
    l hl' hls B hB hBr).imp (Anc.mono hsub) (Anc.mono hsub)

end Core

/-- A supporting half-committee at a receiver's next-slot vote branch clears old incompatible
labels for a receiver that is still honest at the later observation, from starts up to the vote
permission. The branch need not emit, so the receiver need not vote in that slot. -/
theorem older_locks_compatible_after_unlock_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {j k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {R : AC.ACState sp.n}
    (hb : AC.VoteBranchAt tr.projAC y j ell R) (hs : sp.slot (tr.time j) = u + 1) (hjk : j < k)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    {S : Set (Fin sp.n)}
    (hS : ∀ x ∈ S,
      x ∈ AC.equivocators (AC.mergedVoteView sp R ell.frame (u + 1)).votes ∨
        ∃ v ∈ (AC.mergedVoteView sp R ell.frame (u + 1)).support,
          v.val = x ∧ (v.slot : Int) = u ∧ AC.AncR ell.frame P v.head)
    (hhalf : sp.committeeSize ≤ 2 * S.ncard) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P :=
  Core.older_locks_compatible_after_unlock_at hrun.toCore hnc hy hb hs hjk hPt hS hhalf

end Consensus.Goldilocks.Healing.Growing

end

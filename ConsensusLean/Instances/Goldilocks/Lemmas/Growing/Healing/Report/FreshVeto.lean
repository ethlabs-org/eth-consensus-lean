module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshViable

public section

/-! # No veto from compatible historical lock roots

Lock labels refer to historical honest blocks, while the veto is evaluated in the
receiver's current frame. Coherence bridges those two domains at the read cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Compatible historical roots cannot veto a proposal in the current frame. -/
theorem no_veto_of_lock_roots_compatible_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ell)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    (hlocks : ∀ l ∈ (tr.projAC.state y k).locks,
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P) :
    ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hPhi := SA.frameIn_of_callAt hr hy hc'
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono
    (hrun.time_nonneg k)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      Compatible (tr.HonestBlocksAt H) Y P → Compatible (tr.HonestBlocksAt H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hU hXY h
  rintro ⟨L, hLive, hconflict⟩
  obtain ⟨hLt, l', ⟨l, hl, B, hB, hBr, _, rfl⟩, hLr⟩ := hLive
  have hanc := SA.anc_viableAncestor ell.frame B
  have hLva : L = ell.frame.viableAncestor B :=
    hPhi.1.coherent.1 hLt (SA.mem_of_anc hanc hB) hLr.symm
  have hcomp := down (hLva ▸ hanc.mono (fun Q hQ => hsub (hPhi.2 hQ)))
    (hlocks l hl B (hsub (hPhi.2 hB)) hBr)
  apply hconflict
  rcases hcomp with h | h
  · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi.1 (fun Q hQ => hsub (hPhi.2 hQ)) hLt h hPt)
  · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi.1 (fun Q hQ => hsub (hPhi.2 hQ)) hPt h hLt)

end Consensus.Goldilocks.Healing.Growing

end

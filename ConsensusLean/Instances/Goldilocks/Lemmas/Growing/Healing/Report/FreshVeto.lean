module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Highest

public section

/-! # No veto from compatible historical lock roots

Lock labels refer to historical honest blocks, while the veto is evaluated in the
receiver's current frame. Coherence bridges those two domains at the read cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

namespace Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- Compatible historical roots cannot veto a proposal in the current frame, over a run bundle
`GoldilocksRunCore`. -/
theorem no_veto_of_lock_roots_compatible_at
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y k ell)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    (hlocks : ∀ l ∈ (tr.projAC.state y k).locks,
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P) :
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  have hr := (hrun.acRun_upTo hnc (hrun.time_nonneg k)).localRun
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hPhi := AC.frameIn_of_callAt hr hy hc'
  have hsub := hrun.upTo_subset (hrun.time_nonneg k)
  have hU := hrun.coherent hnc
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      Compatible (tr.HonestBlocksAt H) Y P → Compatible (tr.HonestBlocksAt H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact AC.anc_total hU hXY h
  intro hconf
  obtain ⟨L, hLive, hconflict⟩ := AC.exists_of_conflictsWithLock hconf
  obtain ⟨hLt, l', ⟨l, hl, B, hB, hBr, _, rfl⟩, hLr⟩ := hLive
  have hanc := AC.anc_viableAncestor ell.frame B
  have hLva : L = ell.frame.viableAncestor B :=
    hPhi.1.coherent.1 hLt (AC.mem_of_anc hanc hB) hLr.symm
  have hcomp := down (hLva ▸ hanc.mono (fun Q hQ => hsub (hPhi.2 hQ)))
    (hlocks l hl B (hsub (hPhi.2 hB)) hBr)
  apply hconflict
  rcases hcomp with h | h
  · exact Or.inr (AC.anc_tree_of_anc_U hU hPhi.1 (fun Q hQ => hsub (hPhi.2 hQ)) hLt h hPt)
  · exact Or.inl (AC.anc_tree_of_anc_U hU hPhi.1 (fun Q hQ => hsub (hPhi.2 hQ)) hPt h hLt)

end Core

/-- Compatible historical roots cannot veto a proposal in the current frame. -/
theorem no_veto_of_lock_roots_compatible_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hc : tr.projAC.CallAt y k ell)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPt : P ∈ ell.frame.tree)
    (hlocks : ∀ l ∈ (tr.projAC.state y k).locks,
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P) :
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P :=
  Core.no_veto_of_lock_roots_compatible_at hrun.toCore hnc hy hc hPt hlocks

end Consensus.Goldilocks.Healing.Growing

end

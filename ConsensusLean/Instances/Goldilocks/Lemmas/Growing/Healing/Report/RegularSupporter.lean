module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase

public section

/-! # The next votes after a supporter of label `s`, under growing faults

`Core.next_votes_of_supporter_at`: the window-free propagation step from a supporter's classified
cast head, independent of the frame's root policy. The stock-window classification wrapper
(`FrameWindow.next_votes_of_supporter_at`) is removed: its classification
(`vote_head_classification_of_service_at`) does not hold under P-U viability. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

namespace Core

/-- Classification and propagation are independent of the frame's root policy. -/
theorem next_votes_of_supporter_at
    {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    {ini : Fin sp.n → (goldilocksNode sp).State} {s : Nat}
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {z : Fin sp.n} {q : Nat} (hz : z ∈ H (tr.time q))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC z q ell e) (hes : e.msg.slot = s)
    (hQU : Q ∈ tr.HonestBlocksAt H) (hQr : Q.root = e.msg.head)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hclass : ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      (Hd ∈ ell.frame.viableHeads ∨ (kindJ ∧ Hd = J) ∨
        (Hd = AC.getAnchor sp e.readPoint ell.frame (tr.time q) ∧
          ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
          ∃ a ≤ q, ∃ D CV, z ∈ H (tr.time a) ∧
            AC.OptimisticLockAt tr.projAC z a e.msg.slot D CV ∧
            sp.ts e.msg.slot ≤ tr.time a ∧ tr.time a < sp.ts e.msg.slot + 2 * sp.Δ ∧
            3 * sp.committeeSize ≤ 4 * (AC.voters CV).ncard ∧ ell.frame.Anc Hd D)))
    (hbase : Q ∈ ell.frame.tree → Q ∈ ell.frame.viableHeads →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hcommon : kindJ → Q = J →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hoptimistic : Q = AC.getAnchor sp e.readPoint ell.frame (tr.time q) →
      ∀ a D CV, z ∈ H (tr.time a) → AC.OptimisticLockAt tr.projAC z a s D CV →
      Anc (tr.HonestBlocksAt H) Q D →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg Q) :
    ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X := by
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := hclass
  have hPhiU := (hrun.frameIn_at hnc hz hc.1).2
  have hEQ : Hd = Q := (hrun.coherent hnc).1
    (hPhiU hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | hj | ho
  · exact hbase hHd hv
  · exact hcommon hj.1 hj.2
  · obtain ⟨hA, l, hl, hls, a, hai, D, CV, hza, hop, -, -, -, hQD⟩ := ho
    have hheads := hoptimistic hA a D CV hza (hes ▸ hop) (hQD.mono hPhiU)
    intro y i ev hy hv hesv
    obtain ⟨W, hW, hWr, hQW⟩ := hheads y i ev hy hv hesv
    exact ⟨W, hW, hWr, hXQ.trans hQW⟩

end Core

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

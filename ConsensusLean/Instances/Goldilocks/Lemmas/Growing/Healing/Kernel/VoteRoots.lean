module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Vote domains from independently observed roots and seeds -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- An origin above the frame's finalized tip is held by every later-label honest voter. -/
theorem high_origin_held_at_vote_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {r l k : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFO : Anc (tr.HonestBlocksAt H) ell.frame.F O) :
    O ∈ (tr.state y k).fg.tree := by
  obtain ⟨W, hW, hOW⟩ := high_origin_frozen_head_at hp ho hrb hy hc hl hFO
  have hWy := (frame_tree_subset_at hp.run hp.noColl hy hc.1).2 hW.1
  exact mem_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg k)
    (fun _ hq => hp.run.time_mono hq.le) hy hOW hWy

/-- The low-root comparison specializes the shared held-seed supplier at a vote. -/
theorem low_root_of_seed_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hm : m < e.msg.slot)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  have hFS := hp.low_finalized_below_origin_at (hp.run.time_nonneg i)
    (fun _ hq => hp.run.time_mono hq.le) hy hib hlow hS hqb
  have hFF : ell.frame.F = (tr.state y i).fg.F := by
    rw [Outcome.frame_of_call hp.run hy hc.1]; rfl
  have hSy := high_origin_held_at_vote_at hp hS hqb hy hc hm (by rw [hFF]; exact hFS)
  exact hp.low_root_of_held_seed_at_call_at hx hBx hrb hy hib hS hqb hc.1 hSy hlow hBS
    (fun hFB => (hheld hFB).1)

/-- A viable frozen descendant yields the target's viable vote-domain membership. -/
theorem vote_viable_of_root_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcomp : Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot) :
    B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg k)).localRun
  have hc' := SA.upTo_castAt.mpr (And.intro le_rfl hc)
  obtain ⟨hPhi, hPhiTree⟩ := frame_tree_subset_at hp.run hp.noColl hy hc.1
  have hPhiU := Outcome.frame_tree_subset hp.run hy hc.1
  have hfr := Outcome.frame_of_call hp.run hy hc.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ell.frame.tree := hD.1
      have hFB := (Anc.mono hPhiU hPhi.F_anc_fcRoot).trans hfB
      have hBt := SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB
      have hPhiBD := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBD hDt
      have hPhifB := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hfB hBt
      refine Or.inl ⟨SA.voterBlockTree_anc hr hy hc' D hD B hPhiBD,
        hPhifB, D, hD, ?_, hPhiBD⟩
      have hfD := hPhifB.trans hPhiBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, Anc.mono (fun X hX => hX.1) hfD, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

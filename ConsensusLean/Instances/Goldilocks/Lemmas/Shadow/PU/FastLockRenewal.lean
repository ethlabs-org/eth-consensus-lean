module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FastLockRenewalCore
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.StockWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fast-lock candidates above a stock-window witness -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing
open Consensus.Goldilocks.Healing.Growing (CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro}

/-- A fast update above an independently held stock witness supplies a later candidate
through its two-slot lifetime. The witness stays viable even across a contest-to-gap change. -/
theorem toFG_candidate_of_fast_update_stock_at' {K : AC.CommitteeDict sp.n}
    {lo hi : Time} {floor : Nat} {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hK : CommitteeHalfUpTo tr H K g b)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ P.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J P)
    {r : Nat} (hgr : gbar g ≤ sp.ts (r + 1 : Nat))
    {y : Fin sp.n} {j : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hfu : AC.FastUpdateAt tr.projAC y j r D CV) (hPD : Anc (tr.HonestBlocksAt H) P D)
    {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hji : j < i)
    (hext : ∀ x k e, x ∈ H (tr.time k) → AC.VoteAt tr.projAC x k e → e.msg.slot = r + 1 →
      tr.time k ≤ tr.time i → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hjlo : lo ≤ tr.time j) (hihi : tr.time i ≤ hi) (hib : tr.time i ≤ b)
    (hslot : sp.slot (tr.time i) ≤ r + 2) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hcore := hrun.toCore
  have hmono := hrun.time_mono
  have hU := hcore.coherent hnc
  obtain ⟨ellj, C, hu, -, hD, -⟩ := id hfu
  have hji' := hmono hji.le
  have hyj := hrun.antitone hji' hy
  have hfrj := hcore.frame_of_projAC_at hyj hu.1
  obtain ⟨hΦj, hΦjU⟩ := hcore.frameIn_at hnc hyj hu.1
  have hDt := (AC.deepest_mem hD).1.1.1
  have hFPj : Anc (tr.HonestBlocksAt H) ellj.frame.F P := by
    rw [hfrj, hcore.frameOf_F]
    exact finalized_below_descendant_stock_at' hframe hrun hnc hyj hz hz
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ (le_max_of_le_left (hrun.time_nonneg j)) (max_le (hji'.trans hib) hcb)))
      hjlo (hji'.trans hihi) hP ⟨hh, hJ⟩ hP .refl
  have hPj : P ∈ ellj.frame.tree := AC.frame_mem_of_between sp hU hΦj hΦjU hDt hPD hFPj
  have hPyj : P ∈ (tr.state y j).fg.tree := by
    rw [hfrj, Node.frame'_eq, Store.toFrame'_tree] at hPj
    exact hPj.1
  have hPk : ∀ k, j ≤ k → k ≤ i → P ∈ (Node.frame' (tr.state y k)).tree ∧
      (Node.frame' (tr.state y k)).Anc (Node.frame' (tr.state y k)).fcRoot P ∧
      P ∈ (Node.frame' (tr.state y k)).viableHeads := by
    intro k hjk hki
    have hkt := hmono hki
    have hyk := hrun.antitone hkt hy
    have hklo := hjlo.trans (hmono hjk)
    have hkhi := hkt.trans hihi
    have hPk' : P ∈ (tr.state y k).fg.tree :=
      Compose.Growing.tree_mono_at' hrun (hrun.time_nonneg k) hyk
        (fun q hq => hmono hq.le) hjk hPyj
    obtain ⟨hFP, hvP⟩ := (windowWitness_of_stock hrun hnc hframe hz hP ⟨hh, hJ⟩).held
      y k hyk hklo hkhi
      (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hrun.time_nonneg k) (hkt.trans hib))) hPk'
    have hFPs := Healing.Growing.store_anc_of_honest_anc_at' hrun hnc
      (hrun.time_nonneg k) (fun q hq => hmono hq.le) hyk hFP hPk'
    have hPt : P ∈ (Node.frame' (tr.state y k)).tree := by
      rw [Node.frame'_eq, Store.toFrame'_tree]
      exact ⟨hPk', hFPs⟩
    have hvHead : P ∈ (Node.frame' (tr.state y k)).viableHeads := by
      rw [Node.frame'_eq, Store.toFrame'_viableHeads]
      exact ⟨hPk', hFPs, hvP⟩
    have hroot : (Node.frame' (tr.state y k)).Anc (Node.frame' (tr.state y k)).fcRoot P := by
      have hΦ := hcore.frameOK_at (hrun.time_nonneg k) hyk (fun q hq => hmono hq.le)
      have hsub : (Node.frame' (tr.state y k)).tree ⊆ tr.HonestBlocksAt H := by
        rw [Node.frame'_eq, Store.toFrame'_tree]
        exact fun B hB => ⟨y, k, tr.time k, hrun.time_nonneg k,
          (fun q hq => hmono hq.le), hyk, hB.1⟩
      apply AC.anc_tree_of_anc_U hU hΦ hsub hΦ.fcRoot_mem _ hPt
      rw [Node.frame'_eq, Store.toFrame'_fcRoot]
      exact hFP
    refine ⟨hPt, hroot, ?_⟩
    exact hvHead
  exact Healing.Growing.Core.toFG_candidate_of_viable_head_at hcore hnc hK hgr hfu hPD hy
    hc hji hext hPk hib hslot

end Consensus.Goldilocks.Shadow.PU.Growing

end

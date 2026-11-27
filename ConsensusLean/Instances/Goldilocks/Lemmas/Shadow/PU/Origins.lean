module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Deep
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family

public section

/-! # P-U shadow: the run-level origin family over `Growing.GoldilocksRun'`

The high-origin facts that the S1/S2 inputs (`Shadow/PU/Frontier`) and the report cover read,
restated over the shadow run and the shadow reset premises `ResetPremisesUpTo'`.

* `Outcome.high_origin_mem_at'` and `Outcome.high_of_anc_at'` are the stock proofs, with Run's
  `σ_eq_honest_at'`, Coherence's `honestBlocksAt_coherent'` and `held_anc_at'`, and the shadow AC
  projection (`Compose.goldilocks_ac_projection_from'`).
* `CoveredUpTo.compatible_highOrigin'` is the stock proof (S1 of the cover, generic in the run).
* R1 (`ResetPremisesUpTo'.origins_compatible_at'`) and
  `ProposalImpl.finalized_compatible_high_origin_at'` are in `Shadow/PU/Kernel`, above the P-U
  vote domain (`Shadow/PU/VoteDomain`). -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The stored block of a high origin is held at its actual honest write
(`Outcome.high_origin_mem_at`). -/
theorem Outcome.high_origin_mem_at' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    B ∈ (tr.state x i).fg.tree := by
  obtain ⟨CV, ell, D, hc, hfl, he⟩ := ho.2.2.1
  have hx := hrun.antitone (le_max_right _ _) ho.1
  have ht := hrun.time_nonneg i
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt x i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo ht) (hnc.upTo _)).localRun
  have hPhi := (AC.frameIn_of_callAt hr hx hc').1
  have hD : D ∈ ell.frame.tree := by
    rcases hfl with ⟨ell', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ell', A, ⟨hc', -⟩, -, hs, -⟩
    · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
      exact (AC.deepest_mem hD).1.1.1
    · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
      unfold AC.optimisticSelect at hs
      dsimp only at hs
      split_ifs at hs
      exact (AC.deepest_mem hs).1.1
  have hB := (AC.viableAncestor_anc hPhi hD).1
  rw [← he, Shadow.PU.Growing.frame_of_projAC_at' hrun hx hc, Node.frame'_eq,
    toFrame'_tree] at hB
  exact hB.1

/-- A held descendant of a high origin is high (`Outcome.high_of_anc_at`). -/
theorem Outcome.high_of_anc_at' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} {i j k : Nat} {t : Time}
    {B W : AC.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hz : z ∈ H t)
    (hW : W ∈ (tr.state z k).fg.tree) (hBW : Anc (tr.HonestBlocksAt H) B W) :
    HZ tr H g + 1 ≤ ((tr.state z k).fg.σ W.root).h := by
  have hBx := Outcome.high_origin_mem_at' hrun hnc ho
  have hBWs := Coherence.held_anc_at' hrun hnc ht hz hle hBW hW
  have hBz := Compose.FrameGeometry.anc_mem hBWs hW
  have hh := h_le_of_store_anc_with finalitySpec_updateFinality'
    (Compose.Growing.reachable_at' hrun ht hz hle).reachableWith hBWs
  have he := σ_eq_honest_at' hrun hnc (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) (hrun.antitone (le_max_right _ _) ho.1) ht hle hz hBx hBz
  rw [← he] at hh
  exact ho.2.2.2.trans hh

/-- **A covered block is compatible with every high origin written by `b`**
(`CoveredUpTo.compatible_highOrigin`; S1 of the cover, the origin being a healed member). -/
theorem CoveredUpTo.compatible_highOrigin' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {m : Nat} {E : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : CoveredUpTo tr H g a b m E) {x : Fin sp.n} {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hib : tr.time i ≤ b)
    (ho : HighOrigin tr H g x i j B) : Compatible (tr.HonestBlocksAt H) E B :=
  let ⟨hc, C, s, hC, _, hEC⟩ := coveredUpTo_iff.1 h
  Compose.Growing.compatible_of_anc_left (Coherence.honestBlocksAt_coherent' hrun hnc) hEC
    (hc.s1 C s B j hC (Compose.Growing.HealedOrigin.of_high hib ho))

end Consensus.Goldilocks.Healing.Growing

end

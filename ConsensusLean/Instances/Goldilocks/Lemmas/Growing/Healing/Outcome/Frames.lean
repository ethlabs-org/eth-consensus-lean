module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready

public section

/-! # Outcome frames at their readers' honest cuts

Only the reader's local execution is retained. Historical ancestry is kept in the
growing honest-block universe, not reconstructed from a terminal cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An AC frame is the local store frame at its own honest call. -/
theorem frame_of_call
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hy : y ∈ H (tr.time i)) (hc : tr.projAC.CallAt y i ell) :
    ell.frame = Node.frame (tr.state y i) := by
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have he := Compose.frame_of_projAC (hrun.upTo (hrun.time_nonneg i)) hy hc'
  rwa [Trace.upTo_state tr y (fun k hk => hrun.time_mono hk.le)] at he

/-- A frame's tree lies in the historical honest-block universe. -/
theorem frame_tree_subset
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hy : y ∈ H (tr.time i)) (hc : tr.projAC.CallAt y i ell) :
    ell.frame.tree ⊆ tr.HonestBlocksAt H := by
  rw [frame_of_call hrun hy hc]
  intro B hB
  exact ⟨y, i, tr.time i, hrun.time_nonneg i, fun k hk => hrun.time_mono hk.le, hy, hB.1⟩

/-- Realization is node-local even when other holders were subsequently compromised. -/
theorem frame_realized
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hy : y ∈ H (tr.time i)) (hc : tr.projAC.CallAt y i ell) :
    FrameOK ell.frame := by
  rw [frame_of_call hrun hy hc]
  exact (Store.frame_realization _ _ _ _ (fg_reachable_at hrun (hrun.time_nonneg i)
    (fun k hk => hrun.time_mono hk.le) hy)).1

/-- Proposal uniqueness before the proposer can be compromised uses only a local prefix. -/
theorem proposal_unique_before_hold
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {p y : Fin sp.n} {k j u : Nat} {P Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H (sp.ts u + Regimes.Growing.hold sp))
    (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hu : 0 < u) (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y j ell)
    (hj : tr.time j ≤ sp.ts u + Regimes.Growing.hold sp)
    (hQ : Q ∈ ell.frame.tree) (hQs : Q.slot = u) : Q = P := by
  have hk : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hactual.2.2
  let t := max (sp.ts u) (tr.time j)
  have ht : 0 ≤ t := (hrun.time_nonneg k).trans (hk ▸ le_max_left _ _)
  have htH : t ≤ sp.ts u + Regimes.Growing.hold sp := by
    apply max_le _ hj
    exact le_add_of_nonneg_right sp.toParams.hΔ.le
  have hp' := hrun.antitone htH hp
  have hy' : y ∈ H t := by
    have hslot : sp.ts u ≤ tr.time j := by
      have hrt := (hrun.upTo (hrun.time_nonneg j))
      have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
      have ha := Compose.goldilocks_ac_projection sp ro dg (H (tr.time j)) _ proposer
        hrt (hnc.upTo _)
      have h := SA.frame_slot_le sp ha.localRun hy hc' Q hQ
      rw [hQs] at h
      exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).mpr (by exact_mod_cast h)
    simpa only [t, max_eq_right hslot] using hy
  have hactual' : (tr.upTo t).ProposesAt p k P := by
    rcases hactual with ⟨⟨⟨acc, hacc⟩, hpos⟩, hprop, htime⟩
    exact ⟨⟨⟨acc, (Trace.upTo_callAt tr).mpr ⟨hk ▸ le_max_left _ _, hacc⟩⟩, hpos⟩,
      hprop, htime⟩
  have hc' : (tr.upTo t).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_max_right _ _, hc⟩
  exact Healing.proposal_frame_unique (hrun.upTo ht) (hnc.upTo t) hp'
    hdesignated hactual' hPs hu hy' hc' hQ hQs

/-- An early cast has the actual proposal in its frame before the hold expires. -/
theorem proposal_mem_of_early_cast
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {p y : Fin sp.n} {k j u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H (sp.ts u + Regimes.Growing.hold sp))
    (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hu : 0 < u) (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hj : tr.time j < sp.ts u + sp.Δ) : P ∈ ell.frame.tree := by
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  have hcast : SA.CastAt (tr.upTo (tr.time j)).projAC y j ell e := ⟨hc', hc.2⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j)) _ proposer
    (hrun.upTo (hrun.time_nonneg j)) (hnc.upTo _)).localRun
  obtain ⟨Q, hQ, hQs, -⟩ := SA.cast_ready hr hy hcast (hes ▸ hj)
  have he := proposal_unique_before_hold hrun hnc hp hdesignated hactual hPs hu hy hc.1
    hj.le hQ (hQs.trans hes)
  exact he ▸ hQ

end Consensus.Goldilocks.Healing.Growing.Outcome

end

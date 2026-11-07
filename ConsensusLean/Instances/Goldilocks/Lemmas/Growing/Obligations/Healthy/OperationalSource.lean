module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Pending
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The recent source of an operational update under growing faults

After the operational selection at the update of a node honest then, every record it looks up
just after the update is the update's own result or has a result or optimistic-lock source of a
node honest at its own cut, before the update and with a label at least the update's. Only the
selection uses the reset; the source is read on the prefix through the update's time, where the
updater is honest throughout (`Compose.record_origin_before`, lifted by `originBefore_of_upTo`).
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing (originBefore_iff)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **Selection repairs source recency**, even if the update retains a strict descendant of the
proposal: the looked-up record has a source of a node honest at its own cut, no later than the
update and with a label at least the update's. -/
theorem operational_update_recent_source_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hlookup : SA.lookup (Node.frame (tr.state y (j + 1)))
      (tr.state y (j + 1)).ac.latestConfirmed = some R) :
    ∃ x q s CV, x ∈ H (tr.time q) ∧ q ≤ j ∧ tr.time q ≤ tr.time j ∧ u ≤ s ∧
      (SA.ResultAt tr.projAC x q s R CV ∨ SA.OptimisticLockAt tr.projAC x q s R CV) := by
  obtain ⟨hPt, hconf, _, _, _, hrecord⟩ :=
    operational_update_selection_at hp hc hhold hdesignated hactual hPs hR hgu hTb hy hup
  have hrun := hp.run
  have hc' := Compose.projAC_callAt.mp hup.1
  have hlaw := hrun.cutLaw y j _ hc' hy
  have hframe : Node.frame (tr.state y (j + 1)) = ell.frame := by
    rw [tr.state_succ_of_call hc', hlaw.1]
    exact congrArg Store.toFrame hlaw.2.2.1
  have hstate : tr.projAC.post j = (tr.state y (j + 1)).ac := by
    rw [tr.state_succ_of_call hc']
    rfl
  have hgrowth := (Obligations.effective_record_update_slot_growth (sp := sp)
    (A := tr.projAC.state y j) (Compose.Growing.frameIn_at hrun hp.noColl hy hup.1).1 hPt).2
  rw [← hrecord, hstate, ← hframe, hlookup] at hgrowth
  simp only [Option.getD_some] at hgrowth
  rcases hgrowth with rfl | hlt
  · exact ⟨y, j, u, _, hy, le_rfl, le_rfl, le_rfl, Or.inl ⟨ell, hup, hconf, rfl⟩⟩
  -- the record's origin, on the prefix through the update's time
  have hd := hrun.time_nonneg j
  have hpre := hrun.upTo hd
  have hncp := hp.noColl.upTo (tr.time j)
  have hst : (tr.upTo (tr.time j)).state y (j + 1) = tr.state y (j + 1) :=
    Trace.upTo_state tr y fun k hk => hrun.time_mono (Nat.le_of_lt_succ hk)
  obtain ⟨C, hC, hCr, hsource⟩ := Compose.record_origin_before hpre hncp hy (j + 1)
  have hU := Compose.honest_blocks_coherent hpre.toLocalRun hncp
  obtain ⟨hRm, hRr⟩ := SA.lookup_eq_some hlookup
  rw [← hst] at hRm hRr
  have heq : C = R := hU.1 ⟨y, hy, j + 1, hC⟩ ⟨y, hy, j + 1, hRm.1⟩ (hCr.trans hRr.symm)
  subst C
  rcases hsource with hz | ⟨s, hs⟩
  · have he := Compose.honest_eq_genesis hpre hU
      (show R ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) from ⟨y, hy, j + 1, hC⟩) hz
    rw [he] at hlt
    exact False.elim (Nat.not_lt_zero _ hlt)
  obtain ⟨x, q, CV, hq, hx, hsrc⟩ :=
    originBefore_iff.mp (Compose.Growing.originBefore_of_upTo hrun hs)
  refine ⟨x, q, s, CV, hx, by omega, hrun.time_mono (by omega), ?_, hsrc⟩
  rw [hPs] at hlt
  rcases hsrc with ⟨e, hu, hsel, _⟩ | ⟨e, A, ho, hslot, hsel, _⟩
  · have hRs := Compose.Growing.frame_slot_le_at hrun hp.noColl hx hu.1 R
      (SA.deepest_mem hsel).1.1
    have hsl : sp.slot (tr.projAC.time q) = s + 1 := by
      rw [hu.2.2.1]
      apply SA.slot_of_mem sp (s + 1) <;>
        simp only [SAParams.ts] <;> push_cast <;> linarith [sp.toParams.hΔ]
    change sp.slot (tr.time q) = s + 1 at hsl
    rw [hsl] at hRs
    omega
  · have hm : R ∈ e.frame.tree := by
      unfold SA.optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel
      exact (SA.deepest_mem hsel).1.1
    have hRs := Compose.Growing.frame_slot_le_at hrun hp.noColl hx ho.1 R hm
    change sp.slot (tr.time q) = s at hslot
    omega

end Consensus.Goldilocks.Healing.Growing

end

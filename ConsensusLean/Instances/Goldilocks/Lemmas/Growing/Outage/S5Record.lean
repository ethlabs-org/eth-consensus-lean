module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Gate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Count
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the early record

An update of the first restored label
`r` by a node honest at it makes its effective record a block above `P` at every later cut read
at a time at which the node is honest (`record_above_of_update_r_by`; at the cut's own time,
`record_above_of_update_r_at`):

* when `P ⪯ Σ.F` at the update, the effective record is a block of the later frame, so it extends
  that frame's `Σ.F`, which extends the update's;
* otherwise the gate's result extends `P` (`gate_result_extends_at` with the cohort majority
  `restored_majority_at_r_at`, charged at the update's cut `t_r + 6Δ ≤ z`), and
  `record_above_from_at` keeps the record above `P`, whether the result is accepted or vetoed. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- **The early record, at a read time**: an update at label `r` by a node honest at it makes its
effective record `⪰ P` at every later cut `c'` read at a time `t` at which it is honest (every cut
before `c'` at a time `≤ t`). -/
theorem record_above_of_update_r_by (D : OutageLockPremises tr H proposer dg ini)
    (hS : ∀ y, ReceiverServiceAfterAt H (tr.HonestBlocksAt H) D.b₁ y tr.projAC)
    (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} {c : Nat} (hw : w ∈ H (tr.time c))
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c D.r ℓ) :
    ∀ c' t, c < c' → 0 ≤ t → (∀ k < c', tr.time k ≤ t) → w ∈ H t →
      Anc (tr.HonestBlocksAt H) D.P
        ((SA.lookup (Node.frame (tr.state w c')) (tr.state w c').ac.latestConfirmed).getD
          (Node.frame (tr.state w c')).F) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hfr : ℓ.frame = Node.frame (tr.state w c) := frame_of_projAC_at D.hrun hw hu.1
  have ht : tr.time c = sp.ts D.r + 6 * sp.Δ := hu.2.2.1
  intro c' t hcc' hd hcut hwt
  by_cases hPF : Anc (tr.HonestBlocksAt H) D.P (tr.state w c).fg.F
  · -- the effective record is a block of the later frame, above its `Σ.F ⪰ P`
    have hΦ := frameOK_at D.hrun hd hwt hcut
    have hΦU : (Node.frame (tr.state w c')).tree ⊆ tr.HonestBlocksAt H :=
      fun Z hZ => tree_held_at hd hwt hcut hZ.1
    have hPF' : Anc (tr.HonestBlocksAt H) D.P (Node.frame (tr.state w c')).F :=
      hPF.trans (F_mono_at D.hrun hd hwt hcut hcc'.le)
    cases he : SA.lookup (Node.frame (tr.state w c')) (tr.state w c').ac.latestConfirmed with
    | none => exact hPF'
    | some E =>
      obtain ⟨hEt, -⟩ := SA.lookup_eq_some he
      exact hPF'.trans (Anc.mono hΦU (hΦ.rooted.2 E hEt))
  -- otherwise `Σ.F ⪯ P`, and the gate's result extends `P`
  have hFP : Anc (tr.HonestBlocksAt H) ℓ.frame.F D.P := by
    rw [hfr]
    exact ((hinv c).caches_at_cut le_rfl hw).1.resolve_right hPF
  have hcallc : ∃ x i, x ∈ H (tr.time i) ∧ tr.IsCall x i ∧ tr.time c ≤ tr.time i :=
    ⟨w, c, hw, ⟨_, projAC_callAt.1 hu.1⟩, le_rfl⟩
  have hcz : tr.time c ≤ D.z := by
    have := ts_le_ts (sp := sp) D.hrk.2
    exact D.hzc _ (by linarith) hcallc
  obtain ⟨⟨C, CV, hR⟩, hall⟩ := gate_result_extends_at D.hrun D.hnc D.facts.hP hw (hS w) hu D.hr.1
    (restored_majority_at_r_at D hinv (honestCall_mono hcallc (by linarith)) _ hcz) hFP
  exact record_above_from_at hinv hu hR le_rfl (hall C CV hR) c' t hcc' hd hcut hwt

/-- **The early record**: an update at label `r` by a node honest at it makes its effective
record `⪰ P` at every later cut at which it is honest. -/
theorem record_above_of_update_r_at (D : OutageLockPremises tr H proposer dg ini)
    (hS : ∀ y, ReceiverServiceAfterAt H (tr.HonestBlocksAt H) D.b₁ y tr.projAC)
    (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} {c : Nat} (hw : w ∈ H (tr.time c))
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c D.r ℓ) :
    ∀ c', c < c' → w ∈ H (tr.time c') → Anc (tr.HonestBlocksAt H) D.P
      ((SA.lookup (Node.frame (tr.state w c')) (tr.state w c').ac.latestConfirmed).getD
        (Node.frame (tr.state w c')).F) := fun c' hcc' hwc' =>
  record_above_of_update_r_by D hS hinv hw hu c' (tr.time c') hcc' (D.hrun.time_nonneg c')
    (fun _ hk => D.hrun.time_mono hk.le) hwc'

end Consensus.Goldilocks.Compose.Growing

end

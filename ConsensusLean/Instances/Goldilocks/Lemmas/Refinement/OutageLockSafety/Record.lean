module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageRead

public section

/-! # Outage lock safety: the record from a restored update (card §8, `record_above_from`)

The writes of an honest record after its update of a restored label `m ≥ r` come from results of
labels `> m` (compatible with `P` by (R)) and from optimistic selections (compatible with `P`,
`fastLock_compatible`); with OB-F this is the landed `EffectiveRecordInterval`
(`record_interval_after`). With the veto case of `late_reader_record_cover` (the live locks are
compatible with `P` by (i)), an update result above `P` keeps the effective record above `P` at
every later cut (`record_above_from`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- **The record interval after the restored labels**: from a cut at or after the update time of
label `r`, every write of `y`'s record is compatible with `P` and `Σ.F` is compatible with `P`. -/
theorem record_interval_after (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {i j : Nat} (hi : sp.ts D.r + 6 * sp.Δ ≤ tr.time i) :
    Refinement.EffectiveRecordInterval tr H y i j D.P := by
  have hac := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hst := projAC_state D.hrun.toLocalRun hy
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  refine ⟨fun q hiq hqj => Or.inl ?_⟩
  refine ⟨(fun C => ∃ s CV, SA.ResultAt tr.projAC y q s C CV ∨
    SA.OptimisticLockAt tr.projAC y q s C CV), ?_, ?_,
    ((hinv (q + 1)).caches y hy (q + 1) le_rfl).1⟩
  · by_cases hcall : ∃ ell, tr.projAC.CallAt y q ell
    · obtain ⟨ell, hcall⟩ := hcall
      have hw := call_writes hac.localRun hy hcall
      rw [← tr.projAC.state_succ_of_call hcall, hst, hst, frame_of_projAC D.hrun hy hcall] at hw
      exact hw
    · have he : (tr.state y (q + 1)).ac.latestConfirmed = (tr.state y q).ac.latestConfirmed := by
        rw [← hst, tr.projAC.state_succ_of_not (fun ell h => hcall ⟨ell, h⟩), hst]
      rw [he]
      exact writes_iff.mpr .refl
  · rintro C ⟨s, CV, hR | hO⟩
    · obtain ⟨ℓ, hu, -, -⟩ := id hR
      have ht : tr.time q = sp.ts s + 6 * sp.Δ := hu.2.2.1
      have hqi := D.hrun.time_mono hiq
      have hrs : D.r ≤ s := by
        by_contra h
        have := ts_le_ts (sp := sp) (show s + 1 ≤ D.r by omega)
        have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
          simp only [SAParams.ts]; push_cast; ring
        linarith
      exact ((hinv (q + 1)).results y hy q (Nat.lt_succ_self q) s C CV hR (Or.inr hrs)).symm
    · exact (fastLock_compatible hinv hy (Or.inr hO)).symm

/-- **`record_above_from`** (§8): after an honest update of a restored label `m ≥ r` whose result
`C` extends `P`, the effective record of the updater extends `P` at every later cut, whether the
result is accepted or vetoed. -/
theorem record_above_from (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} (hw : w ∈ H)
    {c m : Nat} {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c m ℓ) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC w c m C CV) (hrm : D.r ≤ m)
    (hPC : Anc (tr.HonestBlocks H) D.P C) :
    ∀ i, c < i → Anc (tr.HonestBlocks H) D.P ((SA.lookup (Node.frame (tr.state w i))
      (tr.state w i).ac.latestConfirmed).getD (tr.state w i).fg.F) := by
  intro i hci
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hfr : ℓ.frame = Node.frame (tr.state w c) :=
    (D.hrun.cutLaw w hw c _ (projAC_callAt.1 hu.1)).1
  have ht : tr.time c = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hrm' := ts_le_ts (sp := sp) hrm
  refine Refinement.late_reader_record_cover D.hrun D.hnc hw hci hu hR hPC (fun L hL => ?_)
    (record_interval_after hinv hw (by linarith [D.hrun.time_mono (Nat.le_succ c)]))
  rw [hfr] at hL
  exact liveLockBlocks_compatible hinv hw c (tr.time c) .refl L hL

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageRead
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the record from a restored update (`record_above_from_at`)

After an update of a restored label `m ≥ r` by a node honest at it, whose result extends `P`, the
updater's effective record extends `P` at every later cut `i` read at a time `t` at which the
updater is honest (every cut before `i` at a time `≤ t`). The argument runs on the prefix through
`t` with the honest set `H t`: the record interval after the update (`record_interval_upTo`: the
writes come from results of labels `≥ r`, compatible with `P` by (R), and from optimistic
selections, compatible with `P` by `fastLock_compatible_at`; `Σ.F` is compatible with `P` by OB-F),
and the veto case of `late_reader_record_cover`, the live locks being compatible with `P` by (i).
Each compatibility comes into the prefix from the blocks held while honest (`compatible_upTo`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}
  {D : OutageLockPremises tr H proposer dg ini}

/-- **The record interval after a restored update, in the prefix through `t`**: from a cut `i`
at or after the update time of label `r`, up to a cut `j` read at `t` (the node honest at `t`,
every cut before `j` at a time `≤ t`), every write of `y`'s record is compatible with `P` and
`Σ.F` is compatible with `P`, in the prefix's honest blocks, when `P` is one of them. -/
private theorem record_interval_upTo (hinv : ∀ i, OutageLockInv D i) {y : Fin sp.n}
    {i j : Nat} {t : Time} (ht0 : 0 ≤ t) (hjt : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t)
    (hPU : D.P ∈ (tr.upTo t).HonestBlocks (H t)) (hi : sp.ts D.r + 6 * sp.Δ ≤ tr.time i) :
    Obligations.EffectiveRecordInterval (tr.upTo t) (H t) y i j D.P := by
  have hm := D.hrun.time_mono
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hrT := D.hrun.upTo ht0
  have hncT := D.hnc.upTo t
  have hprojT : (tr.upTo t).projAC = tr.projAC.upTo t := RunTrace.upTo_projAC
  have hac := Compose.goldilocks_ac_projection_from hrT hncT
  have hst := projAC_state hrT.toLocalRun hy
  have down : ∀ X ∈ (tr.upTo t).HonestBlocks (H t), Compatible (tr.HonestBlocksAt H) X D.P →
      Compatible ((tr.upTo t).HonestBlocks (H t)) D.P X := fun X hX h =>
    (compatible_upTo D.hrun D.hnc ht0 hX hPU h).symm
  refine ⟨fun q hiq hqj => Or.inl ?_⟩
  have hqt : tr.time q ≤ t := hjt q hqj
  have hyq : y ∈ H (tr.time q) := D.hrun.antitone hqt hy
  refine ⟨(fun C => ∃ s CV, SA.ResultAt (tr.upTo t).projAC y q s C CV ∨
    SA.OptimisticLockAt (tr.upTo t).projAC y q s C CV), ?_, ?_, ?_⟩
  · by_cases hcall : ∃ ell, (tr.upTo t).projAC.CallAt y q ell
    · obtain ⟨ell, hcall⟩ := hcall
      have hw := call_writes hac.localRun hy hcall
      rw [← (tr.upTo t).projAC.state_succ_of_call hcall, hst, hst,
        frame_of_projAC hrT hy hcall] at hw
      exact hw
    · have he : ((tr.upTo t).state y (q + 1)).ac.latestConfirmed =
          ((tr.upTo t).state y q).ac.latestConfirmed := by
        rw [← hst, (tr.upTo t).projAC.state_succ_of_not (fun ell h => hcall ⟨ell, h⟩), hst]
      rw [he]
      exact writes_iff.mpr .refl
  · rintro C ⟨s, CV, hR | hO⟩
    · rw [hprojT] at hR
      obtain ⟨-, hR⟩ := (sa_resultAt_upTo hm).1 hR
      obtain ⟨ℓ, hu, hC, -⟩ := id hR
      have ht : tr.time q = sp.ts s + 6 * sp.Δ := hu.2.2.1
      have hqi := hm hiq
      have hrs : D.r ≤ s := by
        by_contra h
        have := ts_le_ts (sp := sp) (show s + 1 ≤ D.r by omega)
        have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
          simp only [SAParams.ts]; push_cast; ring
        linarith
      exact down C (mem_upTo_of_frame D.hrun hy hqt hu.1 (SA.deepest_mem hC).1.1)
        ((hinv (q + 1)).results y q (Nat.lt_succ_self q) hyq s C CV hR (Or.inr hrs))
    · rw [hprojT] at hO
      obtain ⟨-, hO⟩ := (sa_optimisticLockAt_upTo hm).1 hO
      have hfl : SA.FastLockAt tr.projAC y q s C CV := Or.inr hO
      have hCt : ∃ ℓ, tr.projAC.CallAt y q ℓ ∧ C ∈ ℓ.frame.tree := by
        obtain ⟨ℓ, A, hpt, -, hsel, -⟩ := id hO
        refine ⟨ℓ, hpt.1, ?_⟩
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact (SA.deepest_mem hsel).1.1
      obtain ⟨ℓ, hcq, hCt⟩ := hCt
      refine down C (mem_upTo_of_frame D.hrun hy hqt hcq hCt)
        (fastLock_compatible_at (hinv (q + 1)).toOutageVoteInv hyq hfl (fun v hv hvH => ?_)
          fun hsK => ?_)
      · obtain ⟨j', hj', e, hve, he⟩ := fastLock_honest_vote_at D.hrun D.hnc hyq hfl hv hvH
        exact ⟨j', by omega, e, hve, he⟩
      · have := fastLockAt_time_le D.hrun hfl
        have := ts_le_ts (sp := sp) hsK
        exact D.hzc _ (by linarith) ⟨y, q, hyq, fastLockAt_isCall hfl, le_rfl⟩
  · have hq1 : ∀ k < q + 1, tr.time k ≤ t := fun k hk => hjt k (by omega)
    have hst1 := Trace.upTo_state tr y hq1
    have hF : (tr.state y (q + 1)).fg.F ∈ (tr.upTo t).HonestBlocks (H t) :=
      ⟨y, hy, q + 1, by rw [hst1]; exact (frameOK_at D.hrun ht0 hy hq1).rooted.1.1⟩
    rw [hst1]
    exact (down _ hF ((hinv (q + 1)).caches y (q + 1) t le_rfl ht0 hq1 hy).1).symm

/-- **The record stays above `P` under growing faults**: after an update of a restored label `m ≥ r`
whose result `C` extends `P`, the effective record of the updater extends `P` at every later cut
`i` read at a time `t` at which it is honest (every cut before `i` at a time `≤ t`), whether the
result is accepted or vetoed. -/
theorem record_above_from_at (hinv : ∀ i, OutageLockInv D i) {w : Fin sp.n} {c m : Nat}
    {ℓ : ACLabel (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)}
    (hu : SA.UpdateAt tr.projAC w c m ℓ) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hR : SA.ResultAt tr.projAC w c m C CV) (hrm : D.r ≤ m)
    (hPC : Anc (tr.HonestBlocksAt H) D.P C) :
    ∀ i t, c < i → 0 ≤ t → (∀ k < i, tr.time k ≤ t) → w ∈ H t →
      Anc (tr.HonestBlocksAt H) D.P ((SA.lookup (Node.frame (tr.state w i))
        (tr.state w i).ac.latestConfirmed).getD (tr.state w i).fg.F) := by
  intro i t hci ht0 hit hw
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hm := D.hrun.time_mono
  have hsub := upTo_subset D.hrun ht0
  have hprojT : (tr.upTo t).projAC = tr.projAC.upTo t := RunTrace.upTo_projAC
  have hct : tr.time c ≤ t := hit c hci
  have hwc : w ∈ H (tr.time c) := D.hrun.antitone hct hw
  have hcut : ∀ k < c, tr.time k ≤ t := fun k hk => hit k (hk.trans hci)
  have ht : tr.time c = sp.ts m + 6 * sp.Δ := hu.2.2.1
  have hrm' := ts_le_ts (sp := sp) hrm
  -- the result, its ancestor `P`, and the update in the prefix through `t`
  have hCU : C ∈ (tr.upTo t).HonestBlocks (H t) := by
    obtain ⟨ℓ', hu', hC, -⟩ := id hR
    obtain rfl : ℓ' = ℓ := Option.some.inj (hu'.1.2.symm.trans hu.1.2)
    exact mem_upTo_of_frame D.hrun hw hct hu.1 (SA.deepest_mem hC).1.1
  have hPC' := RunTrace.anc_upTo_of_right D.hrun.toLocalRun D.hnc ht0 hCU hPC
  have hPU : D.P ∈ (tr.upTo t).HonestBlocks (H t) := by
    by_cases hPCe : D.P = C
    · exact hPCe ▸ hCU
    · exact (Anc.mem hPC' hPCe).1
  have hu' : SA.UpdateAt (tr.upTo t).projAC w c m ℓ := by
    rw [hprojT]; exact (sa_updateAt_upTo hm).2 ⟨hct, hu⟩
  have hR' : SA.ResultAt (tr.upTo t).projAC w c m C CV := by
    rw [hprojT]; exact (sa_resultAt_upTo hm).2 ⟨hct, hR⟩
  -- the live locks at the update are compatible with `P`, in the prefix
  have hlocks : ∀ L ∈ SA.liveLockBlocks sp ((tr.upTo t).state w c).ac.locks ℓ.frame
      ((tr.upTo t).time c), Compatible ((tr.upTo t).HonestBlocks (H t)) L D.P := by
    intro L hL
    rw [Trace.upTo_state tr w hcut, frame_of_projAC_at D.hrun hwc hu.1] at hL
    have hLU : L ∈ (tr.upTo t).HonestBlocks (H t) :=
      ⟨w, hw, c, by rw [Trace.upTo_state tr w hcut]; exact hL.1.1⟩
    exact compatible_upTo D.hrun D.hnc ht0 hLU hPU
      (liveLockBlocks_compatible_by hinv ht0 hcut hw (tr.time c) .refl L hL)
  have hint := record_interval_upTo hinv (i := c + 1) ht0 hit hw hPU
    (by linarith [hm (Nat.le_succ c)])
  have h := Obligations.late_reader_record_cover (D.hrun.upTo ht0) (D.hnc.upTo t) hw hci hu' hR'
    hPC' hlocks hint
  rw [Trace.upTo_state tr w hit] at h
  exact h.mono hsub

end Consensus.Goldilocks.Compose.Growing

end

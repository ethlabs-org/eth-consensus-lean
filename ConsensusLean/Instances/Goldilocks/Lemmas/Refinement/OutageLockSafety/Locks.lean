module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

/-! # Outage lock safety: (i), no honest lock conflicting with `P` (card §5.2)

Every stored honest lock lies below a block written at an earlier cut (`lock_origin`,
`fast_lock_provenance`, `slow_lock_compatible`):

* a lock of a label `< j₀` lies below an origin within `b₀` (§4.2);
* a fast lock (update or optimistic) of a slot `≥ j₀` on a block conflicting with `P` would have
  its counted validators in `Hᶜ ∪ W` (OL-W), against `n ≤ 2·|counted|` and N6;
* a slow lock has an unpolluted label in its window (`exists_unpolluted_label`), whose results
  are compatible with `P` (R). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {D : OutageLockPremises tr H proposer dg}

/-- A counted vote of an honest validator at an honest fast lock was cast at a cut no later than
the lock's. -/
theorem fastLock_honest_vote (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt tr.projAC y j s B CV) {v : Vote sp.n}
    (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j' ≤ j, ∃ e, SA.VoteAt tr.projAC v.val j' e ∧ e.msg = v := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  rcases hfl with ⟨ℓ, C, -, -, -, -, rfl⟩ | ⟨ℓ, A, hpt, -, -, rfl⟩
  · obtain ⟨j', hj', e, hve, he⟩ := hrun'.honest.pool_vote y hy j s v hv.1 hvH
    exact ⟨j', hj'.le, e, hve, he⟩
  · obtain ⟨-, j', hj', e, hve, he⟩ := SA.optimisticPoint_pool_vote hrun' hy hpt hv.1 hvH
    exact ⟨j', hj', e, hve, he⟩

/-- An origin of a label below `j₀` whose event precedes the cut is within `b₀`. -/
private theorem within_of_label_lt (D : OutageLockPremises tr H proposer dg)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s n : Nat} (hC : OriginBefore tr H C s n)
    (hs : s < D.j₀) : OriginWithin tr H C s D.b₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨z, hz, k, -, CV, hRO⟩ := originBefore_iff.1 hC
  have hsj := ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hj₀ := D.hj₀.1
  refine originWithin_iff.2 ⟨z, hz, k, CV, ?_, hRO⟩
  rcases hRO with ⟨ℓ, hu, -, -⟩ | ⟨ℓ, A, -, hslot, -⟩
  · have ht : tr.time k = sp.ts s + 6 * sp.Δ := hu.2.2.1
    linarith
  · have : tr.time k < sp.ts (s + 1 : Nat) := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) ((s + 1 : Nat) : Int)).1 (not_lt.1 h)
      rw [hslot] at this
      omega
    linarith

/-- **(i) at a cut** (§5.2): with (H)/S5V at the cuts before `n` and (R) at the cuts before `n`,
every lock stored at cut `n` by an honest node names a held block compatible with `P`. -/
theorem OutageVoteInv.locks_compatible {n : Nat} (hvi : OutageVoteInv D n)
    (hres : ∀ y ∈ H, ∀ k < n, ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
      (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P)
    {y : Fin sp.n} (hy : y ∈ H) {l : SA.Lock} (hl : l ∈ (tr.state y n).ac.locks) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P := by
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hr := hrun'.localRun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨L, hL, hLr, C, hCo, hLC⟩ := lock_origin D.hrun D.hnc hy n l hl
  have hLU : L ∈ tr.HonestBlocks H := ⟨y, hy, n, hL⟩
  refine ⟨L, hL, hLr, ?_⟩
  have hl' : l ∈ (tr.projAC.state y n).locks := by
    rw [projAC_state D.hrun.toLocalRun hy n]; exact hl
  by_cases hs : l.slot < D.j₀
  · -- §4.2: below an origin within `b₀`
    exact D.compatible_of hLU fun hP => compatible_of_anc hU hLC
      (D.hpre.origins_compatible C l.slot D.P D.σ (within_of_label_lt D hCo hs) hP)
  cases hf : l.fast
  · -- a slow lock: an unpolluted label of its window
    obtain ⟨L', hL'U, hL'r, hcomp⟩ := slow_lock_compatible D.hrun D.hnc hy hl hf (B := D.P) (by
      obtain ⟨m, h1, h2, h3⟩ := exists_unpolluted_label sp D.hΔ D.hgap l.slot
      by_cases hm0 : 0 ≤ m
      · refine ⟨m, h1, h2, hm0, fun c C CV hc hR => hres y hy c hc m.toNat C CV hR ?_⟩
        have hmn : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
        rcases h3 with h | h
        · left
          by_contra hgt
          have := ts_le_ts (sp := sp) (show D.j₀ + 1 ≤ m.toNat by omega)
          rw [hmn] at this
          linarith [D.hj₀.2]
        · right
          exact D.hr.2 m.toNat (by rw [hmn]; exact h)
      · refine ⟨0, by omega, by omega, le_rfl, fun c C CV hc hR => hres y hy c hc 0 C CV hR
          (Or.inl (Nat.zero_le _))⟩)
    obtain rfl : L' = L := hU.1 hL'U hLU (hL'r.trans hLr.symm)
    exact hcomp
  · -- a fast lock of a slot `≥ j₀`: the counted validators outnumber `Hᶜ ∪ W`
    obtain ⟨j, hj, B, CV, hfl, L', hL'U, hL'r, hL'B⟩ := SA.fast_lock_provenance hr hy n l hl' hf
    obtain rfl : L' = L := hU.1 hL'U hLU (hL'r.trans hLr.symm)
    refine compatible_of_anc hU hL'B (by_contra fun hB => ?_)
    obtain ⟨hcount, hCV⟩ := SA.fastLock_counted hrun' hy hfl
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ Hᶜ ∪ D.W := by
      rintro u ⟨v, hv, rfl⟩
      by_contra hu
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hu
      obtain ⟨hvs, R, hRU, hRr, -, hBR⟩ := hCV v hv
      obtain ⟨j', hj', e, hve, rfl⟩ := fastLock_honest_vote D.hrun D.hnc hy hfl hv hu.1
      exact hB (compatible_of_voteCompat hU hRU hRr hBR
        (hvi.voteCompat_of_not_lateWaker hu.1 hu.2 (by omega) hve (by omega)))
    have := Set.ncard_le_ncard hsub
    have := D.two_mul_lt
    omega

end Consensus.Goldilocks.Compose

end

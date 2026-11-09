module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyReader
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

namespace Consensus.Goldilocks.FamilySafety

open SA (SAParams ReplayOrder Payload Vote SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}
  {F : SAFamily sp (List (FG.Att sp.n)) ro A} {tr : RunTrace A.toAC}
  {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {sg : M → Fin sp.n}

/-- The origin exit is observed, not a reachable full engine state. -/
def OriginBefore (F : SAFamily sp (List (FG.Att sp.n)) ro A) (tr : RunTrace A.toAC)
    (H : Set (Fin sp.n)) (C : SA.Blk sp.n (List (FG.Att sp.n))) (s n : Nat) : Prop :=
  ∃ x ∈ H, ∃ k < n, ∃ CV, SA.ResultAt (F.proj tr.projAC) x k s C CV ∨
    SA.OptimisticLockAt (F.proj tr.projAC) x k s C CV

/-- Execution-derived lock exits. None specifies a whole handler or local run.
The origin field applies to every stored lock, hence also to live locks. -/
structure LockFacts (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (tr : RunTrace A.toAC) (H : Set (Fin sp.n)) : Prop where
  origin : ∀ y ∈ H, ∀ n l, l ∈ ((F.proj tr.projAC).state y n).locks →
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧
      ∃ C, OriginBefore F tr H C l.slot n ∧ Anc (tr.HonestBlocks H) L C
  fastOrigin : ∀ y ∈ H, ∀ n l, l ∈ ((F.proj tr.projAC).state y n).locks → l.fast = true →
    ∃ j < n, ∃ B CV, SA.FastLockAt (F.proj tr.projAC) y j l.slot B CV ∧
      ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Anc (tr.HonestBlocks H) L B
  counted : ∀ y ∈ H, ∀ c s B CV, SA.FastLockAt (F.proj tr.projAC) y c s B CV →
    sp.n ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ tr.HonestBlocks H,
        R.root = v.head ∧ R.slot ≤ s ∧ Anc (tr.HonestBlocks H) B R
  honest : ∀ y ∈ H, ∀ c s B CV, SA.FastLockAt (F.proj tr.projAC) y c s B CV →
    ∀ v ∈ CV, v.val ∈ H → ∃ j ≤ c, ∃ e, SA.VoteAt (F.proj tr.projAC) v.val j e ∧ e.msg = v
  slow : ∀ y ∈ H, ∀ i l, l ∈ ((F.proj tr.projAC).state y i).locks → l.fast = false →
    ∀ B : SA.Blk sp.n (List (FG.Att sp.n)),
    (∃ m : Int, (l.slot : Int) - sp.k < m ∧ m ≤ l.slot ∧ 0 ≤ m ∧
      ∀ c C CV, c < i → SA.ResultAt (F.proj tr.projAC) y c m.toNat C CV →
        Compatible (tr.HonestBlocks H) C B) →
    ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L B

/-- Goldilocks discharges the sealed exits using the existing proofs. -/
theorem lockFacts_goldilocks {tr : GoldilocksTrace sp ro}
    (hr : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    LockFacts (SA.goldilocksFamily sp _ ro) tr H := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hr hnc
  constructor
  · intro y hy n l hl
    obtain ⟨L, hL, hLr, C, hC, hLC⟩ := Compose.lock_origin hr hnc hy n l
      ((Compose.projAC_state hr.toLocalRun hy n) ▸ hl)
    exact ⟨L, hL, hLr, C, Compose.originBefore_iff.mp hC, hLC⟩
  · intro y hy n l hl hf
    exact SA.fast_lock_provenance hac.localRun hy n l hl hf
  · intro y hy c s B CV hfl
    exact SA.fastLock_counted hac hy hfl
  · intro y hy c s B CV hfl v hv hvH
    rcases hfl with ⟨ℓ, C, -, -, -, -, rfl⟩ | ⟨ℓ, A, hpt, -, -, rfl⟩
    · obtain ⟨j, hj, e, he, hm⟩ := hac.honest.pool_vote y hy c s v hv.1 hvH
      exact ⟨j, hj.le, e, he, hm⟩
    · obtain ⟨-, j, hj, e, he, hm⟩ := SA.optimisticPoint_pool_vote hac hy hpt hv.1 hvH
      exact ⟨j, hj, e, he, hm⟩
  · intro y hy i l hl hf B hg
    exact Compose.slow_lock_compatible hr hnc hy
      ((Compose.projAC_state hr.toLocalRun hy i) ▸ hl) hf hg

/-- The fast-lock vote provenance exit, independent of how the lock was written. -/
theorem fastLock_honest_vote_family (hf : LockFacts F tr H) {y : Fin sp.n} (hy : y ∈ H)
    {j s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt (F.proj tr.projAC) y j s B CV) {v : Vote sp.n}
    (hv : v ∈ CV) (hvH : v.val ∈ H) :
    ∃ j' ≤ j, ∃ e, SA.VoteAt (F.proj tr.projAC) v.val j' e ∧ e.msg = v :=
  hf.honest y hy j s B CV hfl v hv hvH

private theorem within_of_label_lt (D : OutageLockPremises F tr H proposer dg sg)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s n : Nat} (hC : OriginBefore F tr H C s n)
    (hs : s < D.j₀) : OriginWithin F tr H C s D.b₀ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨z, hz, k, -, CV, hRO⟩ := hC
  have hsj := Compose.ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hj₀ := D.hj₀.1
  refine ⟨z, hz, k, CV, ?_, hRO⟩
  rcases hRO with ⟨ℓ, hu, -, -⟩ | ⟨ℓ, A, -, hslot, -⟩
  · have ht : tr.time k = sp.ts s + 6 * sp.Δ := by
      simpa only [F.time, RunTrace.projAC] using hu.2.2.1
    linarith
  · have ht : tr.time k < sp.ts (s + 1 : Nat) := by
      by_contra h
      have hh := (SA.ts_le_iff_le_slot sp (D.hrun.time_nonneg k)
        ((s + 1 : Nat) : Int)).1 (not_lt.1 h)
      have hslot' : sp.slot (tr.time k) = s := by
        simpa only [F.time, RunTrace.projAC] using hslot
      omega
    linarith

/-- Lock compatibility uses origin/count/saved-result exits, not SA reachability. -/
theorem OutageVoteInv.locks_compatible (hf : LockFacts F tr H)
    (ht : VoteTiming (F.proj tr.projAC) H) {D : OutageLockPremises F tr H proposer dg sg}
    {n : Nat} (hvi : OutageVoteInv D n)
    (hres : ∀ y ∈ H, ∀ k < n, ∀ m C CV, SA.ResultAt (F.proj tr.projAC) y k m C CV →
      (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocks H) C D.P)
    {y : Fin sp.n} (hy : y ∈ H) {l : SA.Lock} (hl : l ∈ ((F.proj tr.projAC).state y n).locks) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocks H) L D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨L, hL, hLr, C, hCo, hLC⟩ := hf.origin y hy n l hl
  have hLU : L ∈ tr.HonestBlocks H := ⟨y, hy, n, hL⟩
  refine ⟨L, hL, hLr, ?_⟩
  by_cases hs : l.slot < D.j₀
  · exact D.compatible_of hLU fun hP => compatible_of_anc_family hU hLC
      (D.hpre.origins_compatible C l.slot D.P D.σ (within_of_label_lt D hCo hs) hP)
  cases hfast : l.fast
  · obtain ⟨L', hL'U, hL'r, hcomp⟩ := hf.slow y hy n l hl hfast D.P (by
      obtain ⟨m, h1, h2, h3⟩ := Compose.exists_unpolluted_label sp D.hgap l.slot
      by_cases hm0 : 0 ≤ m
      · refine ⟨m, h1, h2, hm0, fun c C CV hc hR => hres y hy c hc m.toNat C CV hR ?_⟩
        have hmn : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
        rcases h3 with h | h
        · left
          by_contra hgt
          have hh := Compose.ts_le_ts (sp := sp) (show D.j₀ + 1 ≤ m.toNat by omega)
          rw [hmn] at hh
          linarith [D.hj₀.2]
        · exact Or.inr (D.hr.2 m.toNat (by rw [hmn]; exact h))
      · exact ⟨0, by omega, by omega, le_rfl, fun c C CV hc hR =>
          hres y hy c hc 0 C CV hR (Or.inl (Nat.zero_le _))⟩)
    obtain rfl : L' = L := hU.1 hL'U hLU (hL'r.trans hLr.symm)
    exact hcomp
  · obtain ⟨j, hj, B, CV, hfl, L', hL'U, hL'r, hL'B⟩ := hf.fastOrigin y hy n l hl hfast
    obtain rfl : L' = L := hU.1 hL'U hLU (hL'r.trans hLr.symm)
    refine compatible_of_anc_family hU hL'B (by_contra fun hB => ?_)
    obtain ⟨hcount, hCV⟩ := hf.counted y hy j l.slot B CV hfl
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ Hᶜ ∪ D.W := by
      rintro u ⟨v, hv, rfl⟩
      by_contra hu
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hu
      obtain ⟨hvs, R, hRU, hRr, -, hBR⟩ := hCV v hv
      obtain ⟨j', hj', e, hve, rfl⟩ := fastLock_honest_vote_family hf hy hfl hv hu.1
      exact hB (compatible_of_voteCompat_family hU hRU hRr hBR
        (hvi.voteCompat_of_not_lateWaker ht hu.1 hu.2 (by omega) hve (by omega)))
    have hh := Set.ncard_le_ncard hsub
    have hh' := D.two_mul_lt
    omega

end Consensus.Goldilocks.FamilySafety

end

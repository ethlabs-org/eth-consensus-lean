module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety under growing faults: fast locks, counted at the writer's cut

A fast lock (a fast update or an optimistic selection) is written at a cut `c` of its writer,
from the votes `CV` of the writer's pool or check point at `c`. The count is made there: the
signers in `CV` honest at `c` have genuine votes (Lemma G at the writer's cut), and the rest are
compromised by `c`. After the write the lock is the writer's own state.

* `fastLock_provenance_at`, `fastLock_counted_at`: the provenance of a stored fast lock (the
  writing cut `c`, at which the writer is honest) and the count at `c`, lifted to the prefix
  through the cut's time;
* `fastLock_honest_vote_at`: a counted vote of a validator honest at the writer's cut was cast by
  it, at a cut no later than `c` at which it was honest;
* `fastLock_compatible_at`: the block of a fast lock of label `s` written at `c` is compatible with
  `P`. Labels `< j₀` are within `b₀`; labels in `[j₀, j₀ + k]` count against `(H z)ᶜ ∪ W` at
  `t_c ≤ z`; later labels count against `(H (t_c))ᶜ` (`late`, and `2 f_{t_c} < n`);
* `OutageVoteInv.stored_fastLock_compatible_at`: every stored fast lock of a node honest at the
  reading cut names a held block compatible with `P`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A fast lock of the prefix's AC trace is a fast lock of the run at a time `≤ d`. -/
private theorem sa_fastLockAt_upTo (hm : Monotone tr.time) {d : Time} {y : Fin sp.n} {c s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} :
    SA.FastLockAt (tr.projAC.upTo d) y c s B CV ↔
      tr.time c ≤ d ∧ SA.FastLockAt tr.projAC y c s B CV := by
  have hm' : Monotone tr.projAC.time := hm
  constructor
  · rintro (⟨ℓ, C, hu, hC, hD, hCV⟩ | hO)
    · obtain ⟨hi, hu⟩ := (sa_updateAt_upTo hm').mp hu
      rw [ac_state_upTo hm' hi] at hC hD hCV
      exact ⟨hi, Or.inl ⟨ℓ, C, hu, hC, hD, hCV⟩⟩
    · obtain ⟨hi, hO⟩ := (sa_optimisticLockAt_upTo hm').mp hO
      exact ⟨hi, Or.inr hO⟩
  · rintro ⟨hi, ⟨ℓ, C, hu, hC, hD, hCV⟩ | hO⟩
    · rw [← ac_state_upTo hm' hi] at hC hD hCV
      exact Or.inl ⟨ℓ, C, (sa_updateAt_upTo hm').mpr ⟨hi, hu⟩, hC, hD, hCV⟩
    · exact Or.inr ((sa_optimisticLockAt_upTo hm').mpr ⟨hi, hO⟩)

/-- A fast lock is written at a call of its writer. -/
theorem fastLockAt_isCall {y : Fin sp.n} {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hfl : SA.FastLockAt tr.projAC y c s B CV) : tr.IsCall y c := by
  rcases hfl with ⟨ℓ, C, hu, -⟩ | ⟨ℓ, A, hpt, -⟩
  · exact ⟨_, projAC_callAt.1 hu.1⟩
  · exact ⟨_, projAC_callAt.1 hpt.1⟩

/-- A fast lock of label `s` is written at or before `t_s + 6Δ`. -/
theorem fastLockAt_time_le (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) : tr.time c ≤ sp.ts s + 6 * sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, hu, -⟩ | ⟨ℓ, A, -, hslot, -⟩
  · exact hu.2.2.1.le
  · have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have : tr.time c < sp.ts (s + 1 : Nat) := by
      by_contra h
      have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg c) ((s + 1 : Nat) : Int)).1 (not_lt.1 h)
      rw [show sp.slot (tr.time c) = s from hslot] at this
      omega
    linarith

/-- **Fast-lock provenance at the reading cut**: a stored fast lock of a node honest at cut `n`
lies below the block of a fast lock of its slot written at an earlier cut `c`, at which the node
was honest. -/
theorem fastLock_provenance_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {n : Nat} (hy : y ∈ H (tr.time n)) {l : SA.Lock}
    (hl : l ∈ (tr.state y n).ac.locks) (hf : l.fast = true) :
    ∃ c < n, ∃ B CV, SA.FastLockAt tr.projAC y c l.slot B CV ∧ y ∈ H (tr.time c) ∧
      ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧ Anc (tr.HonestBlocksAt H) L B := by
  have hd := hrun.time_nonneg n
  have hl' : l ∈ ((tr.projAC.upTo (tr.time n)).state y n).locks := by
    rw [projAC_upTo_state hrun le_rfl, projAC_state_at hrun hy]; exact hl
  obtain ⟨c, hc, B, CV, hfl, L, hL, hLr, hLB⟩ :=
    SA.fast_lock_provenance (acRun_upTo hrun hnc hd).localRun hy n l hl' hf
  obtain ⟨hcd, hfl⟩ := (sa_fastLockAt_upTo hrun.time_mono).mp hfl
  exact ⟨c, hc, B, CV, hfl, hrun.antitone hcd hy, L, upTo_subset hrun hd hL, hLr,
    hLB.mono (upTo_subset hrun hd)⟩

/-- **The fast-lock count at the writer's cut**: the counted validators are at least half of the
committee, and every counted vote is of the slot with a head held while honest above the
block. -/
theorem fastLock_counted_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) :
    sp.n ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ R.slot ≤ s ∧
        Anc (tr.HonestBlocksAt H) B R := by
  have hd := hrun.time_nonneg c
  have hsub := upTo_subset hrun hd
  obtain ⟨hcount, hCV⟩ := SA.fastLock_counted (acRun_upTo hrun hnc hd) hy
    ((sa_fastLockAt_upTo hrun.time_mono).mpr ⟨le_rfl, hfl⟩)
  refine ⟨hcount, fun v hv => ?_⟩
  obtain ⟨hvs, R, hR, hRr, hRs, hBR⟩ := hCV v hv
  exact ⟨hvs, R, hsub hR, hRr, hRs, hBR.mono hsub⟩

/-- **Lemma G at a fast lock**: a counted vote of a validator honest at the writer's cut `c` was
cast by it at a cut no later than `c`, at which it was honest. -/
theorem fastLock_honest_vote_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) {v : Vote sp.n} (hv : v ∈ CV)
    (hvH : v.val ∈ H (tr.time c)) :
    ∃ j ≤ c, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v := by
  have hd := hrun.time_nonneg c
  rcases hfl with ⟨ℓ, C, -, -, -, rfl⟩ | ⟨ℓ, A, hpt, -, -, rfl⟩
  · obtain ⟨j, hj, e, hve, he⟩ := pool_vote_at hrun hnc hy hv.1 hvH
    exact ⟨j, hj.le, e, hve, he⟩
  · obtain ⟨-, j, hj, e, hve, he⟩ := SA.optimisticPoint_pool_vote (acRun_upTo hrun hnc hd) hy
      (by
        refine ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hpt.1, ?_⟩
        rw [projAC_upTo_state hrun le_rfl]
        exact hpt.2) hv.1 hvH
    obtain ⟨hjd, hve⟩ := sa_voteAt_upTo.mp hve
    exact ⟨j, hj, e, hVoteAt_iff.2 ⟨hrun.antitone hjd hvH, hve⟩, he⟩

variable {D : OutageLockPremises tr H proposer dg}

/-- **A fast lock block is compatible with `P`, counted at the writer's cut**: a fast update or
an optimistic selection of label `s` by a node honest at its cut `c`, whose counted votes of
validators honest at `c` were cast at cuts before `n`, from (H)/S5V at the cuts before `n` only.
For a label at most `j₀ + k` the write is at a time `≤ z`. -/
theorem fastLock_compatible_at {n : Nat} (hvi : OutageVoteInv D n) {y : Fin sp.n} {c s : Nat}
    (hyc : y ∈ H (tr.time c)) {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV)
    (hcut : ∀ v ∈ CV, v.val ∈ H (tr.time c) → ∃ j < n, ∃ e, HVoteAt tr H v.val j e ∧ e.msg = v)
    (hcz : s ≤ D.j₀ + sp.k → tr.time c ≤ D.z) :
    Compatible (tr.HonestBlocksAt H) B D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hcount, hCV⟩ := fastLock_counted_at D.hrun D.hnc hyc hfl
  have hcall := fastLockAt_isCall hfl
  by_cases hs : s < D.j₀
  · -- an update or a selection of a label `< j₀` is within `b₀`
    have hj₀ := D.hj₀.1
    have hsj := ts_le_ts (sp := sp) (show s + 1 ≤ D.j₀ by omega)
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    rcases hfl with ⟨ℓ, C, hu, hC, hD, -⟩ | hO
    · have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
      obtain ⟨-, hΦU⟩ := frameIn_at D.hrun D.hnc hyc hu.1
      have hBC : ℓ.frame.Anc B C := (SA.deepest_mem hD).1.1.2.2
      have hCU : C ∈ tr.HonestBlocksAt H := hΦU (SA.deepest_mem hC).1.1
      exact compatible_of_head_anc hU (hBC.mono hΦU) (D.compatible_of_within
        (OriginWithin.of_result hyc (by linarith) ⟨ℓ, hu, hC, rfl⟩) hCU)
    · obtain ⟨ℓ, A, hpt, hslot, hsel, -⟩ := id hO
      have hlt : tr.time c < sp.ts (s + 1 : Nat) := by
        by_contra h
        have := (SA.ts_le_iff_le_slot sp (D.hrun.time_nonneg c) ((s + 1 : Nat) : Int)).1
          (not_lt.1 h)
        rw [show sp.slot (tr.time c) = s from hslot] at this
        omega
      obtain ⟨-, hΦU⟩ := frameIn_at D.hrun D.hnc hyc hpt.1
      have hBt : B ∈ ℓ.frame.tree := by
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact (SA.deepest_mem hsel).1.1
      exact D.compatible_of_within (OriginWithin.of_optimistic hyc (by linarith) hO) (hΦU hBt)
  refine by_contra fun hB => ?_
  -- a counted validator honest at `c` whose vote is compatible with `P` makes `B` compatible
  have hgood : ∀ v ∈ CV, v.val ∈ H (tr.time c) →
      (∀ j < n, ∀ e, HVoteAt tr H v.val j e → e.msg = v → e.msg.slot = s →
        VoteCompat (tr.HonestBlocksAt H) e.msg D.P) → False := by
    intro v hv hvH hcomp
    obtain ⟨hvs, R, hRU, hRr, -, hBR⟩ := hCV v hv
    obtain ⟨j, hj, e, hve, rfl⟩ := hcut v hv hvH
    exact hB (compatible_of_voteCompat hU hRU hRr hBR (hcomp j hj e hve rfl hvs))
  by_cases hsK : s ≤ D.j₀ + sp.k
  · -- the cohort count at `t_c ≤ z`: the counted validators lie in `(H z)ᶜ ∪ W`
    have hcz := hcz hsK
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ (H D.z)ᶜ ∪ D.W := by
      rintro u ⟨v, hv, rfl⟩
      by_contra hu
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hu
      exact hgood v hv (D.hrun.antitone hcz hu.1) fun j hj e hve he hes =>
        hvi.voteCompat_of_not_lateWaker_at hj hve (by omega) fun _ => hu
    have := Set.ncard_le_ncard hsub
    have := D.two_mul_lt
    omega
  · -- `late` at the cuts before `n`: the counted validators lie in `(H (t_c))ᶜ`
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ (H (tr.time c))ᶜ := by
      rintro u ⟨v, hv, rfl⟩ hu
      exact hgood v hv hu fun j hj e hve he hes => hvi.late v.val j hj e hve (by omega)
    have := Set.ncard_le_ncard hsub
    have := D.two_faults_lt_at hyc hcall
    omega

/-- **Every stored fast lock of a node honest at the reading cut `n` names a held block
compatible with `P`**, from (H)/S5V at the cuts before `n`: the lock's writing cut `c < n`
(`fastLock_provenance_at`), the count at `c`. -/
theorem OutageVoteInv.stored_fastLock_compatible_at {n : Nat} (hvi : OutageVoteInv D n)
    {y : Fin sp.n} (hy : y ∈ H (tr.time n)) {l : SA.Lock} (hl : l ∈ (tr.state y n).ac.locks)
    (hf : l.fast = true) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨L, hL, hLr, -⟩ := lock_origin_at D.hrun D.hnc hy l hl
  obtain ⟨c, hc, B, CV, hfl, hyc, L', hL'U, hL'r, hL'B⟩ :=
    fastLock_provenance_at D.hrun D.hnc hy hl hf
  obtain rfl : L' = L := hU.1 hL'U (mem_honestBlocksAt D.hrun hy hL) (hL'r.trans hLr.symm)
  refine ⟨L', hL, hLr, compatible_of_head_anc hU hL'B (fastLock_compatible_at hvi hyc hfl
    (fun v hv hvH => ?_) fun hsK => ?_)⟩
  · obtain ⟨j, hj, e, hve, he⟩ := fastLock_honest_vote_at D.hrun D.hnc hyc hfl hv hvH
    exact ⟨j, by omega, e, hve, he⟩
  · have := fastLockAt_time_le D.hrun hfl
    have := ts_le_ts (sp := sp) hsK
    exact D.hzc _ (by linarith) ⟨y, c, hyc, fastLockAt_isCall hfl, le_rfl⟩

end Consensus.Goldilocks.Compose.Growing

end

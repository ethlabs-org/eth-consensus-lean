module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage lock safety under growing faults: fast locks, counted at the writer's cut

A fast lock (a fast update or an optimistic selection) is written at a cut `c` of its writer,
from the votes `CV` of the writer's pool or check point at `c`. The count is made there: the
signers in `CV` honest at `c` have genuine votes (Lemma G at the writer's cut), and the rest are
compromised by `c`. After the write the lock is the writer's own state.

* `fastLock_provenance_at`, `fastLock_counted_at`: the provenance of a stored fast lock (the
  writing cut `c`, at which the writer is honest) and the count at `c`, lifted to the prefix
  through the cut's time; the counted signers lie in the slot's committee `K s` (P);
* `fastLock_honest_vote_at`: a counted vote of a validator honest at the writer's cut was cast by
  it, at a cut no later than `c` at which it was honest;
* `fastLock_compatible_at`: the block of a fast lock of label `s` written at `c` is compatible with
  `P`. Labels `< j₀` are within `b₀`; labels in `[j₀, j₀ + k]` count against
  `K s ∩ ((H z)ᶜ ∪ W)` at `t_c ≤ z`; later labels count against `K s ∩ (H (t_c))ᶜ` (`late`, and
  `2·|K s ∩ (H t_c)ᶜ| < committeeSize`);
* `OutageVoteInv.stored_fastLock_compatible_at`: every stored fast lock of a node honest at the
  reading cut names a held block compatible with `P`;
* `slow_lock_compatible_at`: a stored slow lock of a node honest at the reading cut is compatible
  with `B` when one result of its node in the slow window is (node-local, the static proof read
  on the prefix through the reading cut);
* `OutageVoteInv.locks_compatible_at` ((i) at a cut): every stored lock of a node honest at the
  reading cut names a held block compatible with `P`, from (H)/S5V and (R) at the earlier cuts. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

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
theorem fastLockAt_time_le (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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

/-- A fast lock of label `s` is written at or after `t_s`. -/
theorem fastLockAt_ts_le (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {c s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) : sp.ts s ≤ tr.time c := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, hu, -⟩ | ⟨ℓ, A, -, hslot, -⟩
  · have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
    linarith
  · exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg c) (s : Int)).2
      (by rw [show sp.slot (tr.time c) = s from hslot])

/-- The AC state of a node at cut `n`, read at a time `t` after every cut before `n` at which the
node is honest, is the AC state of the prefix through `t`. -/
private theorem projAC_state_by
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {y : Fin sp.n}
    {n : Nat}
    {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) :
    (tr.projAC.upTo t).state y n = (tr.state y n).ac := by
  have h := projAC_state (hrun.upTo ht0).toLocalRun hy n
  rwa [RunTrace.upTo_projAC, Trace.upTo_state tr y ht] at h

/-- **Fast-lock provenance at a read time**: a stored fast lock of a node honest at cut `n`
lies below the block of a fast lock of its slot written at an earlier cut `c`, at which the node
was honest. The lock is read at a time `t` at which the node is honest, after every cut before
`n`. -/
theorem fastLock_provenance_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {n : Nat} {t : Time} (ht0 : 0 ≤ t)
    (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) {l : SA.Lock}
    (hl : l ∈ (tr.state y n).ac.locks) (hf : l.fast = true) :
    ∃ c < n, ∃ B CV, SA.FastLockAt tr.projAC y c l.slot B CV ∧ y ∈ H (tr.time c) ∧
      ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧ Anc (tr.HonestBlocksAt H) L B := by
  have hl' : l ∈ ((tr.projAC.upTo t).state y n).locks := by
    rw [projAC_state_by hrun ht0 ht hy]; exact hl
  obtain ⟨c, hc, B, CV, hfl, L, hL, hLr, hLB⟩ :=
    SA.fast_lock_provenance_from (acRun_upTo hrun hnc ht0).localRun hrun.vstart hy n l hl' hf
  obtain ⟨hcd, hfl⟩ := (sa_fastLockAt_upTo hrun.time_mono).mp hfl
  exact ⟨c, hc, B, CV, hfl, hrun.antitone hcd hy, L, upTo_subset hrun ht0 hL, hLr,
    hLB.mono (upTo_subset hrun ht0)⟩

/-- A stored lock of a node at cut `n`, read at a time `t` at which it is honest after every cut
before `n`, names a block of its tree. -/
private theorem lock_held_by
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {n : Nat} {t : Time} (ht0 : 0 ≤ t)
    (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t) {l : SA.Lock}
    (hl : l ∈ (tr.state y n).ac.locks) : ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block := by
  have hst := Trace.upTo_state tr y ht
  obtain ⟨L, hL, hLr, -⟩ := lock_origin (hrun.upTo ht0) (hnc.upTo _) hy n l (by rw [hst]; exact hl)
  rw [hst] at hL
  exact ⟨L, hL, hLr⟩

/-- **The fast-lock count at the writer's cut**: the counted validators are at least half of the
committee and lie in the slot's committee (P), and every counted vote is of the slot with a head
held while honest above the block. -/
theorem fastLock_counted_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {K : SA.CommitteeDict sp.n} (hP : SA.CommitteePAt K tr.projAC H)
    {y : Fin sp.n} {c s : Nat} (hy : y ∈ H (tr.time c))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) :
    sp.committeeSize ≤ 2 * {u | ∃ v ∈ CV, v.val = u}.ncard ∧
      {u | ∃ v ∈ CV, v.val = u} ⊆ K.committee s ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ tr.HonestBlocksAt H, R.root = v.head ∧ R.slot ≤ s ∧
        Anc (tr.HonestBlocksAt H) B R := by
  have hd := hrun.time_nonneg c
  have hsub := upTo_subset hrun hd
  have hK : {u | ∃ v ∈ CV, v.val = u} ⊆ K.committee s := by
    rintro u ⟨v, hv, rfl⟩
    rcases hfl with ⟨ℓ, C, -, -, -, rfl⟩ | ⟨ℓ, A, hpt, -, -, rfl⟩
    · exact hP.1 (tr.time c) y hy c (fun _ hk => hrun.time_mono hk.le) s v hv.1
    · exact hP.2 y c ℓ A hy hpt s v hv.1
  obtain ⟨hcount, hCV⟩ := SA.fastLock_counted (acRun_upTo hrun hnc hd) hy
    ((sa_fastLockAt_upTo hrun.time_mono).mpr ⟨le_rfl, hfl⟩)
  refine ⟨hcount, hK, fun v hv => ?_⟩
  obtain ⟨hvs, R, hR, hRr, hRs, hBR⟩ := hCV v hv
  exact ⟨hvs, R, hsub hR, hRr, hRs, hBR.mono hsub⟩

/-- **Lemma G at a fast lock**: a counted vote of a validator honest at the writer's cut `c` was
cast by it at a cut no later than `c`, at which it was honest. -/
theorem fastLock_honest_vote_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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

variable {D : OutageLockPremises tr H proposer dg ini}

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
  obtain ⟨hcount, hCVK, hCV⟩ := fastLock_counted_at D.hrun D.hnc D.facts.hP hyc hfl
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
  · -- the opponents count at `t_c ≤ z`: the counted validators lie in `K s ∩ ((H z)ᶜ ∪ W)`
    have hcz := hcz hsK
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ D.K.committee s ∩ ((H D.z)ᶜ ∪ D.W) := by
      intro u hu
      refine ⟨hCVK hu, ?_⟩
      obtain ⟨v, hv, rfl⟩ := hu
      by_contra hu
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hu
      exact hgood v hv (D.hrun.antitone hcz hu.1) fun j hj e hve he hes =>
        hvi.voteCompat_of_not_opponent_at hj hve (by omega) fun _ => hu
    have := Set.ncard_le_ncard hsub
    have := D.two_mul_lt_K (not_lt.1 hs) hsK ⟨y, c, hyc, hcall, fastLockAt_ts_le D.hrun hfl⟩
    omega
  · -- `late` at the cuts before `n`: the counted validators lie in `K s ∩ (H (t_c))ᶜ`
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ D.K.committee s ∩ (H (tr.time c))ᶜ := by
      intro u hu
      refine ⟨hCVK hu, ?_⟩
      obtain ⟨v, hv, rfl⟩ := hu
      exact fun hu => hgood v hv hu fun j hj e hve he hes => hvi.late v.val j hj e hve (by omega)
    have := Set.ncard_le_ncard hsub
    have := D.two_faults_lt_K (fastLockAt_ts_le D.hrun hfl) (fastLockAt_time_le D.hrun hfl)
      ⟨y, c, hyc, hcall, le_rfl⟩
    omega

/-- **Every stored fast lock of a node at cut `n`, read at a time `t` at which it is honest after
every cut before `n`, names a held block compatible with `P`**, from (H)/S5V at the cuts before
`n`: the lock's writing cut `c < n` (`fastLock_provenance_at`), the count at `c`. -/
theorem OutageVoteInv.stored_fastLock_compatible_at {n : Nat} (hvi : OutageVoteInv D n)
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t)
    {l : SA.Lock} (hl : l ∈ (tr.state y n).ac.locks) (hf : l.fast = true) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P := by
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨L, hL, hLr⟩ := lock_held_by D.hrun D.hnc ht0 ht hy hl
  obtain ⟨c, hc, B, CV, hfl, hyc, L', hL'U, hL'r, hL'B⟩ :=
    fastLock_provenance_at D.hrun D.hnc ht0 ht hy hl hf
  obtain rfl : L' = L := hU.1 hL'U (tree_held_at ht0 hy ht hL) (hL'r.trans hLr.symm)
  refine ⟨L', hL, hLr, compatible_of_head_anc hU hL'B (fastLock_compatible_at hvi hyc hfl
    (fun v hv hvH => ?_) fun hsK => ?_)⟩
  · obtain ⟨j, hj, e, hve, he⟩ := fastLock_honest_vote_at D.hrun D.hnc hyc hfl hv hvH
    exact ⟨j, by omega, e, hve, he⟩
  · have := fastLockAt_time_le D.hrun hfl
    have := ts_le_ts (sp := sp) hsK
    exact D.hzc _ (by linarith) ⟨y, c, hyc, fastLockAt_isCall hfl, le_rfl⟩

/-- **A slow lock is compatible with `B` when one result in its slow window is**: at a cut `i`
of a node read at a time `t` at which it is honest after every cut before `i`, a stored slow lock
names a held block compatible with `B` when every result of the node at an earlier cut of one
label `m` of the window is compatible with `B`. -/
theorem slow_lock_compatible_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t)
    (ht : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    {l : SA.Lock} (hl : l ∈ (tr.state x i).ac.locks) (hlf : l.fast = false)
    (hgood : ∃ m : Int, (l.slot : Int) - sp.k < m ∧ m ≤ l.slot ∧ 0 ≤ m ∧
      ∀ c C CV, c < i → SA.ResultAt tr.projAC x c m.toNat C CV →
        Compatible (tr.HonestBlocksAt H) C B) :
    ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L B := by
  have hsub := upTo_subset hrun ht0
  have hU := honestBlocksAt_coherent hrun hnc
  have hr := (acRun_upTo hrun hnc ht0).localRun
  have hl' : l ∈ ((tr.projAC.upTo t).state x i).locks := by
    rw [projAC_state_by hrun ht0 ht hx]; exact hl
  obtain ⟨c, hci, ℓ, C, CV, hu, hC, Lb, hLb, hLbC, ⟨L, hL, hLr, hLLb⟩, hsave⟩ :=
    SA.slow_lock_saved hr hrun.vstart hx i l hl' hlf
  obtain ⟨-, hC⟩ := (sa_resultAt_upTo hrun.time_mono).mp hC
  obtain ⟨m, hm, hms, hm0, hgood⟩ := hgood
  obtain ⟨-, hΦU⟩ := SA.frameIn_of_callAt hr hx hu.1
  refine ⟨L, hsub hL, hLr, compatible_of_head_anc hU (hLLb.mono hsub) ?_⟩
  rcases hms.lt_or_eq with hms | hms
  · obtain ⟨S, hS, hsaved, hLbS⟩ := hsave m hm hms
    have hmn : (m.toNat : Int) = m := Int.toNat_of_nonneg hm0
    obtain ⟨k, hkc, C', CV', hC', hroot⟩ := SA.saved_result hr hrun.vstart
      hx c m.toNat (by simpa only [hmn] using hsaved)
    obtain ⟨ℓ', hu', hconf, -⟩ := id hC'
    have hC'mem := (SA.frameIn_of_callAt hr hx hu'.1).2 (SA.deepest_mem hconf).1.1
    have heq : C' = S := hr.coherent.1 hC'mem (hΦU hS) hroot
    obtain ⟨-, hC'⟩ := (sa_resultAt_upTo hrun.time_mono).mp hC'
    exact compatible_of_head_anc hU ((Anc.mono hΦU hLbS).mono hsub)
      (heq ▸ hgood k C' CV' (hkc.trans hci) hC')
  · have hmn : m.toNat = l.slot := by omega
    exact compatible_of_head_anc hU ((Anc.mono hΦU hLbC).mono hsub)
      (hgood c C CV hci (hmn ▸ hC))

/-- **(i) at a cut, read at a time**: with (H)/S5V at the cuts before `n` and (R) at the cuts before
`n`, every lock stored at cut `n` by a node read at a time `t` at which it is honest, after every
cut before `n`, names a held block compatible with `P`. A fast lock
is counted at its writing cut (`stored_fastLock_compatible_at`); a slow lock has an unpolluted
label in its window (`exists_unpolluted_label`), whose results are compatible with `P` (R). -/
theorem OutageVoteInv.locks_compatible_at {n : Nat} (hvi : OutageVoteInv D n)
    (hres : ∀ y k, k < n → y ∈ H (tr.time k) → ∀ m C CV, SA.ResultAt tr.projAC y k m C CV →
      (m ≤ D.j₀ ∨ D.r ≤ m) → Compatible (tr.HonestBlocksAt H) C D.P)
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (ht : ∀ k < n, tr.time k ≤ t) (hy : y ∈ H t)
    {l : SA.Lock} (hl : l ∈ (tr.state y n).ac.locks) :
    ∃ L ∈ (tr.state y n).fg.tree, L.root = l.block ∧ Compatible (tr.HonestBlocksAt H) L D.P := by
  cases hf : l.fast
  swap
  · exact hvi.stored_fastLock_compatible_at ht0 ht hy hl hf
  have hU := D.coherent
  obtain ⟨L, hL, hLr⟩ := lock_held_by D.hrun D.hnc ht0 ht hy hl
  have hgood : ∃ m : Int, (l.slot : Int) - sp.k < m ∧ m ≤ l.slot ∧ 0 ≤ m ∧
      ∀ c C CV, c < n → SA.ResultAt tr.projAC y c m.toNat C CV →
        Compatible (tr.HonestBlocksAt H) C D.P := by
    obtain ⟨m, h1, h2, h3⟩ := exists_unpolluted_label sp D.hgap l.slot
    have hres' : ∀ c C CV, c < n → ∀ m', SA.ResultAt tr.projAC y c m' C CV →
        (m' ≤ D.j₀ ∨ D.r ≤ m') → Compatible (tr.HonestBlocksAt H) C D.P :=
      fun c C CV hc m' hR hm' => hres y c hc (D.hrun.antitone (ht c hc) hy)
        m' C CV hR hm'
    by_cases hm0 : 0 ≤ m
    · refine ⟨m, h1, h2, hm0, fun c C CV hc hR => hres' c C CV hc m.toNat hR ?_⟩
      have hmn : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
      rcases h3 with h | h
      · left
        by_contra hgt
        have := ts_le_ts (sp := sp) (show D.j₀ + 1 ≤ m.toNat by omega)
        rw [hmn] at this
        linarith [D.hj₀.2]
      · right
        exact D.hr.2 m.toNat (by rw [hmn]; exact h)
    · exact ⟨0, by omega, by omega, le_rfl, fun c C CV hc hR => hres' c C CV hc 0 hR
        (Or.inl (Nat.zero_le _))⟩
  obtain ⟨L', hL'U, hL'r, hcomp⟩ := slow_lock_compatible_at D.hrun D.hnc ht0 ht hy hl hf hgood
  obtain rfl : L' = L := hU.1 hL'U (tree_held_at ht0 hy ht hL) (hL'r.trans hLr.symm)
  exact ⟨L', hL, hLr, hcomp⟩

end Consensus.Goldilocks.Compose.Growing

end

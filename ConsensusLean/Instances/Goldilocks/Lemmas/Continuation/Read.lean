module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The continued reads after a hand-over

Ready-reader safety of the confirmed output from a time `t₀` through `b ≥ T`, after a hand-over
at `T`, from the seeded invariant (`SeededInvariant`, floors `rL`, `rO`, from `t₁ ≤ t₀`). A ready
read is the reader's effective record: the block named by its record when its frame holds it,
else its finalized block `Σ.F`.

* `healed_record_cover_at`: the effective record of a reader honest at a read point `t ∈ [t₁, b]`
  is `Σ.F` or below a result or optimistic selection of label `≥ rO`, written by a node honest at
  its cut, before the read.
* `effective_record_on_healed_chain_at`: so the effective record is on the healed chain: `Σ.F` is
  by the cache facts, and an origin of label `≥ rO` written before `b` is a family member.
* `seeded_records_compatible_at` (agreement): two such records are compatible, since the family
  members are pairwise compatible.
* `seeded_effective_record_mono_at` (monotonicity): one reader's effective record only extends
  between two read points from `t₀ ≥ t_{rO+1}` on. Every result or optimistic selection of the
  reader in between is written from `t_{rO+1}` on, so its label is `≥ rO` and it is a family
  member, compatible with the earlier record; so is every later `Σ.F`. The effective record
  survives such an interval (`effective_record_of_interval_at`): a candidate strictly below the
  record is refused by the record update's no-regression guard, and a compatible floor change
  keeps the record's block.
* `seeded_ready_read_record_at` (open): a ready read is the effective record.
* `continued_safe_on_at`: `ReadySafeOn` from `t₀` through `b`.
* `continued_safe_engine_at`: the engine's confirmed output is `ReadySafe` with catch-up `c + 1`
  from `t₀ + 1`, from the trace form through the horizon; the read point's clock is at most one
  time unit behind its engine cut. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-- **The record cover from `t₁` through `b`**: the effective record of a reader honest at a read
point `t ∈ [t₁, b]` is its `Σ.F`, or below a result or optimistic selection of label `≥ rO`
written by a node honest at its cut, before the read. -/
theorem healed_record_cover_at {rL rO : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) {y : Fin sp.n} {n : Nat} {t : Time}
    (ht₁ : t₁ ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hrp : Regimes.ReadPoint tr n t) :
    HealedRecordCoverAt tr H rO y n t
      ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F) :=
  hinv.record y n t ht₁ htb hy hrp

/-- **A reader at a read point from `t₁` on has called since just before the reset**: a call of
its own before the read point, at a time `≥ t_{r−k−3}`. The cache and full-read facts of the
seeded invariant are stated for such readers.

Open (`sorry`): a placeholder of the expected shape for the lemma that discharges that premise,
to be replaced by it; a reader honest at `t ≥ t₁` was honest and awake, hence calling, on the
window before `t₁` that follows `t_{r−k−3}`. -/
theorem seeded_reader_called_at {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b) {y : Fin sp.n} {n : Nat} {t : Time}
    (ht₁ : t₁ ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hrp : Regimes.ReadPoint tr n t) :
    ∃ c < n, tr.IsCall y c ∧ sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c := by
  sorry

/-- Two blocks on the healed chain are compatible when the family members are pairwise
compatible. -/
theorem OnHealedChain.compatible_chain (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {b : Time}
    (hP : ∀ C s C' s', HealedOrigin tr H g rL rO C s b → HealedOrigin tr H g rL rO C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (hX : OnHealedChain tr H g rL rO X b)
    (hY : OnHealedChain tr H g rL rO Y b) : Compatible (tr.HonestBlocksAt H) X Y := by
  obtain ⟨C, s, hC, hYC⟩ := onHealedChain_iff.1 hY
  exact (compatible_of_anc_left (honestBlocksAt_coherent hrun hnc) hYC
    (hX.compatible hrun hnc hP hC).symm).symm

/-- **The effective record is on the healed chain**: for a reader honest at a read point
`t ∈ [t₁, b]`, its `Σ.F` is on the healed chain by the cache facts, and an origin of label `≥ rO`
written before the read is a member of the family. -/
theorem effective_record_on_healed_chain_at {rL rO : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) {y : Fin sp.n} {n : Nat} {t : Time}
    (ht₁ : t₁ ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hrp : Regimes.ReadPoint tr n t) :
    OnHealedChain tr H g rL rO
      ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F) b := by
  rcases healedRecordCoverAt_iff.1 (healed_record_cover_at hinv ht₁ htb hy hrp) with h |
    ⟨x, q, s, C, CV, hx, -, hqt, hs, hC, hRC⟩
  · rw [h]
    exact (hinv.caches y n t ht₁ hrp.1 htb hy).1
  · refine onHealedChain_iff.2 ⟨C, s, HealedOrigin.of_origin hs ?_, hRC⟩
    rcases hC with hC | hC
    · exact OriginWithin.of_result hx (hqt.trans htb) hC
    · exact OriginWithin.of_optimistic hx (hqt.trans htb) hC

/-- **Agreement of the effective records**: the effective records of two readers, each honest at
a read point in `[t₁, b]`, are compatible inside the blocks held while honest. -/
theorem seeded_records_compatible_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) {y z : Fin sp.n} {i j : Nat} {t t' : Time}
    (ht₁ : t₁ ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hi : Regimes.ReadPoint tr i t)
    (ht₁' : t₁ ≤ t') (htb' : t' ≤ b) (hz : z ∈ H t') (hj : Regimes.ReadPoint tr j t') :
    Compatible (tr.HonestBlocksAt H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (tr.state y i).fg.F)
      ((SA.lookup (Node.frame (tr.state z j)) (tr.state z j).ac.latestConfirmed).getD
        (tr.state z j).fg.F) :=
  OnHealedChain.compatible_chain hrun hnc hinv.origins_compatible
    (effective_record_on_healed_chain_at hinv ht₁ htb hy hi)
    (effective_record_on_healed_chain_at hinv ht₁' htb' hz hj)

/-- A result or optimistic selection written at or after `t_{rO+1}` has label at least `rO`: a
result of label `s` is written at `t_s + 6Δ`, an optimistic selection in its slot `s`. -/
private theorem origin_label_ge {x : Fin sp.n} {q s rO : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hq : sp.ts (rO + 1 : Nat) ≤ tr.time q)
    (hC : SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) :
    rO ≤ s := by
  have hΔ := sp.toParams.hΔ
  have h0 : (0 : Time) ≤ tr.time q := (ts_natCast_nonneg _).trans hq
  rcases hC with ⟨ℓ, ⟨-, -, htq, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · replace htq : tr.time q = sp.ts s + 6 * sp.Δ := htq
    by_contra hlt
    have hle : ((s + 1 : Nat) : Int) ≤ (rO : Int) := by exact_mod_cast (not_le.mp hlt)
    have hmul := mul_le_mul_of_nonneg_left hle (show (0 : Time) ≤ 4 * sp.Δ by linarith)
    simp only [SAParams.ts] at htq hq
    push_cast at hmul hq htq
    nlinarith
  · replace hsl : sp.slot (tr.time q) = s := hsl
    have := (SA.ts_le_iff_le_slot sp h0 _).1 hq
    rw [hsl] at this
    omega

/-- **The effective record only extends** between two read points of one reader from
`t₀ ≥ t_{rO+1}` on, both in `[t₁, b]`. The reader's results and optimistic selections in between
are written from `t_{rO+1}` on, so their labels are `≥ rO` and they are family members; with
every later `Σ.F` they are compatible with the earlier record, which is on the healed chain, so
the effective record survives the interval. -/
theorem seeded_effective_record_mono_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {t₁ t₀ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) (ht₁ : t₁ ≤ t₀)
    (hdt : sp.ts (rO + 1 : Nat) ≤ t₀) {y : Fin sp.n} {i j : Nat} {t t' : Time}
    (hi : Regimes.ReadPoint tr i t) (hj : Regimes.ReadPoint tr j t') (hij : i ≤ j)
    (htt : t ≤ t') (ht₀ : t₀ ≤ t) (ht'b : t' ≤ b) (hy : y ∈ H t) (hy' : y ∈ H t') :
    Anc (tr.HonestBlocksAt H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (tr.state y i).fg.F)
      ((SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (tr.state y j).fg.F) := by
  have ht0' : (0 : Time) ≤ t' :=
    (ts_natCast_nonneg _).trans (hdt.trans (ht₀.trans htt))
  have hO := effective_record_on_healed_chain_at hinv (ht₁.trans ht₀) (htt.trans ht'b) hy hi
  refine Obligations.Growing.effective_record_of_interval_at hrun hnc ht0' hj.1 hy' hij
    (Obligations.Growing.effectiveRecordInterval_of_candidates_before_at hrun hnc ht0' hj.1 hy'
      (fun q hiq hqj D s CV hD => ?_) (fun q hiq hqj => ?_)) .refl
  · have hqt' : tr.time q ≤ t' := hj.1 q hqj
    have hqi : sp.ts (rO + 1 : Nat) ≤ tr.time q :=
      hdt.trans (ht₀.trans (hi.2.trans (hrun.time_mono hiq)))
    have hyq : y ∈ H (tr.time q) := hrun.antitone hqt' hy'
    have hDm : HealedOrigin tr H g rL rO D s b := by
      refine HealedOrigin.of_origin (origin_label_ge hqi hD) ?_
      rcases hD with hD | hD
      · exact OriginWithin.of_result hyq (hqt'.trans ht'b) hD
      · exact OriginWithin.of_optimistic hyq (hqt'.trans ht'b) hD
    exact hO.compatible hrun hnc hinv.origins_compatible hDm
  · have hq1 : ∀ k < q + 1, tr.time k ≤ t' := fun k hk => hj.1 k (by omega)
    exact OnHealedChain.compatible_chain hrun hnc hinv.origins_compatible
      (hinv.caches y (q + 1) t' (ht₁.trans (ht₀.trans htt)) hq1 ht'b hy').1 hO

/-- **A ready read is the effective record after a hand-over.** At a read point `(j, t)` with
`t ∈ [t₁, b]` of a node ready at `t`, the confirmed read is the block named by the record when the
frame holds it, else `Σ.F`.

Open (`sorry`): the genesis proof (`ready_read_record_at`) puts the record's block at or below
the anchor at `t`, or viable with a strict majority of the latest view's voters as supporters
(`read_head_support_at`), from the read invariant of the prefix through `t`. Its chain predicate
is the origin chain, which must hold the record's block, the stored locks and both caches; after a
hand-over the healed chain holds the record's block and `Σ.F` (`healed_record_cover_at`,
`SeededInvariant.caches`) and the live locks (`SeededInvariant.locks`), but not every stored lock or
a low `Σ.J`, which compare with the family only through `fc_root` (`SeededInvariant.caches`, second
part) and the held seed (`SeededInvariant.seedHeld`). -/
theorem seeded_ready_read_record_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelow tr H) (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    {y : Fin sp.n} {j : Nat} {t : Time} (hrp : Regimes.ReadPoint tr j t) (ht₁ : t₁ ≤ t)
    (htb : t ≤ b) (hready : Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y t) :
    Regimes.readAfter tr y j t =
      (SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (tr.state y j).fg.F := by
  sorry

/-- Readiness with a longer catch-up implies readiness with a shorter one. -/
private theorem readyAt_of_le {c c' : Time} (hcc : c' ≤ c) {y : Fin sp.n} {t : Time}
    (h : Regimes.Growing.ReadyAt tr H c y t) : Regimes.Growing.ReadyAt tr H c' y t :=
  ⟨h.1, fun τ hτ hτt => h.2 τ (le_trans (max_le_max le_rfl (by linarith)) hτ) hτt⟩

/-- **Ready-reader safety after a hand-over** from `t₀` through `b ≥ T`, for a catch-up
`c ≥ catchUp`: from the seeded invariant from `t₁ ≤ t₀`, with `t₀ ≥ t_{rO+1}` (`rO = r + k − 1`).
A ready read is the effective record (`seeded_ready_read_record_at`); two effective records are
compatible (`seeded_records_compatible_at`), and one reader's only extends
(`seeded_effective_record_mono_at`). -/
theorem continued_safe_on_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ t₀ b : Time} (hTb : T ≤ b)
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hcv : ChainConvictedBelow tr H) (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    (ht₁ : t₁ ≤ t₀) (hdt : sp.ts (r + sp.k : Nat) ≤ t₀) {c : Time} (hc : Regimes.catchUp sp ≤ c) :
    Regimes.Growing.ReadySafeOn tr H c t₀ b := by
  have hdt' : sp.ts (r + sp.k - 1 + 1 : Nat) ≤ t₀ := by
    have hk := sp.two_le_k
    rwa [show r + sp.k - 1 + 1 = r + sp.k by omega]
  have hread : ∀ {y j t}, Regimes.ReadPoint tr j t → t₀ ≤ t → t ≤ b →
      Regimes.Growing.ReadyAt tr H c y t → Regimes.readAfter tr y j t =
        (SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
          (tr.state y j).fg.F := fun hrp ht htb hready =>
    seeded_ready_read_record_at hrun hnc hseed hTb hsvc hB hcv hinv hrp (ht₁.trans ht) htb
      (readyAt_of_le hc hready)
  refine ⟨fun y z i j t t' hi hj _ _ ht htb ht' htb' hy hz => ?_,
    fun y i j t t' hi hj _ _ hij htt ht htb hy hy' => ?_⟩
  · rw [hread hi ht htb hy, hread hj ht' htb' hz]
    exact seeded_records_compatible_at hrun hnc hinv (ht₁.trans ht) htb hy.1 hi
      (ht₁.trans ht') htb' hz.1 hj
  · rw [hread hi ht (htt.trans htb) hy, hread hj (ht.trans htt) htb hy']
    exact seeded_effective_record_mono_at hrun hnc hinv ht₁ hdt' hi hj hij htt ht htb hy.1 hy'.1

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The engine reads from the trace's ready-reader safety.** If the canonical trace is
`ReadySafeOn` with catch-up `c ≥ 0` from `t₀` through the horizon, the engine's confirmed output is
`ReadySafe` with catch-up `c + 1` from `t₀ + 1`: an engine reader ready at a cut from `t₀ + 1` is
read at the read point of its last own event (`engine_read_point`), whose clock is at most one time
unit behind the cut (`stored_now_ge_cutTime_sub_one`), and ancestry of the reads inside the blocks
held while honest is a prefix of their confirmed chains (`read_prefix`). -/
theorem continued_safe_engine_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {c t₀ : Time} (hc : 0 ≤ c)
    (hsafe : Regimes.Growing.ReadySafeOn (simTraceAt S rho hn) (honestKeysAt S rho) c t₀
      rho.horizon) :
    (chainTrace rho).ReadySafe (c + 1) .confirmed (t₀ + 1) := by
  have hlag : ∀ v i, (chainTrace rho).InCuts (t₀ + 1) i →
      rho.point.Ready (c + 1) v (rho.cutTime i) → t₀ ≤ (stateAt S rho hn v i).now := by
    intro v i hi hr
    have := stored_now_ge_cutTime_sub_one S rho hn hv hi.1 hc hr
    have h2 : t₀ + 1 ≤ rho.cutTime i := hi.2
    linarith
  constructor
  · intro u v i j hi hj hu hv'
    obtain ⟨hrp, h0, hh, hra, hread⟩ := engine_read_point S rho hn hv hc hi.1 hu
    obtain ⟨hrp', h0', hh', hra', hread'⟩ := engine_read_point S rho hn hv hc hj.1 hv'
    rw [hread, hread']
    rcases hsafe.agree _ _ _ _ _ _ hrp hrp' (cutMap_boundary S rho hn _ _)
        (cutMap_boundary S rho hn _ _) (hlag _ _ hi hu) hh (hlag _ _ hj hv') hh' hra hra' with
      hc | hc
    · exact Or.inl (read_prefix S rho hn hv hnc h0 hrp.1 hra.1 h0' hrp'.1 hra'.1 hc)
    · exact Or.inr (read_prefix S rho hn hv hnc h0' hrp'.1 hra'.1 h0 hrp.1 hra.1 hc)
  · intro v i j hi hij hj hvi hvj
    obtain ⟨hrp, h0, -, hra, hread⟩ := engine_read_point S rho hn hv hc hi.1 hvi
    obtain ⟨hrp', h0', hh', hra', hread'⟩ := engine_read_point S rho hn hv hc hj.1 hvj
    rw [hread, hread']
    exact read_prefix S rho hn hv hnc h0 hrp.1 hra.1 h0' hrp'.1 hra'.1
      (hsafe.mono _ _ _ _ _ hrp hrp' (cutMap_boundary S rho hn _ _)
        (cutMap_boundary S rho hn _ _) (cutMap_mono S rho hn (lastOwn_mono S rho v hij))
        (now_mono S rho hn hv v hij) (hlag _ _ hi hvi) hh' hra hra')

end Consensus.Goldilocks.Obligations.Growing

end

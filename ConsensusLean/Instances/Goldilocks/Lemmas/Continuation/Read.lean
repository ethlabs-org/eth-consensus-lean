module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The continued reads after a hand-over

Ready-reader safety of the confirmed output from a time `t₀` through `b ≥ T`, after a hand-over
at `T`, from the seeded invariant (`SeededInvariant`, floors `rL`, `rO`, from `t₁ ≥ t_{r+k}`), with
`t₀ ≥ t₁ + 8Δ`. A ready
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
* `seeded_ready_read_record_at`: a ready read from `t_{r+k}` on is the effective record, through
  the head certificate at the read (`read_eq_record_of_current_votes_at`): the live locks and the
  record are on the healed chain; a record written by the reader with a label `≥ rO` is a viable
  member extended by the later votes, or a recent optimistic selection whose fast lock is still
  live, below the anchor.
* `seeded_stale_record_viable_at`: the same viability for a record the reader wrote with a label
  `< rO`, from `seeded_chain_candidate_at` (a held block of the healed chain of a reader that has
  called from `t_{r−k−3}` on is an ancestor candidate) and `seeded_reader_called_at`.
* `seeded_stale_record_votes_at`: the later honest votes extend such a record, which is below a
  member of label below the latest view's slot by the record cover at a read point a slot earlier
  (reads from `t₁ + 8Δ` on).
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
`t ∈ [t₁, b]` that has called from `t_{rL−k−3}` on before it, its `Σ.F` is on the healed chain
by the cache facts, and an origin of label `≥ rO`
written before the read is a member of the family. -/
theorem effective_record_on_healed_chain_at {rL rO : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) {y : Fin sp.n} {n : Nat} {t : Time}
    (ht₁ : t₁ ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hrp : Regimes.ReadPoint tr n t)
    (hcall : ∃ c < n, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c) :
    OnHealedChain tr H g rL rO
      ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F) b := by
  rcases healedRecordCoverAt_iff.1 (healed_record_cover_at hinv ht₁ htb hy hrp) with h |
    ⟨x, q, s, C, CV, hx, -, hqt, hs, hC, hRC⟩
  · rw [h]
    exact (hinv.caches y n t ht₁ hrp.1 htb hy hcall).1
  · exact onHealedChain_iff.2 ⟨C, s, HealedOrigin.of_origin hs
      (originWithin_iff.2 ⟨x, q, CV, hx, hqt.trans htb, hC⟩), hRC⟩

/-- **Agreement of the effective records**: the effective records of two readers, each honest at
a read point in `[t₁, b]` and having called from `t_{rL−k−3}` on before it, are compatible
inside the blocks held while honest. -/
theorem seeded_records_compatible_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {rL rO : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g rL rO t₁ b) {y z : Fin sp.n} {i j : Nat} {t t' : Time}
    (ht₁ : t₁ ≤ t) (htb : t ≤ b) (hy : y ∈ H t) (hi : Regimes.ReadPoint tr i t)
    (hci : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c)
    (ht₁' : t₁ ≤ t') (htb' : t' ≤ b) (hz : z ∈ H t') (hj : Regimes.ReadPoint tr j t')
    (hcj : ∃ c < j, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt z c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c) :
    Compatible (tr.HonestBlocksAt H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (tr.state y i).fg.F)
      ((SA.lookup (Node.frame (tr.state z j)) (tr.state z j).ac.latestConfirmed).getD
        (tr.state z j).fg.F) :=
  OnHealedChain.compatible_chain hrun hnc hinv.origins_compatible
    (effective_record_on_healed_chain_at hinv ht₁ htb hy hi hci)
    (effective_record_on_healed_chain_at hinv ht₁' htb' hz hj hcj)

/-- A result or optimistic selection of label `s` is written in `[t_s, t_s + 6Δ]`: a result at
`t_s + 6Δ`, an optimistic selection in its slot `s`. -/
private theorem origin_time_bounds {x : Fin sp.n} {q s : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)} (h0 : 0 ≤ tr.time q)
    (hC : SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) :
    sp.ts s ≤ tr.time q ∧ tr.time q ≤ sp.ts s + 6 * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  rcases hC with ⟨ℓ, ⟨-, -, htq, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · replace htq : tr.time q = sp.ts s + 6 * sp.Δ := htq
    exact ⟨by linarith, htq.le⟩
  · replace hsl : sp.slot (tr.time q) = s := hsl
    have hhi : tr.time q < sp.ts ((s : Int) + 1) := lt_of_not_ge fun h => by
      have := (SA.ts_le_iff_le_slot sp h0 _).1 h
      omega
    simp only [SAParams.ts] at hhi
    exact ⟨(SA.ts_le_iff_le_slot sp h0 _).2 (by omega), by simp only [SAParams.ts]; linarith⟩

/-- A result or optimistic selection written at or after `t_{rO+1}` has label at least `rO`. -/
private theorem origin_label_ge {x : Fin sp.n} {q s rO : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hq : sp.ts (rO + 1 : Nat) ≤ tr.time q)
    (hC : SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) :
    rO ≤ s := by
  have hΔ := sp.toParams.hΔ
  have hhi := (origin_time_bounds ((ts_natCast_nonneg _).trans hq) hC).2
  by_contra hlt
  have hle : ((s + 1 : Nat) : Int) ≤ (rO : Int) := by exact_mod_cast (not_le.mp hlt)
  have hmul := mul_le_mul_of_nonneg_left hle (show (0 : Time) ≤ 4 * sp.Δ by linarith)
  simp only [SAParams.ts] at hhi hq
  push_cast at hmul hq hhi
  nlinarith

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
    (htt : t ≤ t') (ht₀ : t₀ ≤ t) (ht'b : t' ≤ b) (hy : y ∈ H t) (hy' : y ∈ H t')
    (hcall : ∃ c < i, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
      sp.ts (rL - sp.k - 3 : Nat) ≤ tr.time c) :
    Anc (tr.HonestBlocksAt H)
      ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (tr.state y i).fg.F)
      ((SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (tr.state y j).fg.F) := by
  have ht0' : (0 : Time) ≤ t' :=
    (ts_natCast_nonneg _).trans (hdt.trans (ht₀.trans htt))
  have hO := effective_record_on_healed_chain_at hinv (ht₁.trans ht₀) (htt.trans ht'b) hy hi
    hcall
  refine Obligations.Growing.effective_record_of_interval_at hrun hnc ht0' hj.1 hy' hij
    (Obligations.Growing.effectiveRecordInterval_of_candidates_before_at hrun hnc ht0' hj.1 hy'
      (fun q hiq hqj D s CV hD => ?_) (fun q hiq hqj => ?_)) .refl
  · have hqt' : tr.time q ≤ t' := hj.1 q hqj
    have hqi : sp.ts (rO + 1 : Nat) ≤ tr.time q :=
      hdt.trans (ht₀.trans (hi.2.trans (hrun.time_mono hiq)))
    have hyq : y ∈ H (tr.time q) := hrun.antitone hqt' hy'
    have hDm : HealedOrigin tr H g rL rO D s b := by
      exact HealedOrigin.of_origin (origin_label_ge hqi hD)
        (originWithin_iff.2 ⟨y, q, CV, hyq, hqt'.trans ht'b, hD⟩)
    exact hO.compatible hrun hnc hinv.origins_compatible hDm
  · have hq1 : ∀ k < q + 1, tr.time k ≤ t' := fun k hk => hj.1 k (by omega)
    exact OnHealedChain.compatible_chain hrun hnc hinv.origins_compatible
      (hinv.caches y (q + 1) t' (ht₁.trans (ht₀.trans htt)) hq1 ht'b hy'
        (let ⟨c, hc, h⟩ := hcall; ⟨c, by omega, h⟩)).1 hO

private theorem catchUp_eq : Regimes.catchUp sp = 18 * sp.Δ := rfl

/-- The latest view at a time `t ≥ 0` of slot at least one is a natural label `L`, the slot of
`t` or the one before, with `t_L + Δ ≤ t < t_L + 6Δ`. -/
private theorem latest_label_at {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} (ht0 : 0 ≤ t) (h1 : 1 ≤ sp.slot t) :
    ∃ L : Nat, (L : Int) = (SA.latestView sp A Φ t).2 ∧ sp.slot t ≤ L + 1 ∧
      sp.ts L + sp.Δ ≤ t ∧ t < sp.ts L + 6 * sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have htlo := (SA.ts_le_iff_le_slot sp ht0 (sp.slot t)).2 le_rfl
  have hthi : t < sp.ts ((sp.slot t : Int) + 1) := lt_of_not_ge fun h => by
    have := (SA.ts_le_iff_le_slot sp ht0 _).1 h
    omega
  simp only [SAParams.ts] at htlo hthi
  by_cases hphase : sp.ts (sp.slot t : Int) + 2 * sp.Δ ≤ t
  · refine ⟨sp.slot t, by simp only [SA.latestView, hphase, ↓reduceIte], by omega, ?_, ?_⟩ <;>
      simp only [SAParams.ts] at hphase ⊢ <;> linarith
  · have hs : ((sp.slot t - 1 : Nat) : Int) = (sp.slot t : Int) - 1 := by omega
    refine ⟨sp.slot t - 1, by simp only [SA.latestView, hphase, ↓reduceIte]; exact hs,
      by omega, ?_, ?_⟩ <;> simp only [SAParams.ts] at hphase ⊢ <;> rw [hs] <;> linarith

/-- **A record above `fc_root` is viable**: at a read point `(j, t)` with `t ∈ [t₁, b]`,
`t ≥ t_{r+k}`, of a reader honest at `t`, a record block `R` not at or below `fc_root` is in the
full viable tree of the frame: it is on the healed chain (`effective_record_on_healed_chain_at`)
and held, so an ancestor candidate (`seeded_chain_candidate_at`), the reader having called from
`t_{r−k−3}` on before the read (`seeded_reader_called_at`). It is used for a record the reader
wrote with a label `< rO`, not a member of the family. -/
theorem seeded_stale_record_viable_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    {y : Fin sp.n} {j : Nat} {t : Time} (hrp : Regimes.ReadPoint tr j t) (ht₁ : t₁ ≤ t)
    (htb : t ≤ b) (hdt : sp.ts (r + sp.k : Nat) ≤ t) (hy : y ∈ H t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed = some R)
    (hRf : ¬ (Node.frame (tr.state y j)).Anc R (Node.frame (tr.state y j)).fcRoot) :
    R ∈ (Node.frame (tr.state y j)).viableTree (Node.frame (tr.state y j)).tree := by
  have hcall := seeded_reader_called_at hrun hseed hy hdt hrp.2
  have hRc : OnHealedChain tr H g r (r + sp.k - 1) R b := by
    have h := effective_record_on_healed_chain_at hinv ht₁ htb hy hrp hcall
    rwa [hR, Option.getD_some] at h
  exact (seeded_chain_candidate_at hinv ht₁ hrp.1 htb hy hcall hRc
    (SA.lookup_eq_some hR).1).resolve_left hRf

/-- **A stale record is extended by the latest view's honest votes**: at a read point `(j, t)`
with `t ∈ [t₁ + 8Δ, b]`, `t₁ ≥ t_{r+k}`, of a reader honest at `t`, let `R` be a record block
above `fc_root` that the reader wrote itself at cut `q < j`, as a result or optimistic selection
of a label `s < rO` (`rO = r + k − 1`), and kept since. Every vote of a node honest at it, at a
time `≤ t`, of the latest view's slot `L` at `t`, extends `R`.

The record cover at the earlier read point `t' = t_L − Δ ≥ t₁` (`healed_record_cover_at`), where
the record is still `R` and held, puts `R` below `Σ.F`, which is excluded, or below a member of
label `≥ rO` written by `t'`, so of label `< L`; the honest votes of slot `L` extend that member
(`SeededInvariant.vote_extends`). -/
theorem seeded_stale_record_votes_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {r : Nat} {t₁ b : Time}
    (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    {y : Fin sp.n} {j : Nat} {t : Time} (hrp : Regimes.ReadPoint tr j t)
    (hdt₁ : sp.ts (r + sp.k : Nat) ≤ t₁) (ht₁ : t₁ + 8 * sp.Δ ≤ t) (htb : t ≤ b) (hy : y ∈ H t)
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed = some R)
    (hRf : ¬ (Node.frame (tr.state y j)).Anc R (Node.frame (tr.state y j)).fcRoot)
    {q s : Nat} {CV : Set (Vote sp.n)} (hRq : R ∈ (tr.state y q).fg.tree)
    (hrest : ∀ m, q < m → m ≤ j → (tr.state y m).ac.latestConfirmed = R.root)
    (hC : SA.ResultAt tr.projAC y q s R CV ∨ SA.OptimisticLockAt tr.projAC y q s R CV)
    (hs : s < r + sp.k - 1) {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y j).ac (Node.frame (tr.state y j)) t).2) :
    ∀ z q' e, HVoteAt tr H z q' e → tr.time q' ≤ t → e.msg.slot = L →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg R := by
  classical
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have h0₁ : (0 : Time) ≤ t₁ := (ts_natCast_nonneg _).trans hdt₁
  have ht0 : (0 : Time) ≤ t := by linarith
  have hU := honestBlocksAt_coherent hrun hnc
  have hRm := (SA.lookup_eq_some hR).1
  have hΦ : FrameOK (Node.frame (tr.state y j)) := by
    have h := Compose.frameOK_state (hrun.upTo ht0).toLocalRun hy j
    rwa [Trace.upTo_state tr y hrp.1] at h
  have hΦU : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, j, t, ht0, hrp.1, hy, hX.1⟩
  -- the latest view's slot and the earlier read time `t' = t_L − Δ`
  have hslot : r + sp.k + 2 ≤ sp.slot t := by
    have h8 : sp.ts ((r + sp.k + 2 : Nat) : Int) ≤ t := by
      have : sp.ts ((r + sp.k + 2 : Nat) : Int) = sp.ts ((r + sp.k : Nat) : Int) + 8 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    have := (SA.ts_le_iff_le_slot sp ht0 _).1 h8
    omega
  obtain ⟨L', hL', -, hLt, hL6⟩ :=
    latest_label_at (A := (tr.state y j).ac) (Φ := Node.frame (tr.state y j)) ht0 (by omega)
  have hLL : L' = L := by exact_mod_cast hL'.trans hL.symm
  rw [hLL] at hLt hL6
  set t' := sp.ts L - sp.Δ with ht'
  have ht₁' : t₁ ≤ t' := by linarith
  have ht't : t' ≤ t := by linarith
  have ht'0 : (0 : Time) ≤ t' := h0₁.trans ht₁'
  have hyt' : y ∈ H t' := hrun.antitone ht't hy
  -- the record was written before `t'`
  have hqt' : tr.time q < t' := by
    have hrk : sp.ts ((r + sp.k : Nat) : Int) + 8 * sp.Δ ≤ sp.ts L + 6 * sp.Δ := by linarith
    have hhi := (origin_time_bounds (hrun.time_nonneg q) hC).2
    have hle := (SA.ts_le_iff sp).2 (show ((s + 2 : Nat) : Int) ≤ ((r + sp.k : Nat) : Int) by
      omega)
    rw [ht']
    simp only [SAParams.ts] at hle hrk hhi ⊢
    push_cast at hle hrk hhi ⊢
    linarith
  -- the read point at `t'`
  have hex : ∃ k, t' ≤ tr.time k := ⟨j, ht't.trans hrp.2⟩
  set n := Nat.find hex with hn
  have hrp' : Regimes.ReadPoint tr n t' :=
    ⟨fun k hk => le_of_lt (not_le.1 (Nat.find_min hex hk)), Nat.find_spec hex⟩
  have hnj : n ≤ j := Nat.find_min' hex (ht't.trans hrp.2)
  have hqn : q < n := by
    by_contra h
    exact absurd ((Nat.find_spec hex).trans (hrun.time_mono (Nat.le_of_not_lt h))) (not_le.2 hqt')
  have hrd : ∀ k < n, tr.time k ≤ t := fun k hk => (hrp'.1 k hk).trans ht't
  have hRn : R ∈ (Node.frame (tr.state y n)).tree :=
    Obligations.Growing.writer_mem_frame_between_at hrun hnc ht0 hrp.1 hy hqn.le hnj hRq hRm
  have hΦn : FrameOK (Node.frame (tr.state y n)) := by
    have h := Compose.frameOK_state (hrun.upTo ht0).toLocalRun hy n
    rwa [Trace.upTo_state tr y hrd] at h
  have hRl : SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed = some R := by
    rw [hrest n hqn hnj]
    exact SA.lookup_of_mem hΦn hRn
  have hcov := healed_record_cover_at hinv ht₁' (ht't.trans htb) hyt' hrp'
  rw [hRl, Option.getD_some] at hcov
  rcases healedRecordCoverAt_iff.1 hcov with hRF | ⟨x, q₀, s₀, C, DV, hx, -, hq₀t, hs₀, hC₀, hRC⟩
  · -- `R = Σ.F` at `n` is below `Σ.F` at `j`
    exfalso
    apply hRf
    have hFF := F_mono_at hrun ht0 hy hrp.1 hnj
    rw [← hRF] at hFF
    exact (SA.anc_tree_of_anc_U hU hΦ hΦU hRm hFF hΦ.rooted.1).trans hΦ.F_anc_fcRoot
  -- the member's label is below `L`
  have hs₀L : s₀ < L := by
    have hlo := (origin_time_bounds (hrun.time_nonneg q₀) hC₀).1
    exact_mod_cast (SA.ts_lt_iff sp).1 (by linarith : sp.ts s₀ < sp.ts L)
  have hmem : HealedOrigin tr H g r (r + sp.k - 1) C s₀ b := HealedOrigin.of_origin hs₀
    (originWithin_iff.2 ⟨x, q₀, DV, hx, (hq₀t.trans ht't).trans htb, hC₀⟩)
  intro z q' e hv hq't hes
  obtain ⟨Hd, hHd, hHdr, hCHd⟩ :=
    hinv.vote_extends C s₀ hmem z q' e hv (hq't.trans htb) (by omega)
  exact ⟨Hd, hHd, hHdr, hRC.trans hCHd⟩

/-- **A ready read is the effective record after a hand-over.** At a read point `(j, t)` with
`t ∈ [t₁ + 8Δ, b]`, `t₁ ≥ t_{r+k}`, of a node ready at `t`, the confirmed read is the block named
by the record when the frame holds it, else `Σ.F`.

The latest view at `t` is a label `L ≥ r + k − 1` with `t_L + Δ ≤ t < t_L + 6Δ`; the reset's
windows from `ḡ` and the slot fault bound give the head certificate
(`read_eq_record_of_current_votes_at`). The live lock blocks and the record's block are on the
healed chain (`SeededInvariant.locks`, `effective_record_on_healed_chain_at`), so the live locks
form a chain and every live candidate is compatible with the record. The record's block `R`, not
at or below `fc_root` and not genesis (which is below `Σ.F`), has a last writer, the reader itself
(`last_record_writer_at`):
* a result, or an optimistic selection of a slot below `L`, of label `≥ rO`: a member of the
  family, viable (`SeededInvariant.viable`) and extended by the later honest votes
  (`SeededInvariant.vote_extends`);
* an optimistic selection of a slot `≥ L`: its fast lock, of expiry at least its slot plus two,
  is kept to the read, since every call in between is at most one slot later and holds `R` as a
  candidate, so `R` is a live lock block, below the anchor;
* a label `< rO`: `seeded_stale_record_viable_at`, `seeded_stale_record_votes_at`. -/
theorem seeded_ready_read_record_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    {y : Fin sp.n} {j : Nat} {t : Time} (hrp : Regimes.ReadPoint tr j t)
    (hdt₁ : sp.ts (r + sp.k : Nat) ≤ t₁) (ht₁₈ : t₁ + 8 * sp.Δ ≤ t) (htb : t ≤ b)
    (hready : Regimes.Growing.ReadyAt tr H (Regimes.catchUp sp) y t) :
    Regimes.readAfter tr y j t =
      (SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
        (tr.state y j).fg.F := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have ht₁ : t₁ ≤ t := by linarith
  have hdt : sp.ts (r + sp.k : Nat) ≤ t := hdt₁.trans ht₁
  have hy := hready.1
  have ht0 : (0 : Time) ≤ t := (ts_natCast_nonneg _).trans hdt
  have hslot : r + sp.k + 2 ≤ sp.slot t := by
    have h8 : sp.ts ((r + sp.k + 2 : Nat) : Int) ≤ t := by
      have : sp.ts ((r + sp.k + 2 : Nat) : Int) = sp.ts ((r + sp.k : Nat) : Int) + 8 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    have := (SA.ts_le_iff_le_slot sp ht0 _).1 h8
    omega
  have hcallj := seeded_reader_called_at hrun hseed hready.1 hdt hrp.2
  obtain ⟨L, hL, hLs, hLt, hL6⟩ :=
    latest_label_at (A := (tr.state y j).ac) (Φ := Node.frame (tr.state y j)) ht0 (by omega)
  have hrL : r ≤ L := by omega
  have hga : SA.gbar g ≤ sp.ts L := by
    have h1 := hseed.timing.2.2
    have h2 : sp.ts (r : Nat) ≤ sp.ts L := (SA.ts_le_iff sp).2 (by exact_mod_cast hrL)
    linarith
  obtain ⟨hw, hj⟩ : tr.awake y t ∧ tr.JoinedAt y t := by
    obtain ⟨hw, hj⟩ := Compose.ready_implies_joined _ _ _ _ _ _ (hrun.upTo ht0) y hy t
      (Regimes.catchUp sp) ht0 (by rw [catchUp_eq]; linarith)
      fun u h1 h2 => ⟨hready.2 u h1 h2, h2⟩
    exact ⟨hw.1, fun k hk hkt => hj k ((RunTrace.upTo_restartAt tr).2 ⟨hkt, hk⟩) hkt⟩
  have hsync := Healing.Growing.sync_window_at_reset_at hrun hsvc (SA.le_gbar g) ht0
  have hcatch := Healing.Growing.catch_window_at_gbar_at hrun hseed.catchRun ht0
  have hfault := hB.slot L t hrL hLt htb hL6.le
  have hU := honestBlocksAt_coherent hrun hnc
  have hrd : ∀ m ≤ j, ∀ k < m, tr.time k ≤ t := fun m hm k hk => hrp.1 k (by omega)
  have hst : ∀ m ≤ j, (tr.upTo t).state y m = tr.state y m :=
    fun m hm => Trace.upTo_state tr y (hrd m hm)
  have hΦm : ∀ m ≤ j, FrameOK (Node.frame (tr.state y m)) := fun m hm => by
    have h := Compose.frameOK_state (hrun.upTo ht0).toLocalRun hy m
    rwa [hst m hm] at h
  have hΦ := hΦm j le_rfl
  have hΦU : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, j, t, ht0, hrp.1, hy, hX.1⟩
  have hcompΦ : ∀ X Y, X ∈ (Node.frame (tr.state y j)).tree →
      Y ∈ (Node.frame (tr.state y j)).tree → OnHealedChain tr H g r (r + sp.k - 1) X b →
      OnHealedChain tr H g r (r + sp.k - 1) Y b →
      Compatible (Node.frame (tr.state y j)).tree X Y := fun X Y hX hY hXc hYc =>
    (OnHealedChain.compatible_chain hrun hnc hinv.origins_compatible hXc hYc).imp
      (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hX h hY)
      (fun h => SA.anc_tree_of_anc_U hU hΦ hΦU hY h hX)
  have hlocks := hinv.locks y j t ht₁ hrp.1 htb hy
  have hlive : ∀ X ∈ SA.liveLockBlocks sp (tr.state y j).ac.locks (Node.frame (tr.state y j)) t,
      ∀ Y ∈ SA.liveLockBlocks sp (tr.state y j).ac.locks (Node.frame (tr.state y j)) t,
      Compatible (Node.frame (tr.state y j)).tree X Y := fun X hX Y hY =>
    hcompΦ X Y hX.1 hY.1 (hlocks X hX) (hlocks Y hY)
  have hanc := SA.anc_getAnchor hΦ hlive
  refine Obligations.Growing.read_eq_record_of_current_votes_at hrun hnc ht0 hy hrp hw hj hsync
    hcatch hL hga (fun R hR => ?_) hLt hfault
  obtain ⟨hRm, -⟩ := SA.lookup_eq_some hR
  have hRc : OnHealedChain tr H g r (r + sp.k - 1) R b := by
    have h := effective_record_on_healed_chain_at hinv ht₁ htb hy hrp hcallj
    rwa [hR, Option.getD_some] at h
  have hsrc : (Node.frame (tr.state y j)).Anc R
        (SA.getAnchor sp (tr.state y j).ac (Node.frame (tr.state y j)) t) ∨
      (R ∈ (Node.frame (tr.state y j)).viableTree (Node.frame (tr.state y j)).tree ∧
        ∀ z q e, HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg R) := by
    by_cases hRf : (Node.frame (tr.state y j)).Anc R (Node.frame (tr.state y j)).fcRoot
    · exact Or.inl (hRf.trans (hanc.2 _ (Or.inr rfl)))
    by_cases hgen : R.root = sp.genesisRoot
    · -- genesis is below `Σ.F`
      exfalso
      apply hRf
      have htree := Store.accepted_tree _ _ _ _
        (Healing.Growing.fg_reachable_at hrun ht0 hrp.1 hy)
      have heq : R = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
        htree.2.1.1 hRm.1 htree.2.2.1 hgen
      have hRF : Anc (tr.HonestBlocksAt H) R (tr.state y j).fg.F := by
        rw [heq]
        exact (htree.2.2.2 _ hΦ.rooted.1.1).mono fun X hX => ⟨y, j, t, ht0, hrp.1, hy, hX⟩
      exact (SA.anc_tree_of_anc_U hU hΦ hΦU hRm hRF hΦ.rooted.1).trans hΦ.F_anc_fcRoot
    obtain ⟨q, hqj, ell, hcall, hRq, hrest, hwriter⟩ :=
      Obligations.Growing.last_record_writer_at hrun hnc ht0 hrp.1 hy hR hgen
    have hqt : tr.time q ≤ t := hrp.1 q hqj
    have hyq : y ∈ H (tr.time q) := hrun.antitone hqt hy
    have hRqfg : R ∈ (tr.state y q).fg.tree :=
      (Compose.Growing.frame_of_projAC_at hrun hyq hcall ▸ hRq).1
    -- a writer of a label below `L`
    have hold : ∀ s CV, (SA.ResultAt tr.projAC y q s R CV ∨
        SA.OptimisticLockAt tr.projAC y q s R CV) → (s : Int) < L →
        R ∈ (Node.frame (tr.state y j)).viableTree (Node.frame (tr.state y j)).tree ∧
          ∀ z q e, HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
            SA.VoteExtends (tr.HonestBlocksAt H) e.msg R := by
      intro s CV hC hsL
      by_cases hs : r + sp.k - 1 ≤ s
      · have hmem : HealedOrigin tr H g r (r + sp.k - 1) R s b :=
          HealedOrigin.of_origin hs (originWithin_iff.2 ⟨y, q, CV, hyq, hqt.trans htb, hC⟩)
        exact ⟨(hinv.viable y j t ht₁ hrp.1 htb hy hcallj R
          (onHealedChain_iff.2 ⟨R, s, hmem, .refl⟩) hRm).resolve_left hRf,
          fun z q' e hv hq't hes => hinv.vote_extends R s hmem z q' e hv (hq't.trans htb)
            (by omega)⟩
      · exact ⟨seeded_stale_record_viable_at hrun hseed hinv hrp ht₁ htb hdt hy hR hRf,
          seeded_stale_record_votes_at hrun hnc hinv hrp hdt₁ ht₁₈ htb hy hR hRf hRqfg hrest
            hC (by omega) hL⟩
    rcases hwriter with ⟨s, CV, hres⟩ | ⟨⟨CV, hop⟩, hlock⟩
    · obtain ⟨-, ⟨-, -, htime, -⟩, -⟩ := id hres
      have hlt := Obligations.result_label_lt_latest_of_time ht0
        ((show tr.time q = sp.ts s + 6 * sp.Δ from htime) ▸ hqt)
        (A := (tr.state y j).ac) (Φ := Node.frame (tr.state y j))
      exact Or.inr (hold s CV (Or.inl hres) (hL ▸ hlt))
    by_cases hsL : ((sp.slot (tr.time q) : Nat) : Int) < L
    · exact Or.inr (hold _ CV (Or.inr hop) hsL)
    -- an optimistic selection of a slot `≥ L`: its fast lock is still stored and live
    left
    set s := sp.slot (tr.time q) with hsdef
    have hs : r + sp.k - 1 ≤ s := by omega
    have hmem : HealedOrigin tr H g r (r + sp.k - 1) R s b :=
      HealedOrigin.of_origin hs (originWithin_iff.2 ⟨y, q, CV, hyq, hqt.trans htb, Or.inr hop⟩)
    have hframe : ∀ m, q ≤ m → m ≤ j → R ∈ (Node.frame (tr.state y m)).tree :=
      fun m hqm hmj => Obligations.Growing.writer_mem_frame_between_at hrun hnc ht0 hrp.1 hy
        hqm hmj hRqfg hRm
    have hqs : sp.ts ((r + sp.k : Nat) : Int) ≤ tr.time q :=
      ((SA.ts_le_iff sp).2 (by omega)).trans
        ((SA.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).2 le_rfl)
    have hcand : ∀ m, q ≤ m → m ≤ j → (Node.frame (tr.state y m)).AncestorCandidate R := by
      intro m hqm hmj
      have hcm : ∃ c < m, ∃ ell : ACLabel (goldilocksNode sp ro), tr.projAC.CallAt y c ell ∧
          sp.ts (r - sp.k - 3 : Nat) ≤ tr.time c := by
        rcases hmj.lt_or_eq with hmj' | rfl
        · exact seeded_reader_called_at hrun hseed (hrun.antitone (hrp.1 m hmj') hy)
            (hqs.trans (hrun.time_mono hqm)) le_rfl
        · exact hcallj
      exact hinv.viable y m t ht₁ (hrd m hmj) htb hy hcm R
        (onHealedChain_iff.2 ⟨R, s, hmem, .refl⟩) (hframe m hqm hmj)
    have hnorm : ∀ m, q ≤ m → m ≤ j → (Node.frame (tr.state y m)).viableAncestor R = R :=
      fun m hqm hmj => SA.viableAncestor_self (hΦm m hmj) (hframe m hqm hmj)
        (hcand m hqm hmj).symm
    rw [Compose.Growing.frame_of_projAC_at hrun hyq hcall, hnorm q le_rfl hqj.le] at hlock
    obtain ⟨e, hlock⟩ := hlock
    have hwf : SA.LocksWF sp (tr.state y (q + 1)).ac.locks := by
      have h := Compose.locksWF_state (hrun.upTo ht0) (hnc.upTo t) hy (q + 1)
      rwa [hst (q + 1) hqj] at h
    have he : s + 2 ≤ e := hwf.floor hlock
    have hslj : ∀ m < j, sp.slot (tr.time m) ≤ sp.slot t :=
      fun m hm => SA.slot_mono sp (hrun.time_nonneg m) (hrp.1 m hm)
    have hl : (⟨R.root, s, true, e⟩ : SA.Lock) ∈ (tr.state y j).ac.locks := by
      have h := Compose.lock_keep_interval_view (hrun.upTo ht0) hy hqj
        (by rw [hst (q + 1) hqj]; exact hlock) (B := R) rfl fun m hqm hmj => by
          rw [hst m hmj.le]
          refine ⟨?_, hframe m (by omega) hmj.le, hnorm m (by omega) hmj.le, fun _ _ => ?_⟩
          · change sp.slot (tr.time m) ≤ e
            have := hslj m hmj
            omega
          · left
            have := hslj m hmj
            change ((sp.slot (tr.time m) : Nat) : Int) - 1 ≤ ((s : Nat) : Int)
            omega
      rwa [hst j le_rfl] at h
    refine Obligations.record_below_anchor_of_stored_live_lock hΦ hl hRm rfl ?_ ?_ hlive
    · change sp.slot t ≤ e
      omega
    · rw [hnorm j hqj.le le_rfl]
      exact .refl
  refine ⟨?_, hsrc⟩
  rintro X (hX | hX)
  · exact hcompΦ X R hX.1 hRm (hlocks X hX) hRc
  · rw [Set.mem_singleton_iff.1 hX]
    rcases hsrc with h | ⟨hv, -⟩
    · have hfc := hanc.2 _ (Or.inr rfl)
      exact (Anc.total hU (hfc.mono hΦU) (h.mono hΦU)).imp
        (fun h' => SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem h' hRm)
        (fun h' => SA.anc_tree_of_anc_U hU hΦ hΦU hRm h' hΦ.fcRoot_mem)
    · exact Or.inl hv.2.1

/-- Readiness with a longer catch-up implies readiness with a shorter one. -/
private theorem readyAt_of_le {c c' : Time} (hcc : c' ≤ c) {y : Fin sp.n} {t : Time}
    (h : Regimes.Growing.ReadyAt tr H c y t) : Regimes.Growing.ReadyAt tr H c' y t :=
  ⟨h.1, fun τ hτ hτt => h.2 τ (le_trans (max_le_max le_rfl (by linarith)) hτ) hτt⟩

/-- **Ready-reader safety after a hand-over** from `t₀` through `b ≥ T`, for a catch-up
`c ≥ catchUp`: from the seeded invariant from `t₁ ≥ t_{r+k}`, with `t₀ ≥ t₁ + 8Δ`.
A ready read is the effective record (`seeded_ready_read_record_at`); two effective records are
compatible (`seeded_records_compatible_at`), and one reader's only extends
(`seeded_effective_record_mono_at`). -/
theorem continued_safe_on_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {T : Time} {r σ : Nat}
    (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ t₀ b : Time}
    (hsvc : Healing.Growing.ResetService tr H g ΔF b) (hB : SleepyBoundsFrom tr H r b)
    (hinv : SeededInvariant tr H g r (r + sp.k - 1) t₁ b)
    (hdt₁ : sp.ts (r + sp.k : Nat) ≤ t₁) (ht₁₈ : t₁ + 8 * sp.Δ ≤ t₀) {c : Time}
    (hc : Regimes.catchUp sp ≤ c) :
    Regimes.Growing.ReadySafeOn tr H c t₀ b := by
  have ht₁ : t₁ ≤ t₀ := by linarith [sp.toParams.hΔ]
  have hdt' : sp.ts (r + sp.k - 1 + 1 : Nat) ≤ t₀ := by
    have hk := sp.two_le_k
    rw [show r + sp.k - 1 + 1 = r + sp.k by omega]
    exact hdt₁.trans ht₁
  have hread : ∀ {y j t}, Regimes.ReadPoint tr j t → t₀ ≤ t → t ≤ b →
      Regimes.Growing.ReadyAt tr H c y t → Regimes.readAfter tr y j t =
        (SA.lookup (Node.frame (tr.state y j)) (tr.state y j).ac.latestConfirmed).getD
          (tr.state y j).fg.F := fun hrp ht htb hready =>
    seeded_ready_read_record_at hrun hnc hseed hsvc hB hinv hrp hdt₁ (ht₁₈.trans ht) htb
      (readyAt_of_le hc hready)
  refine ⟨fun y z i j t t' hi hj _ _ ht htb ht' htb' hy hz => ?_,
    fun y i j t t' hi hj _ _ hij htt ht htb hy hy' => ?_⟩
  · rw [hread hi ht htb hy, hread hj ht' htb' hz]
    exact seeded_records_compatible_at hrun hnc hinv (ht₁.trans ht) htb hy.1 hi
      (seeded_reader_called_at hrun hseed hy.1 (hdt₁.trans (ht₁.trans ht)) hi.2)
      (ht₁.trans ht') htb' hz.1 hj
      (seeded_reader_called_at hrun hseed hz.1 (hdt₁.trans (ht₁.trans ht')) hj.2)
  · rw [hread hi ht (htt.trans htb) hy, hread hj (ht.trans htt) htb hy']
    exact seeded_effective_record_mono_at hrun hnc hinv ht₁ hdt' hi hj hij htt ht htb hy.1 hy'.1
      (seeded_reader_called_at hrun hseed hy.1 (hdt₁.trans (ht₁.trans ht)) hi.2)

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

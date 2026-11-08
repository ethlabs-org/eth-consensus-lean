module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The record cover past the hand-over

The hand-over seed covers the record of every reader honest at a read point up to `T`: it is the
reader's finalized block, or below a result or optimistic selection of label `≥ r + k − 1` by a
node honest at its cut, written before the read. Past `T` the cover carries over cut by cut from
the read point at `T`:

* a step that keeps the record's root keeps the looked-up block (`record_lookup_of_later_at`).
  A block below an origin stays below it. A block equal to the old finalized block is still in
  the frame, hence above the new finalized block, which is above the old one; so it is the new
  finalized block;
* a step that writes a new root writes the root of a result or optimistic selection of the
  reader at that cut (`record_step_origin_at`), at a time `≥ T ≥ t_σ + 8Δ`. A result of label `s`
  is written at `t_s + 6Δ`, and an optimistic selection of label `s` in slot `s`, so `s ≥ σ`, and
  `σ ≥ r + k − 1` by the seed's timing.

* `Compose.Growing.seeded_record_cover_at`: the record cover from `t₁` through `b`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF : Time}

/-- **The record cover from `t₁` through `b`**. From the cover up to `T`, the record of a reader
honest at a read point `t ∈ [t₁, b]` is its `Σ.F` or below an origin of label `≥ r + k − 1`
written before the read. Past `T` the cover runs over the reader's cuts from the read point at
`T` (the seed's own cover): a kept root keeps the block or follows `Σ.F`, and a new root is the
reader's own result or selection, of label `≥ σ` after `T`. The service, the counts, conviction
and the drain are not read: the argument is the reader's own record steps. -/
theorem seeded_record_cover_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {T : Time} {r σ : Nat} (hseed : HandoverSeed tr H proposer dg g ΔF T r σ) {t₁ b : Time}
    (_hTb : T ≤ b) (_hsvc : Healing.Growing.ResetService tr H g ΔF b)
    (_hB : SleepyBoundsFrom tr H r b) (_hcv : ChainConvictedBelow tr H)
    (_hdt : sp.ts (r + sp.k : Nat) ≤ t₁)
    (hcov : ∀ y n t, t₁ ≤ t → t ≤ T → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F)) :
    ∀ y n t, t₁ ≤ t → t ≤ b → y ∈ H t → Regimes.ReadPoint tr n t →
      HealedRecordCoverAt tr H (r + sp.k - 1) y n t
        ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
          (tr.state y n).fg.F) := by
  intro y n t ht₁ _ hy hrp
  rcases le_or_gt t T with htT | hTt
  · exact hcov y n t ht₁ htT hy hrp
  obtain ⟨tc, htcT, hcovT⟩ := hseed.covered
  obtain ⟨hσT, hrσ, -⟩ := hseed.timing
  have hΔ := sp.toParams.hΔ
  have hU := honestBlocksAt_coherent hrun hnc
  have hT0 : 0 ≤ T := by linarith [ts_natCast_nonneg (sp := sp) σ]
  have ht0 : 0 ≤ t := hT0.trans hTt.le
  -- the read point at `T`: the first cut at a time `≥ T`
  classical
  have hex : ∃ k, T ≤ tr.time k := ⟨n, hTt.le.trans hrp.2⟩
  have hn₀n : Nat.find hex ≤ n := Nat.find_min' hex (hTt.le.trans hrp.2)
  have hrp₀ : Regimes.ReadPoint tr (Nat.find hex) T :=
    ⟨fun k hk => (not_le.1 (Nat.find_min hex hk)).le, Nat.find_spec hex⟩
  have hyT : y ∈ H T := hrun.antitone hTt.le hy
  -- the reader's results and selections from there on have labels `≥ σ ≥ r + k − 1`
  have hlab : ∀ k, Nat.find hex ≤ k → ∀ s C CV, SA.ResultAt tr.projAC y k s C CV ∨
      SA.OptimisticLockAt tr.projAC y k s C CV → r + sp.k - 1 ≤ s := by
    intro k hk s C CV hs
    have htk : T ≤ tr.time k := (Nat.find_spec hex).trans (hrun.time_mono hk)
    have hσs : σ ≤ s := by
      rcases hs with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
      · have ht : tr.time k = sp.ts s + 6 * sp.Δ := hu.2.2.1
        have hh := (SA.ts_le_iff sp).mp (show sp.ts σ ≤ sp.ts s by linarith)
        omega
      · have hh := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) σ).mp (by linarith)
        change sp.slot (tr.time k) = s at hslot
        omega
    omega
  have hind : ∀ k, Nat.find hex ≤ k → k ≤ n → ∀ R,
      SA.lookup (Node.frame (tr.state y k)) (tr.state y k).ac.latestConfirmed = some R →
      R = (tr.state y k).fg.F ∨ ∃ x q s C CV, x ∈ H (tr.time q) ∧ q < k ∧ tr.time q ≤ t ∧
        r + sp.k - 1 ≤ s ∧
        (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
        Anc (tr.HonestBlocksAt H) R C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _ R hR
      have h := hcovT y _ T htcT le_rfl hyT hrp₀
      rw [hR, Option.getD_some, healedRecordCoverAt_iff] at h
      rcases h with h | ⟨x, q, s, C, CV, hx, hq, hqT, hs, hC, hRC⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, q, s, C, CV, hx, hq, hqT.trans hTt.le, hs, hC, hRC⟩
    | succ k hk ih =>
      intro hkn R hR
      have hle1 : ∀ q < k + 1, tr.time q ≤ t := fun q hq => hrp.1 q (by omega)
      have hle0 : ∀ q < k, tr.time q ≤ t := fun q hq => hrp.1 q (by omega)
      have hkt : tr.time k ≤ t := hrp.1 k (by omega)
      have hyk : y ∈ H (tr.time k) := hrun.antitone hkt hy
      rcases Obligations.Growing.record_step_origin_at hrun hyk with heq | ⟨C, hC, hCr, s, CV, hs⟩
      · have hRk := Obligations.Growing.record_lookup_of_later_at hrun hnc ht0 hle1 hy
          (Nat.le_succ k) heq hR
        rcases ih (by omega) R hRk with hRF | ⟨x, q, s, B, DV, hx, hqk, hqt, hsl, hB, hRB⟩
        · obtain ⟨hRm, -⟩ := SA.lookup_eq_some hR
          have h₁ : Anc (tr.HonestBlocksAt H) (tr.state y (k + 1)).fg.F R :=
            (show Anc (tr.state y (k + 1)).fg.tree _ _ from hRm.2).mono
              (tree_subset_at ht0 hle1 hy)
          have h₂ : Anc (tr.HonestBlocksAt H) R (tr.state y (k + 1)).fg.F := by
            rw [hRF]
            exact F_mono_at hrun ht0 hy hle1 (Nat.le_succ k)
          exact Or.inl (Anc.antisymm hU h₂ h₁)
        · exact Or.inr ⟨x, q, s, B, DV, hx, Nat.lt_succ_of_lt hqk, hqt, hsl, hB, hRB⟩
      · obtain ⟨hRm, hRr⟩ := SA.lookup_eq_some hR
        obtain rfl : R = C := hU.1 ⟨y, k + 1, t, ht0, hle1, hy, hRm.1⟩
          ⟨y, k, t, ht0, hle0, hy, hC⟩ (hRr.trans hCr.symm)
        exact Or.inr ⟨y, k, s, R, CV, hyk, Nat.lt_succ_self _, hkt, hlab k hk s R CV hs, hs,
          .refl⟩
  rw [healedRecordCoverAt_iff]
  cases hl : SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed with
  | none => exact Or.inl (by simp only [Option.getD_none])
  | some R =>
    rcases hind n hn₀n le_rfl R hl with h | ⟨x, q, s, C, CV, hx, hqn, hqt, hs, hC, hRC⟩
    · exact Or.inl (by simpa only [Option.getD_some] using h)
    · exact Or.inr ⟨x, q, s, C, CV, hx, hqn, hqt, hs, hC,
        by simpa only [Option.getD_some] using hRC⟩

end Consensus.Goldilocks.Compose.Growing

end

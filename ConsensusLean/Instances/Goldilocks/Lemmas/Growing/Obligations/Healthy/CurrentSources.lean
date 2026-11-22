module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FinalizedSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalReplay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The current-record sources under growing faults

The record geometry of healed safety for a healed-safety query, with
every reader honest at its read time and every source writer honest at its own cut:

* `healthy_current_sources_compatible_at`: two record covers (`RecordCover`) of readers
  honest at their read points compare;
* `healthy_current_record_interval_at`: after the repair window, a reader's results and
  optimistic selections over an interval of cuts, and its floors after them, compare with its
  record at the start of the interval (the current-record cover at the start, from
  `record_sources_before_now_at`), so the interval contract holds.

Finalized blocks compare by FG finalized safety at the later read time; a finalized block and a
clean source, and two clean sources, by the clean-source comparisons
(`finalized_compatible_clean_source_at`, `clean_sources_compatible_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The fault bound of the reset schedule is below the FG quorum excess at every time up to the
query's bound. -/
private theorem faults_lt_excess (D : RepairSchedule tr H proposer dg g b cm βK) {t : Time}
    (ht : 0 ≤ t) (htb : t ≤ b) :
    (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
  have h := D.reset.faults t ht htb
  have hn := sp.toParams.hn
  change 3 * (H t)ᶜ.ncard ≤ sp.toParams.n - 1 at h
  change (H t)ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.toParams.n
  clear * - h hn
  omega

/-- **Finalized safety at two read points**: the finalized blocks of two readers, each honest at
its read time, compare, with the certificate intersection charged at the later read time. -/
private theorem finalized_safe_read (D : RepairSchedule tr H proposer dg g b cm βK)
    {y z : Fin sp.n} {n n' : Nat} {t t' : Time} (ht : 0 ≤ t)
    (hrp : Regimes.ReadPoint tr n t) (htb : t ≤ b) (hy : y ∈ H t) (ht' : 0 ≤ t')
    (hrp' : Regimes.ReadPoint tr n' t') (ht'b : t' ≤ b)
    (hz : z ∈ H t') :
    Goldilocks.Compatible (tr.HonestBlocksAt H)
      (tr.state y n).fg.F (tr.state z n').fg.F := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have fg : Consensus.Goldilocks.Growing.FGLocalRun
      (goldilocksNode sp ro).genesisPayload H
      (tr.HonestBlocksAt H) tr.projFG :=
    Compose.Growing.fg_projection _ _ _ _ _ _ _
      (fun y => Compose.requirements_from _ _ (hrun.vstart y))
      hrun.genesis_root_ok hrun.toLocalRun hnc
  have store_eq : ∀ {x : Fin sp.n} {m : Nat} {s : Time}, 0 ≤ s →
      (∀ k < m, tr.time k ≤ s) → x ∈ H s →
      tr.projFG.store x m = (tr.state x m).fg := by
    intro x m s hs hle hx
    have h := Compose.projFG_state (hrun.toLocalRun.upTo hs) hx m
    rw [RunTrace.upTo_projFG, Trace.upTo_state tr.projFG x hle,
      Trace.upTo_state tr x hle] at h
    exact congrArg Prod.fst h
  -- certificate intersection at `max t t'`
  have hf := faults_lt_excess D (le_max_of_le_left ht) (max_le htb ht'b)
  rw [← store_eq ht hrp.1 hy, ← store_eq ht' hrp'.1 hz]
  by_contra hne
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, ha₁⟩ := fg.finalized_chain_upTo_at ht hrp.1 hy
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, ha₂⟩ := fg.finalized_chain_upTo_at ht' hrp'.1 hz
  obtain ⟨Sv, hS, hSv⟩ := FG.accountable_safety sp.toParams.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ Sv, v ∈ H (max t t') := by
    by_contra! hS'
    have hcard := Set.ncard_le_ncard
      (s := (Sv : Set (Fin sp.toParams.fg.n))) (t := (H (max t t'))ᶜ) hS'
    rw [Set.ncard_coe_finset] at hcard
    have : ((H (max t t'))ᶜ : Set (Fin sp.toParams.fg.n)).ncard =
        ((H (max t t'))ᶜ : Set (Fin sp.n)).ncard := rfl
    have : sp.toParams.fg.n = sp.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  have signs : ∀ x ∈ sp.toParams.fg.chainAtts c₁ ++ sp.toParams.fg.chainAtts c₂,
      x.val = a.val → ∃ k, tr.time k ≤ max t t' ∧ tr.projFG.SignAt a.val k x := by
    intro x hx hxv
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, hk, hs⟩ := ha₁ x hx (hxv ▸ fg.antitone (le_max_left _ _) hv)
      exact ⟨k, (hrp.1 k hk).trans (le_max_left _ _), hxv ▸ hs⟩
    · obtain ⟨k, hk, hs⟩ := ha₂ x hx (hxv ▸ fg.antitone (le_max_right _ _) hv)
      exact ⟨k, (hrp'.1 k hk).trans (le_max_right _ _), hxv ▸ hs⟩
  obtain ⟨k, hk, hka⟩ := signs a ha rfl
  obtain ⟨l, hl, hlb⟩ := signs b hb hab.1.symm
  exact fg.non_framing hka hlb (fg.antitone (max_le hk hl) hv) hab

/-- A finalized block of a reader honest at its read point compares with a clean source of a
writer honest at its write. -/
private theorem finalized_compatible_source (D : RepairSchedule tr H proposer dg g b cm βK)
    {y : Fin sp.n} {n : Nat} {t : Time} (ht : 0 ≤ t) (hrp : Regimes.ReadPoint tr n t)
    (htb : t ≤ b) (hy : y ∈ H t) {x : Fin sp.n} {r s : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : D.cleanLabel + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) :
    Goldilocks.Compatible (tr.HonestBlocksAt H) (tr.state y n).fg.F C := by
  exact D.reset.finalized_compatible_clean_source_at hx hC
    (by simpa only [D.cleanLabel_eq] using hs) hrb ht hrp.1 hy htb

/-- **Two record covers compare**: the records of two readers, each honest at its read point,
covered by their finalized blocks or by clean sources of writers honest at their writes, are
compatible in the blocks held while honest. -/
theorem healthy_current_sources_compatible_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {y z : Fin sp.n} {n n' : Nat} {t t' : Time} (ht : 0 ≤ t)
    (hrp : Regimes.ReadPoint tr n t) (htb : t ≤ b) (hy : y ∈ H t) (ht' : 0 ≤ t')
    (hrp' : Regimes.ReadPoint tr n' t') (ht'b : t' ≤ b) (hz : z ∈ H t')
    {R R' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : RecordCover tr H D.cleanLabel y n t R)
    (hR' : RecordCover tr H D.cleanLabel z n' t' R') :
    Goldilocks.Compatible (tr.HonestBlocksAt H) R R' := by
  have hU := Compose.Growing.honest_blocks_coherent D.reset.run D.reset.noColl
  rw [recordCover_iff] at hR hR'
  rcases hR with rfl | ⟨x, r, s, B, CV, hx, -, hrt, hs, hB, hRB⟩
  · rcases hR' with rfl | ⟨x', q, s', E, DV, hx', -, hqt, hs', hE, hRE⟩
    · exact finalized_safe_read D ht hrp htb hy ht' hrp' ht'b hz
    · exact tips_comparable_of_origin_witnesses_at hU .refl hRE
        (finalized_compatible_source D ht hrp htb hy hx' hE hs' (hqt.trans ht'b))
  · rcases hR' with rfl | ⟨x', q, s', E, DV, hx', -, hqt, hs', hE, hRE⟩
    · exact (tips_comparable_of_origin_witnesses_at hU .refl hRB
        (finalized_compatible_source D ht' hrp' ht'b hz hx hB hs (hrt.trans htb))).symm
    · exact tips_comparable_of_origin_witnesses_at hU hRB hRE
        (D.reset.clean_sources_compatible_at hx hx' hB hE
          (by simpa only [D.cleanLabel_eq] using hs)
          (by simpa only [D.cleanLabel_eq] using hs') (hrt.trans htb) (hqt.trans ht'b))

/-- **The current-record interval.** After the repair window, for a reader honest at the later
of two read points, its results and optimistic selections between the two cuts, and its floors
after them, compare with its record at the first read point: the interval contract of that
record holds. -/
theorem healthy_current_record_interval_at (D : RepairSchedule tr H proposer dg g b cm βK)
    (O : RepairOpening D) {y : Fin sp.n} {n n' : Nat} {t t' : Time}
    (hrp : Regimes.ReadPoint tr n t) (hrp' : Regimes.ReadPoint tr n' t')
    (htt : t ≤ t') (ht'b : t' ≤ b) (hy : y ∈ H t')
    (hrep : sp.ts O.slot + 6 * sp.Δ ≤ t) (hcut : sp.ts O.slot + 6 * sp.Δ < tr.time n) :
    EffectiveRecordIntervalAt tr H y n n'
      ((SA.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F) := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have htb : t ≤ b := htt.trans ht'b
  have hyt : y ∈ H t := hrun.antitone htt hy
  have hlo : sp.ts D.oldLabel ≤ sp.ts O.slot :=
    (SA.ts_le_iff sp).mpr (by exact_mod_cast O.old_lt.le)
  have h6 : (0 : Time) ≤ 6 * sp.Δ := mul_nonneg (by norm_num) hΔ.le
  have ht0 : 0 ≤ t := by
    linarith only [Compose.Growing.ts_natCast_nonneg (sp := sp) O.slot, h6, hrep]
  have ht'0 : 0 ≤ t' := ht0.trans htt
  have hcover := record_sources_before_now_at D O hrp hyt hrep hcut
  rw [recordCover_iff] at hcover
  apply effectiveRecordInterval_of_candidates_before_at hrun hnc ht'0 hrp'.1 hy
  · intro q hnq hqn' B s CV hB
    have hqt' : tr.time q ≤ t' := hrp'.1 q hqn'
    have hqb : tr.time q ≤ b := hqt'.trans ht'b
    have hyq : y ∈ H (tr.time q) := hrun.antitone hqt' hy
    have htq : t ≤ tr.time q := hrp.2.trans (hrun.time_mono hnq)
    have hbudget : sp.ts D.oldLabel + 6 * sp.Δ < tr.time q := by
      linarith only [hlo, hcut, hrun.time_mono hnq]
    have hs : D.cleanLabel + 2 * sp.k + 1 ≤ s := by
      apply D.old_bound.trans
      rcases hB with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
      · have htime : tr.time q = sp.ts s + 6 * sp.Δ := hu.2.2.1
        have hlt := (SA.ts_lt_iff sp).mp (show sp.ts D.oldLabel < sp.ts s by
          linarith only [htime, hbudget])
        exact_mod_cast hlt.le
      · have hh := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg q) D.oldLabel).mp
          (show sp.ts D.oldLabel ≤ tr.time q by linarith only [hbudget, hΔ])
        change sp.slot (tr.time q) = s at hslot
        rw [← hslot]
        exact_mod_cast hh
    rcases hcover with hF | ⟨x, r, s', E, DV, hx, -, hrt, hs', hE, hRE⟩
    · rw [hF]
      exact (finalized_compatible_source D ht0 hrp htb hyt hyq hB hs hqb)
    · exact tips_comparable_of_origin_witnesses_at hU hRE .refl
        (D.reset.clean_sources_compatible_at hx hyq hE hB
          (by simpa only [D.cleanLabel_eq] using hs')
          (by simpa only [D.cleanLabel_eq] using hs) (hrt.trans htb) hqb)
  · intro q hnq hqn'
    have hle1 : ∀ k < q + 1, tr.time k ≤ t' := fun k hk => hrp'.1 k (by omega)
    rcases hcover with hF | ⟨x, r, s', E, DV, hx, -, hrt, hs', hE, hRE⟩
    · rw [hF]
      -- the reader's own finalized block only moves to descendants on the prefix through `t'`
      exact Or.inr (hrun.toLocalRun.finalized_mono_on_prefix ht'0 hy (by omega) hle1)
    · exact tips_comparable_of_origin_witnesses_at hU .refl hRE
        (D.reset.finalized_compatible_clean_source_at hx hE
          (by simpa only [D.cleanLabel_eq] using hs') (hrt.trans htb) ht'0 hle1 hy ht'b)

end Consensus.Goldilocks.Obligations.Growing

end

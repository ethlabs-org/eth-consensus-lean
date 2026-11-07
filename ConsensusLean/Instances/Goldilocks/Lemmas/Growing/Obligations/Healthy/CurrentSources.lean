module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Effective
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FinalizedSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalReplay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The current-record sources under growing faults

The record geometry of healed safety (`Obligations/HealedSafety`) for a healed-safety query, with
every reader honest at its read time and every source writer honest at its own cut:

* `healthy_current_sources_compatible_at`: two record covers (`HealthyRecordCoverAt`) of readers
  honest at their read points compare;
* `healthy_current_record_interval_at`: after the repair window, a reader's results and
  optimistic selections over an interval of cuts, and its floors after them, compare with its
  record at the start of the interval (the current-record cover at the start, from
  `healthy_current_record_sources_before_now_at`), so the interval contract holds.

Finalized blocks compare by FG finalized safety at the later read time; a finalized block and a
clean source, and two clean sources, by the reset kernel (`CurrentSourcesPending`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- At a read point before any cut the reader's finalized block is genesis. -/
private theorem finalized_zero (Q : HealthyPreparationQueryAt S A V) (y : Fin Q.params.n) :
    (Q.trace.state y 0).fg.F =
      Q.params.toParams.genesisBlock (goldilocksNode Q.params (S.ro _)).genesisPayload := by
  have h := simTrace_init_eq S Q.run.2 Q.hn y
  have h2 : Q.trace.state y 0 = Q.trace.init y := rfl
  have h3 : Q.trace.init y = (simTrace S Q.run.2 Q.hn).init y :=
    congrArg (fun T => Trace.init T y) (simTraceAt_eq S Q.run.2 Q.hn)
  rw [h2, h3, h]
  rfl

/-- A read point at a negative time is before every cut. -/
private theorem readPoint_zero (Q : HealthyPreparationQueryAt S A V) {n : Nat} {t : Time}
    (hrp : Regimes.ReadPoint Q.trace n t) (ht : t < 0) : n = 0 := by
  by_contra hn
  have := hrp.1 0 (Nat.pos_of_ne_zero hn)
  have := (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid).time_nonneg 0
  linarith

/-- The block of a result or optimistic selection of a node honest at its write is held while
honest. -/
private theorem source_mem (Q : HealthyPreparationQueryAt S A V) {x : Fin Q.params.n}
    {r s : Nat} {C : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {CV : Set (SA.Vote Q.params.n)}
    (hx : x ∈ Q.keys (Q.trace.time r))
    (hC : SA.ResultAt Q.trace.projAC x r s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x r s C CV) :
    C ∈ Q.trace.HonestBlocksAt Q.keys := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hC' : ∃ ell, Q.trace.projAC.CallAt x r ell ∧ C ∈ ell.frame.tree := by
    rcases hC with ⟨ell, hu, hconf, -⟩ | ⟨ell, A, hpt, -, hsel, -⟩
    · exact ⟨ell, hu.1, (SA.deepest_mem hconf).1.1⟩
    · unfold SA.optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel
      exact ⟨ell, hpt.1, (SA.deepest_mem hsel).1.1⟩
  obtain ⟨ell, hc, hCt⟩ := hC'
  exact ⟨x, r, Q.trace.time r, hrun.time_nonneg r, fun q hq => hrun.time_mono hq.le, hx,
    (Healing.Growing.frame_tree_subset_at hrun hnc hx hc).2 hCt⟩

/-- The fault bound of the reset schedule is below the FG quorum excess at every time of the
horizon. -/
private theorem faults_lt_excess (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) {t : Time} (ht : 0 ≤ t) (htb : t ≤ Q.run.2.horizon) :
    (Q.keys t)ᶜ.ncard < 2 * Q.params.toParams.fg.q - Q.params.n := by
  have h := D.reset.faults t ht htb
  have := Q.hn
  change (Q.keys t)ᶜ.ncard < 2 * ((2 * Fintype.card V + 2) / 3) - Fintype.card V
  change 3 * (Q.keys t)ᶜ.ncard ≤ Fintype.card V - 1 at h
  omega

/-- **Finalized safety at two read points**: the finalized blocks of two readers, each honest at
its read time, compare, with the certificate intersection charged at the later read time. -/
private theorem finalized_safe_read (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) {y z : Fin Q.params.n} {n n' : Nat} {t t' : Time}
    (hrp : Regimes.ReadPoint Q.trace n t) (htb : t ≤ Q.run.2.horizon) (hy : y ∈ Q.keys t)
    (hrp' : Regimes.ReadPoint Q.trace n' t') (ht'b : t' ≤ Q.run.2.horizon)
    (hz : z ∈ Q.keys t') :
    Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys)
      (Q.trace.state y n).fg.F (Q.trace.state z n').fg.F := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have h := SA.interface_requirements Q.params (List (FG.Att Q.params.n)) (S.ro _)
  have fg : Consensus.Goldilocks.Growing.FGLocalRun
      (goldilocksNode Q.params (S.ro _)).genesisPayload Q.keys
      (Q.trace.HonestBlocksAt Q.keys) Q.trace.projFG :=
    Compose.Growing.fg_projection _ _ _ _ _ _ _
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid _ _ _⟩
      hrun.genesis_root_ok hrun.toLocalRun hnc
  have store_eq : ∀ {x : Fin Q.params.n} {m : Nat} {s : Time}, 0 ≤ s →
      (∀ k < m, Q.trace.time k ≤ s) → x ∈ Q.keys s →
      Q.trace.projFG.store x m = (Q.trace.state x m).fg := by
    intro x m s hs hle hx
    have h := Compose.projFG_state (hrun.toLocalRun.upTo hs) hx m
    rw [RunTrace.upTo_projFG, Trace.upTo_state Q.trace.projFG x hle,
      Trace.upTo_state Q.trace x hle] at h
    exact congrArg Prod.fst h
  -- a reader read before every cut holds genesis, which is below every held block
  have gen : ∀ {x : Fin Q.params.n} {m : Nat} {s : Time}, 0 ≤ s →
      (∀ k < m, Q.trace.time k ≤ s) → x ∈ Q.keys s →
      (Q.trace.state x m).fg.F ∈ Q.trace.HonestBlocksAt Q.keys := by
    intro x m s hs hle hx
    obtain ⟨-, -, -, -, hF, -⟩ := fg.finalized_chain_upTo_at hs hle hx
    rwa [store_eq hs hle hx] at hF
  rcases lt_or_ge t 0 with ht | ht
  · obtain rfl := readPoint_zero S A V Q hrp ht
    rw [finalized_zero]
    rcases lt_or_ge t' 0 with ht' | ht'
    · obtain rfl := readPoint_zero S A V Q hrp' ht'
      rw [finalized_zero]
      exact Or.inl .refl
    · exact Or.inl (Compose.Growing.honestAt_genesis_anc hrun (gen ht' hrp'.1 hz)).2
  rcases lt_or_ge t' 0 with ht' | ht'
  · obtain rfl := readPoint_zero S A V Q hrp' ht'
    rw [finalized_zero]
    exact Or.inr (Compose.Growing.honestAt_genesis_anc hrun (gen ht hrp.1 hy)).2
  -- certificate intersection at `max t t'`
  have hf := faults_lt_excess S A V Q D (le_max_of_le_left ht) (max_le htb ht'b)
  rw [← store_eq ht hrp.1 hy, ← store_eq ht' hrp'.1 hz]
  by_contra hne
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, ha₁⟩ := fg.finalized_chain_upTo_at ht hrp.1 hy
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, ha₂⟩ := fg.finalized_chain_upTo_at ht' hrp'.1 hz
  obtain ⟨Sv, hS, hSv⟩ := FG.accountable_safety Q.params.toParams.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ Sv, v ∈ Q.keys (max t t') := by
    by_contra! hS'
    have hcard := Set.ncard_le_ncard
      (s := (Sv : Set (Fin Q.params.toParams.fg.n))) (t := (Q.keys (max t t'))ᶜ) hS'
    rw [Set.ncard_coe_finset] at hcard
    have : ((Q.keys (max t t'))ᶜ : Set (Fin Q.params.toParams.fg.n)).ncard =
        ((Q.keys (max t t'))ᶜ : Set (Fin Q.params.n)).ncard := rfl
    have : Q.params.toParams.fg.n = Q.params.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  have signs : ∀ x ∈ Q.params.toParams.fg.chainAtts c₁ ++ Q.params.toParams.fg.chainAtts c₂,
      x.val = a.val → ∃ k, Q.trace.time k ≤ max t t' ∧ Q.trace.projFG.SignAt a.val k x := by
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
private theorem finalized_compatible_source (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (hrp : Regimes.ReadPoint Q.trace n t) (htb : t ≤ Q.run.2.horizon) (hy : y ∈ Q.keys t)
    {x : Fin Q.params.n} {r s : Nat} {C : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    {CV : Set (SA.Vote Q.params.n)} (hx : x ∈ Q.keys (Q.trace.time r))
    (hC : SA.ResultAt Q.trace.projAC x r s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x r s C CV)
    (hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s) (hrb : Q.trace.time r ≤ Q.run.2.horizon) :
    Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) (Q.trace.state y n).fg.F C := by
  rcases lt_or_ge t 0 with ht | ht
  · obtain rfl := readPoint_zero S A V Q hrp ht
    rw [finalized_zero]
    exact Or.inl (Compose.Growing.honestAt_genesis_anc
      (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid) (source_mem S A V Q hx hC)).2
  exact D.reset.finalized_compatible_clean_source_at (healthy_repair_catch_at S A V Q) hx hC
    (by simpa only [D.cleanLabel_eq] using hs) hrb ht hrp.1 hy htb

/-- **Two record covers compare**: the records of two readers, each honest at its read point,
covered by their finalized blocks or by clean sources of writers honest at their writes, are
compatible in the blocks held while honest. -/
theorem healthy_current_sources_compatible_at (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) {y z : Fin Q.params.n} {n n' : Nat} {t t' : Time}
    (hrp : Regimes.ReadPoint Q.trace n t) (htb : t ≤ Q.run.2.horizon) (hy : y ∈ Q.keys t)
    (hrp' : Regimes.ReadPoint Q.trace n' t') (ht'b : t' ≤ Q.run.2.horizon)
    (hz : z ∈ Q.keys t') {R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : HealthyRecordCoverAt S A V Q D.cleanLabel y n t R)
    (hR' : HealthyRecordCoverAt S A V Q D.cleanLabel z n' t' R') :
    Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) R R' := by
  rw [healthyRecordCoverAt_iff] at hR hR'
  rcases hR with rfl | ⟨x, r, s, B, CV, hx, -, hrt, hs, hB, hRB⟩
  · rcases hR' with rfl | ⟨x', q, s', E, DV, hx', -, hqt, hs', hE, hRE⟩
    · exact finalized_safe_read S A V Q D hrp htb hy hrp' ht'b hz
    · exact tips_comparable_of_origin_witnesses_at S A V Q .refl hRE
        (finalized_compatible_source S A V Q D hrp htb hy hx' hE hs' (hqt.trans ht'b))
  · rcases hR' with rfl | ⟨x', q, s', E, DV, hx', -, hqt, hs', hE, hRE⟩
    · exact (tips_comparable_of_origin_witnesses_at S A V Q .refl hRB
        (finalized_compatible_source S A V Q D hrp' ht'b hz hx hB hs (hrt.trans htb))).symm
    · exact tips_comparable_of_origin_witnesses_at S A V Q hRB hRE
        (D.reset.clean_sources_compatible_at (healthy_repair_catch_at S A V Q) hx hx' hB hE
          (by simpa only [D.cleanLabel_eq] using hs)
          (by simpa only [D.cleanLabel_eq] using hs') (hrt.trans htb) (hqt.trans ht'b))

set_option linter.unusedVariables false in
/-- **The current-record interval.** After the repair window, for a reader honest at the later
of two read points, its results and optimistic selections between the two cuts, and its floors
after them, compare with its record at the first read point: the interval contract of that
record holds. -/
theorem healthy_current_record_interval_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.run.2.horizon) (D : HealthyRepairScheduleAt S A V Q)
    (O : HealthyRepairOpeningAt S A V Q D) (hrepair : HealthyReceiverRepairAt S A V Q D O)
    {y : Fin Q.params.n} {n n' : Nat} {t t' : Time}
    (hrp : Regimes.ReadPoint Q.trace n t) (hrp' : Regimes.ReadPoint Q.trace n' t')
    (hnn : n ≤ n') (htt : t ≤ t') (ht'b : t' ≤ Q.run.2.horizon) (hy : y ∈ Q.keys t')
    (hrep : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ < t) :
    EffectiveRecordIntervalAt Q.trace Q.keys y n n'
      ((SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed).getD
        (Q.trace.state y n).fg.F) := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hΔ := Q.params.toParams.hΔ
  have hc := healthy_repair_catch_at S A V Q
  have htb : t ≤ Q.run.2.horizon := htt.trans ht'b
  have hyt : y ∈ Q.keys t := hrun.antitone htt hy
  have hlow := D.lower
  simp only [max_le_iff] at hlow
  obtain ⟨-, -, hlo, -, hq0⟩ := hlow
  have hi0 : (0 : Time) ≤ (4 * (Q.index : Time) + 6) * Q.params.Δ :=
    mul_nonneg (by positivity) hΔ.le
  have ht0 : 0 ≤ t := by linarith only [hq0, hi0, hrep]
  have ht'0 : 0 ≤ t' := ht0.trans htt
  have hcover := healthy_current_record_sources_before_now_at S A V Q D O hrepair hrp htb hyt hrep
  rw [healthyRecordCoverAt_iff] at hcover
  apply effectiveRecordInterval_of_candidates_before_at hrun hnc ht'0 hrp'.1 hy
  · intro q hnq hqn' B s CV hB
    have hqt' : Q.trace.time q ≤ t' := hrp'.1 q hqn'
    have hqb : Q.trace.time q ≤ Q.run.2.horizon := hqt'.trans ht'b
    have hyq : y ∈ Q.keys (Q.trace.time q) := hrun.antitone hqt' hy
    have htq : t ≤ Q.trace.time q := hrp.2.trans (hrun.time_mono hnq)
    have hbudget : Q.params.ts D.oldLabel + 6 * Q.params.Δ < Q.trace.time q := by
      have : (6 : Time) * Q.params.Δ ≤ (4 * (Q.index : Time) + 6) * Q.params.Δ := by
        have : (0 : Time) ≤ 4 * (Q.index : Time) * Q.params.Δ :=
          mul_nonneg (by positivity) hΔ.le
        linarith
      linarith only [hlo, hrep, htq, this]
    have hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s := by
      apply D.old_bound.trans
      rcases hB with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
      · have htime : Q.trace.time q = Q.params.ts s + 6 * Q.params.Δ := hu.2.2.1
        have hlt := (SA.ts_lt_iff Q.params).mp (show Q.params.ts D.oldLabel < Q.params.ts s by
          linarith only [htime, hbudget])
        exact_mod_cast hlt.le
      · have hh := (SA.ts_le_iff_le_slot Q.params (hrun.time_nonneg q) D.oldLabel).mp
          (show Q.params.ts D.oldLabel ≤ Q.trace.time q by linarith only [hbudget, hΔ])
        change Q.params.slot (Q.trace.time q) = s at hslot
        rw [← hslot]
        exact_mod_cast hh
    rcases hcover with hF | ⟨x, r, s', E, DV, hx, -, hrt, hs', hE, hRE⟩
    · rw [hF]
      exact (finalized_compatible_source S A V Q D hrp htb hyt hyq hB hs hqb)
    · exact tips_comparable_of_origin_witnesses_at S A V Q hRE .refl
        (D.reset.clean_sources_compatible_at hc hx hyq hE hB
          (by simpa only [D.cleanLabel_eq] using hs')
          (by simpa only [D.cleanLabel_eq] using hs) (hrt.trans htb) hqb)
  · intro q hnq hqn'
    have hle1 : ∀ k < q + 1, Q.trace.time k ≤ t' := fun k hk => hrp'.1 k (by omega)
    rcases hcover with hF | ⟨x, r, s', E, DV, hx, -, hrt, hs', hE, hRE⟩
    · rw [hF]
      -- the reader's own finalized block only moves to descendants on the prefix through `t'`
      have hmono := Healing.run_F_mono (hrun.upTo ht'0).toLocalRun hy (show n ≤ q + 1 by omega)
      rw [Trace.upTo_state Q.trace y (fun k hk => hrp'.1 k (by omega)),
        Trace.upTo_state Q.trace y hle1] at hmono
      exact Or.inr (hmono.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono ht'0))
    · exact tips_comparable_of_origin_witnesses_at S A V Q .refl hRE
        (D.reset.finalized_compatible_clean_source_at hc hx hE
          (by simpa only [D.cleanLabel_eq] using hs') (hrt.trans htb) ht'0 hle1 hy ht'b)

end Consensus.Goldilocks.Obligations.Growing

end

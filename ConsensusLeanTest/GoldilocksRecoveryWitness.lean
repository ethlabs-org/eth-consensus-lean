module
public import ConsensusLeanTest.GoldilocksHealingWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Cache
public import ConsensusLean.Instances.Goldilocks.Proofs.Healing.Main
@[expose] public section

/-! # The one-validator tick run through the Recovery statements

On the tick run of `GoldilocksWitness` (`n = 1`, `f = 0`, `Δ = 1`, `k = δ_t = 2`, `t_s = 4s`, a
tick at every time, cut `i` at time `⌊i/8⌋`, no restart), with the parameters of
`GoldilocksHealingWitness` (`g = 0`, `Δ_F = 1`, `G_p = 4`; `ḡ = 0`, `H_z = 3`, `a_z = 16`) and
the pattern parameters `W = 1`, `M = 24`, `c_F = 2`, `k_F = 0` (the weak-timeout regime
`c_F + k_F = δ_t`):

* The constants (computed from the definitions): `M* = 24` (`Mstar_sp1`), `R* = 1092`
  (`Rstar_sp1`), `T_rec = 1209` (`T_rec_sp1`).
* (a) `recovery_premises`: `GoldilocksRun` and `PatternPremises` at these parameters, the
  premises of O.1 and C1.3. `blk6_cache_premise`: the claims' HR.5 per-acceptance premises at the
  acceptance of `blk 6` (cut `194`, time `24 ≥ a_z`): its replay-finalized block `blk 4` is held
  with state height `4 = H_z + 1`, the bound met with equality (the Lean HR.5 needs only the held
  block and its root).
* (b) `tickRun_cacheAcceptance` (HR.5, through `Healing.cache_acceptance_after_reset`): `blk 4`
  is below the finality cache after that acceptance; `finalized_after_blk6`: so the cache there
  is `blk 4` or `blk 5` (the chain invariant `FGGood` alone gives only `≤ blk 5`).
* (b) `tickRun_patternRecovery` (O.1) and `tickRun_finalizingCoverage` (C1.3), each from its
  field `Prop`: `Rec(1209)` and a high finality cache (height `≥ 4`) at every call from `1197`;
  and some proposal `blk s`, `273 ≤ s ≤ 299`, below the finality cache at every call from `1197`
  (requested at `t = R*`). `tickRun_recovery` discharges both fields with the proved bundle
  `Healing.recovery_statements`, so the two conclusions hold on the run unconditionally.

**Limits.** One validator and no fault (`n = 1`, `f = 0`), so the fault bounds are met only as
`0 < …`; `Δ_F = Δ` (`Δ_F < Δ` is impossible at `Δ = 1`); `Rec`'s `clean` and `records` parts are
returned but not specialised to concrete cuts; the finality cache is not computed independently
of the statements (`FGGood` bounds it from above only). -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

/-! ## The constants -/

/-- `M* = acqSlots + oldSlots + 2(c_F + k_F) + 1 = 13 + 6 + 4 + 1 = 24`. -/
theorem Mstar_sp1 : Healing.Mstar sp1 1 4 2 0 = 24 := by decide

/-- `R* = ḡ + Z_reset + (8k + 20)Δ = 0 + 1056 + 36 = 1092`. -/
theorem Rstar_sp1 : Healing.Rstar sp1 0 1 4 = 1092 := by decide

/-- `T_rec = Z_reset + (8k + 20)Δ + 4Δ(W + 1 + M) + 13Δ = 1056 + 36 + 104 + 13 = 1209`. -/
theorem T_rec_sp1 : Healing.T_rec sp1 1 4 1 24 = 1209 := by decide

/-! ## (a) The premises -/

/-- (a) The premises of O.1 and C1.3 on the tick run. -/
theorem recovery_premises :
    GoldilocksRun (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Healing.PatternPremises (tickRun N1 dg1) Set.univ (fun _ => v0) dg1 0 1 4 1 24 2 0 :=
  ⟨tickRun_goldilocksRun, patternPremises_tickRun 0 4 24 (by norm_num) (by rw [Mstar_sp1])⟩

/-- The validator accepts `blk 6` at cut `194` (the tick of `t_6 = 24`). -/
theorem blk6_accept : (tickRun N1 dg1).AcceptAt v0 194 (blk 6) := ⟨rfl, blk_label 5⟩

/-- The FG state after that acceptance holds the chain up to `blk 6`. -/
theorem post194_good : FGGood ((tickRun N1 dg1).post 194).fg 6 := by
  rw [← (tickRun N1 dg1).state_succ_of_call blk6_accept]
  exact state_fgGood 195

/-- (a) HR.5's premises at the acceptance of `blk 6`, after the reset `a_z = 16`: the
replay-finalized block of `blk 6` is `blk 4`, held, with state height `4 = H_z + 1`. -/
theorem blk6_cache_premise :
    16 ≤ (tickRun N1 dg1).time 194 ∧ blk 4 ∈ ((tickRun N1 dg1).post 194).fg.tree ∧
      (blk 4).root = (((tickRun N1 dg1).post 194).fg.σ (blk 6).root).F ∧
      Healing.HZ (tickRun N1 dg1) Set.univ 0 + 1 ≤
        (((tickRun N1 dg1).post 194).fg.σ (blk 4).root).h := by
  have hg := post194_good
  refine ⟨by decide, (mem_tree_iff hg.blocks).2 ⟨4, by omega, rfl⟩, ?_, ?_⟩
  · rw [(hg.sigma 6 le_rfl).F]; rfl
  · rw [(hg.sigma 4 (by omega)).h, hz_zero]; decide

/-! ## (b) The conclusions -/

/-- (b) **HR.5 on the run**: after accepting `blk 6`, the finality cache extends `blk 4`. -/
theorem tickRun_cacheAcceptance :
    ((tickRun N1 dg1).post 194).fg.Anc (blk 4) ((tickRun N1 dg1).post 194).fg.F := by
  obtain ⟨-, hmem, hroot, -⟩ := blk6_cache_premise
  exact Healing.cache_acceptance_after_reset sp1 ro1 (fun _ => v0) dg1 Set.univ
    (tickRun N1 dg1) 0 1 tickRun_goldilocksRun (tickRun_healthy 0) (dg1_noColl _) v0 trivial 194
    (blk 6) blk6_accept (blk 4) hmem hroot

/-- (b) The finality cache after accepting `blk 6` is `blk 4` or `blk 5`. -/
theorem finalized_after_blk6 :
    ∃ f, 4 ≤ f ∧ f ≤ 5 ∧ ((tickRun N1 dg1).post 194).fg.F = blk f := by
  have hg := post194_good
  obtain ⟨f, hf, hF⟩ := hg.F
  have h := tickRun_cacheAcceptance
  rw [hF] at h
  exact ⟨f, le_of_anc_blk (onChain_tree hg.blocks) h, by simpa [jexp] using hf, hF⟩

/-- (b) **O.1 on the run** (from `PatternRecovery`): `Rec(1209)`, and from `1197` every call sees
a finality cache of state height at least `H_z + 1 = 4`. -/
theorem tickRun_patternRecovery (h : Healing.PatternRecovery) :
    Healing.Rec (tickRun N1 dg1) Set.univ 1209 ∧
      ∀ k, (tickRun N1 dg1).IsCall v0 k → 1197 ≤ (tickRun N1 dg1).time k →
        4 ≤ (((tickRun N1 dg1).state v0 k).fg.σ ((tickRun N1 dg1).state v0 k).fg.F.root).h := by
  obtain ⟨hrun, hp⟩ := recovery_premises
  obtain ⟨hR, hF⟩ := h sp1 ro1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) 0 1 4 1 24 2 0 hrun hp
  rw [gbar_zero, T_rec_sp1, zero_add] at hR hF
  refine ⟨hR, fun k hk ht => ?_⟩
  have := hF v0 trivial k hk (by linarith)
  rwa [hz_zero] at this

/-- The honest blocks of the run are chain blocks. -/
theorem honest_onChain : OnChain ((tickRun N1 dg1).HonestBlocks Set.univ) := by
  rintro B ⟨y, -, i, hB⟩
  obtain rfl : y = v0 := Subsingleton.elim _ _
  exact onChain_tree (state_fgGood i).blocks B hB

/-- (b) **C1.3 on the run** (from `FinalizingCoverage`, at `t = R* = 1092`): some proposal
`blk s` with `273 ≤ s ≤ 299` is below the finality cache at every call from `1197`. -/
theorem tickRun_finalizingCoverage (h : Healing.FinalizingCoverage) :
    ∃ p, 273 ≤ p ∧ p ≤ 299 ∧ ∀ k, (tickRun N1 dg1).IsCall v0 k →
      1197 ≤ (tickRun N1 dg1).time k → ∃ f, p ≤ f ∧ ((tickRun N1 dg1).state v0 k).fg.F = blk f := by
  obtain ⟨hrun, hp⟩ := recovery_premises
  obtain ⟨q, kP, P, -, hPr, ht1, ht2, -, hall⟩ :=
    h sp1 ro1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) 0 1 4 1 24 2 0 hrun hp 1092
      (by rw [Rstar_sp1])
  obtain ⟨⟨⟨acc, hc⟩, -⟩, -, -⟩ := hPr
  obtain ⟨s, -, -, rfl, -⟩ := blockCall_eq hc.2
  have hΔ : sp1.Δ = 1 := rfl
  rw [blk_slot, ts_eq] at ht1 ht2
  rw [hΔ] at ht2
  push_cast at ht1 ht2
  refine ⟨s, by dsimp only [Consensus.Time] at *; omega,
    by dsimp only [Consensus.Time] at *; omega, fun k hk ht => ?_⟩
  obtain ⟨f, -, hF⟩ := (state_fgGood k).F
  have hanc := hall v0 trivial k hk (by rw [hΔ]; push_cast; linarith)
  rw [hF] at hanc ⊢
  exact ⟨f, le_of_anc_blk honest_onChain hanc, rfl⟩

/-- (b) **O.1 and C1.3 on the run, closed** by the proved `Healing.recovery_statements`. -/
theorem tickRun_recovery :
    (Healing.Rec (tickRun N1 dg1) Set.univ 1209 ∧
      ∀ k, (tickRun N1 dg1).IsCall v0 k → 1197 ≤ (tickRun N1 dg1).time k →
        4 ≤ (((tickRun N1 dg1).state v0 k).fg.σ ((tickRun N1 dg1).state v0 k).fg.F.root).h) ∧
    ∃ p, 273 ≤ p ∧ p ≤ 299 ∧ ∀ k, (tickRun N1 dg1).IsCall v0 k →
      1197 ≤ (tickRun N1 dg1).time k → ∃ f, p ≤ f ∧ ((tickRun N1 dg1).state v0 k).fg.F = blk f :=
  ⟨tickRun_patternRecovery Healing.recovery_statements.patternRecovery,
    tickRun_finalizingCoverage Healing.recovery_statements.finalizingCoverage⟩

end Consensus.Goldilocks.Witness.One

end

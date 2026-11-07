module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Arming
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Arming
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage engine part under growing faults: the premise package of the lock module

`outageLockPremises_of_arming_at` builds the trace-level premise package
`Compose.Growing.OutageLockPremises` of the lock module from an outage query, its pre-start
service and an armed ready source, with `P` its origin, `A₀ = holdersAt`, `W = lateKeysAt`,
`j₀` the cover label and `r` the restored label.

* The cohort premises come from the outage's no-sleep and cohort counts on the view retained
  through the cohort time `cohortAt = outageEnd = z`, with no rewrite of the retained view:
  `A₀ ⊆ H z`, `W ⊆ H z`, `|(H z)ᶜ ∪ W| < |A₀|`, and a validator honest at `z` awake in `[a, z]`
  is in `A₀ ∪ W`.
* The two count shapes through every horizon come from the η-sleepy premise (η-sleepy implies
  sleepy at half readiness, `sleepy_bounds_at`); the Sleepy invariant up to the start from the
  pre-start service and those counts (`sleepy_invariant_at`).
* `hzc` from the window numbers (`query_numbers_at`): every time up to `t_{j₀+k} + 6Δ` within
  the horizon is at or before `z`; `hA₀join` from the run law (`restart_le_of_awake_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A restart of a node awake on `[a, z]`** and honest at `z`, at a time `≤ z`, is by `a + Δ`:
the node ticks at the first public time from `a`, so the restart (its first call after a sleep)
cannot be later. -/
theorem restart_le_of_awake_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {x : Fin sp.n} {a z : Time}
    (hx : x ∈ H z) (ha0 : 0 ≤ a) (haw : ∀ u, a ≤ u → u ≤ z → tr.awake x u) {k : Nat}
    (hk : tr.RestartAt x k) (hkz : tr.time k ≤ z) : tr.time k ≤ a + sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  by_contra hlt
  push Not at hlt
  set p := a + (-a) % sp.Δ with hp
  have hm0 : 0 ≤ (-a) % sp.Δ := Int.emod_nonneg _ hΔ.ne'
  have hm1 : (-a) % sp.Δ < sp.Δ := Int.emod_lt_of_pos _ hΔ
  have hpub : sp.toParams.IsPublic p :=
    ⟨-((-a) / sp.Δ), by rw [hp, Int.emod_def]; ring⟩
  obtain ⟨j, y, hg⟩ := hrun.tick_of_awake x p (hrun.antitone (by linarith) hx) (by linarith) hpub
    (haw p (by linarith) (by linarith))
  obtain ⟨hne, hks, -⟩ := hg
  obtain ⟨hn0, ht0, -, -, hl0⟩ := hks 0 (List.length_pos_of_ne_nil hne)
  simp only [Nat.add_zero] at hn0 ht0 hl0
  have hcall : tr.IsCall x j := ⟨_, hn0, hl0⟩
  obtain ⟨u, -, huk, hnaw, hcalls⟩ := hrun.sleep_of_restart x k (hrun.antitone hkz hx) hk
  have hjk : j < k := by
    by_contra h
    have := hrun.time_mono (show k ≤ j by omega)
    linarith
  have hpu := hcalls j hjk hcall
  exact hnaw (haw u (by linarith) (by linarith))

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- **The adapter**: the premise package of the lock module under growing faults from an armed
ready source, with `P` its origin, `A₀` the cohort, `W` its late wakers, `j₀` the cover label and
`r` the restored label. -/
noncomputable def outageLockPremises_of_arming_at (Q : OutageQueryAt S A V)
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    {v : V} (hsh : Q.start ≤ Q.run.2.horizon)
    (ar : OutageArmingAt Q v) :
    Compose.Growing.OutageLockPremises Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) :=
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hnum := query_numbers_at Q
  have hr := restoredLabel_spec Q
  have hΔ := Q.params.toParams.hΔ
  have hk2 := Q.params.two_le_k
  have hT0 : 0 ≤ Q.T := Q.outage.1.1
  have hlag := outage_node_lag_at Q
  have hTs : Q.T ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 6) * Q.params.Δ := by positivity
    linarith
  have hhalf : Q.run.2.point.SleepyOn (1 / 2) (Regimes.catchUp Q.params) (5 * Q.params.Δ) 0
      Q.run.2.horizon := fun t ht htb => by
    have h := (Q.outage.2.2.1 t ht htb).readyAbove (by change (0 : ℚ) ≤ 1 / 2; norm_num)
    rw [Q.aheadDur_eq] at h
    exact half_ready_of_duration V _ (outage_duration_supply_at Q) h
  have hBb : ∀ b, b ≤ Q.run.2.horizon → Compose.Growing.SleepyBounds Q.trace Q.keys b :=
    fun b hb => sleepy_bounds_at S Q.run.2 Q.hn Q.valid hb fun t ht htb => hhalf t ht (htb.trans hb)
  have hwin := outage_window_cover_at Q
  have hzh : (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run ≤ Q.run.2.horizon :=
    min_le_right _ _
  have hkeyz : ∀ x : Fin (Fintype.card V), x ∈ Q.keys
      ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run) ↔
      Q.run.2.key x ∉ Q.run.2.point.faultyAt
        ((Sys (goldilocks S) V).cohortAt (K S A) Q.stop Q.run) := fun x => by
    rw [mem_honestKeysAt_iff, min_eq_left hzh, Q.cohortAt_eq]; rfl
  { b₀ := Q.start
    b₁ := Q.stop
    a := (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run
    z := (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run
    P := ar.origin
    σ := if ar.origin.root = Q.params.genesisRoot then 0 else ar.σ
    j₀ := Compose.coverLabel Q.params Q.start
    r := Q.restoredLabel
    A₀ := Q.holdersAt
    W := Q.lateKeysAt
    hrun := hrun
    hnc := hnc
    hj₀ := ⟨hnum.1, hnum.2.1⟩
    hr := hr
    hσ := by
      split_ifs with hg
      · have := (Compose.armed_label_lt (σ := 0) hT0 hlag
          (by simp only [SA.SAParams.ts]; simpa using hT0)).2
        change 0 + Q.params.k < _
        omega
      · rcases ar.armed with ⟨htg, ho⟩ | ⟨-, hσk⟩
        · exact absurd (ho ▸ htg) hg
        · exact hσk
    hrk := by
      obtain ⟨-, -, -, -, hK, hjs, -⟩ := hnum
      refine ⟨?_, hr.2 _ hK⟩
      by_contra h
      have := (SA.ts_le_iff Q.params).2
        (show (Q.restoredLabel : Int) ≤ (Compose.coverLabel Q.params Q.start : Nat) by omega)
      linarith [hr.1]
    hgap := hnum.2.2.1
    hb₀ := hnum.2.2.2.1
    hP := by
      refine ⟨ar.origin_held, ?_⟩
      split_ifs with hg
      · exact Or.inl hg
      · rcases ar.armed with ⟨htg, ho⟩ | ⟨hCw, -⟩
        · exact absurd (ho ▸ htg) hg
        · exact Or.inr (hCw.mono hTs)
    hpre := Compose.Growing.sleepy_invariant_at hrun hnc (hT0.trans hTs) service (hBb _ hsh)
    hpreSvc := service
    hB := fun b ⟨_, _, _, hc, hle⟩ => hBb b (hle.trans (Q.call_le_horizon hc))
    hA₀ := fun x hx => by
      obtain ⟨hxh, -⟩ := Finset.mem_filter.1 (OutageQueryAt.mem_holdersAt.1 hx)
      exact (hkeyz x).2 (Finset.mem_sdiff.mp hxh).2
    hW := ⟨fun x hx => by
        obtain ⟨_, t, _, _, hh, _⟩ :=
          Finset.mem_filter.1 (Finset.mem_sdiff.1 (OutageQueryAt.mem_lateKeysAt.1 hx)).1
        exact (hkeyz x).2 hh,
      Set.disjoint_left.2 fun _ h₁ h₂ =>
        (Finset.mem_sdiff.1 (OutageQueryAt.mem_lateKeysAt.1 h₂)).2
          (OutageQueryAt.mem_holdersAt.1 h₁)⟩
    hcohort := by
      have heq : (Q.keys ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run))ᶜ ∪
          Q.lateKeysAt = Q.run.2.key ⁻¹'
          (↑(Q.run.2.point.faultyAt ((Sys (goldilocks S) V).cohortAt (K S A) Q.stop Q.run) ∪
            (Q.run.2.point.retain ((Sys (goldilocks S) V).cohortAt (K S A) Q.stop
              Q.run)).lateWakers ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
              ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run)) : Set V) := by
        ext x
        simp only [Set.mem_union, Set.mem_compl_iff, hkeyz, not_not, Set.mem_preimage,
          Finset.coe_union, Finset.mem_coe, OutageQueryAt.mem_lateKeysAt]
      have hA : Q.holdersAt = Q.run.2.key ⁻¹' (↑((Q.run.2.point.retain
          ((Sys (goldilocks S) V).cohortAt (K S A) Q.stop Q.run)).awakeAt
          ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)) : Set V) := by
        ext x; simp [OutageQueryAt.mem_holdersAt]
      rw [heq, hA, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
          (by simp [Q.run.2.key.surjective.range_eq]),
        Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
          (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset,
        Set.ncard_coe_finset]
      exact Q.outage.2.2.2.2
    hawake := fun x t hat htz hxz haw => by
      rw [simTraceAt_awake_bounds] at haw
      by_cases hxa : Q.run.2.key x ∈ (Q.run.2.point.retain ((Sys (goldilocks S) V).cohortAt
          (K S A) Q.stop Q.run)).awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
      · exact Or.inl (OutageQueryAt.mem_holdersAt.2 hxa)
      · exact Or.inr (OutageQueryAt.mem_lateKeysAt.2 (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2
          ⟨Finset.mem_univ _, t, hat, htz, (hkeyz x).1 hxz, haw.1⟩, hxa⟩))
    hA₀awake := fun x hx t hat htz => by
      obtain ⟨hxh, hxa⟩ := Finset.mem_filter.1 (OutageQueryAt.mem_holdersAt.1 hx)
      rw [simTraceAt_awake_bounds]
      exact ⟨Q.outage.2.2.2.1 _ (Finset.mem_sdiff.mp hxh).2 _ le_rfl (hat.trans htz) hxa t hat htz,
        hwin.1.trans hat, htz.trans hzh⟩
    hA₀join := fun x hx k hk hkz => by
      obtain ⟨hxh, hxa⟩ := Finset.mem_filter.1 (OutageQueryAt.mem_holdersAt.1 hx)
      refine Compose.Growing.restart_le_of_awake_at hrun ((hkeyz x).2 (Finset.mem_sdiff.mp hxh).2)
        hwin.1 (fun u hau huz => ?_) hk hkz
      rw [simTraceAt_awake_bounds]
      exact ⟨Q.outage.2.2.2.1 _ (Finset.mem_sdiff.mp hxh).2 _ le_rfl (hau.trans huz) hxa u hau huz,
        hwin.1.trans hau, huz.trans hzh⟩
    ha := by
      have h := hwin.2.1
      have hj : (Q.params.k : Int) < Compose.coverLabel Q.params Q.start :=
        by exact_mod_cast (Compose.armed_label_lt (σ := 0) hT0 hlag
          (by simp only [SA.SAParams.ts]; simpa using hT0)).2
      simp only [SA.SAParams.ts] at h ⊢
      have : (0 : Time) ≤ (Q.params.k : Int) - 1 := by linarith
      linarith [mul_nonneg this Q.params.toParams.hΔ.le]
    hzc := fun t ht ⟨_, _, _, hc, hle⟩ => hnum.2.2.2.2.2.2 t ht (hle.trans (Q.call_le_horizon hc))
    lockPrev := fun x hx hg ⟨_, _, _, hc, hle⟩ => by
      obtain ⟨c, ℓ, hu, hb⟩ := ar.lockPrev x hx hg (hle.trans (Q.call_le_horizon hc))
      exact ⟨c, ℓ, hu, Compose.Growing.prevBaseAt_iff.2 hb⟩
    lockCover := fun x hx hg ⟨_, _, _, hc, hle⟩ => by
      obtain ⟨c, ℓ, hu, hfirst, hcond⟩ := ar.lockCover x hx hg (hle.trans (Q.call_le_horizon hc))
      exact ⟨c, ℓ, hu, hfirst, fun hF hVA hN =>
        Compose.Growing.coverBaseAt_iff.2 (hcond hF hVA hN)⟩
    PG := fun w c m ℓ hw hu hrm x i e hve hes =>
      outage_pool_delivery_query_at Q w c m ℓ hw hu (hr.1.trans (by
        have := (SA.ts_le_iff Q.params).2 (show (Q.restoredLabel : Int) ≤ m by exact_mod_cast hrm)
        linarith)) x i e (Compose.Growing.hVoteAt_iff.1 hve).1
        (Compose.Growing.hVoteAt_iff.1 hve).2 hes }

end Consensus.Goldilocks.Obligations.Growing

end

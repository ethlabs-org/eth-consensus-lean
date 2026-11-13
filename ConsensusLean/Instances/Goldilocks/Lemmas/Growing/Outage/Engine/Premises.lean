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
  is in `A₀ ∪ W`; inside each band committee `K m`, `|K m ∩ ((H z)ᶜ ∪ W)| < |K m ∩ A₀|`
  (`cohort_lt_K`, from the committee cohort premise).
* The slot committees are the query's `Q.K`, with their facts `Q.facts` (size, P, T, frames,
  gate) and their count shapes `Q.boundsK` (from the committee η-sleepy premise).
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
    {ini} (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) {x : Fin sp.n}
    {a z : Time}
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
variable {S : BoundSetup} {A : ContractAssumptions S.toSetup} {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- **The adapter**: the premise package of the lock module under growing faults from an armed
ready source, with `P` its origin, `A₀` the cohort, `W` its late wakers, `j₀` the cover label and
`r` the restored label. -/
noncomputable def outageLockPremises_of_arming_at (Q : OutageQueryAt S A V)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start)
    {v : V} (hsh : Q.start ≤ Q.run.2.horizon)
    (ar : OutageArmingAt Q v) :
    Compose.Growing.OutageLockPremises Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) (simIni S Q.run.2 Q.hn) :=
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hmv := simIni_mayVote S Q.run.2 Q.hn -- TEMP(C2): C3b-final removes after C3a/C3c
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hnum := query_numbers_at Q
  have hr := restoredLabel_spec Q
  have hΔ := Q.params.toParams.hΔ
  have hk2 := Q.params.two_le_k
  have hT0 : 0 ≤ Q.T := Q.outage.times.1
  have hlag := outage_node_lag_at Q
  have hTs : Q.T ≤ Q.start := by
    have : (0 : Time) ≤ (4 * Q.params.k + 6) * Q.params.Δ := by positivity
    linarith
  have hBb : ∀ b, b ≤ Q.run.2.horizon → Compose.Growing.SleepyBoundsFrom Q.trace Q.keys 0 b :=
    fun b hb => Q.bounds hb
  have hwin := outage_window_cover_at Q
  { b₀ := Q.start
    b₁ := Q.stop
    a := (Sys (goldilocksWith S) V).outageStart (K S.toSetup A) Q.start Q.run
    z := (Sys (goldilocksWith S) V).outageEnd (K S.toSetup A) Q.stop Q.run
    P := ar.origin
    σ := if ar.origin.root = Q.params.genesisRoot then 0 else ar.σ
    j₀ := Compose.coverLabel Q.params Q.start
    r := Q.restoredLabel
    A₀ := Q.holdersAt
    W := Q.lateKeysAt
    hrun := hrun
    K := Q.K
    facts := Q.facts hrun
    hmv := hmv
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
    hpre := Compose.Growing.sleepy_invariant_at hrun hnc (Q.facts hrun) (hT0.trans hTs) service
      (hBb _ hsh) (Q.boundsK hrun hsh)
    hpreSvc := service
    hB := fun b ⟨_, _, _, hc, hle⟩ => hBb b (hle.trans (Q.call_le_horizon hc))
    hBK := fun b ⟨_, _, _, hc, hle⟩ => Q.boundsK hrun (hle.trans (Q.call_le_horizon hc))
    hA₀ := Q.holdersAt_subset
    hW := ⟨Q.lateKeysAt_subset, Q.holdersAt_disjoint⟩
    hcohort := Q.cohort_lt
    hcohortK := fun m h₁ h₂ ⟨_, _, _, hc, hle⟩ =>
      Q.cohort_lt_K h₁ h₂ (hle.trans (Q.call_le_horizon hc)) hsh
    hawake := fun x t hat htz hxz haw => Q.classify hat htz hxz haw
    hA₀awake := fun x hx t hat htz => Q.holder_awake hx hat htz
    hA₀join := fun x hx k hk hkz =>
      Compose.Growing.restart_le_of_awake_at hrun (Q.holdersAt_subset hx) hwin.1
        (fun u hau huz => Q.holder_awake hx hau huz) hk hkz
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

section Projections

variable {Q : OutageQueryAt S A V} [Fact (S.vote.participationKind = none)] -- TEMP(C2)
  {service : Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start} {v : V}
  {hsh : Q.start ≤ Q.run.2.horizon} {ar : OutageArmingAt Q v}

theorem outageLockPremises_of_arming_at_P :
    (outageLockPremises_of_arming_at Q service hsh ar).P = ar.origin := by rfl

theorem outageLockPremises_of_arming_at_j₀ :
    (outageLockPremises_of_arming_at Q service hsh ar).j₀ =
      Compose.coverLabel Q.params Q.start := by rfl

theorem outageLockPremises_of_arming_at_b₁ :
    (outageLockPremises_of_arming_at Q service hsh ar).b₁ = Q.stop := by rfl

theorem outageLockPremises_of_arming_at_r :
    (outageLockPremises_of_arming_at Q service hsh ar).r = Q.restoredLabel := by rfl

end Projections

end Consensus.Goldilocks.Obligations.Growing

end

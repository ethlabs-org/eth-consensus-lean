module
public import AvailableChainSAPC.Proofs.HealthyCoverage
public import AvailableChainSAPC.Proofs.PendingProtection

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The common P1 assembly for slow and fast admission. All healthy
record, finite-root, PC-authority, and in-flight HEAD premises are derived.
Only the policy-specific admission test remains an input. -/
theorem resilient_of_pending_admission {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (C : Constants) (T b₀ b₁ : Time)
    (ho : OutageRegime (sapc p) E (sapcInterface p).toInterface C rho T b₀ b₁)
    (lag : 4 * p.Δ ≤ C.armingLag) (budget : C.budget ≤ lifetime p)
    (admission : ∀ r, earlyTime p r ≤ b₀ → b₀ < gateTime p r → gateTime p r ≤ rho.horizon →
      ∀ source ∈ rho.honest, ∀ B, B ≠ .genesis →
        Block.Preceq B (stable (Run.readAt (sapc p) rho T source)) →
        ∀ v ∈ rho.honest, releaseThreshold p ∈
          @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
            (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B) :
    PersistsThrough (sapc p) rho (sapcInterface p).stable T b₀ b₁ := by
  intro source hs B below t ht0 ht1
  change Block.Preceq B (stable (Run.readAt (sapc p) rho T source)) at below
  by_cases gen : B = .genesis
  · subst B; exact fun _ _ => GridCO.genesis_prefix _
  have first : gateTime p 0 ≤ T := by
    by_contra hn
    rw [read_stable_before_first_gate p rho T (lt_of_not_ge hn) source] at below
    exact gen (by simpa [Block.Preceq, Block.preceq] using below)
  obtain ⟨l, hlo, hhi⟩ := GridCO.exists_latest_gate p.engine b₀ (first.trans ho.interval.2.1)
  have before : T < gateTime p l := by
    have step : gateTime p (l + 1) = gateTime p l + 4 * p.Δ := by
      change 4 * p.Δ * ((l + 1 : Nat) : Time) + 6 * p.Δ =
        4 * p.Δ * (l : Time) + 6 * p.Δ + 4 * p.Δ
      push_cast; ring
    change b₀ < gateTime p (l + 1) at hhi
    rw [step] at hhi
    linarith [ho.armed]
  have hh : gateTime p l ≤ rho.horizon := hlo.trans (ho.interval.2.2.1.trans ho.interval.2.2.2)
  have records := healthy_record_after_stable p E rho hΔ ho.execution ho.rootInjective b₀
    ho.healthy ho.acceptedRelay ho.sleepyBefore l hlo hh T before source hs B below
  by_cases pending : t < gateTime p (l + 1)
  · intro v hv
    change Block.Preceq B (stable (Run.readAt (sapc p) rho t v))
    rw [read_stable_eq_latest_gate p E rho ho.execution.toScheduleWellFormed l t
        (hlo.trans ht0) pending v]
    exact records v hv
  · have hgt : gateTime p (l + 1) ≤ t := le_of_not_gt pending
    have horizon := hgt.trans (ht1.le.trans ho.interval.2.2.2)
    have early : earlyTime p (l + 1) ≤ b₀ := by
      rw [show earlyTime p (l + 1) = gateTime p l from GridCO.early_next_eq_gate p.engine l]
      exact hlo
    have earlyH : earlyTime p (l + 1) ≤ rho.horizon := early.trans
      (ho.interval.2.2.1.trans ho.interval.2.2.2)
    have voteBefore : voteTime p (l + 1) < b₀ := by
      apply lt_of_lt_of_le _ early
      change 4 * p.Δ * ((l + 1 : Nat) : Time) + p.Δ <
        4 * p.Δ * ((l + 1 : Nat) : Time) + 2 * p.Δ
      linarith [p.deltaPos]
    have nonneg : 0 ≤ voteTime p (l + 1) := by
      change 0 ≤ 4 * p.Δ * ((l + 1 : Nat) : Time) + p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg (l + 1)]
    have heads := healthy_stable_heads p E rho hΔ ho.execution ho.rootInjective b₀
      ho.healthy ho.acceptedRelay ho.sleepyBefore (l + 1) early earlyH T
      (ho.interval.2.1.trans_lt hhi) source hs B below
    have old : ∀ v ∈ rho.honest, Block.Preceq B
        (stable (Run.stateBeforeTime (sapc p) rho (gateTime p (l + 1)) v)) := by
      intro v hv
      have input : Run.stateBeforeTime (sapc p) rho (gateTime p (l + 1)) =
          Run.readAt (sapc p) rho (gateTime p (l + 1) - 1) := by
        simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
      rw [input, read_stable_eq_latest_gate p E rho ho.execution.toScheduleWellFormed l
        (gateTime p (l + 1) - 1)
        (by change 4 * p.Δ * (l : Time) + 6 * p.Δ ≤
              4 * p.Δ * ((l + 1 : Nat) : Time) + 6 * p.Δ - 1
            have deltaOne : 1 ≤ p.Δ := Int.add_one_le_iff.mpr p.deltaPos
            push_cast; nlinarith)
        (by exact Int.sub_lt_self _ (by norm_num : (0 : Time) < 1))]
      exact records v hv
    have headH : voteTime p (l + 1 + 1) ≤ rho.horizon := by
      apply le_trans _ horizon
      change 4 * p.Δ * ((l + 1 + 1 : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((l + 1 : Nat) : Time) + 6 * p.Δ
      push_cast; linarith [p.deltaPos]
    have deadline : t < gateTime p (l + 1) + lifetime p := by
      have bound := ho.withinBudget.trans budget
      linarith
    intro v hv
    exact (pending_prefix_protection p E rho ho.execution hΔ b₀ ho.healthy ho.acceptedRelay
      (l + 1) early horizon (ho.sleepyBefore _ nonneg voteBefore) B gen heads old
      (admission (l + 1) early hhi horizon source hs B gen below)
      (healthy_pending_gate_guard p E rho hΔ ho.execution ho.rootInjective b₀ ho.healthy
        ho.acceptedRelay ho.sleepyBefore (l + 1) early earlyH)
      (fun w hw => healthy_pending_gate_pcOK p E rho hΔ ho.execution ho.rootInjective b₀
        ho.healthy ho.acceptedRelay ho.sleepyBefore (l + 1) early horizon w hw B heads)
      (fun w hw => healthy_pending_head_root p E rho hΔ ho.execution ho.rootInjective b₀
        ho.healthy ho.acceptedRelay ho.sleepyBefore (l + 1) early earlyH w hw B (heads w hw))
      (fun w hw => healthy_pending_head_pc_compatible p E rho hΔ ho.execution ho.rootInjective b₀
        ho.healthy ho.acceptedRelay ho.sleepyBefore (l + 1) early headH w hw B heads)
      t hgt deadline v hv).2

/-- General P1 with the unchanged SA slow lag and budget, for all a<h.
The full raw window supplies the pending prefix's first lease. -/
theorem stable_resilient_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho T b₀ b₁) :
    PersistsThrough (sapc p) rho (sapcInterface p).stable T b₀ b₁ := by
  apply resilient_of_pending_admission p E rho hΔ (sapcConstants p G) T b₀ b₁ ho
    (SA.fastLag_le_slowLag p G) (min_le_right _ _)
  intro r early pending hh source hs B nonzero below v hv
  have first : gateTime p 0 ≤ T := by
    by_contra hn
    rw [read_stable_before_first_gate p rho T (lt_of_not_ge hn) source] at below
    exact nonzero (by simpa [Block.Preceq, Block.preceq] using below)
  have lag : T + 4 * ((p.k : Time) - 1) * p.Δ ≤ b₀ := ho.armed
  have len : p.k ≤ r + 1 := by
    by_contra hn
    have cast : (r : Time) + 1 < p.k := by exact_mod_cast Nat.lt_of_not_ge hn
    change 4 * p.Δ * (0 : Time) + 6 * p.Δ ≤ T at first
    simp only [mul_zero, zero_add] at first
    change b₀ < 4 * p.Δ * (r : Time) + 6 * p.Δ at pending
    nlinarith [p.deltaPos]
  have slow := slowEligible_of_input_covers p E rho ho.execution.toScheduleWellFormed hΔ
    v hv r B len hh (by
      intro s hsr window
      have before : T < gateTime p s := by
        have cast : (r : Time) + 1 ≤ (s : Time) + p.k := by exact_mod_cast window
        change b₀ < 4 * p.Δ * (r : Time) + 6 * p.Δ at pending
        change T < 4 * p.Δ * (s : Time) + 6 * p.Δ
        nlinarith [p.deltaPos]
      have earlyLe : earlyTime p s ≤ earlyTime p r := by
        have cast : (s : Time) ≤ r := by exact_mod_cast hsr.le
        change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
        nlinarith [p.deltaPos]
      have earlyH : earlyTime p s ≤ rho.horizon := by
        apply le_trans _ hh
        have cast : (s : Time) ≤ r := by exact_mod_cast hsr.le
        change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
        nlinarith [p.deltaPos]
      exact healthy_result_after_stable p E rho hΔ ho.execution ho.rootInjective b₀
        ho.healthy ho.acceptedRelay ho.sleepyBefore s (earlyLe.trans early) earlyH T before
        source hs B below v hv)
  exact (SA.admissionLevels_iff p _ r B (releaseThreshold p)).mpr ⟨rfl, Or.inr slow⟩

/-- Fast P1 with SA's 4Δ lag and the full-prefix high participation
premise of Draft 4.3. It has no fault-cap premise. -/
theorem fastP1_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (G : Time) (hΔ : E.Δ = p.Δ) :
    ∀ (rho : Run V (sapc p)) T b₀ b₁,
      FastOutageRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho T b₀ b₁ →
      PersistsThrough (sapc p) rho (sapcInterface p).stable T b₀ b₁ := by
  intro rho T b₀ b₁ ho
  apply resilient_of_pending_admission p E rho hΔ _ T b₀ b₁ ho.toOutageRegime
    (le_refl _) (min_le_right _ _)
  intro r early pending hh source hs B _ below v hv
  have earlyH : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have nonneg : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have voteBefore : voteTime p r < b₀ := by
    apply lt_of_lt_of_le _ early
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  exact healthy_fast_admission p E rho ho.execution hΔ b₀ ho.healthy ho.acceptedRelay
    r early earlyH (ho.highParticipation _ nonneg voteBefore) B
    (healthy_stable_heads p E rho hΔ ho.execution ho.rootInjective b₀ ho.healthy ho.acceptedRelay
      ho.sleepyBefore r early earlyH T (ho.interval.2.1.trans_lt pending) source hs B below)
    v hv

end AvailableChain.SAPC
end

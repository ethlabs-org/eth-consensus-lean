module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowAssembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetOfDrainRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.DrainWarm
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposerGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Lemmas.Blocks.Facts

public section

/-! # Goldilocks Refinement: the reset premises and the placement of a final query (#136)

consensus-lean#136, route A, workbench `heal_bound.md`. `final_reset_premises_of_query` has the
statement of the leaf `final_reset_premises` (Accepted.lean): one reset `a` with (H1) its premises
`ResetPremisesUpTo` through the horizon at GST `Q.gst`, and (H3) the placement with
`u_min = finalSeedMin Q a = slot a + 2k + 5`. It is the instance at the protocol row delay
`ΔF := rowDelay` and the gap `c = cF r` of `final_reset_premises_of_shared`, which takes the shared
HS premises at a forwarding delay `ΔF` and the final pattern `[0, c, 2c, 3c]` with `2 ≤ c` and
`3c ≤ δ_t` (workbench `two_bound_network.md` §4).

The reset is `exists_reset_of_drain_rounds_awake` (the rise-round route) at the ready scalar
`ready` (`ready ≥ 1`), the gap `G = X = Q.index`, the drain length
`L_drain = healthyDrainLen = 2k + X`, `λ = 2Δ` and the service horizon `b = horizon`; its bound is
`B = ready + healthyResetCoeff·Δ`.
The run premises come from the shared HS premises at `Δ_F`, Catch from `catchRun_of_psync`, the
drain from `drainOutputs_of_service`. The gap is `final_query_gap`: `recurrence_gap` on the final
pattern (span `3c`) with the guarded duty → proposal adapter `duty_proposal_run`.

The coefficient input is `accepted_heal_ge_final` (AcceptanceDefs.lean): the heal coefficient of
the final capability is at least `catchUp + M_f`, `M_f = 20 L_drain + 8k + 28δ_t + 28X + 56`
(in node delays `Δ = Δe`). With it,
`B + (8k + 20)Δ + 4(X + δ_t − 1)Δ − 1 = ready + M_f·Δ − 1 ≤ heal ≤ query`, which is (H3), and
`B + (12c − 2)Δ ≤ heal ≤ horizon` (`final_heal_horizon_fit`, for every `c` with `3c ≤ δ_t`),
which pays the gap's horizon. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The final heal margin covers a window of span `3c`** (symbolic in `c`). With the reset bound
`B = ready + (20 L_drain + 24δ_t + 24X + 40)·Δ` and `M_f = 20 L_drain + 8k + 28δ_t + 28X + 56`
(`accepted_heal_ge_final`), the horizon step of a gap-`c` window, `B + (12c − 2)·Δ`, stays below
`ready + M_f·Δ − 1` for every `c` with `3c ≤ δ_t`: the slack `M_f − (B − ready)/Δ − 12c + 2 =
8k + 4δ_t + 4X + 18 − 12c ≥ 8k + 4X + 18` is positive. So `accepted_heal` needs no change for a
gap `c` with `3c ≤ δ_t`. -/
theorem final_heal_horizon_fit {D Ld k δt X c : Time} (hD : 0 < D) (hk : 0 ≤ k) (hX : 0 ≤ X)
    (h3c : 3 * c ≤ δt) :
    (20 * Ld + 24 * δt + 24 * X + 40 + (12 * c - 2)) * D + 1 ≤
      (20 * Ld + 8 * k + 28 * δt + 28 * X + 56) * D := by
  have h1 : 0 ≤ (4 * δt - 12 * c) * D := mul_nonneg (by linarith) hD.le
  have h2 : 0 ≤ k * D := mul_nonneg hk hD.le
  have h3 : 0 ≤ X * D := mul_nonneg hX hD.le
  have key : (20 * Ld + 8 * k + 28 * δt + 28 * X + 56) * D -
      ((20 * Ld + 24 * δt + 24 * X + 40 + (12 * c - 2)) * D + 1) =
      8 * (k * D) + (4 * δt - 12 * c) * D + 4 * (X * D) + 18 * D - 1 := by ring
  have hD1 : (1 : Time) ≤ D := by change (0 : ℤ) < D at hD; change (1 : ℤ) ≤ D; omega
  linarith

/-- **The honest-proposer gap of a final query** (premise `hgp` of the rise at `G = X`): for the
final pattern `[0, c, 2c, 3c]` (`hpat`, span `3c`), with `max ready 0 + 4Δ ≤ t_{s₀}` and
`t_{N + 3c} ≤ horizon`, every slot window `[x₀, x₀ + X)` inside `[s₀, N]` has an actual honest
designated proposal. -/
theorem final_query_gap (Q : FinalQuery S A V) {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * c : Nat) ≤ Q.run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (Q.index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ honestKeys S Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (finalGrid S A V Q) ⟨finalWindow A, Q.index⟩
      ((Sys (family S) V).cDur (K S A) Q.run) ((Sys (family S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, acceptanceContract, ↓reduceIte,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using Q.progress
  have hL : (finalGrid S A V Q).slotLen = 4 * Q.params.Δ := by
    have h1 := finalGrid_slotTime S A V Q 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith
  have hspan : (finalGrid S A V Q).slotTime N +
      (((⟨finalWindow A, Q.index⟩ : Recurrence).pattern.span : Nat) : Time) *
        (finalGrid S A V Q).slotLen = Q.params.ts (N + 3 * c : Nat) := by
    rw [← finalGrid_slotTime S A V Q, (finalGrid S A V Q).slotTime_add]
    simp [finalWindow_span_of_offsets S A hpat]
  have hgap := recurrence_gap hrec (by rw [hpat]; simp) (s₀ := s₀) (N := N)
    (by rw [hL, finalGrid_slotTime]; exact hs) (by rw [hspan]; exact hN)
    (by rw [hspan]; exact hN)
  have hΔ := Q.params.toParams.hΔ
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap x₀ hx₀ hxN
  have hxr : x < x₀ + (Q.index : Nat) := hxr
  have hxN : x₀ + (Q.index : Nat) ≤ N + 1 := hxN
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have hs0 : s₀ = 0 := by omega
      subst hs0
      have := le_max_right ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0
      simp only [SA.SAParams.ts] at hs
      push_cast at hs
      linarith
    · exact h
  have hxts : Q.params.ts x ≤ Q.params.ts (N + 3 * c : Nat) :=
    (SA.ts_le_iff Q.params).2 (by exact_mod_cast (show x ≤ N + 3 * c by omega))
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := duty_proposal_run S A V Q.run Q.hn Q.valid
    Q.noCollision hx0 (hxts.trans hN) hx
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

/-- **The reset premises and the placement of a final query, at a forwarding delay `ΔF` and a
gap `c`.** From the shared HS premises `hs` at `ΔF` (whose `timeoutDelay` is `6Δ + ΔF ≤ 4Δ·δ_t`),
the final pattern `[0, c, 2c, 3c]` (`hpat`) with `2 ≤ c` and `3c ≤ δ_t`: a reset `a` with its
premises through the horizon at GST `Q.gst` and `ΔR = ΔF`, and the placement `(P)` with
`u_min = finalSeedMin Q a`. The horizon of the gap uses `final_heal_horizon_fit`. -/
theorem final_reset_premises_of_shared (Q : FinalQuery S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {ΔF : Time}
    (hs : Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen := by
  classical
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  set H := honestKeys S Q.run.2
  set X : Nat := (Q.index : Nat) with hXdef
  set Ld : Nat := healthyDrainLen S Q.index with hLddef
  set ready := (Sys (family S) V).ready (K S A) Q.gst Q.run with hreadydef
  set D := Q.params.Δ with hDdef
  have hD : 0 < D := Q.params.toParams.hΔ
  have hDe : D = Q.run.1.Δ := rfl
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hk : Q.params.k = S.k := rfl
  -- the ready scalar
  have hC : (Sys (family S) V).cDur (K S A) Q.run =
      ((accepted_catchUp S A : Nat) : Time) * Q.run.1.Δ := by
    simp only [System.cDur, Params.standard, accepted_coefficients_catchUp]
    rfl
  have hready : ready = max Q.gst 0 + ((accepted_catchUp S A : Nat) : Time) * Q.run.1.Δ + 1 := by
    rw [hreadydef, ← hC]; rfl
  have hr0 : 0 ≤ ready := by
    rw [hready]; have := le_max_right Q.gst 0; positivity
  have hrmax : max ready 0 = ready := max_eq_left hr0
  have hgr : gbar Q.gst ≤ ready := by
    change max Q.gst 0 ≤ ready
    rw [hready]; have : (0 : Time) ≤ ((accepted_catchUp S A : Nat) : Time) * Q.run.1.Δ := by
      positivity
    linarith
  have hcz := cutZ_fit_of_catchUp A V (accepted_coefficients S A)
    (by rw [accepted_coefficients_catchUp]; exact accepted_catchUp_ge_sleepy S A) Q.run Q.hn Q.gst
  change Healing.cutZ Q.params.toParams Q.gst + D + 1 ≤ max ready 0 + 4 * D at hcz
  rw [hrmax] at hcz
  -- heal and the coefficient budget, in node delays `D = Δe`
  have hheal : max Q.gst 0 + ((K S A).params.heal .final Q.index : Time) * Q.run.1.Δ ≤ Q.query :=
    Q.mature
  have hbud : ((accepted_catchUp S A : Nat) : Time) +
      (20 * (Ld : Time) + 8 * S.k + 28 * S.δt + 28 * X + 56) ≤
      ((K S A).params.heal .final Q.index : Time) := by
    have h := accepted_heal_ge_final S A Q.index
    have he : (K S A).params.heal .final Q.index = accepted_heal S A .final Q.index := by
      simp only [Params.standard, accepted_coefficients_heal]
    rw [he]
    exact_mod_cast h
  set Mf : Time := 20 * (Ld : Time) + 8 * S.k + 28 * S.δt + 28 * X + 56 with hMf
  have hMf0 : 0 ≤ Mf := by rw [hMf]; positivity
  have hq : ready + Mf * D - 1 ≤ Q.query := by
    have h1 := mul_le_mul_of_nonneg_right hbud (by linarith : (0 : Time) ≤ Q.run.1.Δ)
    rw [hready, hDe]; nlinarith
  have hqh : Q.query ≤ Q.run.2.horizon := by
    have := Q.bounded
    have : (0 : Time) ≤ ((K S A).params.latency .final Q.index : Time) * Q.run.1.Δ := by
      positivity
    linarith
  -- the reset bound `B`
  set B := resetBoundRounds ready D (2 * D) Q.params.toParams.fg.δt X Ld with hBdef
  have hBeq : B = ready + (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D := by
    rw [hBdef, resetBoundRounds_eq, hδeq]; ring
  have hk2 : (2 : Time) ≤ S.k := by exact_mod_cast S.two_le_k
  have hX1 : (1 : Time) ≤ X := by exact_mod_cast Q.index.pos
  have hBc : B + (12 * (c : Time) - 2) * D ≤ Q.run.2.horizon := by
    have := final_heal_horizon_fit (k := (S.k : Time)) (Ld := (Ld : Time)) hD (by positivity)
      (Nat.cast_nonneg X) (show 3 * (c : Time) ≤ (S.δt : Time) by exact_mod_cast h3c)
    rw [hBeq]; rw [hMf] at hq; linarith
  have hc2' : (2 : Time) ≤ c := by exact_mod_cast hc2
  have hBh : B ≤ Q.run.2.horizon := by nlinarith
  -- whole-run no restart: a restart is a labelled call, at a time `≤ horizon`
  have hnr : Healing.NoRestartAfter Q.trace H (gbar Q.gst) :=
    fun y hy k hk => hs.noRestart y hy k hk
      (simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid (by
        obtain ⟨ℓ, hc, -⟩ := hk
        obtain ⟨_, hl⟩ := hc
        intro hn
        simp [hn] at hl))
  -- an honest node exists
  have hH : H.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hf := hs.faults
    rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
    have hn := Q.params.toParams.hn
    change 0 < Q.params.n at hn
    have hf' : 3 * Q.params.n ≤ Q.params.n - 1 := hf
    omega
  -- Catch with `κ = 2Δ`
  have hcatch : Healing.CatchRun Q.trace H Q.gst (2 * D) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync S Q.run.2 Q.hn Q.valid
      (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision) hnet Q.healthy.2.1.2
  -- the drain
  have hdrain : DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) H Q.gst X Ld
      Q.run.2.horizon :=
    drainOutputs_of_service hrun hs.noColl hs.sync hs.awake hs.faults hcatch hnr
      (by rw [hLddef, healthyDrainLen_val, hk]; omega)
  -- the reset
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_awake hrun hs.noColl hs.faults hs.sync
    hs.awake hcatch hnr hH (by rw [hδeq]; omega) (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz hBh
    (fun s₀ N hs₀ hN => final_query_gap S A V Q hpat (by rw [hrmax]; exact hs₀) (by
      have : Q.params.ts (N + 3 * c : Nat) = Q.params.ts N + 12 * (c : Time) * D := by
        simp only [SA.SAParams.ts]; push_cast; ring
      rw [this]; linarith))
    hdrain
  have hLd0 : (0 : Time) ≤ Ld := by positivity
  have h4B : ready + 4 * D ≤ B := by
    have : (4 : Time) * D ≤ (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D :=
      mul_le_mul_of_nonneg_right (by linarith) hD.le
    rw [hBeq]; linarith
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake hrun hs.awake hH (b := Q.run.2.horizon)
    (by linarith)
  refine ⟨ΔF, a, ⟨hrun, hs.noColl, hs.sync, hs.awake, hs.faults, ha, hab.trans hBh,
    ⟨j, hj, hjt⟩⟩, ?_⟩
  -- the placement (H3)
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, _, k, _, _, _, hka⟩, _⟩ := ha
    rw [← hka]; exact hrun.time_nonneg k
  have hsa : Q.params.ts (Q.params.slot a : Int) ≤ a :=
    (SA.ts_le_iff_le_slot Q.params ha0 _).2 le_rfl
  have hL : (finalGrid S A V Q).slotLen = 4 * D := by
    have h1 := finalGrid_slotTime S A V Q 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith
  have hseed : (finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) ≤
      a + 4 * D * (2 * S.k + 5) := by
    have hu : finalSeedMin S A V Q a = Q.params.slot a + 2 * S.k + 5 := rfl
    rw [finalGrid_slotTime, hu]
    simp only [SA.SAParams.ts] at hsa ⊢
    rw [← hDdef] at hsa ⊢
    push_cast; linarith
  rw [hL, hrmax]
  push_cast
  have hXδ : (0 : Time) ≤ (X + S.δt) * (4 * D) := by positivity
  apply add_le_of_le_sub_right
  apply max_le
  · have : (4 * (X : Time) + 4 * S.δt) * D ≤ Mf * D := by
      apply mul_le_mul_of_nonneg_right _ hD.le
      rw [hMf]; have : (0 : Time) ≤ Ld := by positivity
      linarith
    linarith
  · have : (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D + 4 * D * (2 * S.k + 5) +
        (X + S.δt) * (4 * D) - 4 * D = Mf * D := by rw [hMf]; ring
    have hab' : a ≤ B := hab
    rw [hBeq] at hab'
    linarith

/-- **The reset premises and the placement of a final query** (the leaf `final_reset_premises`,
Accepted.lean): a reset `a` with its premises through the horizon at GST `Q.gst`, and the
placement `(P)` with `u_min = finalSeedMin Q a`. `final_reset_premises_of_shared` at the gap
`c = cF r` of `finalWindow` and the protocol row delay `ΔF := rowDelay`
(`FinalQuery.hsSharedUpTo`). -/
theorem final_reset_premises_of_query (Q : FinalQuery S A V) :
    ∃ ΔR a : Time,
      Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (family S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGrid S A V Q).slotTime (finalSeedMin S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGrid S A V Q).slotLen ≤
        Q.query + (finalGrid S A V Q).slotLen :=
  final_reset_premises_of_shared S A V Q A.two_le_cF A.timeout (finalWindow_offsets A)
    Q.hsSharedUpTo

end Consensus.Goldilocks.Refinement

end

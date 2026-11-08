module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalDutyProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowAssembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalResetPremises
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Lemmas.Blocks.Facts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset premises and the placement of a final query, under growing faults

The growing form of `Obligations/FinalResetPremises`, with each node honest at its own cut and
the fault bound per time:

* `final_query_gap_at` (`final_query_gap`): the honest-proposer gap of a final query, as the
  kernel's `ProposalGap` (the designated proposer honest through its slot's hold);
* `final_reset_premises_of_shared_at` (`final_reset_premises_of_shared`): from the shared HS
  premises at a forwarding delay `ΔF` and the final pattern `[0, c, 2c, 3c]` with `2 ≤ c` and
  `3c ≤ δ_t`, a reset `a` with its finite premises through the horizon and the placement;
* `final_reset_premises_at`: its instance at the FG gap `c = fgSlots` and the protocol FG delay.

The reset is the growing kernel's `exists_reset_of_drain_rounds_awake_at` on the drain
`drainOutputs_of_service_at`, at the static ready scalar and reset bound; the snapshot is the
static `snapshot_of_awake` on the prefix through the horizon. The coefficient arithmetic is the
static one. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The honest-proposer gap of a final query**, under growing faults: every slot window
`[x₀, x₀ + X)` inside `[s₀, N]` has an actual designated proposal whose proposer is honest
through its slot's hold. -/
theorem final_query_gap_at (Q : FinalQueryAt S A V) {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0 + 4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * c : Nat) ≤ Q.run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (Q.index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ Q.keys (Q.params.ts x + Q.params.Δ) ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (finalGridAt S A V Q) ⟨finalWindow A, Q.index, 1⟩
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ↓reduceIte,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using Q.progress
  have hL : (finalGridAt S A V Q).slotLen = 4 * Q.params.Δ := by
    have h1 := finalGridAt_slotTime S A V Q 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith only [h1]
  have hspan : (finalGridAt S A V Q).slotTime N +
      (((⟨finalWindow A, Q.index, 1⟩ : Recurrence).pattern.span : Nat) : Time) *
        (finalGridAt S A V Q).slotLen = Q.params.ts (N + 3 * c : Nat) := by
    rw [← finalGridAt_slotTime S A V Q, (finalGridAt S A V Q).slotTime_add]
    simp [finalWindow_span_of_offsets S A hpat]
  have hgap := recurrence_gap hrec (by rw [hpat]; simp) (s₀ := s₀) (N := N)
    (by rw [hL, finalGridAt_slotTime]; exact hs) (by rw [hspan]; exact hN)
    (by rw [hspan]; exact hN)
  have hΔ := Q.params.toParams.hΔ
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap x₀ hx₀ hxN
  have hxr : x < x₀ + (Q.index : Nat) := hxr
  have hxN : x₀ + (Q.index : Nat) ≤ N + 1 := hxN
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have hs0 : s₀ = 0 := Nat.eq_zero_of_le_zero (hx₀.trans (hxl.trans h.le))
      subst hs0
      have := le_max_right ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0
      simp only [SA.SAParams.ts] at hs
      push_cast at hs
      linarith only [hs, this, hΔ]
    · exact h
  have hxts : Q.params.ts x ≤ Q.params.ts (N + 3 * c : Nat) :=
    (SA.ts_le_iff Q.params).2 (by exact_mod_cast
      (Nat.le_of_lt_succ (hxr.trans_le hxN)).trans (Nat.le_add_right N (3 * c)))
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := final_duty_proposal_run_at S A V Q hx0 (hxts.trans hN)
    (by simpa using hx)
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

/-- **The reset premises and the placement of a final query, at a forwarding delay `ΔF` and a
gap `c`**, under growing faults. -/
theorem final_reset_premises_of_shared_at (Q : FinalQueryAt S A V) {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {ΔF : Time}
    (hs : Healing.Growing.HSSharedUpTo Q.trace Q.keys (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
        Q.query + (finalGridAt S A V Q).slotLen := by
  classical
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  set H := Q.keys
  let X : Nat := (Q.index : Nat)
  set Ld : Nat := healthyDrainLen S Q.index with hLddef
  set ready := (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run with hreadydef
  set D := Q.params.Δ with hDdef
  have hD : 0 < D := Q.params.toParams.hΔ
  have hDe : D = Q.run.1.ΔAC := rfl
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hk : Q.params.k = S.k := rfl
  -- the ready scalar
  have hC : (Sys (goldilocks S) V).cDur (K S A) Q.run =
      ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC := by
    change (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC = _
    rw [contract_coefficients_catchUp]
  have hready : ready = max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
    rw [hreadydef, ← hC]; rfl
  have hcd : (0 : Time) ≤ ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd)
  have hr0 : 0 ≤ ready := by
    rw [hready]; linarith only [le_max_right Q.gst 0, hcd]
  have hrmax : max ready 0 = ready := max_eq_left hr0
  have hgr : gbar Q.gst ≤ ready := by
    change max Q.gst 0 ≤ ready
    rw [hready]; linarith only [hcd]
  have hcz := cutZ_fit_of_catchUp A V (contract_coefficients S A)
    (by rw [contract_coefficients_catchUp]; exact contract_catchUp_ge_sleepy S A) Q.run Q.hn Q.gst
  change Healing.cutZ Q.params.toParams Q.gst + D + 1 ≤ max ready 0 + 4 * D at hcz
  rw [hrmax] at hcz
  -- heal and the coefficient budget, in node delays `D = Δe`
  have hheal : max Q.gst 0 + ((K S A).params.heal .final Q.index : Time) * Q.run.1.ΔAC ≤ Q.query :=
    Q.mature
  have hbud : ((contract_catchUp S A : Nat) : Time) +
      (20 * (Ld : Time) + 8 * S.k + 28 * S.δt + 28 * X + 56) ≤
      ((K S A).params.heal .final Q.index : Time) := by
    have h := contract_heal_ge_final S A Q.index
    have he : (K S A).params.heal .final Q.index = contract_heal S A .final Q.index := by
      simp only [Params.standard, contract_coefficients_heal]
    rw [he]
    exact_mod_cast h
  set Mf : Time := 20 * (Ld : Time) + 8 * S.k + 28 * S.δt + 28 * X + 56 with hMf
  have hq : ready + Mf * D - 1 ≤ Q.query := by
    have h1 := mul_le_mul_of_nonneg_right hbud (zero_le_one.trans hd)
    rw [hready, hDe]; linarith only [h1, hheal]
  have hqh : Q.query ≤ Q.run.2.horizon := by
    linarith only [Q.bounded, (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd) :
      (0 : Time) ≤ ((K S A).params.latency .final Q.index : Time) * Q.run.1.ΔAC)]
  have hb0 : (0 : Time) ≤ Q.run.2.horizon := by
    have := mul_nonneg (Nat.cast_nonneg (α := Time) ((K S A).params.heal .final Q.index))
      (zero_le_one.trans hd)
    linarith only [hheal, hqh, le_max_right Q.gst 0, this]
  -- the reset bound `B`
  set B := resetBoundRounds ready D (2 * D) Q.params.toParams.fg.δt X Ld with hBdef
  have hBeq : B = ready + (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D := by
    rw [hBdef, resetBoundRounds_eq, hδeq]; ring
  have hk2 : (2 : Time) ≤ S.k := by exact_mod_cast S.two_le_k
  have hX1 : (1 : Time) ≤ X := by exact_mod_cast Q.index.pos
  have hBc : B + (12 * (c : Time) - 2) * D ≤ Q.run.2.horizon := by
    have := final_heal_horizon_fit (k := (S.k : Time)) (Ld := (Ld : Time)) hD (Nat.cast_nonneg _)
      (Nat.cast_nonneg X) (show 3 * (c : Time) ≤ (S.δt : Time) by exact_mod_cast h3c)
    rw [hBeq]; rw [hMf] at hq; linarith only [this, hq, hqh]
  have hc2' : (2 : Time) ≤ c := by exact_mod_cast hc2
  have hBh : B ≤ Q.run.2.horizon := by
    linarith only [hBc, mul_nonneg (show (0 : Time) ≤ 12 * c - 2 by linarith only [hc2']) hD.le]
  -- whole-run no restart: a restart is a labelled call, at a time `≤ horizon`
  have hnr : Healing.Growing.NoRestartAfter Q.trace H (gbar Q.gst) :=
    fun y k hy hk => hs.noRestart y k hy hk (by
      obtain ⟨ℓ, hc, -⟩ := hk
      obtain ⟨_, hl⟩ := hc
      have hl' : (simTrace S Q.run.2 Q.hn).label k ≠ none := by
        rw [← simTraceAt_eq S Q.run.2 Q.hn]
        exact fun h => by rw [h] at hl; cases hl
      have h := simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid hl'
      rwa [← simTraceAt_eq S Q.run.2 Q.hn] at h)
  -- an honest node exists
  have hH : (H Q.run.2.horizon).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hf := hs.faults Q.run.2.horizon hb0 le_rfl
    rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
    have hn := Q.params.toParams.hn
    change 0 < Q.params.n at hn
    have hf' : 3 * Q.params.n ≤ Q.params.n - 1 := hf
    exact lt_irrefl _ (hf'.trans_lt
      ((Nat.sub_lt hn Nat.one_pos).trans_le (Nat.le_mul_of_pos_left _ (by decide))))
  -- Catch with `κ = 2Δ`
  have hcatch : Healing.Growing.CatchRun Q.trace H Q.gst (2 * D) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync_at S Q.run.2 Q.hn Q.valid hs.noColl hnet
      (fun v t ht hb _ hv => Q.healthy.2.1.2 v t ht hb hv)
  -- the drain
  have hdrain : Healing.Growing.DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) H Q.gst X Ld
      Q.run.2.horizon :=
    Healing.Growing.drainOutputs_of_service_at hrun hs.noColl hs.sync hs.awake hs.faults hcatch
      hnr
      (by rw [hLddef, healthyDrainLen_val, hk]; exact Nat.le_succ _)
  -- the reset
  obtain ⟨a, ha, hab⟩ := Healing.Growing.exists_reset_of_drain_rounds_awake_at hrun hs.noColl
    hs.faults hs.sync hs.awake hcatch hnr hH
    (by rw [hδeq]; exact (Nat.le_mul_of_pos_right 3 ((by decide : 0 < 2).trans_le hc2)).trans h3c)
    (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz hBh
    (fun s₀ N hs₀ hN => Healing.Growing.proposalGap_iff.mpr <| final_query_gap_at S A V Q hpat
      (by rw [hrmax]; exact hs₀) (by
      have : Q.params.ts (N + 3 * c : Nat) = Q.params.ts N + 12 * (c : Time) * D := by
        simp only [SA.SAParams.ts]; push_cast; ring
      rw [this]; linarith only [hN, hBc]))
    hdrain
  have hLd0 : (0 : Time) ≤ Ld := Nat.cast_nonneg _
  have h4B : ready + 4 * D ≤ B := by
    have : (4 : Time) * D ≤ (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D :=
      mul_le_mul_of_nonneg_right (by linarith only [hLd0, hX1, Nat.cast_nonneg (α := Time) S.δt])
        hD.le
    rw [hBeq]; linarith only [this]
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake (hrun.upTo hb0)
    (fun y hy t ht htb => ⟨hs.awake y t (hrun.antitone htb hy) ht htb, htb⟩) hH
    (b := Q.run.2.horizon) (by linarith only [hcz, h4B, hBh])
  refine ⟨ΔF, a, ⟨hrun, hs.noColl, hs.sync, hs.awake, hs.faults, ha, hab.trans hBh,
    ⟨j, hj, hjt⟩⟩, ?_⟩
  -- the placement (H3)
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := ha
    rw [← hka]; exact hrun.time_nonneg k
  have hsa : Q.params.ts (Q.params.slot a : Int) ≤ a :=
    (SA.ts_le_iff_le_slot Q.params ha0 _).2 le_rfl
  have hL : (finalGridAt S A V Q).slotLen = 4 * D := by
    have h1 := finalGridAt_slotTime S A V Q 1
    simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
    push_cast at h1
    linarith only [h1]
  have hseed : (finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) ≤
      a + 4 * D * (2 * S.k + 5) := by
    have hu : finalSeedMinAt S A V Q a = Q.params.slot a + 2 * S.k + 5 := rfl
    rw [finalGridAt_slotTime, hu]
    simp only [SA.SAParams.ts] at hsa ⊢
    rw [← hDdef] at hsa ⊢
    push_cast; linarith only [hsa]
  rw [hL, hrmax]
  push_cast
  apply add_le_of_le_sub_right
  apply max_le
  · have : (4 * (X : Time) + 4 * S.δt) * D ≤ Mf * D := by
      apply mul_le_mul_of_nonneg_right _ hD.le
      rw [hMf]
      linarith only [hLd0, Nat.cast_nonneg (α := Time) S.k, Nat.cast_nonneg (α := Time) S.δt,
        Nat.cast_nonneg (α := Time) X]
    have h1D : (1 : Time) ≤ D := hD
    linarith only [this, hq, h1D]
  · have : (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D + 4 * D * (2 * S.k + 5) +
        (X + S.δt) * (4 * D) - 4 * D = Mf * D := by rw [hMf]; ring
    have hab' : a ≤ B := hab
    rw [hBeq] at hab'
    linarith only [this, hab', hseed, hq]

/-- **The reset premises and the placement of a final query**, under growing faults. -/
theorem final_reset_premises_at (Q : FinalQueryAt S A V) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt S A V Q).slotTime (finalSeedMinAt S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) * (finalGridAt S A V Q).slotLen ≤
        Q.query + (finalGridAt S A V Q).slotLen :=
  final_reset_premises_of_shared_at S A V Q A.two_le_fgSlots A.timeout (finalWindow_offsets A)
    (FinalQueryAt.hsSharedUpTo_at Q)

end Consensus.Goldilocks.Obligations.Growing

end

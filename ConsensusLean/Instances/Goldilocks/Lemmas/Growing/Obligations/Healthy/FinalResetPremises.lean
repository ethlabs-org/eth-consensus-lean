module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalDutyProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Supply.Fields
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalQueryTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HonestNonempty
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.BoundariesCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset premises and the placement of a final query, under growing faults

Each node is honest at its own cut and the fault bound is per time:

* `final_query_gap_at`: the honest-proposer gap of a final query, as the
  kernel's `ProposalGap` (the designated proposer honest through its slot's hold);
* `final_reset_premises_of_shared_within_at`: from the shared HS premises at a forwarding delay
  `ΔF` and release hold `RΔ`, the final pattern `[0, c, 2c, 3c]` with `2 ≤ c` and `3c ≤ δ_t`, and
  a vote latency `d`, a reset `a` with its finite premises through the horizon and the placement.

The reset is the healing supplier's real-time reset `Generic.exists_reset_within` at the
canonical supplier `goldilocks_ac_healing`, on the honest sets truncated after the horizon; the
snapshot is the static `snapshot_of_awake` on the prefix through the horizon. The ready scalar,
the reset bound, the horizon of the gap and the placement are the static
`final_reset_bounds_within`,
the duties of the gap the static `final_query_duty`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape
open AC (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The honest-proposer gap of a final query**, under growing faults: every slot window
`[x₀, x₀ + X)` inside `[s₀, N]` has an actual designated proposal whose proposer is honest
through its slot's hold. -/
theorem final_query_gap_at
    (Q : FinalQueryAt S A V) {c : Nat}
    (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0 +
      4 * Q.params.Δ ≤
      Q.params.ts s₀)
    (hN : Q.params.ts (N + 3 * c : Nat) ≤ Q.run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (Q.index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ Q.keys (Q.params.ts x + Q.params.Δ) ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧
        P.slot = x := by
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx0, hxh, hx⟩ :=
    final_query_duty S A V Q.run Q.hn Q.index Q.gst Q.progress hpat hs hN x₀ hx₀ hxN
  obtain ⟨k, P, hP, hk, -, -, hPs, -⟩ := final_duty_proposal_run_at S A V Q hx0 hxh hx
  exact ⟨x, hxl, hxr, hP.1, k, P, hk, hPs⟩

/-- **The reset premises and the placement of a final query, at a forwarding delay `ΔF` and a
gap `c`**, under growing faults. -/
theorem final_reset_premises_of_shared_within_at
    (Q : FinalQueryAt S A V)
    {c : Nat} (hc2 : 2 ≤ c)
    (h3c : 3 * c ≤ S.δt) (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {ΔF : Time}
    (hs : Healing.Growing.HSSharedUpTo Q.trace Q.keys
      (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon ((A.releaseGap : Time) * Q.params.Δ))
    {d : Time} {L : Nat} (hd0 : 0 ≤ d) (hdL : d ≤ (L : Time) * Q.run.1.ΔAC)
    {Gs : Nat} (hGsA : Gs ≤ A.signGap)
    (hmature : (Sys (goldilocks S) V).heal (K S A) .final Q.index Q.gst Q.run +
      5 * (L : Time) * Q.run.1.ΔAC ≤ Q.query)
    (hlat : Generic.VoteLatencyAt Q.trace Q.keys d)
    (htimeout : 6 * Q.params.Δ + (d + (Gs : Time) * Q.params.Δ) + ΔF ≤
      4 * Q.params.Δ * (S.δt : Time))
    {sign : Fin Q.params.n → Time → Bool}
    (hcal : Q.trace.SignCalendarAt (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys sign)
    (hgap : SignGapAt Q.params.toParams sign Gs 0)
    (hδG : 3 + (Gs + 3) / 4 ≤ Q.params.toParams.fg.δt)
    (hd5 : 5 * d + 1 ≤ 20 * Q.params.Δ)
    (hcover : ∀ a T, Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a T
        (runCommittee S Q.run.2 Q.hn) (K S A).params.βK ((A.releaseGap : Time) * Q.params.Δ) →
      (∀ D, Q.params.deepDepth = some D →
        T ≤ Healing.cutZ Q.params.toParams Q.gst + 4 * D * Q.params.Δ) →
      Healing.drainTime Q.params a + 4 * Q.params.Δ ≤ T → T ≤ Q.run.2.horizon →
      Healing.Growing.HighSourceCover Q.trace Q.keys Q.gst a Q.run.2.horizon) :
    ∃ ΔR a : Time,
      Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst ΔR a Q.run.2.horizon
        (runCommittee S Q.run.2 Q.hn) (K S A).params.βK ((A.releaseGap : Time) * Q.params.Δ) ∧
      max (max ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run) 0)
          ((finalGridAt
            S A V Q).slotTime
            (finalSeedMinAt
            S A V Q a) - 1) +
          ((((Q.index : Nat) + S.δt : Nat) : Time)) *
          (finalGridAt S A V
          Q).slotLen ≤
        Q.query + (finalGridAt
            S A V Q).slotLen := by
  classical
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  set H := Q.keys
  have hD : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hk : Q.params.k = S.k := rfl
  have hGD : (0 : Time) ≤ (Gs : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hD.le
  obtain ⟨hr0, hgr, hcz, h4B, hBh, hgapN, hplace⟩ :=
    final_reset_bounds_within S A V Q.run Q.hn Q.index Q.gst Q.query (d := d + Gs * Q.params.Δ)
      (L := L + Gs) (by linarith only [hd0, hGD])
      (by change _ ≤ _ * Q.params.Δ at hdL; change _ ≤ _ * Q.params.Δ; push_cast
          linarith only [hdL])
      (by have hG : (Gs : Time) ≤ (A.signGap : Time) := by exact_mod_cast hGsA
          have := Q.run.1.ΔAC_pos
          push_cast; nlinarith) Q.bounded hc2 h3c
  have hb0 : (0 : Time) ≤ Q.run.2.horizon := by linarith only [hr0, h4B, hBh, hD]
  have hH : (H Q.run.2.horizon).Nonempty :=
    nonempty_of_fault_bound (hs.faults Q.run.2.horizon hb0 le_rfl) Q.params.toParams.hn
  have hstart := simIni_eq_runStart S Q.run.2 Q.hn Q.valid ▸ hrun
  have hfacts := runCommittee_facts S Q.run.2 Q.hn Q.valid hs.noColl
  have hβ : (K S A).params.βK ≤ 1 / 2 := by
    rw [goldilocksContract_params_eq]; exact le_rfl
  have hcf := committeeFaultsUpTo_of_healthyOn S Q.run.2 Q.hn Q.valid Q.healthy.2.2.2
  -- Catch with `κ = 2Δ`
  have hcatch : Healing.Growing.CatchRun Q.trace H Q.gst (2 * Q.params.Δ) := by
    have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
      (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
    exact catchRun_of_psync_at S Q.run.2 Q.hn Q.valid hs.noColl hnet
      (fun v t ht hb _ hv => Q.healthy.2.1.2 v t ht hb hv)
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake (hrun.upTo hb0).toLocalRun
    (fun y hy t ht htb => ⟨hs.awake y t (hrun.antitone htb hy) ht htb, htb⟩) hH
    (b := Q.run.2.horizon) (by linarith only [hcz, h4B, hBh])
  -- the reset of the healing supplier, under latency `d`
  have hgrid : ∀ s : Nat, Q.params.toParams.slotTime s = (s : Time) * (4 * Q.params.Δ) :=
    fun s => by rw [Q.params.slotTime_eq]; ring
  obtain ⟨R, O, hRd, hW, -, hG, -⟩ := Generic.goldilocks_ac_healing (sp := Q.params)
    (sign := sign) (G := Gs) (Rg := A.releaseGap) hδG
  have hRun : R.Run (runCommittee S Q.run.2 Q.hn) (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) Q.keys Q.trace := by
    rw [hRd.1]
    exact ⟨hstart, S.committeeSize_pos _ Q.hn, runCommittee_ncard S Q.run.2 Q.hn Q.valid,
      runCommittee_facts S Q.run.2 Q.hn Q.valid, hcal, hgap⟩
  have hPr := Generic.premises_truncH (b := Q.run.2.horizon)
    (sg := fun v : (goldilocksNode Q.params).Msg => v.val)
    (proposer := runProposer S Q.run.2 Q.hn) hcf hs.noColl
    ⟨hs.sync.deltaF, hs.sync.message, hs.sync.block, hs.sync.relay, hs.sync.signedRow,
      hs.sync.hold_le⟩ hs.awake hs.faults hcatch
    (fun y k hy hr hk => hs.noRestart y k hy hr hk)
    ((Generic.timeout_grid_equation _ hgrid).mpr hs.timeoutDelay)
    (Generic.slotLen_of_grid hgrid) ⟨j, hj, hjt⟩ hH
  -- the supplier's four-attempt bound is within the reset bound
  have hB4 : (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run +
      (16 * (healthyDrainLen S Q.index : Time) +
        24 * ((Q.params.toParams.δt + (Q.index : Nat) - 1 : Nat) : Time) + 52) * Q.params.Δ +
      4 * (d + (Gs : Time) * Q.params.Δ) ≤
      (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run +
        (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        5 * (d + (Gs : Time) * Q.params.Δ) := by
    have hX := Q.index.1.pos
    have hρ : ((Q.params.toParams.δt + (Q.index : Nat) - 1 : Nat) : Time) =
        (S.δt : Time) + ((Q.index : Nat) : Time) - 1 := by
      rw [Nat.cast_sub (by change 1 ≤ S.δt + _; omega)]; push_cast; rfl
    have hL0 : (0 : Time) ≤ (healthyDrainLen S Q.index : Time) * Q.params.Δ := by positivity
    rw [hρ, healthyResetCoeff_val]
    push_cast
    nlinarith only [hL0, hD, hd0, hGD]
  obtain ⟨a, ha, hab⟩ := Generic.exists_reset_within O (Gp := (Q.index : Nat))
    (L := healthyDrainLen S Q.index) hβ hgrid hRun hPr hlat hd0
    (by rw [hG]; exact htimeout) Q.index.1.pos
    (by rw [hW, healthyDrainLen_val, hk]; omega) hgr hcz
    (fun s₀ N hs₀ hN => by
      rw [hG] at hN
      intro c hc hcN
      obtain ⟨x, hxl, hxr, hx, hP⟩ := final_query_gap_at S A V Q hpat
        (by rw [max_eq_left hr0]; exact hs₀) (hgapN N (by
          rw [Q.params.slotTime_eq] at hN
          simp only [AC.ACParams.ts]
          linarith only [hN, hB4])) c hc hcN
      have hts : Q.params.toParams.slotTime x = Q.params.ts (x : Int) := by
        rw [Q.params.slotTime_eq]; simp only [AC.ACParams.ts]
      exact ⟨x, hxl, hxr, by rw [hts]; exact hx, hP⟩)
    (by rw [hG]; linarith only [hB4, hBh])
  rw [hG] at hab
  replace hab := hab.trans hB4
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := ha
    rw [← hka]; exact hrun.time_nonneg k
  -- the drain of the reset ends before the deep quarantine (`DeepAdmits` of the index)
  have hdrain : ∀ D, Q.params.deepDepth = some D →
      Healing.drainTime Q.params a + 4 * Q.params.Δ ≤
        Healing.cutZ Q.params.toParams Q.gst + 4 * D * Q.params.Δ := by
    intro D hD
    have hadm := Q.index.2 D hD
    rw [healMargin_val, healthyDrainLen_val] at hadm
    have hadm' : ((11 + (20 * (2 * S.k + (Q.index.1 : Nat)) + 8 * S.k + 28 * S.δt +
        28 * (Q.index.1 : Nat) + 56 + 5 * A.signGap) : Nat) : Time) ≤ ((4 * D : Nat) : Time) := by
      exact_mod_cast hadm
    push_cast at hadm'
    have hready : (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run =
        max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
      change max Q.gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC +
        1 = _
      rw [contract_coefficients_catchUp]
    rw [contract_catchUp_val] at hready
    have hDe : Q.params.Δ = Q.run.1.ΔAC := rfl
    have hz := Healing.lt_cutZ Q.params Q.gst
    have hgb : AC.gbar Q.gst = max Q.gst 0 := rfl
    have hsa : Q.params.ts (Q.params.slot a : Int) ≤ a :=
      (AC.ts_le_iff_le_slot Q.params ha0 _).2 le_rfl
    have hdr : Healing.drainTime Q.params a =
        Q.params.ts (Q.params.slot a : Int) + 4 * Q.params.Δ * (2 * (Q.params.k : Time) + 5) := by
      rw [Healing.drainTime_eq]; simp only [AC.ACParams.ts]; push_cast; ring
    have hδ6 : (6 : Time) ≤ S.δt := by exact_mod_cast A.six_le_δt
    have hX1 : (1 : Time) ≤ (Q.index.1 : Nat) := by exact_mod_cast Q.index.1.pos
    have hGs : (Gs : Time) ≤ A.signGap := by exact_mod_cast hGsA
    have hΔ0 : (0 : Time) ≤ Q.params.Δ :=
      (show (0 : Time) < Q.params.Δ from Q.params.toParams.hΔ).le
    -- the linear facts in `Δ`-units
    have e1 := mul_le_mul_of_nonneg_right hadm' hΔ0
    have e2 := mul_le_mul_of_nonneg_right hδ6 hΔ0
    have e3 := mul_le_mul_of_nonneg_right hX1 hΔ0
    have e4 := mul_le_mul_of_nonneg_right hGs hΔ0
    rw [healthyResetCoeff_val, healthyDrainLen_val] at hab
    rw [hdr]
    have hkk : (Q.params.k : Time) = S.k := by exact_mod_cast hk
    have hmax : max Q.gst 0 = AC.gbar Q.gst := rfl
    rw [hready, hmax, ← hDe] at hab
    rw [hkk]
    push_cast at hab
    generalize Healing.cutZ Q.params.toParams Q.gst = z at hz ⊢
    generalize Q.params.ts (Q.params.slot a : Int) = w at hsa ⊢
    ring_nf at hab e1 e2 e3 e4 hz ⊢
    linarith
  refine ⟨ΔF, a, Healing.Growing.resetPremisesUpTo_of_reset_cover_at
    hstart hs.noColl hs.sync
    hs.awake hs.faults ha ha0 (hab.trans hBh) ⟨j, hj, hjt⟩ hcatch
    (Healing.Growing.noRestartUpTo_iff.mpr hs.noRestart) (by rw [hδeq]; exact hs.timeoutDelay) hH
    hfacts hβ (S.committeeSize_pos (Model.pubOf Q.run.1) Q.hn) hcf hdrain (hcover a), ?_⟩
  -- the placement (H3)
  exact hplace a ha0 hab

end Consensus.Goldilocks.Obligations.Growing

end

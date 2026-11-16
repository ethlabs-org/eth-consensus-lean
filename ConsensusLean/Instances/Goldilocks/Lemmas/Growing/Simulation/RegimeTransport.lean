module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.SleepyWindows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.ServiceEquivalence
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Regime transport at the canonical run map

`goldilocks_regimeTransport`: at the local data equations and the endpoint contract `K S A`, the
canonical run map transports the three regime rows.

* **sleepy**: the finite sleepy service from `SyncUntil` (`sleepyServiceBefore_of_syncUntil_at`),
  read as the AC-owned retained-evidence service of the local supplier, and the slot counts at
  the look-ahead `5Δ` (`sleepy_faultBoundAt`);
* **healthy**: the generic `Service` from partial synchrony (`healthy_preparation_service_at`),
  full participation (`healthy_preparation_awake_at`), the population bound through the
  validator map, and the committee bound (`committeeFaultsUpTo_of_healthyOn`);
* **ready**: engine readiness at a cut is a ready read at its mapped cut.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic Obligations
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The regime rows of the canonical run map at the local data equations and `K S A`. -/
theorem goldilocks_regimeTransport (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    (hsg : (fun v => v.val) = (goldilocksRunMap S rho hn hv).signer) :
    RegimeTransport (goldilocksRunMap S rho hn hv) (K S A) (hsg ▸ C) := by
  classical
  obtain ⟨es, el, -⟩ := local_data_cast hsg C
  obtain ⟨-, -, -, hl, -, -, -, -, -, -, -, -, -, hserved⟩ := hC
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  refine ⟨?_, ?_, ?_⟩
  · -- sleepy
    intro hv' hc hs
    have hd : Regimes.catchUp (S.params (pubOf E) hn) ≤ (Sys (goldilocks S) V).cDur (K S A)
        ⟨E, rho⟩ := by
      have hc19 : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
        exact_mod_cast contract_catchUp_ge_sleepy S A
      have hd1 : (1 : Time) ≤ E.ΔAC := E.ΔAC_pos
      simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
      change 18 * E.ΔAC ≤ (contract_catchUp S A : Nat) * E.ΔAC
      nlinarith
    have hnc := noCollRun_simTraceAt S rho hn hv' hc
    have hsync := sleepyServiceBefore_of_syncUntil_at S rho hn hv' hnc le_rfl
      (sleepy_raw_syncUntil S A V ⟨E, rho⟩ hv' hs rho.horizon)
    have hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
        (5 * (S.params (pubOf E) hn).Δ) 0 rho.horizon :=
      Growing.sleepyOn_of_duration V _ hd hs.2.1
    have h0 : 0 ≤ rho.horizon :=
      (cutTime_bounds S rho hv' (Nat.zero_le _)).1.trans
        (cutTime_bounds S rho hv' (Nat.zero_le _)).2
    simp only [goldilocksRunMap_trace, goldilocksRunMap_honest]
    refine ⟨h0, ⟨E.ΔFG_pos, ?_, ?_⟩, ?_⟩
    · intro x i m hx hm hi0 y j ℓ hy hcall hdb hdl
      have hsrc : (simTraceAt S rho hn).projAC.SendOrAdmit x i m := by
        obtain ⟨ℓ₀, hc₀, hm₀⟩ := hm
        refine ⟨ℓ₀, Compose.projAC_callAt.mpr hc₀, ?_⟩
        rw [Compose.Growing.projAC_state_at hrun hx]
        exact hm₀
      have h := hsync.message x i m hx hsrc hi0 y j ℓ hy (Compose.projAC_callAt.mpr hcall)
        (by rw [Compose.projAC_deadline]; exact hdb) (by rw [Compose.projAC_deadline]; exact hdl)
      rw [es, hserved]
      exact (SA.FamilyFacts.messageServedBefore_iff_old ..).mpr h
    · exact hsync.relay
    · intro s d hd' hsd
      have hd0 : 0 ≤ d := by
        rcases hd' with rfl | rfl | rfl
        · exact le_rfl
        · exact hΔ.le
        · change 0 ≤ 2 * (S.params (pubOf E) hn).Δ
          linarith
      have ht0 : 0 ≤ (S.params (pubOf E) hn).toParams.slotTime s + d := by
        have : (0 : Time) ≤ (S.params (pubOf E) hn).toParams.slotTime s := by
          change (0 : Time) ≤ 4 * E.ΔAC * (s : Time)
          have := E.ΔAC_pos
          positivity
        linarith
      rw [el, hl]
      exact Growing.sleepy_faultBoundAt S rho hn hv' le_rfl hhalf ht0 ht0 hsd
  · -- healthy
    intro hv' hc g hh
    obtain ⟨hnet, hon, -, hcom⟩ := hh
    have hs := Obligations.Growing.healthy_preparation_service_at (S := S) ⟨E, rho⟩ hn hv' hc
      le_rfl hnet
    rw [protoFGDelay_eq] at hs
    simp only [goldilocksRunMap_trace, goldilocksRunMap_honest, goldilocksRunMap_committee]
    have hfaults : ∀ d, 0 ≤ d → d ≤ rho.horizon →
        (honestKeysAt S rho d)ᶜ.ncard = (rho.faultyAt d).card := by
      intro d _ hdb
      have heq : (honestKeysAt S rho d)ᶜ = rho.key ⁻¹' (↑(rho.faultyAt d) : Set V) := by
        ext k
        simp [mem_honestKeysAt_iff, min_eq_left hdb]
      rw [heq, Set.ncard_preimage_of_injective_subset_range rho.key.injective
        (by simp [rho.key.surjective.range_eq]), Set.ncard_coe_finset]
    refine ⟨Healing.Growing.ResetService.toService hs,
      fun y t hgt htb hy =>
        Obligations.Growing.healthy_preparation_awake_at (S := S) ⟨E, rho⟩ hn le_rfl hon y t hy
          hgt htb, ?_, committeeFaultsUpTo_of_healthyOn S rho hn hv' hcom⟩
    intro d hd0 hdb
    rw [hfaults d hd0 hdb]
    have hle : ((rho.faultyAt d).card : ℚ) ≤ (rho.faultyAt rho.horizon).card := by
      exact_mod_cast Finset.card_le_card (rho.faultyAt_mono hdb)
    have hf := hon.1
    change ((rho.faultyAt rho.horizon).card : ℚ) < (K S A).params.β * Fintype.card V at hf
    change _ < (K S A).params.β * (Fintype.card V : ℚ)
    linarith
  · -- ready
    intro c v i hi hr
    obtain ⟨h0, hh⟩ := cutTime_bounds S rho hv hi
    have hrd := Growing.ready_transport_at S rho hn hv h0 hh hr
    obtain ⟨hy, ⟨hb, ha⟩, h0', hh'⟩ :=
      (goldilocksRunMap_engineReadPoint S rho hn hv).honest hv v i hi hr.1
    refine ⟨hy, hb, ha, h0', hh', fun u hu hut => ?_⟩
    rw [goldilocksRunMap_trace, goldilocksRunMap_validator]
    exact hrd.2 u hu hut

end Consensus.Goldilocks.Simulation

end

module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Endpoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Query
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Read
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Handover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Proofs.Behaviour.Main
import ConsensusLean.Lemmas.Problem.Facts.Transfer
import ConsensusLean.Lemmas.Blocks.Facts
import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Continued safety after a hand-over

`continued_safe_growing`, the `continuedSafe` claim of `Continues` for Goldilocks: on a valid
run that hands over at `T ≥ heal` with progress on `[ready, heal]`, ready readers of the available
and the stable output are safe from the heal point, or the run has a hash collision.

* At or after the horizon the hand-over is the healthy regime (`continued_safe_past_horizon`).
* Before the horizon the run is a healed-safety query bounded at `T` (`handoverQuery`). Its seed
  and seeded invariant (`handover_invariant_at`) start reading at `t₁` with `t₁ + 8Δ + 1 ≤ heal`.
  The invariant's premises through the horizon come from the run: the reset service from partial
  synchrony (`resetService_of_psync_at`), the slot counts from `r` from the sleepy budget, which
  full participation on `[ḡ, T]` extends back to `ready` (`Handover.sleepyOn_from_ready`,
  `sleepy_bounds_at`, with `ready ≤ t_r + Δ` by the seed's timing), and conviction below a third
  on held chains from `ConvictedBelow` (`chainConvictedBelow_at`). The trace is then ready-safe
  from `heal − 1` with catch-up `cDur − 1 ≥ 18Δ` (`continued_safe_on_at`), the engine's confirmed
  output from `heal` with catch-up `cDur` (`continued_safe_engine_at`), and the ledger trace as its
  image under `ledgerOf`. -/

namespace Consensus.Goldilocks

open AsChainShape Simulation
open Blocks Shape

/-- **`continuedSafe`**: on a valid run that hands over at `T` with `heal ≤ T` and progress on
`[ready, heal]`, the available and the stable output are ready-safe from the heal point, or the
run has a hash collision. -/
theorem continued_safe_growing (hc : GoldilocksCorrect) (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    ∀ cap g, (cap = .available ∨ cap = .stable) → Sy.schema.output cap = some g →
      ∀ i gst T, Sy.Holds
        (fun r => Sy.Handover K gst T r ∧ Sy.heal K cap i gst r ≤ T ∧
          Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K gst r)
            (Sy.heal K cap i gst r) r)
        (fun r => (Sy.trace r).ReadySafe (Sy.cDur K r) g (Sy.heal K cap i gst r)) := by
  intro Sy K cap g hcap hg i gst T r hv ⟨hh, hhT, hp⟩
  rcases le_total (Sy.pt r).horizon T with hT | hT
  · exact continued_safe_past_horizon hc S A V cap g hcap hg i gst T r hv hh hT hp
  obtain ⟨E, rho⟩ := r
  by_cases hx : rho.HashCollision
  · exact Or.inr hx
  left
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst hg'
  by_cases hn : 1 ≤ Fintype.card V
  swap
  · have hempty : IsEmpty V :=
      Fintype.card_eq_zero_iff.mp (Nat.lt_one_iff.mp (Nat.lt_of_not_le hn))
    exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩
  change (Sy.trace ⟨E, rho⟩).ReadySafe _ _ _
  rw [show Sy.trace ⟨E, rho⟩ = _ from ledgerTrace rho]
  refine Trace.ReadySafe.map ledgerOf_prefix ?_
  have hΔ : (1 : Time) ≤ E.ΔAC := E.ΔAC_pos
  have hcD : Sy.cDur K ⟨E, rho⟩ = 19 * E.ΔAC := by
    simp only [Sy, K, System.cDur, Params.standard, Obligations.contract_coefficients_catchUp]
    change ((contract_catchUp S A : Nat) : Time) * E.ΔAC = _
    rw [Obligations.contract_catchUp_val]
    norm_num
  -- the query bounded at `T`, its seed and seeded invariant
  obtain ⟨h0, hb, hp'⟩ := Obligations.Growing.handover_query_at hn hv hx hcap hh hT hhT hp
  obtain ⟨r', σ, hseed, t₁, -, hdt, hlate, hinv⟩ :=
    Obligations.Growing.handover_invariant_at
      (Obligations.Growing.handoverQuery S A V hn hv hx hcap i hh hT) h0 hb hp'
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ rho hn hv hx
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ rho hn hv
  -- the reset service through the horizon, from partial synchrony
  have hsvc := Obligations.Growing.resetService_of_psync_at S rho hn hv hnc
    ((Model.sysOf_delivers_iff _ _ _ _).mp hh.1)
    (Obligations.Growing.signed_row_service_psync_at S rho hn hv)
    (Obligations.protoFGDelay_pos _)
  -- the slot counts from `r'` through the horizon, from the sleepy budget from `ready`
  let sp := S.params (Model.pubOf E) hn
  obtain ⟨hσT, hrσ, hgr⟩ : sp.ts σ + 8 * sp.Δ ≤ T ∧ r' + sp.k ≤ σ + 1 ∧
      max gst 0 + 20 * sp.Δ ≤ sp.ts r' := hseed.timing
  have hready : Sy.ready K gst ⟨E, rho⟩ = max gst 0 + 19 * E.ΔAC + 1 := by
    change max gst 0 + Sy.cDur K ⟨E, rho⟩ + 1 = _
    rw [hcD]
  have hlate' : t₁ + 8 * sp.Δ + 1 ≤ Sy.heal K cap i gst ⟨E, rho⟩ := hlate
  have hrT : sp.ts r' + sp.Δ ≤ T := by
    have h1 := Compose.ts_le_ts (sp := sp) (show r' ≤ σ by have := sp.two_le_k; omega)
    have : 0 ≤ sp.Δ := sp.toParams.hΔ.le
    linarith
  have hσr : Sy.ready K gst ⟨E, rho⟩ ≤ sp.ts r' + sp.Δ := by
    rw [hready]
    linarith
  have hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp sp)
      (5 * sp.Δ) (Sy.ready K gst ⟨E, rho⟩) rho.horizon := by
    have hs := hh.sleepyOn_from_ready hT (by change (1 / 2 : ℚ) ≤ 1; norm_num)
    intro t ht htb
    refine Obligations.half_ready_of_duration V _ ?_ (hs t ht htb)
    change 18 * E.ΔAC ≤ Sy.cDur K ⟨E, rho⟩
    rw [hcD]
    linarith
  have hB := Obligations.Growing.sleepy_bounds_at ⟨S, stock⟩ rho hn hv le_rfl hhalf hσr
    (le_max_of_le_left ((hσr.trans hrT).trans hT))
  -- conviction below a third on held chains
  have hcv := Obligations.Growing.chainConvictedBelow_at S A rho hn hv hh.2.2.2.2
  have hinv' := hinv rho.horizon hT hsvc hB hcv
  -- the trace, then the engine
  have hc1 : Regimes.catchUp sp ≤ Sy.cDur K ⟨E, rho⟩ - 1 := by
    change 18 * E.ΔAC ≤ _
    rw [hcD]
    linarith
  have hsafe := Compose.Growing.continued_safe_on_at hrun hnc hseed hsvc hB hinv' hdt
    (t₀ := Sy.heal K cap i gst ⟨E, rho⟩ - 1) (by linarith) hc1
  have heng := Obligations.Growing.continued_safe_engine_at S rho hn hv hnc
    (by rw [hcD]; linarith) hsafe
  rw [sub_add_cancel, sub_add_cancel] at heng
  exact heng

end Consensus.Goldilocks

end

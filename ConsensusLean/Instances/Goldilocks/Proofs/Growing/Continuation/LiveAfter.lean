module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Live
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Query
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Continuation.Handover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Proofs.Behaviour.Main
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Continued liveness after the hand-over time

`continued_live_after_handover`: on a valid run that hands over at `T ≥ heal` with progress on
`[ready, horizon]`, the `TxLive` conclusion of `continuedLive` for every deadline after `T`, or the
run has a hash collision. Deadlines up to `T` are the healthy prefix's
(`continued_live_upTo_handover`).

Each query `q ≥ heal` with deadline `> T` is a confirmed query in the hand-over regime
(`handover_query_regime`). Its proposal liveness (`continued_proposal_live_at`) takes the seed and
the read start `t₁` of the seeded invariant of the hand-over query bounded at `T`
(`handover_invariant_at`: `t_{r+k} ≤ t₁`, `t₁ + 8Δ + 1 ≤ heal ≤ q`), the reset service from
partial synchrony (`resetService_of_psync_at`), the slot counts from `r` from the sleepy budget
from `ready` (`sleepy_bounds_at`), conviction below a third on held chains
(`chainConvictedBelow_at`), all restricted to the deadline, and `ready ≤ t_r ≤ t₁ ≤ q` from the
seed's timing. The payload bridge for the deadlines after `T` (`proposalLive_txLive_above`) gives
the transaction reads. -/

namespace Consensus.Goldilocks

open AsChainShape Simulation
open Blocks Shape

/-- **`continuedLive` after the hand-over time**: on a valid run that hands over at `T` with
`heal ≤ T` and progress on `[ready, horizon]`, a transaction submitted at `t` is read by every
ready reader of the available and the stable output at every deadline
`t' ∈ [max t heal + ΔAC + lat, horizon]` with `T < t'`, or the run has a hash collision. -/
theorem continued_live_after_handover (S : Setup) (A : ContractAssumptions S) (V : Type)
    [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    ∀ cap g, (cap = .available ∨ cap = .stable) → Sy.schema.output cap = some g →
      ∀ i gst T r, Sy.Valid r → Sy.Handover K gst T r → Sy.heal K cap i gst r ≤ T →
        Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K gst r) (Sy.pt r).horizon r →
        (∀ x t t', (Sy.pt r).SubmittedToSome x t →
          max t (Sy.heal K cap i gst r) + (Sy.pt r).env.ΔAC + Sy.lat K cap i r ≤ t' → T < t' →
          t' ≤ (Sy.pt r).horizon →
          ∀ v, (Sy.pt r).Ready (Sy.cDur K r) v t' → x ∈ (Sy.trace r).readAt g v t') ∨
          Sy.Excuse r := by
  intro Sy K cap g hcap hg i gst T r hv hh hhT hp
  obtain ⟨E, rho⟩ := r
  by_cases hx : rho.HashCollision
  · exact Or.inr hx
  left
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst hg'
  intro x t t' hsub hdt hTt hth v hv'
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hTh : T ≤ rho.horizon := hTt.le.trans hth
  have hΔ : (1 : Time) ≤ E.ΔAC := E.ΔAC_pos
  have hcD : Sy.cDur K ⟨E, rho⟩ = 19 * E.ΔAC := by
    simp only [Sy, K, System.cDur, Params.standard, Obligations.contract_coefficients_catchUp]
    change ((contract_catchUp S A : Nat) : Time) * E.ΔAC = _
    rw [Obligations.contract_catchUp_val]
    norm_num
  -- the seed, its read start `t₁` and the seeded invariant of the query bounded at `T`
  obtain ⟨h0, hb, hp'⟩ := Obligations.Growing.handover_query_at hn hv hx hcap hh hTh hhT
    ((shapeProgress (goldilocks S) V).mono le_rfl (hhT.trans hTh) hp)
  obtain ⟨r', σ, hseed, t₁, -, hdt₁, hlate, hinv⟩ :=
    Obligations.Growing.handover_invariant_at
      (Obligations.Growing.handoverQuery S A V hn hv hx hcap i hh hTh) h0 hb hp'
  have hnc := noCollRun_simTraceAt S rho hn hv hx
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
  have hrk : sp.ts r' ≤ sp.ts (r' + sp.k : Nat) := Compose.ts_le_ts (sp := sp) (by omega)
  have hrT : sp.ts r' + sp.Δ ≤ T := by
    have h1 := Compose.ts_le_ts (sp := sp) (show r' ≤ σ by have := sp.two_le_k; omega)
    have : 0 ≤ sp.Δ := sp.toParams.hΔ.le
    linarith
  have hσr : Sy.ready K gst ⟨E, rho⟩ ≤ sp.ts r' + sp.Δ := by
    rw [hready]
    linarith
  have hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp sp)
      (5 * sp.Δ) (Sy.ready K gst ⟨E, rho⟩) rho.horizon := by
    have hs := hh.sleepyOn_from_ready hTh (by change (1 / 2 : ℚ) ≤ 1; norm_num)
    intro t ht htb
    refine Obligations.half_ready_of_duration V _ ?_ (hs t ht htb)
    change 18 * E.ΔAC ≤ Sy.cDur K ⟨E, rho⟩
    rw [hcD]
    linarith
  have hB := Obligations.Growing.sleepy_bounds_at S rho hn hv le_rfl hhalf hσr
    (le_max_of_le_left ((hσr.trans hrT).trans hTh))
  -- conviction below a third on held chains
  have hcv := Obligations.Growing.chainConvictedBelow_at S A rho hn hv hh.2.2.2.2
  -- the payload bridge for the deadlines after `T`
  rw [show Sy.trace ⟨E, rho⟩ = _ from ledgerTrace rho, Trace.map_eq]
  refine proposalLive_txLive_above (b := T + 1) hv (c₀ := contract_catchUp S A)
    (by rw [Obligations.contract_catchUp_val]; norm_num) (psync_of_sys hh.1)
    (gst_le_heal K rho cap i gst) ?_ x t t' hsub hdt hTt hth v hv'
  intro q hq hTq hqh hrq
  let Q : Obligations.Growing.ConfirmedQueryAt S A V := ⟨⟨E, rho⟩, hn, cap, hcap, i, gst, q, hv,
    hx, Or.inr (Or.inr (Obligations.Growing.handover_query_regime S A V hh hhT hp hq)), hqh, hrq⟩
  have hqb : Q.deadline ≤ rho.horizon := hqh
  have hsvc' : Healing.Growing.ResetService Q.trace Q.keys gst
      (Obligations.protoFGDelay (Model.pubOf E)) Q.deadline :=
    ⟨hsvc.deltaF, hsvc.message, hsvc.block, hsvc.relay,
      fun x i att hx hs y j hy hc hj => hsvc.signedRow x i att hx hs y j hy hc (hj.trans hqb)⟩
  have hTQ : T ≤ Q.deadline := by
    change T ≤ q + _
    linarith
  exact Obligations.Growing.continued_proposal_live_at S A V Q hcv hseed hTQ hsvc' (hB.mono hqb)
    (hinv Q.deadline hTQ hsvc' (hB.mono hqb) hcv) hp (by rw [hready]; linarith) hdt₁
    (by change t₁ + 8 * sp.Δ ≤ q; linarith)

end Consensus.Goldilocks

end

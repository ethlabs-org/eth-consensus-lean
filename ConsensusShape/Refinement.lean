module
public import ConsensusShape.Claims
public import ConsensusShape.Payload
public import ConsensusProblem.Transfer

@[expose] public section

/-! # Refinement: shape claims give problem claims (L2)

`refinement F K V`: if shape family `F` meets `ShapeClaims F K`, then its
compiled system, with `progress` interpreted by `shapeExec`, meets the layer-0
headline `ProblemClaims` for contract `K`. The bridges are visible:

* `ledgerTrace`: the compiled ledger trace is the chain trace mapped by
  `ledgerOf` (definitionally); with `ledgerOf_prefix` every prefix-based
  property (safety, nesting, monotonicity, resilience, ready safety)
  transfers.
* `premiseBridge`: shape premises are layer-0 premises (definitionally).
* `proposalLive_txLive`: proposal liveness and partial synchrony give
  transaction liveness (the payload bridge, at the release time `τ`).
* Accountability: the conviction sets of the chain trace and of the ledger
  system coincide.
* Laws and non-framing are layer-½ theorems (`sysOf_laws`, `sysOf_nonFraming`). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf sysOf Obj)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The compiled ledger trace is the chain trace mapped by `ledgerOf`. -/
theorem ledgerTrace (rho : Model.Run (compiled F) E) :
    (sysOf O (compiled F) V).trace ⟨E, rho⟩ = (chainTrace rho).map ledgerOf :=
  rfl

/-- Transaction bridge (D-14; at the release time `τ`): apply `ProposalLive`
at `t' − D·Δ`; the honest proposal is released at `τ > max t GST + Δ`
(strictly), within the horizon, by a key ready, so awake, at `τ − 1`. Partial
synchrony (L0 delivery, endpoint rule) at the start `a := τ − Δ − 1 ≥ max t GST`
puts the transaction in that key's inbox by the deadline `τ − 1` (receipt at
the deadline counts), so in its mempool at the tick `τ`, which is the
proposal's payload. The strict `τ > …` of `ProposalLive` absorbs the one time
unit between receipt at the deadline and processing at the next tick. -/
theorem proposalLive_txLive {rho : Model.Run (compiled F) E} {c₀ : Nat} {g : O.Id}
    {start : Time} {D : Nat} (hv : rho.ExecutionValid) (hs : rho.PartialSynchrony)
    (hl : ProposalLive rho (((c₀ : Nat) : Time) * E.Δ) g start D) :
    ((chainTrace rho).map ledgerOf).TxLive (((c₀ : Nat) : Time) * E.Δ) g start
      (((D : Nat) : Time) * E.Δ) := by
  intro x t t' ht hsub hdt hh v hv'
  change max t E.gst + E.Δ + (D : Time) * E.Δ ≤ t' at hdt
  change rho.point.SubmittedToSome x t at hsub
  change t' ≤ rho.horizon at hh
  have hΔ := E.Δ_pos
  have hmt := le_max_left t E.gst
  have hmg := le_max_right t E.gst
  obtain ⟨τ, k, h, hτ, hready, hprop, hin⟩ := hl (t' - (D : Time) * E.Δ)
    (by dsimp only [Time] at *; omega) (by dsimp only [Time] at *; omega)
  have he : t' - (D : Time) * E.Δ + (D : Time) * E.Δ = t' := sub_add_cancel _ _
  rw [he] at hin
  have hmem : x ∈ decodeTxs h.input := by
    rw [honestProposal_payload hprop, decode_encodeTxs]
    obtain ⟨u, hu, τ₀, hτ₀, hτ₀t, haw, hx⟩ := hsub
    have hτa : τ₀ ≤ τ - E.Δ - 1 := by dsimp only [Time] at *; omega
    have hga : E.gst ≤ τ - E.Δ - 1 := by dsimp only [Time] at *; omega
    have hdl : max (τ - E.Δ - 1) E.gst + E.Δ = τ - 1 := by
      rw [max_eq_left hga]; dsimp only [Time] at *; omega
    have hτh : τ ≤ rho.horizon := by
      obtain ⟨-, -, -, -, i, hi, -⟩ := hprop
      exact (hv.in_horizon _ (List.mem_of_getElem? hi)).2
    have hawake : E.awake (rho.key k) (τ - 1) = true := by
      refine hready.2 (τ - 1) ?_ ?_
      · have hm : 0 ≤ ((c₀ : Nat) : Int) * E.Δ := mul_nonneg (by positivity) hΔ.le
        apply max_le <;> dsimp only [Time] at * <;> omega
      · dsimp only [Time]; omega
    have hτ1 : τ - 1 ≤ rho.point.horizon := by
      change τ - 1 ≤ rho.horizon; dsimp only [Time] at *; omega
    have held : CommLog.TxHeld rho.log (rho.key k) x (max (τ - E.Δ - 1) E.gst + E.Δ) :=
      hs.txs u hu x τ₀ hτ₀ haw hx (rho.key k) hready.1 (τ - E.Δ - 1) hτa
        (by change _ + E.Δ ≤ _; rw [hdl]; exact hτ1) (by change _ + E.Δ ≤ _; rw [hdl]; exact hτ1)
        (by change E.awake _ (_ + E.Δ) = true; rw [hdl]; exact hawake)
    rw [hdl] at held
    exact rho.txHeld_mem_mempool held (by dsimp only [Time]; omega)
  change x ∈ ledgerOf ((chainTrace rho).readAt g v t')
  exact (mem_ledgerOf _ _).mpr ⟨h, hin v hv', hmem⟩

/-- An object is in a node's system view iff it is in its run view. -/
theorem mem_sysView (rho : Model.Run (compiled F) E) (v : V) (i : Nat)
    (o : (protoOf (compiled F) E).Object) :
    (⟨E, o⟩ : (sysOf O (compiled F) V).Obs) ∈ (sysOf O (compiled F) V).view ⟨E, rho⟩ v i ↔
      o ∈ rho.ViewIdx v i := by
  constructor
  · rintro ⟨o', ho', he⟩
    cases he
    exact ho'
  · intro ho
    exact ⟨o, ho, rfl⟩

/-- Chain-level local accountability is ledger-level local accountability:
the two conviction sets coincide, and compatibility transfers along `ledgerOf`. -/
theorem accountablySafe_ledger (rho : Model.Run (compiled F) E) {α : ℚ} {g : O.Id}
    (h : (chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable α g 0) :
    (sysOf O (compiled F) V).AccountablySafe ⟨E, rho⟩ α g 0 := by
  intro u hu v hv i j hi hj
  rcases h u hu v hv i j hi hj with hh | hh
  · exact Or.inl (Compatible.map ledgerOf_prefix hh)
  · right
    have hset : {o' | (⟨E, o'⟩ : (sysOf O (compiled F) V).Obs) ∈
        (sysOf O (compiled F) V).view ⟨E, rho⟩ u i ∪ (sysOf O (compiled F) V).view ⟨E, rho⟩ v j} =
        rho.ViewIdx u i ∪ rho.ViewIdx v j := by
      ext o
      exact or_congr (mem_sysView rho u i o) (mem_sysView rho v j o)
    have hconv : Consensus.convicted ((sysOf O (compiled F) V).convicts ⟨E, rho⟩)
        ((sysOf O (compiled F) V).view ⟨E, rho⟩ u i ∪ (sysOf O (compiled F) V).view ⟨E, rho⟩ v j) =
        Consensus.convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j) := by
      unfold Consensus.convicted
      congr 1
      funext x
      exact congrArg (fun A => rho.Slashable A x) hset
    rw [hconv]
    exact hh

/-- The headline: shape claims give the problem claims of the compiled
system, with `progress` interpreted by `shapeExec`. -/
theorem refinement (F : ShapeFamily O Info) (K : Contract O ProgressReq) (V : Type)
    [Fintype V] [DecidableEq V] :
    ShapeClaims F K → ProblemClaims (sysOf O (compiled F) V) (shapeExec F V) K := by
  intro hc
  refine ⟨hc.wf, Model.sysOf_laws _ _ _, hc.provided, hc.complete,
    Model.sysOf_nonFraming _ _ _, ?_, ?_, ?_⟩
  · rintro c₁ c₂ g₁ g₂ hlt h₁ h₂ ⟨E, rho⟩ hv
    exact (hc.nested c₁ c₂ g₁ g₂ hlt h₁ h₂ V E rho hv).map ledgerOf_prefix
  · rintro g hg ⟨E, rho⟩ hv
    exact (hc.finalMonotone g hg V E rho hv).map ledgerOf_prefix
  · intro c g s hg hs
    have hcc := hc.caps c g s hg hs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro σ ⟨E, rho⟩ hv hA
      exact (hcc.safe V E rho σ hv hA).imp (fun h => h.map ledgerOf_prefix) id
    · rintro i σ ⟨E, rho⟩ hv hA
      have hsync : rho.PartialSynchrony := ((hc.liveSync c s hs i).1).sync_of_eval hA
      exact (hcc.live V E rho i σ hv hA).imp (proposalLive_txLive hv hsync) id
    · rintro α ha ⟨E, rho⟩ hv -
      exact (hcc.accountable α ha V E rho hv).imp (accountablySafe_ledger rho) id
    · rintro P hP σ ⟨E, rho⟩ hv hA
      exact (hcc.persists P hP V E rho σ hv hA).imp (fun h => h.map ledgerOf_prefix) id
    · rintro R hR i σ ⟨E, rho⟩ hv hA
      exact (hcc.recoverySafe R hR V E rho i σ hv hA).imp (fun h => h.map ledgerOf_prefix) id
    · rintro R hR i σ ⟨E, rho⟩ hv hA
      have hsync : rho.PartialSynchrony := ((hc.liveSync c s hs i).2 R hR).sync_of_eval hA
      exact (hcc.recoveryLive R hR V E rho i σ hv hA).imp
        (proposalLive_txLive hv hsync) id

end Consensus.Shape

end

module
public import ConsensusLean.Spec.Shape.Claims
public import ConsensusLean.Lemmas.Shape.Payload
public import ConsensusLean.Lemmas.Problem.Facts.Transfer

public section

/-! # Refinement: shape claims give the L0 behaviour (L2)

`refinement F K V`: if shape family `F` meets `ShapeClaims F K`, the numbers
are admissible and the schema serves a ledger, then its compiled system, with
the progress reader `shapeProgress`, has the L0 `Behaviour` for contract `K`.
The bridges are visible:

* `ledgerTrace`: the compiled ledger trace is the chain trace mapped by
  `ledgerOf` (definitionally); with `ledgerOf_prefix` every prefix-based
  property (safety, nesting, monotonicity, resilience, ready safety)
  transfers.
* Regimes: the shape claims use the L0 regimes of the compiled system.
* `proposalLive_txLive`: reader-conditional proposal liveness and partial synchrony with a GST at
  or before the start give transaction liveness (the payload bridge, at the
  release time `τ`).
* Accountability: the conviction sets of the chain trace and of the ledger
  system coincide.
* Laws and non-framing are L1 theorems (`sysOf_laws`, `sysOf_nonFraming`). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf protoOf sysOf Obj)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V] {E : Env V}

/-- The compiled ledger trace is the chain trace mapped by `ledgerOf`. -/
theorem ledgerTrace (rho : Model.Run (compiled F) E) :
    (sysOf O (compiled F) V).trace ⟨E, rho⟩ = (chainTrace rho).map ledgerOf := by
  rw [Trace.map_eq]
  rfl

/-- Transaction bridge (at the release time `τ`): apply
`ProposalLiveReady` at `t' − D·Δ`, with the reader `v` ready at the deadline
`t'` as the witness that a ready reader exists; the honest proposal is released at
`τ > max t start + Δ` (strictly), within the horizon, by a key ready at `τ` with
catch-up `c₀·Δ ≥ Δ` (`1 ≤ c₀`, which admissible numbers give), so awake throughout
`[τ − Δ − 1, τ − 1]`. Partial synchrony with GST `gst ≤ start` (L0 delivery) at the
start `a := τ − Δ − 1 ≥ max t start ≥ gst`, whose delivery interval is
`[τ − Δ − 1, τ − 1]`, puts the transaction in that key's inbox by the deadline
`τ − 1` (receipt at the deadline counts), so in its mempool at
the tick `τ`, which is the proposal's payload. The strict `τ > …` of
`ProposalLiveReady` absorbs the one time unit between arrival at the deadline and
use by the tick at `τ`. Every submission is served, including those before
`start` (deadline `max t start + Δ + D·Δ`). -/
theorem proposalLive_txLive {rho : Model.Run (compiled F) E} {c₀ : Nat} {g : O.Id}
    {start gst : Time} {D : Nat} (hv : rho.ExecutionValid) (hc₀ : 1 ≤ c₀)
    (hs : CommLog.PSync rho.point rho.log gst) (hgs : gst ≤ start)
    (hl : ProposalLiveReady rho (((c₀ : Nat) : Time) * E.Δ) g start D) :
    ((chainTrace rho).map ledgerOf).TxLive (((c₀ : Nat) : Time) * E.Δ) g start
      (((D : Nat) : Time) * E.Δ) := by
  rw [Trace.map_eq]
  intro x t t' hsub hdt hh v hv'
  change max t start + E.Δ + (D : Time) * E.Δ ≤ t' at hdt
  change rho.point.SubmittedToSome x t at hsub
  change t' ≤ rho.horizon at hh
  have hΔ := E.Δ_pos
  have hmt := le_max_left t start
  have hms := le_max_right t start
  obtain ⟨τ, k, h, hτ, hready, hprop, hin⟩ := hl (t' - (D : Time) * E.Δ)
    (by dsimp only [Time] at *; omega) (by dsimp only [Time] at *; omega)
    ⟨v, by rw [sub_add_cancel]; exact hv'⟩
  have he : t' - (D : Time) * E.Δ + (D : Time) * E.Δ = t' := sub_add_cancel _ _
  rw [he] at hin
  have hmem : x ∈ decodeTxs h.input := by
    rw [honestProposal_payload hv hprop, decode_encodeTxs]
    obtain ⟨u, hu, τ₀, hτ₀, hτ₀t, haw, hx⟩ := hsub
    have hτa : τ₀ ≤ τ - E.Δ - 1 := by dsimp only [Time] at *; omega
    have hga : gst ≤ τ - E.Δ - 1 := by dsimp only [Time] at *; omega
    have hdl : max (τ - E.Δ - 1) gst + E.Δ = τ - 1 := by
      rw [max_eq_left hga]; dsimp only [Time] at *; omega
    have hτh : τ ≤ rho.horizon := by
      obtain ⟨-, -, -, -, i, hi | ⟨_, hi⟩, -⟩ := hprop <;>
        exact (hv.in_horizon _ (List.mem_of_getElem? hi)).2
    have hawake : rho.point.AwakeOnClosed (rho.key k) (τ - E.Δ - 1) (τ - 1) := by
      intro u hu₁ hu₂
      refine hready.2 u ?_ ?_
      · have hm : E.Δ ≤ ((c₀ : Nat) : Int) * E.Δ :=
          le_mul_of_one_le_left hΔ.le (by exact_mod_cast hc₀)
        apply max_le <;> dsimp only [Time] at * <;> omega
      · dsimp only [Time] at *; omega
    have hτ1 : τ - 1 ≤ rho.point.horizon := by
      change τ - 1 ≤ rho.horizon; dsimp only [Time] at *; omega
    have held : CommLog.TxHeld rho.log (rho.key k) x (max (τ - E.Δ - 1) gst + E.Δ) :=
      hs.txs u hu x τ₀ hτ₀ haw hx (rho.key k) hready.1 (τ - E.Δ - 1) hτa
        (by change _ + E.Δ ≤ _; rw [hdl]; exact hτ1) (by change _ + E.Δ ≤ _; rw [hdl]; exact hτ1)
        (by change rho.point.AwakeOnClosed _ _ (_ + E.Δ); rw [hdl]; exact hawake)
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

/-- Partial synchrony of the compiled system's log is partial synchrony of
the run's log. -/
theorem psync_of_sys {rho : Model.Run (compiled F) E} {gst : Time}
    (h : CommLog.PSync ((sysOf O (compiled F) V).trace ⟨E, rho⟩).point
      ((sysOf O (compiled F) V).log ⟨E, rho⟩) gst) :
    CommLog.PSync rho.point rho.log gst :=
  (Model.sysOf_delivers_iff rho _ _ _).mp h

/-- The heal point is at or after the GST. -/
theorem gst_le_heal (K : Contract ProgressReq) (rho : Model.Run (compiled F) E)
    (cap : Capability) (i : K.Idx) (gst : Time) : gst ≤ (Sys F V).heal K cap i gst ⟨E, rho⟩ := by
  change gst ≤ max gst 0 + ((K.params.heal cap i : Nat) : Time) * E.Δ
  have : (0 : Time) ≤ ((K.params.heal cap i : Nat) : Time) * E.Δ :=
    mul_nonneg (by positivity) E.Δ_pos.le
  have := le_max_left gst 0
  linarith

/-- The headline: shape claims, admissible numbers and a served ledger give
the L0 behaviour of the compiled system, with progress read by
`shapeProgress`. -/
theorem refinement (F : ShapeFamily O Info) (K : Contract ProgressReq) (V : Type)
    [Fintype V] [DecidableEq V] (hc : ShapeClaims F K) (ha : K.params.Admissible)
    (hs : O.Serves) : Behaviour (sysOf O (compiled F) V) (shapeProgress F V) K := by
  have hc := hc V
  refine ⟨Model.sysOf_laws _ _ _, ha, hs, Model.sysOf_nonFraming _ _ _, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rintro c₁ c₂ g₁ g₂ hlt h₁ h₂ ⟨E, rho⟩ hv
    rw [ledgerTrace]
    exact (hc.nested c₁ c₂ g₁ g₂ hlt h₁ h₂ ⟨E, rho⟩ hv).map ledgerOf_prefix
  · rintro g hg ⟨E, rho⟩ hv
    rw [ledgerTrace]
    simp only [Trace.Monotone, Trace.map_point]
    exact (hc.finalMonotone g hg ⟨E, rho⟩ hv).map ledgerOf_prefix
  · rintro g hg ⟨E, rho⟩ hv -
    exact (hc.finalAccountable g hg ⟨E, rho⟩ hv trivial).imp (accountablySafe_ledger rho) id
  · rintro cap g hg i gst ⟨E, rho⟩ hv hA
    simp only [ledgerTrace]
    exact (hc.healthyLive cap g hg i gst ⟨E, rho⟩ hv hA).imp
      (proposalLive_txLive hv ha.catchUp_pos (psync_of_sys hA.1.1) (gst_le_heal K rho cap i gst)) id
  · rintro cap g hcap hg ⟨E, rho⟩ hv hS
    simp only [ledgerTrace]
    exact (hc.sleepySafe cap g hcap hg ⟨E, rho⟩ hv hS).imp (fun h => h.map ledgerOf_prefix) id
  · rintro cap g hcap hg i ⟨E, rho⟩ hv hA
    simp only [ledgerTrace]
    exact (hc.sleepyLive cap g hcap hg i ⟨E, rho⟩ hv hA).imp
      (proposalLive_txLive hv ha.catchUp_pos (psync_of_sys hA.1.1) le_rfl) id
  · rintro cap g hcap hg i gst ⟨E, rho⟩ hv hA
    simp only [ledgerTrace]
    exact (hc.healedSafe cap g hcap hg i gst ⟨E, rho⟩ hv hA).imp (fun h => h.map ledgerOf_prefix) id
  · rintro g hg T b₀ b₁ ⟨E, rho⟩ hv hO
    simp only [ledgerTrace]
    refine (hc.persists g hg T b₀ b₁ ⟨E, rho⟩ hv hO).imp (fun h => ?_) id
    unfold Trace.ProtectedReadyFrom
    rw [Trace.map_point]
    exact h.map ledgerOf_prefix

end Consensus.Shape

end

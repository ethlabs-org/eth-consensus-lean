module
public import AvailableChainFGSAProofs.Proofs.Healing.Reset -- shake: keep (R1–R3 tests)
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.HealingInputExport -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing
public import AvailableChainFGSAProofs.Proofs.Foundations.Cap
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService
public import AvailableChainFGSAProofs.Proofs.Finality.Height
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum

set_option linter.privateModule false

public section

/-! Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 T.
DC: SAME discharge the actual source producer and test all reset field support.
R1/R2 are applied with a hypothetical named HG.5 input (producer HG2A-RECEIPT F3).
The numeric tests cover both allowance choices and integer subtraction. -/

namespace AvailableChain.FGSA.Run.Tests.HealingReset
open AvailableChain.SimplexFG

private theorem resetEmittedPairs (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {r : Nat}
    {a : RowWire p.n} {e : Height × BlockId}
    (ha : HonestRowAt p c E rho j x r a) (he : namedEntry a.payload.height_pair = some e) :
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = ((heightView p C).h, (heightView p C).T_h.root) ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
  obtain ⟨C, G, hC, hh, _, hG, hCG, hf⟩ :=
    sourceDiscipline_emittedName p c E rho hs ha he
  refine ⟨C, G, hC, ?_, hG, hCG, hf⟩
  rw [heightView_eq_simplex p]
  exact hh

private theorem resetSearchWithPorts (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) : FrontierSearchStatement p c E rho G ΔF := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  exact healing_frontierSearch_recovery E rho hset (fgsa_rMonoAll p c E rho) crossing
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ) origin
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho hset.base hset.fault)
    (fgsa_tRows_recovery p c E rho hset.toRecovery₂).receipt
    (fgsa_batchCoverage p ΔF .progress c E rho) (fgsa_foldTrichotomy_progress p) faultQ
    (kmid_honest_quorum p c rho hset.base.linked hset.fault)

-- All frozen H0Reset fields are built from the exported first-row contract.
-- R1 (healing_resetWitness) derives this contract from the named HG.5 input.
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF deadline : Time}
    (hset : HealingSet p c E rho G ΔF)
    (firstRow : FirstHeightRowBy p c E rho (resetCutFrontier p c E rho + 1) deadline) :
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar ≤ deadline :=
  healing_reset_fields p c E rho
    (resetEmittedPairs p c E rho hset.base.valid.toScheduleWellFormed) hset firstRow

private def resetParams (k : Nat) (hk : 2 ≤ k) : Params where
  Δ := 1
  n := 4
  k := k
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := hk
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

-- The short-lease branch attains the minimum: 339 = 3·12 + 159 + 144.
example : let p := resetParams 2 (by decide)
    B'_resetF p 6 8 = 339 ∧
    (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + B_cF p 6 8 (ρ₁ p 8)) = 159 ∧
    (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + D_cF p (ρ₁ p 8)) = 144 ∧
    B'_resetF p 6 8 = 3 * P p + (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + B_cF p 6 8 (ρ₁ p 8)) +
      (E_gF p 6 8 (ρ₁ p 8) + E_jF p 6 8 (ρ₁ p 8) + D_cF p (ρ₁ p 8)) := by decide

-- k > 2R+1 selects the two-lease allowance.
example : let p := resetParams 8 (by decide)
    ¬ p.k ≤ 2 * p.R + 1 ∧
    B'_resetF p 6 12 = 3 * P p +
      (E_gF p 6 12 (ρΓ p 12) + E_jF p 6 12 (ρΓ p 12) + B_cF p 6 12 (ρΓ p 12)) +
      (E_gF p 6 12 (ρΓ p 12) + E_jF p 6 12 (ρΓ p 12) + D_cF p (ρΓ p 12)) := by decide

-- A negative allowance tests Int subtraction without Nat truncation.
example : let p := resetParams 2 (by decide)
    B_resetF p 6 8 (-100) = -209 ∧
    B_resetF p 6 8 (-100) = 3 * P p + (E_gF p 6 8 (-100) + E_jF p 6 8 (-100) + B_cF p 6 8 (-100)) +
      (E_gF p 6 8 (-100) + E_jF p 6 8 (-100) + D_cF p (-100)) := by decide

-- The strict-cut step reaches the strict reset deadline with the chosen minimum.
example : let p := resetParams 2 (by decide)
    ∃ ρbar, (ρbar = ρΓ p 8 ∨ (ρbar = ρ₁ p 8 ∧ p.k ≤ 2 * p.R + 1)) ∧
      45 + (E_gF p 6 8 ρbar + E_jF p 6 8 ρbar + B_cF p 6 8 ρbar) +
        (E_gF p 6 8 ρbar + E_jF p 6 8 ρbar + D_cF p ρbar) < 10 + B'_resetF p 6 8 :=
  healing_reset_budget_lt _ 8 6 10 45 (by decide)

-- The same arithmetic holds for every integer allowance.
example (p : Params) (G ΔF ρbar : Time) :
    B_resetF p ΔF G ρbar = 3 * P p +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) := healing_reset_budget_sum p G ΔF ρbar

-- R1: the reset witness and the strict deadline from a hypothetical HG.5 input.
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) (hδ : p.δt = 2 * p.R)
    (hbound : LivenessBoundW p ΔF) (hsearch : FrontierSearchStatement p c E rho G ΔF)
    (hhor : recoveryStart p E + B'_resetF p ΔF G ≤ rho.horizon) :
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G :=
  healing_resetWitness p c E rho
    (resetEmittedPairs p c E rho hset.base.valid.toScheduleWellFormed)
    hset hδ hbound hsearch hhor

-- R2: the frozen reset-arrival statement from a hypothetical all-run HG.5 input.
example (p : Params) (G ΔF : Time)
    (hsearch : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      FrontierSearchStatement p c E rho G ΔF) :
    ResetArrivalStatement p G ΔF :=
  by
    intro hδ V _ _ In c E rho hset hbound hhor
    exact healing_resetWitness p c E rho
      (resetEmittedPairs p c E rho hset.base.valid.toScheduleWellFormed)
      hset hδ hbound (hsearch c E rho hset hbound) hhor

-- HG5-BRIDGE: the named recovery producer supplies all search services.
example (p : Params) (G ΔF : Time) : ResetArrivalStatement p G ΔF :=
  by
    intro hδ V _ _ In c E rho hset hbound hhor
    exact healing_resetWitness p c E rho
      (resetEmittedPairs p c E rho hset.base.valid.toScheduleWellFormed)
      hset hδ hbound (resetSearchWithPorts p c E rho hset) hhor

-- HG5-BRIDGE: HG.5 holds on every healing run.
example (p : Params) {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) : FrontierSearchStatement p c E rho G ΔF :=
  resetSearchWithPorts p c E rho hset

end AvailableChain.FGSA.Run.Tests.HealingReset
end

module
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
-- shake: keep (concrete examples and axiom audit commands)

public section

namespace AvailableChain.FGSA.Run

@[expose] def boundsWParams (R : Nat) (hR : 2 ≤ R) : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := R
  δt := 2 * R
  RLarge := hR
  digest := fun d => ⟨d.slot + 1⟩

example : kappaF (boundsWParams 2 (by decide)) 2 = 2 := by decide
example : kappaF (boundsWParams 3 (by decide)) 6 = 3 := by decide
example : LivenessBoundW (boundsWParams 3 (by decide)) 6 := ⟨by decide⟩

/-- κ=R, and the row deadline equals the carrier time and the next opening. -/
example : ActionDeliveryBoundsW (boundsWParams 3 (by decide)) 6 1 :=
  action_delivery_boundsW _ _ _ (by decide) ⟨by decide⟩
example : (boundsWParams 3 (by decide)).actionTime 1 + 6 =
    carrierTimeW (boundsWParams 3 (by decide)) 6 1 := by decide
example : KernelBeforeNextActionW (boundsWParams 3 (by decide)) 6 1 :=
  kernel_before_next_actionW _ _ _ ⟨by decide⟩

example : betaF (boundsWParams 3 (by decide)) 6 = 12 ∧
    epsF (boundsWParams 3 (by decide)) 6 = 4 ∧
    carrierTimeW (boundsWParams 3 (by decide)) 6 1 = 24 ∧
    kernelDeadlineW (boundsWParams 3 (by decide)) 6 1 = 25 ∧
    W_W (boundsWParams 3 (by decide)) 6 1 = 49 := by decide

/-- The complete third numeric row of blueprint 21:1850–1863. -/
example : E_gF (boundsWParams 3 (by decide)) 6 8 25 = 56 ∧
    E_jF (boundsWParams 3 (by decide)) 6 8 25 = 52 ∧
    B_cF (boundsWParams 3 (by decide)) 6 8 25 = 51 ∧
    D_cF (boundsWParams 3 (by decide)) 25 = 36 ∧
    B_resetF (boundsWParams 3 (by decide)) 6 8 25 = 339 ∧
    BF (boundsWParams 3 (by decide)) 6 8 25 = 351 ∧
    B_H2F (boundsWParams 3 (by decide)) 6 8 = 381 ∧
    B_H1F (boundsWParams 3 (by decide)) 6 8 = 351 ∧
    B_HF (boundsWParams 3 (by decide)) 6 8 = 351 ∧
    B'_resetF (boundsWParams 3 (by decide)) 6 8 = 339 ∧
    B_bestF (boundsWParams 3 (by decide)) 6 8 1 = 351 := by decide

example : B_HF (boundsWParams 2 (by decide)) 2 8 = 295 ∧
    B_HF (boundsWParams 3 (by decide)) 2 8 = 343 := by decide

/-- A W recurrence with κ = R = 3 and a nonempty search horizon. -/
example : F4_W (boundsWParams 3 (by decide)) 6 (fun s => 0 < s) 0 61 1 ∧
    FE_W (boundsWParams 3 (by decide)) 6 (fun s => 0 < s) 0 61 1 := by
  have h : F4_W (boundsWParams 3 (by decide)) 6 (fun s => 0 < s) 0 61 1 := by
    change Gen.Pure.RecF4_W (fun s => 0 < s) 3 3 12 1 12 0 61 1
    refine ⟨by decide, ?_⟩
    intro q hq _ _
    refine ⟨q, ⟨le_rfl, by omega⟩, ?_⟩
    rw [Gen.Pure.FGood4_W_def, Gen.Pure.FGoodE_W_def]
    exact ⟨⟨by change (0 : Nat) < q * 3; omega,
      by change (0 : Nat) < (q + 1) * 3; omega,
      ⟨(q + 2) * 3, by omega, le_rfl, by change (0 : Nat) < (q + 2) * 3; omega⟩,
      by change (0 : Nat) < (q + 2) * 3 + 3; omega⟩,
      by change (0 : Nat) < (q + 1) * 3 + 3; omega⟩
  exact ⟨h, F4_W_implies_FE_W h⟩

example : ((1 : Time) + 1 + 1) * P (boundsWParams 3 (by decide)) +
    betaF (boundsWParams 3 (by decide)) 6 + (boundsWParams 3 (by decide)).Δ ≤ 61 := by decide

example : FGoodE_Wp (boundsWParams 3 (by decide)) 6 (fun s => 0 < s) 1 ∧
    FGood4_Wp (boundsWParams 3 (by decide)) 6 (fun s => 0 < s) 1 ∧
    Tail_Wp (boundsWParams 3 (by decide)) 6 (fun s => 0 < s) 1 := by
  exact ⟨⟨by decide, by decide, ⟨9, by decide, by decide, by decide⟩, by decide⟩,
    ⟨⟨by decide, by decide, ⟨9, by decide, by decide, by decide⟩, by decide⟩, by decide⟩,
    ⟨by decide, ⟨6, by decide, by decide, by decide⟩, by decide⟩⟩

/-- The first two rows also hold at Δ = 7, away from the unit-time examples. -/
example : let p : Params := { boundsWParams 2 (by decide) with Δ := 7, deltaPos := by decide }
    B_HF p 14 (8 * p.Δ) = 295 * p.Δ := by
  dsimp only
  exact B_HF_numeric_295 _ _ rfl rfl (by decide) (by decide)

example : let p : Params := { boundsWParams 3 (by decide) with Δ := 7, deltaPos := by decide }
    B_HF p 0 (8 * p.Δ) = 343 * p.Δ := by
  dsimp only
  exact B_HF_numeric_343 _ _ rfl rfl (by decide) (by decide)

example : B_FW (boundsWParams 3 (by decide)) 6 8 1 = 400 := by decide

#print axioms kappaF_ceiling
#print axioms kappaF_eq_two_iff
#print axioms action_delivery_boundsW
#print axioms kernel_before_next_actionW
#print axioms B_HF_bounds
#print axioms B_bestF_le_healing
#print axioms B_HF_numeric_351

end AvailableChain.FGSA.Run

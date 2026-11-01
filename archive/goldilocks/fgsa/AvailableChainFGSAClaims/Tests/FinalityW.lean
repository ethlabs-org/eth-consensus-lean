module
public import AvailableChainFGSAClaims.Statements.Packages.Finality
-- shake: keep (package examples)
public import AvailableChainFGSAClaims.Statements.Packages.Healing
-- shake: keep (joined kernel examples)

set_option linter.privateModule false
set_option linter.defProp false

@[expose] public section

/-! ROOT-DIGEST W3: explicit small roots for statement fixtures. -/

namespace AvailableChain.FGSA.Run.Tests.FinalityW
open Gen.Pure

private abbrev params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩, 3, 6, by decide, 2, by decide, fun d =>
      ⟨d.slot + 1⟩⟩
private abbrev codec : AppCodec Nat := ⟨id, some, fun _ => rfl⟩
private abbrev env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
-- This finite schedule checks recurrence guards. It is not a healing execution witness.
private abbrev run : V2.D.Run (Fin 1) (fgsa params codec) where
  honest := Finset.univ
  horizon := 512
  events := (List.range 513).map (fun t => .tick 0 (t : Time))
  seatOf := fun _ _ => 0
  input := fun _ _ => 0

-- κ=R=3, ΔF>2Δ. Action-row receipt is exactly at the carrier time.
example : kappaF params 6 = params.R ∧ 2 * params.Δ < (6 : Time) := by decide
example : params.actionTime 1 + 6 = carrierTimeW params 6 1 := by decide
example : kernelDeadlineW params 6 3 = 49 := by decide
example : W_W params 6 1 = 49 := by decide
example : finalityWindow_W params 6 .recFE 1 = finalityWindow_W params 6 .recF4 1 := rfl

private def honest {s : Slot} (hs : 0 < s) :
    Gen.V2.Duty.HonestSlot run (fgsaInterface params codec) s := by
  rw [Gen.V2.Duty.HonestSlot_def]
  exact ⟨hs, Finset.mem_univ _⟩

private def good (r : Nat) (hr : 1 ≤ r) :
    FGoodE_W (Gen.V2.Duty.HonestSlot run (fgsaInterface params codec))
      params.R (kappaF params 6) r := by
  rw [FGoodE_W_def]
  refine ⟨honest (by change 0 < r * 3; omega), honest (by change 0 < (r + 1) * 3; omega),
    ⟨(r + 2) * 3, ?_, ?_, honest (by change 0 < (r + 2) * 3; omega)⟩, ?_⟩
  · change (r + 1) * 3 + 3 ≤ (r + 2) * 3
    omega
  · exact le_rfl
  · apply honest
    change 0 < (r + 2) * 3 + 3
    omega

example : FGoodE_W (Gen.V2.Duty.HonestSlot run (fgsaInterface params codec))
    params.R 3 1 := good 1 (by decide)

private def recurrence : FE_W params 6
    (Gen.V2.Duty.HonestSlot run (fgsaInterface params codec)) (recoveryStart params env)
      run.horizon 1 := by
  rw [FE_W_def, RecFE_W_def]
  refine ⟨le_rfl, ?_⟩
  intro q hq _ _
  exact ⟨q, (by rw [InWindow_def]; exact ⟨le_rfl, Nat.lt_succ_self q⟩), good q hq⟩

-- The recurrence has a real search at q=1, with the complete receipt horizon.
example : ((1 : Time) + 1 + 1) * P params + betaF params 6 + params.Δ ≤ run.horizon := by
  decide
example : FE_W params 6 (Gen.V2.Duty.HonestSlot run (fgsaInterface params codec))
    (recoveryStart params env) run.horizon 1 := recurrence

private def recurrenceF4 : F4_W params 6
    (Gen.V2.Duty.HonestSlot run (fgsaInterface params codec)) (recoveryStart params env)
      run.horizon 1 := by
  rw [F4_W_def, RecF4_W_def]
  refine ⟨le_rfl, ?_⟩
  intro q hq _ _
  refine ⟨q, ?_, ?_⟩
  · rw [InWindow_def]
    exact ⟨le_rfl, Nat.lt_succ_self q⟩
  · rw [FGood4_W_def]
    exact ⟨good q hq, honest (by change 0 < (q + 1) * 3 + 3; omega)⟩

-- These constructors check finite package budgets with the supplied run input.
-- They do not construct a Recovery₂ or HealingInput execution witness.
private def finiteSet (form : FinFormW)
    (recovery : RecoverySleep₂ params codec env run 4 6) :
    FinalitySet_W params codec env run 4 6 form 1 := by
  refine ⟨recovery, ⟨by decide⟩, ?_⟩
  cases form <;> rw [FinFormW.holdsW_def]
  · exact recurrence
  · exact recurrenceF4

example (form : FinFormW) (w : HealingWitness)
    (recovery : RecoverySleep₂ params codec env run 4 6)
    (input : HealingInput params codec env run w 6)
    (start : tstar params w ≤ 50) :
    FinalityLivenessPrem_W params codec 4 6 form 1 w env run ⟨50⟩ :=
  ⟨finiteSet form recovery, input, start, by decide⟩

example (form : FinFormW) (w : HealingWitness)
    (recovery : RecoverySleep₂ params codec env run 4 6)
    (input : HealingInput params codec env run w 6)
    (start : tstar params w ≤ 50) :
    AboveFrontierPrem_W params codec 4 6 form 1 w env run ⟨50⟩ :=
  ⟨finiteSet form recovery, input, start, by decide, by decide⟩

example (form : FinFormW) (w : HealingWitness) (X : Block)
    (recovery : RecoverySleep₂ params codec env run 4 6)
    (input : HealingInput params codec env run w 6)
    (start : tstar params w ≤ 50)
    (prop : HonestProposal env run (fgsaInterface params codec) 13 X) :
    ProposalFinalPrem_W params codec 4 6 form 1 w env run ⟨13, X⟩ :=
  ⟨finiteSet form recovery, input, prop,
    le_trans start (by change (50 : Time) ≤ 52; decide),
    by change (52 : Time) + 49 ≤ 512; decide⟩

example (form : FinFormW) (recovery : RecoverySleep₂ params codec env run 4 6) :
    FirstFinalityPrem_W params codec 4 6 form 1 env run () :=
  ⟨finiteSet form recovery, by decide⟩

example (w : HealingWitness) (recovery : RecoverySleep₂ params codec env run 4 6)
    (input : HealingInput params codec env run w 6) (start : tstar params w ≤ 50) :
    KernelJoinedPrem params codec 4 6 env run ⟨5⟩ :=
  ⟨recovery.toRecovery₂, ⟨by decide⟩, good 5 (by decide),
    ⟨w, input, le_trans start (by decide)⟩, by decide⟩

-- Package projections enforce the common witness, the W window and both FF7 horizons.
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
  {G ΔF : Time} {form : FinFormW} {g : Nat} {w : HealingWitness}
  {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {pt : PtT}

example (h : AboveFrontierPrem_W p c G ΔF form g w E rho pt) :
    pt.t + W_W p ΔF g ≤ rho.horizon ∧
    pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon := ⟨h.firstHorizon, h.hhor⟩

example (h : AboveFrontierPrem_W p c G ΔF form g w E rho pt) :
    pt.t + 2 * W_W p ΔF g ≤ rho.horizon := by
  simpa only [two_mul, ← add_assoc] using h.hhor

example (ptR : PtR) (h : KernelJoinedPrem p c G ΔF E rho ptR) :
    FGoodE_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) p.R (kappaF p ΔF) ptR.r :=
  h.window

example (ptR : PtR) (h : KernelJoinedPrem p c G ΔF E rho ptR) :
    ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w ≤ ↑ptR.r * P p := h.start

end AvailableChain.FGSA.Run.Tests.FinalityW
end

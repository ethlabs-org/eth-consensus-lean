module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge

public section

/-! # The Goldilocks bridge's release hold at release gap `0`

The Goldilocks supplier contracts read the healing and local suppliers at the release hold
`Rg·Δ` of a release gap `Rg` (`goldilocksACHealing`, `goldilocksACCorrectLocal`), and
`GoldilocksLocalData` records it (`fgHold_eq`). Each `…Old` below is main's form, without the
release hold, verbatim but for the names. At `Rg = 0` the hold is `(0 : ℕ) · Δ = 0` and each
contract is its main text (`…_iff_old`), for every signing calendar and signing gap. -/

namespace Consensus.Goldilocks.Generic.BridgeHold

open AC (ACParams ReplayOrder)
open Generic

/-- `GoldilocksHealingData` as stated on main. -/
def GoldilocksHealingDataOld (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    {R : ACRun (goldilocksNode sp ro) (fun v => v.val)}
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) : Prop :=
  GoldilocksRunData sp ro R sign G ∧
    O.warmup = 2 * sp.k ∧ O.follow = 3 + (G + 3) / 4 ∧ O.reportDelay = G ∧ O.drain = 2 * sp.k + 5 ∧
    O.deepBudget = sp.deepDepth ∧
    O.Origin = (fun tr x i j B => tr.JoinedAt x (tr.time i) ∧
      ∃ CV, Compose.StoredFastLockAt tr x i j B CV)

/-- `goldilocksACHealing` as stated on main. -/
def goldilocksACHealingOld (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) : Prop :=
  ∃ R : ACRun (goldilocksNode sp ro) (fun v => v.val),
    ∃ O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R,
    GoldilocksHealingDataOld sp ro O sign G

/-- `GoldilocksLocalData` as stated on main. -/
structure GoldilocksLocalDataOld (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val))
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) : Prop where
  healing : GoldilocksHealingDataOld sp ro C.healing sign G
  θ : C.θ = 1 / 2
  catchUp : C.catchUp = 18 * sp.Δ
  look : C.look = 5 * sp.Δ
  committeeLook : C.committeeLook = 5 * sp.Δ
  hold : C.hold = sp.Δ
  margin : C.margin = 6 * sp.Δ
  latency : C.latency = 6 * sp.Δ
  recovery : C.recovery = 9 * sp.Δ
  outageEta : C.outageEta = ((12 * sp.k + 7 : Nat) : Time) * sp.Δ
  outageLag : C.outageLag = ((4 * sp.k + 6 : Nat) : Time) * sp.Δ
  outageBudget : C.outageBudget = ((4 * sp.k - 5 : Nat) : Time) * sp.Δ
  payload : C.payload = (fun B => {tx | tx ∈ Blocks.decodeTxs B.input})
  served : C.served = (fun tr y j τ m => AC.FamilyFacts.MessageServedBefore tr.projAC y j τ m)

/-- `goldilocksACCorrectLocal` as stated on main. -/
def goldilocksACCorrectLocalOld (sp : ACParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) : Prop :=
  ∃ C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val),
    GoldilocksLocalDataOld sp ro C sign G

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {sign : Fin sp.n → Time → Bool} {G : Nat}

theorem hold_zero : ((0 : Nat) : Time) * sp.Δ = 0 := by simp

/-- At hold `0`, `GoldilocksHealingData` is its main text. -/
theorem goldilocksHealingData_iff_old {R : ACRun (goldilocksNode sp ro) (fun v => v.val)}
    (O : ACHealing (goldilocksNode sp ro) (fun v => v.val) R) :
    GoldilocksHealingData sp ro O sign G ↔ GoldilocksHealingDataOld sp ro O sign G :=
  Iff.rfl

/-- At `Rg = 0`, `goldilocksACHealing` is its main text. -/
theorem goldilocksACHealing_iff_old :
    goldilocksACHealing sp ro sign G 0 ↔ goldilocksACHealingOld sp ro sign G := by
  unfold goldilocksACHealing goldilocksACHealingOld
  rw [hold_zero]
  rfl

/-- At hold `0` and `Rg = 0`, `GoldilocksLocalData` is its main text (`fgHold_eq` holds). -/
theorem goldilocksLocalData_iff_old
    (C : ACCorrectLocal (goldilocksNode sp ro) (fun v => v.val)) :
    GoldilocksLocalData sp ro C sign G 0 ↔ GoldilocksLocalDataOld sp ro C sign G :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14,
      hold_zero.symm⟩⟩

/-- At `Rg = 0`, `goldilocksACCorrectLocal` is its main text. -/
theorem goldilocksACCorrectLocal_iff_old :
    goldilocksACCorrectLocal sp ro sign G 0 ↔ goldilocksACCorrectLocalOld sp ro sign G := by
  unfold goldilocksACCorrectLocal goldilocksACCorrectLocalOld
  rw [hold_zero]
  exact exists_congr fun C => goldilocksLocalData_iff_old C

end Consensus.Goldilocks.Generic.BridgeHold

end

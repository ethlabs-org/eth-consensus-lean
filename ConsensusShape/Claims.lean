module
public import ConsensusShape.Regimes
@[expose] public section

/-! Block-level obligations over the compiled model. Escaped fields use the model
collision predicate; unconditional fields assume ExecutionValid. -/
namespace Consensus.Shape
open Model
open Run

/-- A property of every run of `F`, over every finite nonempty validator set
and every environment. -/
def AllRuns (F : Family)
    (Q : ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V],
      (E : Env V) → Model.Run (compiled F) E → Prop) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (E : Env V) (rho : Model.Run (compiled F) E), Q E rho

/-- The block contract over the compiled engine. Fields used by refinement
come first; additional block-level guarantees follow. -/
structure ShapeClaims (F : Family) (A : Assumptions) (C : Constants) : Prop where
  catchUp_pos : 0 < A.catchUp
  constants : C.Valid
  slotTicks : ∀ pub, (F pub).slotTicks = C.slotTicks
  outputOrder : AllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).Nested .finalized .stable ∧ (chainTrace rho).Nested .stable .confirmed
  finalizedMonotone : AllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).Monotone .finalized 0
  honestNeverSlashed : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.HonestNeverSlashed
  finalizedAccountable : AllRuns F fun _ rho => rho.ExecutionValid →
    ((chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable A.accFrac .finalized 0) ∨
      rho.HashCollision ∨ (Model.sysOf (compiled F) _).Slashed A.accFrac ⟨_, rho⟩
  confirmedSafe : AllRuns F fun _ rho => Sleepy rho A →
    ((chainTrace rho).Safe .confirmed 0) ∨ rho.HashCollision
  stableSafe : AllRuns F fun _ rho => Sleepy rho A →
    ((chainTrace rho).Safe .stable 0) ∨ rho.HashCollision
  confirmedLive : AllRuns F fun _ rho => ∀ k, LiveSleepy rho A k →
    (LiveFrom rho A (protoOf F _).confirmed 0 (C.growth.eval k)) ∨ rho.HashCollision
  stableLive : AllRuns F fun _ rho => ∀ k, LiveSleepy rho A k →
    (LiveFrom rho A (protoOf F _).stable 0 (C.stableGrowth.eval k)) ∨ rho.HashCollision
  stableResilient : AllRuns F fun E rho => ∀ T b₀ b₁, Outage rho A T b₀ b₁ →
    (chainTrace rho).PersistsThrough ((A.catchUp : Time) * E.Δ) .stable T b₀ b₁ ∨
      rho.HashCollision
  stableResilientFast : AllRuns F fun E rho => ∀ T b₀ b₁, FastOutage rho A T b₀ b₁ →
    (chainTrace rho).PersistsThrough ((A.catchUp : Time) * E.Δ) .stable T b₀ b₁ ∨
      rho.HashCollision
  recovered : AllRuns F fun E rho => ∀ k, Recovery rho A C k →
    (RecoveredAt rho A C (E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ)) ∨
      rho.HashCollision ∨ (Model.sysOf (compiled F) _).Slashed A.accFrac ⟨_, rho⟩
  finalizedLive : AllRuns F fun E rho => ∀ k, Finality rho A C k →
    (LiveFrom rho A (protoOf F _).finalized
      (E.gst + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)) ∨ rho.HashCollision
  /-- Additional block-level guarantees. -/
  outputValid : AllRuns F fun _ rho => rho.ExecutionValid →
    OutputValid rho (protoOf F _).confirmed ∧ OutputValid rho (protoOf F _).stable ∧
      OutputValid rho (protoOf F _).finalized
  confirmedIncluded : AllRuns F fun _ rho => Sleepy rho A →
    (IncludedFrom rho A (protoOf F _).confirmed 0 C.D_c) ∨ rho.HashCollision
  stableIncluded : AllRuns F fun _ rho => StableSleepy rho A →
    (IncludedFrom rho A (protoOf F _).stable 0 C.D_s) ∨ rho.HashCollision
  stableIncludedFast : AllRuns F fun _ rho => Fast rho A →
    (IncludedFrom rho A (protoOf F _).stable 0 C.D_f) ∨ rho.HashCollision
  recoveredLive : AllRuns F fun E rho => ∀ k, Recovery rho A C k →
    (LiveFrom rho A (protoOf F _).confirmed
      (E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ) (C.recGrowth.eval k) ∧
      LiveFrom rho A (protoOf F _).stable
        (E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ) (C.recGrowth.eval k)) ∨ rho.HashCollision
  finalizedIncluded : AllRuns F fun E rho => ∀ k, Finality rho A C k →
    (IncludedFrom rho A (protoOf F _).finalized
      (E.gst + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)) ∨ rho.HashCollision

end Consensus.Shape
end

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
structure ShapeClaims (F : Family) (C : Constants) : Prop where
  constants : C.Valid
  slotTicks : ∀ pub, (F pub).slotTicks = C.slotTicks
  outputOrder : AllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).Nested .finalized .stable ∧ (chainTrace rho).Nested .stable .confirmed
  finalizedMonotone : AllRuns F fun _ rho => rho.ExecutionValid →
    (chainTrace rho).Monotone .finalized 0
  honestNeverSlashed : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.HonestNeverSlashed
  finalizedAccountable : AllRuns F fun _ rho => rho.ExecutionValid →
    ((chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable .finalized 0) ∨ rho.HashCollision
  confirmedSafe : AllRuns F fun _ rho => Sleepy rho C →
    ((chainTrace rho).Safe .confirmed 0) ∨ rho.HashCollision
  stableSafe : AllRuns F fun _ rho => Sleepy rho C →
    ((chainTrace rho).Safe .stable 0) ∨ rho.HashCollision
  confirmedLive : AllRuns F fun _ rho => ∀ k, LiveSleepy rho C k →
    (LiveFrom rho C (protoOf F _).confirmed 0 (C.growth.eval k)) ∨ rho.HashCollision
  stableLive : AllRuns F fun _ rho => ∀ k, LiveSleepy rho C k →
    (LiveFrom rho C (protoOf F _).stable 0 (C.stableGrowth.eval k)) ∨ rho.HashCollision
  stableResilient : AllRuns F fun E rho => ∀ T b₀ b₁, Outage rho C T b₀ b₁ →
    (chainTrace rho).PersistsThrough ((C.catchUp : Time) * E.Δ) .stable T b₀ b₁ ∨
      rho.HashCollision
  stableResilientFast : AllRuns F fun E rho => ∀ T b₀ b₁, FastOutage rho C T b₀ b₁ →
    (chainTrace rho).PersistsThrough ((C.catchUp : Time) * E.Δ) .stable T b₀ b₁ ∨
      rho.HashCollision
  recovered : AllRuns F fun E rho => ∀ k, Recovery rho C k →
    (RecoveredAt rho C (E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ)) ∨ rho.HashCollision
  finalizedLive : AllRuns F fun E rho => ∀ k, Finality rho C k →
    (LiveFrom rho C (protoOf F _).finalized
      (E.gst + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)) ∨ rho.HashCollision
  /-- Additional block-level guarantees. -/
  outputValid : AllRuns F fun _ rho => rho.ExecutionValid →
    OutputValid rho (protoOf F _).confirmed ∧ OutputValid rho (protoOf F _).stable ∧
      OutputValid rho (protoOf F _).finalized
  confirmedIncluded : AllRuns F fun _ rho => Sleepy rho C →
    (IncludedFrom rho C (protoOf F _).confirmed 0 C.D_c) ∨ rho.HashCollision
  stableIncluded : AllRuns F fun _ rho => StableSleepy rho C →
    (IncludedFrom rho C (protoOf F _).stable 0 C.D_s) ∨ rho.HashCollision
  stableIncludedFast : AllRuns F fun _ rho => Fast rho C →
    (IncludedFrom rho C (protoOf F _).stable 0 C.D_f) ∨ rho.HashCollision
  recoveredLive : AllRuns F fun E rho => ∀ k, Recovery rho C k →
    (LiveFrom rho C (protoOf F _).confirmed
      (E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ) (C.recGrowth.eval k) ∧
      LiveFrom rho C (protoOf F _).stable
        (E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ) (C.recGrowth.eval k)) ∨ rho.HashCollision
  finalizedIncluded : AllRuns F fun E rho => ∀ k, Finality rho C k →
    (IncludedFrom rho C (protoOf F _).finalized
      (E.gst + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)) ∨ rho.HashCollision

end Consensus.Shape
end

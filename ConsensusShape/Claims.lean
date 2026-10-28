module
public import ConsensusShape.Regimes
@[expose] public section

/-! Block-level obligations over the compiled model. Escaped fields use the model
collision predicate; unconditional fields assume ShapeValid. -/
namespace Consensus.Shape
open AvailableChain (Slot Time)
open AvailableChain.Generic
open Model
open Run

/-- A property of every run of `F`, over every finite nonempty validator set
and every environment. -/
def AllRuns (F : Family)
    (Q : ∀ {V : Type} [Fintype V] [DecidableEq V], (E : Env V) → Model.Run (compiled F) E →
    Prop) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (E : Env V) (rho : Model.Run (compiled F) E), Q E rho

/-- How an escaped claim `X` of run `rho` is stated. -/
abbrev Escape (F : Family) :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {E : Env V}, Model.Run (compiled F) E → Prop → Prop

/-- "X, or a hash collision was observed". -/
def orCollision (F : Family) : Escape F := fun rho X => X ∨ rho.HashCollision

/-- "If the hash is injective (and never 0), then X". -/
def ifInjective (F : Family) : Escape F := fun rho X => rho.InjectiveHash → X

/-- The contract, with the escaped fields in the form `W`. -/
structure ClaimsWith (F : Family) (C : Constants) (W : Escape F) : Prop where
  constants : C.Valid
  /-- The slot length is the reported one, for all public parameters. -/
  slotTicks : ∀ pub, (F pub).slotTicks = C.slotTicks
  /-- Provenance, linkage and slot order of every output. Unconditional. -/
  outputValid : AllRuns F fun _ rho => ShapeValid rho →
    OutputValid rho (protoOf F _).confirmed ∧ OutputValid rho (protoOf F _).stable ∧
      OutputValid rho (protoOf F _).finalized
  /-- Stable is a prefix of confirmed. Unconditional. -/
  outputOrder : AllRuns F fun _ rho => ShapeValid rho →
    Below rho (protoOf F _).stable (protoOf F _).confirmed
  confirmedSafe : AllRuns F fun _ rho => ∀ t₀, Sleepy rho C t₀ →
    W rho (SafeFrom rho (protoOf F _).confirmed t₀)
  stableSafe : AllRuns F fun _ rho => ∀ t₀, Sleepy rho C t₀ →
    W rho (SafeFrom rho (protoOf F _).stable t₀)
  confirmedIncluded : AllRuns F fun _ rho => ∀ t₀, Sleepy rho C t₀ →
    W rho (IncludedFrom rho C (protoOf F _).confirmed t₀ C.D_c)
  stableIncluded : AllRuns F fun _ rho => ∀ t₀, StableSleepy rho C t₀ →
    W rho (IncludedFrom rho C (protoOf F _).stable t₀ C.D_s)
  stableIncludedFast : AllRuns F fun _ rho => ∀ t₀, Fast rho C t₀ →
    W rho (IncludedFrom rho C (protoOf F _).stable t₀ C.D_f)
  confirmedLive : AllRuns F fun _ rho => ∀ t₀ k, LiveSleepy rho C t₀ k →
    W rho (LiveFrom rho C (protoOf F _).confirmed t₀ (C.growth.eval k))
  stableLive : AllRuns F fun _ rho => ∀ t₀ k, LiveSleepy rho C t₀ k →
    W rho (LiveFrom rho C (protoOf F _).stable t₀ (C.stableGrowth.eval k))
  stableResilient : AllRuns F fun _ rho => ∀ T b₀ b₁, Outage rho C T b₀ b₁ →
    W rho (PersistsThrough rho C (protoOf F _).stable T b₀ b₁)
  stableResilientFast : AllRuns F fun _ rho => ∀ T b₀ b₁, FastOutage rho C T b₀ b₁ →
    W rho (PersistsThrough rho C (protoOf F _).stable T b₀ b₁)
  recovered : AllRuns F fun E rho => ∀ k, Recovery rho C k →
    W rho (RecoveredAt rho C (E.t_GST + ((C.recovery.eval k : Nat) : Time) * E.Δ))
  /-- Additional O4 growth obligation, retained at L1 until refinement is proved. -/
  recoveredLive : AllRuns F fun E rho => ∀ k, Recovery rho C k →
    W rho (LiveFrom rho C (protoOf F _).confirmed
      (E.t_GST + (C.recovery.eval k : Time) * E.Δ) (C.recGrowth.eval k) ∧
      LiveFrom rho C (protoOf F _).stable
        (E.t_GST + (C.recovery.eval k : Time) * E.Δ) (C.recGrowth.eval k))
  /-- Each honest node's finalized output only extends, in every valid run.
  Unconditional. -/
  finalizedMonotone : AllRuns F fun _ rho => ShapeValid rho →
    MonotoneFrom rho (protoOf F _).finalized 0
  /-- Conflicting finalized reads expose a third of the validators (or a hash
  collision). -/
  finalizedAccountable : AllRuns F fun _ rho => ShapeValid rho →
    W rho (AccountablySafeFrom rho (protoOf F _).finalized 0)
  /-- No honest validator is ever slashable, in every valid run.
  Unconditional. -/
  honestNeverSlashed : AllRuns F fun _ rho => ShapeValid rho →
    rho.HonestNeverSlashed
  finalizedIncluded : AllRuns F fun E rho => ∀ k, Finality rho C k →
    W rho (IncludedFrom rho C (protoOf F _).finalized
      (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k))
  finalizedLive : AllRuns F fun E rho => ∀ k, Finality rho C k →
    W rho (LiveFrom rho C (protoOf F _).finalized
      (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k))

/-- The contract: every escaped claim holds or a hash collision was observed. -/
abbrev Claims (F : Family) (C : Constants) : Prop := ClaimsWith F C (orCollision F)

/-- The contract for injective hashes only: what an instance may prove
instead of `Claims`. Equivalence is not proved in this library. -/
abbrev ClaimsInj (F : Family) (C : Constants) : Prop := ClaimsWith F C (ifInjective F)

/-- The block contract over the compiled engine. -/
abbrev ShapeClaims (F : Family) (C : Constants) : Prop := Claims F C

end Consensus.Shape
end

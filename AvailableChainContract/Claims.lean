module
public import AvailableChainContract.Regimes

@[expose] public section

/-! # The claims

`Claims F C` is the whole contract for a protocol family `F` with constants
`C`. Every field holds for every finite nonempty validator set, every
environment (`Δ`, GST, awake profile) and every run (honest set, events,
seats, proposers, inputs). An instance proves `Claims F C` for its family and a
literal `C`; nothing else of the instance is needed to state what is proved.

Outputs are pinned from above (safety, accountable safety, output order,
provenance) and from below (inclusion of the honest proposer's own block,
growth, persistence), so the getters cannot be degenerate. The slashing rule is
pinned from above (`honestNeverSlashed`) and from below (accountable safety with
finality liveness). -/

namespace AvailableChain.Contract

open AvailableChain.Generic

/-- A property of every run of `F`, over every finite nonempty validator set
and every environment. -/
def AllRuns (F : Family)
    (Q : ∀ {V : Type} [Fintype V] [DecidableEq V], (E : Env V) → Run F E → Prop) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (E : Env V) (rho : Run F E), Q E rho

/-- The contract. -/
structure Claims (F : Family) (C : Constants) : Prop where
  constants : C.Valid
  /-- The slot length is the reported one, for all public parameters. -/
  slotTicks : ∀ pub, (F pub).slotTicks = C.slotTicks
  /-- Provenance and slot order of every output. -/
  outputValid : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.OutputValid (protoOf F _).confirmed ∧ rho.OutputValid (protoOf F _).stable ∧
      rho.OutputValid (protoOf F _).finalized
  /-- Stable is below confirmed. -/
  outputOrder : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.Below (protoOf F _).stable (protoOf F _).confirmed
  confirmedSafe : AllRuns F fun _ rho => ∀ t₀, rho.Sleepy C t₀ →
    rho.SafeFrom (protoOf F _).confirmed t₀
  stableSafe : AllRuns F fun _ rho => ∀ t₀, rho.Sleepy C t₀ →
    rho.SafeFrom (protoOf F _).stable t₀
  confirmedIncluded : AllRuns F fun _ rho => ∀ t₀, rho.Sleepy C t₀ →
    rho.IncludedFrom C (protoOf F _).confirmed t₀ C.D_c
  stableIncluded : AllRuns F fun _ rho => ∀ t₀, rho.StableSleepy C t₀ →
    rho.IncludedFrom C (protoOf F _).stable t₀ C.D_s
  stableIncludedFast : AllRuns F fun _ rho => ∀ t₀, rho.Fast C t₀ →
    rho.IncludedFrom C (protoOf F _).stable t₀ C.D_f
  confirmedLive : AllRuns F fun _ rho => ∀ t₀ k, rho.LiveSleepy C t₀ k →
    rho.LiveFrom C (protoOf F _).confirmed t₀ (C.growth.eval k)
  stableLive : AllRuns F fun _ rho => ∀ t₀ k, rho.LiveSleepy C t₀ k →
    rho.LiveFrom C (protoOf F _).stable t₀ (C.stableGrowth.eval k)
  stableResilient : AllRuns F fun _ rho => ∀ T b₀ b₁, rho.Outage C T b₀ b₁ →
    rho.PersistsThrough C (protoOf F _).stable T b₀ b₁
  stableResilientFast : AllRuns F fun _ rho => ∀ T b₀ b₁, rho.FastOutage C T b₀ b₁ →
    rho.PersistsThrough C (protoOf F _).stable T b₀ b₁
  recovered : AllRuns F fun E rho => ∀ k, rho.Recovery C k →
    rho.RecoveredAt C (E.t_GST + ((C.recovery.eval k : Nat) : Time) * E.Δ)
  /-- Each honest node's finalized output only extends, in every valid run. -/
  finalizedMonotone : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.MonotoneFrom (protoOf F _).finalized 0
  /-- Conflicting finalized reads expose a third of the validators. -/
  finalizedAccountable : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.AccountablySafeFrom (protoOf F _).finalized 0
  /-- No honest validator is ever slashable, in every valid run. -/
  honestNeverSlashed : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.HonestNeverSlashed
  finalizedIncluded : AllRuns F fun E rho => ∀ k, rho.Finality C k →
    rho.IncludedFrom C (protoOf F _).finalized
      (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)
  finalizedLive : AllRuns F fun E rho => ∀ k, rho.Finality C k →
    rho.LiveFrom C (protoOf F _).finalized
      (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k)

end AvailableChain.Contract

end

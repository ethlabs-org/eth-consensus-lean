module
public import AvailableChainContract.Regimes

@[expose] public section

/-! # The claims

`Claims F C` is the whole contract for a protocol family `F` with constants
`C`. Every field holds for every finite nonempty validator set, every
environment (`Δ`, GST, awake profile) and every run (honest set, events,
seats, proposers, inputs, hash function). An instance proves `Claims F C` for
its family and a literal `C`; nothing else of the instance is needed to state
what is proved.

Hashes. The hash is arbitrary run data, so it may have collisions. Most
claims hold "or a hash collision was observed" (`Run.HashCollision`), as
accountability holds "or a third is slashable". Honest code learns the hash only
through the digests the engine passes, of observed signed headers.
`ClaimsWith` takes the form of the escaped fields as a parameter:
* `Claims`: "X ∨ HashCollision", for every hash;
* `ClaimsInj`: "InjectiveHash → X".
`claims_iff_claimsInj` (AvailableChainContractProofs/Lift.lean) proves the two
equivalent: the escape adds nothing beyond the injective case, and an instance
may prove its claims for injective hashes only.
Provenance (`outputValid`), output order, finalized monotonicity and
`honestNeverSlashed` are unconditional in both forms.

Outputs are pinned from above (safety, accountable safety, output order,
provenance) and from below (inclusion of the honest proposer's own header,
growth, persistence). The slashing rule is pinned from above
(`honestNeverSlashed`) and from below (accountable safety with finality
liveness). -/

namespace AvailableChain.Contract

open AvailableChain.Generic

/-- A property of every run of `F`, over every finite nonempty validator set
and every environment. -/
def AllRuns (F : Family)
    (Q : ∀ {V : Type} [Fintype V] [DecidableEq V], (E : Env V) → Run F E → Prop) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (E : Env V) (rho : Run F E), Q E rho

/-- How an escaped claim `X` of run `rho` is stated. -/
abbrev Escape (F : Family) :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {E : Env V}, Run F E → Prop → Prop

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
  outputValid : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.OutputValid (protoOf F _).confirmed ∧ rho.OutputValid (protoOf F _).stable ∧
      rho.OutputValid (protoOf F _).finalized
  /-- Stable is a prefix of confirmed. Unconditional. -/
  outputOrder : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.Below (protoOf F _).stable (protoOf F _).confirmed
  confirmedSafe : AllRuns F fun _ rho => ∀ t₀, rho.Sleepy C t₀ →
    W rho (rho.SafeFrom (protoOf F _).confirmed t₀)
  stableSafe : AllRuns F fun _ rho => ∀ t₀, rho.Sleepy C t₀ →
    W rho (rho.SafeFrom (protoOf F _).stable t₀)
  confirmedIncluded : AllRuns F fun _ rho => ∀ t₀, rho.Sleepy C t₀ →
    W rho (rho.IncludedFrom C (protoOf F _).confirmed t₀ C.D_c)
  stableIncluded : AllRuns F fun _ rho => ∀ t₀, rho.StableSleepy C t₀ →
    W rho (rho.IncludedFrom C (protoOf F _).stable t₀ C.D_s)
  stableIncludedFast : AllRuns F fun _ rho => ∀ t₀, rho.Fast C t₀ →
    W rho (rho.IncludedFrom C (protoOf F _).stable t₀ C.D_f)
  confirmedLive : AllRuns F fun _ rho => ∀ t₀ k, rho.LiveSleepy C t₀ k →
    W rho (rho.LiveFrom C (protoOf F _).confirmed t₀ (C.growth.eval k))
  stableLive : AllRuns F fun _ rho => ∀ t₀ k, rho.LiveSleepy C t₀ k →
    W rho (rho.LiveFrom C (protoOf F _).stable t₀ (C.stableGrowth.eval k))
  stableResilient : AllRuns F fun _ rho => ∀ T b₀ b₁, rho.Outage C T b₀ b₁ →
    W rho (rho.PersistsThrough C (protoOf F _).stable T b₀ b₁)
  stableResilientFast : AllRuns F fun _ rho => ∀ T b₀ b₁, rho.FastOutage C T b₀ b₁ →
    W rho (rho.PersistsThrough C (protoOf F _).stable T b₀ b₁)
  recovered : AllRuns F fun E rho => ∀ k, rho.Recovery C k →
    W rho (rho.RecoveredAt C (E.t_GST + ((C.recovery.eval k : Nat) : Time) * E.Δ))
  /-- Each honest node's finalized output only extends, in every valid run.
  Unconditional. -/
  finalizedMonotone : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.MonotoneFrom (protoOf F _).finalized 0
  /-- Conflicting finalized reads expose a third of the validators (or a hash
  collision). -/
  finalizedAccountable : AllRuns F fun _ rho => rho.ExecutionValid →
    W rho (rho.AccountablySafeFrom (protoOf F _).finalized 0)
  /-- No honest validator is ever slashable, in every valid run.
  Unconditional. -/
  honestNeverSlashed : AllRuns F fun _ rho => rho.ExecutionValid →
    rho.HonestNeverSlashed
  finalizedIncluded : AllRuns F fun E rho => ∀ k, rho.Finality C k →
    W rho (rho.IncludedFrom C (protoOf F _).finalized
      (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k))
  finalizedLive : AllRuns F fun E rho => ∀ k, rho.Finality C k →
    W rho (rho.LiveFrom C (protoOf F _).finalized
      (E.t_GST + ((C.finStart.eval k : Nat) : Time) * E.Δ) (C.finDelay.eval k))

/-- The contract: every escaped claim holds or a hash collision was observed. -/
abbrev Claims (F : Family) (C : Constants) : Prop := ClaimsWith F C (orCollision F)

/-- The contract for injective hashes only: what an instance may prove
instead of `Claims` (`claims_of_claimsInj`). -/
abbrev ClaimsInj (F : Family) (C : Constants) : Prop := ClaimsWith F C (ifInjective F)

end AvailableChain.Contract

end

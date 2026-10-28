module
public import ConsensusShape.Run

@[expose] public section

/-! # Shape claims (L2)

What a shape family proves about its compiled runs, for a contract `K`
(numbers and progress requirements): the chain-level mirror of the L0
behaviour table (`Behaviour`), each claim on every valid run of every
validator set and environment, stated on the compiled system `Sys F V` with
the L0 regimes and `System.Holds`: each risk-bearing claim holds "or an
observed hash collision" (output validity, nesting and final monotonicity are
unconditional, `HoldsAlways`):

* always: output validity, nesting, final monotonicity;
* final: local accountability for fraction `α`, and `ProposalLiveReady` from
  the heal point when healthy from a GST with progress from `readyFrom`;
* available and stable: ready-reader safety and `ProposalLiveReady` when
  sleepy, and from the heal point when healthy from a GST (safety needs
  progress only on `[readyFrom, heal]`);
* stable: outage resilience into the resilience target.

`ProposalLiveReady` replaces transaction liveness (the payload bridge,
`proposalLive_txLive`). It owes a proposal only when a node is ready at the
inclusion deadline, exactly as L0 `TxLive` owes inclusion only to ready
readers. Prefix forms are not restated: they follow from the
L0 prefix closure (`Good.*_prefix`). Non-framing is an L1 theorem, so there is
no field for it. `refinement` turns these into `Behaviour`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- The chain-level claims at validators `V`, on the compiled system
`Sys F V`. Each field is its L0 `Behaviour` counterpart (`Holds`: on valid
runs satisfying the regime, or an observed hash collision; `HoldsAlways`: no
escape), with the chain trace of the run `r.2` for the ledger trace and
`ProposalLiveReady` for `TxLive`; latencies are the `Nat` coefficients
`K.params.latency`. -/
structure ShapeClaimsAt (F : ShapeFamily O Info) (K : Contract ProgressReq) (V : Type)
    [Fintype V] [DecidableEq V] : Prop where
  /-- Every provided output is valid. -/
  outputValid : (Sys F V).HoldsAlways fun r => ∀ c g, O.output c = some g → OutputValid r.2 g
  /-- Lower-rank chains are prefixes of higher-rank ones. -/
  nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
    (Sys F V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂
  /-- The final chain never rolls back. -/
  finalMonotone : ∀ g, O.output .final = some g →
    (Sys F V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0
  /-- Local accountability of the final chain for fraction `α`, in every
  environment: conflicting honest reads convict `α` from their own views. -/
  finalAccountable : ∀ g, O.output .final = some g → (Sys F V).Holds (fun _ => True)
    fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0
  /-- Final liveness: healthy from `gst` with progress from `readyFrom` to the
  horizon, proposals are included from the heal point. -/
  finalLive : ∀ g, O.output .final = some g → ∀ (i : K.Idx) (gst : Time), (Sys F V).Holds
    (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K .final i
      ((Sys F V).ready K gst r) ((Sys F V).pt r).horizon r)
    fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g ((Sys F V).heal K .final i gst r)
      (K.params.latency .final i)
  /-- Sleepy safety of an available or stable chain, for ready readers. -/
  sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    (Sys F V).Holds ((Sys F V).Sleepy K) fun r =>
      (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0
  /-- Sleepy liveness, with progress on the whole run. -/
  sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ i : K.Idx, (Sys F V).Holds
      (fun r => (Sys F V).Sleepy K r ∧ (Sys F V).prog (shapeProgress F V) K cap i 0
        ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 (K.params.latency cap i)
  /-- Healed safety: healthy from `gst` with progress on `[readyFrom, heal]`,
  ready readers are safe from the heal point. -/
  healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K cap i
        ((Sys F V).ready K gst r) ((Sys F V).heal K cap i gst r) r)
      fun r => (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g ((Sys F V).heal K cap i gst r)
  /-- Healed liveness: healthy from `gst` with progress from `readyFrom` to the
  horizon, proposals are included from the heal point. -/
  healedLive : ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
    ∀ (i : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K cap i
        ((Sys F V).ready K gst r) ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g ((Sys F V).heal K cap i gst r)
        (K.params.latency cap i)
  /-- Outage resilience of the stable chain, into the resilience target. -/
  persists : ∀ g, O.output .stable = some g → ∀ T b₀ b₁,
    (Sys F V).Holds ((Sys F V).Outage K T b₀ b₁) fun r =>
      (chainTrace r.2).ProtectedThrough ((Sys F V).cDur K r) g (resilienceTarget O g) T b₀ b₁

/-- The chain-level claims of a shape family for contract `K`: at every finite
validator type. -/
def ShapeClaims (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], ShapeClaimsAt F K V

end Consensus.Shape

end

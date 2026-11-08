module
public import ConsensusLean.Comparison.Basic
public import ConsensusLean.Spec.Shape.Run

@[expose] public section

/-! # Slice 0 latency profiles (statements)

Two latency axes, kept distinct, on synchronous runs (`PSync 0`) with full participation
(`FullAwake`); the only parameter is the fault cap `fcap` (`faultCount horizon ≤ fcap`), with the
order of `ℕ`.

* `TxLatency0 S X K cap i lat`: upstream's `TxLive` from `0` with delay `lat f·ΔAC`, under the
  progress premise of `(cap, i)` on the whole run. It includes submission and relay timing and the
  wait for an honest proposer, so it is not proposal latency.
* `ProposalLatency0 F K cap i lat` (chain shapes, L2): upstream's `ProposalLiveReady` from `0` with
  coefficient `lat f`, under the same premises. It has no contract default; it is proved per
  protocol.

Coverage (`TxLatencyCoverage0`, `ProposalLatencyCoverage0`): for every feasible cap (`f ≤ n − 2`)
with a finite bound, a valid, excuse-free run of the class with exactly `f` validators compromised
by the horizon, the progress premise and the claim active. -/

namespace Consensus.Comparison

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}

section L0

variable (S : System V) (X : Progress S Prog) (K : Contract Prog)

/-- **Slice 0's synchronous run class** at fault cap `f`: synchrony (`PSync 0`), at most `f`
validators compromised by the horizon, full participation. -/
def Sync0Class (f : ℕ) (r : S.Run) : Prop :=
  (S.log r).PSync (S.pt r) 0 ∧ (S.pt r).faultCount (S.pt r).horizon ≤ f ∧ FullAwake S r

/-- **Slice 0 transaction latency** of `cap` at index `i` with bound `lat`: on valid runs of the
synchronous class at `f` with the progress premise of `(cap, i)` on `[0, horizon]`, unless the run's
excuse holds, every transaction submitted by `t` to an honest awake node is in every ready read of
`cap`'s output from `max t 0 + ΔAC + lat f·ΔAC`. -/
structure TxLatency0 (cap : Capability) (i : K.Idx) (lat : Bound ℕ) : Prop where
  mono : AdverseMonotone lat
  live : ∀ f (d : ℕ), lat f = d → ∀ g, S.schema.output cap = some g →
    S.Holds (fun r => Sync0Class S f r ∧ S.prog X K cap i 0 (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g 0 ((d : Time) * (S.pt r).env.ΔAC))

/-- **Coverage of a transaction latency bound**: for every `f ≤ n − 2` with `lat f` finite, a
valid, excuse-free run of the synchronous class with exactly `f` validators compromised by the
horizon, the progress premise of `(cap, i)` on the whole run, and active liveness from `0` with
delay `lat f·ΔAC`. -/
structure TxLatencyCoverage0 (cap : Capability) (i : K.Idx) (lat : Bound ℕ) : Prop where
  covers : ∀ (f d : ℕ), f + 2 ≤ Fintype.card V → lat f = d → ∃ r, S.Valid r ∧ ¬ S.Excuse r ∧
    Sync0Class S f r ∧ (S.pt r).faultCount (S.pt r).horizon = f ∧
    S.prog X K cap i 0 (S.pt r).horizon r ∧
    (S.pt r).TxLiveActive (S.cDur K r) 0 ((d : Time) * (S.pt r).env.ΔAC)

end L0

section L2

open Shape

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  (F : ChainShapeFamily O Info) (K : Contract Blocks.ProgressReq)

/-- **Slice 0 proposal latency** of a chain shape family's `cap` at index `i` with bound `lat`: on
valid runs of the compiled system in the synchronous class at `f` with the progress premise of
`(cap, i)` on `[0, horizon]`, unless the run's excuse holds, `ProposalLiveReady` from `0` with
coefficient `lat f`: for every `t ≥ 0` with a reader ready at `t + lat f·ΔAC` within the horizon,
a header released after `t` by a ready key in a proposal role is in every ready read by then. -/
structure ProposalLatency0 (V : Type) [Fintype V] [DecidableEq V] (cap : Capability) (i : K.Idx)
    (lat : Bound ℕ) : Prop where
  mono : AdverseMonotone lat
  live : ∀ f (d : ℕ), lat f = d → ∀ g, O.output cap = some g →
    (Sys F V).Holds
      (fun r => Sync0Class (Sys F V) f r ∧
        (Sys F V).prog (shapeProgress F V) K cap i 0 ((Sys F V).pt r).horizon r)
      (fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 d)

/-- **Coverage of a proposal latency bound**: for every `f ≤ n − 2` with `lat f` finite, a valid,
excuse-free run of the synchronous class with exactly `f` validators compromised by the horizon,
the progress premise of `(cap, i)` on the whole run, and a node ready at a deadline
`t + lat f·ΔAC` within the horizon for some `t ≥ 0` (the claim is reader-conditional). -/
structure ProposalLatencyCoverage0 (V : Type) [Fintype V] [DecidableEq V] (cap : Capability)
    (i : K.Idx) (lat : Bound ℕ) : Prop where
  covers : ∀ (f d : ℕ), f + 2 ≤ Fintype.card V → lat f = d → ∃ r, (Sys F V).Valid r ∧
    ¬ (Sys F V).Excuse r ∧ Sync0Class (Sys F V) f r ∧
    ((Sys F V).pt r).faultCount ((Sys F V).pt r).horizon = f ∧
    (Sys F V).prog (shapeProgress F V) K cap i 0 ((Sys F V).pt r).horizon r ∧
    ∃ t v, 0 ≤ t ∧ t + (d : Time) * ((Sys F V).pt r).env.ΔAC ≤ ((Sys F V).pt r).horizon ∧
      ((Sys F V).pt r).Ready ((Sys F V).cDur K r) v (t + (d : Time) * ((Sys F V).pt r).env.ΔAC)

end L2

end Consensus.Comparison

end

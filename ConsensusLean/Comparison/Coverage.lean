module
public import ConsensusLean.Comparison.Heal
public import ConsensusLean.Comparison.Latency
public import ConsensusLean.Spec.Shape.Claims
public import ConsensusLean.Spec.Shape.ProgressFit

@[expose] public section

/-! # Slice 0 coverage for chain shapes (statements)

`HealCoverage0`, `TxLatencyCoverage0` and `ProposalLatencyCoverage0` ask, for every feasible
parameter point with a finite claim, for a valid, excuse-free witness run that attains the
environment parameters with the claim active. These statements say which bounds of a chain
shape family are covered: those that claim only where such a witness can exist.

* `AdmitsFaults π f`: the progress requirement `π` can hold with `f` validators compromised for
  the whole run (a recurrence always: its proposers can be honest; a bound on the validators not
  ready only if it is at least `f`). The witnesses have exactly `fcap` compromised validators and
  carry the profile's progress premise, so a bound that is finite where the requirement cannot
  hold is not covered.
* `HealSupport0`: at every feasible point with a finite heal claim, the requirement admits `fcap`;
  for a split incident moreover `fcap < β·n`. The split witness needs a message an honest node
  sends during the incident, and in a chain shape the only send the contract guarantees is an
  honest proposal, from healthy liveness (`ShapeClaimsAt.healthyLive`), which needs the healthy
  fault bound.
* `ProposalsNotFGAtt F`: no header signed in a proposal role is an FG attestation, so a held
  proposal is a held message of the `ΔAC` class (`Exercised` asks for one).
* `ShapeHealCoverage0`, `ShapeTxLatencyCoverage0`, `ShapeProposalLatencyCoverage0`: the three
  coverage packages of Slice 0 for chain shape families, under those premises, the progress fit
  of the contract, an FG delay of at least one `ΔAC`, and the provided output. The heal
  package also takes the chain-level claims (for the split witness's honest send); the latency
  packages do not need them (their class constrains no incident). -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (Obj)

/-- The progress requirement `π` admits `f` validators compromised for the whole run: always for a
recurrence (its proposers can be honest), and for a bound on the validators not ready when the
bound is at least `f`. -/
def AdmitsFaults : ProgressReq → ℕ → Prop
  | .recur _, _ => True
  | .notReadyAtMost m, f => f ≤ m

variable {V : Type} [Fintype V]

/-- **Support of the heal bounds** at `(cap, i)`: at every feasible point with a finite safety
claim, or finite liveness and latency claims, the progress requirement of `(cap, i)` admits
`fcap` compromised validators, and a split incident has `fcap < β·n`. -/
def HealSupport0 (K : Contract ProgressReq) (cap : Capability) (i : K.Idx)
    (hs hl lat : Bound (Slice0Q V)) : Prop :=
  ∀ q : Slice0Q V, q.Feasible → (hs q < ⊤ ∨ (hl q < ⊤ ∧ lat q < ⊤)) →
    AdmitsFaults (K.progress cap i) q.fcap ∧
      match q.a with
      | .any => True
      | .split _ => (q.fcap : ℚ) < K.params.β * Fintype.card V

variable (V) in
/-- **Support of a latency bound** at `(cap, i)`: at every cap `f ≤ n − 2` with a finite bound,
the progress requirement of `(cap, i)` admits `f` compromised validators. -/
def LatencySupport0 (K : Contract ProgressReq) (cap : Capability) (i : K.Idx) (lat : Bound ℕ) :
    Prop :=
  ∀ f (d : ℕ), f + 2 ≤ Fintype.card V → lat f = d → AdmitsFaults (K.progress cap i) f

/-- No header signed in a proposal role is an FG attestation. -/
def ProposalsNotFGAtt {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) : Prop :=
  ∀ (pub : Model.Public) (k : Fin pub.n) (r : ShapeRole (F pub).skel.Kind) (h : Header Info)
    (cs : List (ShapeObj pub.n (F pub).skel.Kind Info (F pub).Body)),
    ProposalRole h r → ¬ (F pub).isFGAtt (Obj.mk (.signed k r) (.item h) cs)

/-- **Heal coverage for chain shapes**: a chain shape family with the chain-level claims, a
fitting progress requirement, proposals that are not FG attestations and an FG delay of at least
one `ΔAC` covers every heal profile `(hs, hl, lat)` at a provided output's `(cap, i)` whose finite
claims lie in the support (`HealSupport0`). -/
def ShapeHealCoverage0 : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V],
    ShapeClaimsAt F K V → ProgressFits K F → ProposalsNotFGAtt F → 1 ≤ K.params.fgDelay →
    ∀ (cap : Capability) (i : K.Idx) (hs hl lat : Bound (Slice0Q V)), (O.output cap).isSome →
      HealSupport0 K cap i hs hl lat →
      HealCoverage0 (Sys F V) (shapeProgress F V) K cap i hs hl lat

/-- **Transaction latency coverage for chain shapes**: a chain shape family with a fitting
progress requirement covers every transaction latency bound at a provided output's `(cap, i)`
whose finite values lie in the support (`LatencySupport0`). -/
def ShapeTxLatencyCoverage0 : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V],
    ProgressFits K F →
    ∀ (cap : Capability) (i : K.Idx) (lat : Bound ℕ), (O.output cap).isSome →
      LatencySupport0 V K cap i lat → TxLatencyCoverage0 (Sys F V) (shapeProgress F V) K cap i lat

/-- **Proposal latency coverage for chain shapes**: a chain shape family with a fitting progress
requirement covers every proposal latency bound at a provided output's `(cap, i)` whose finite
values lie in the support (`LatencySupport0`). -/
def ShapeProposalLatencyCoverage0 : Prop :=
  ∀ {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V],
    ProgressFits K F →
    ∀ (cap : Capability) (i : K.Idx) (lat : Bound ℕ), (O.output cap).isSome →
      LatencySupport0 V K cap i lat → ProposalLatencyCoverage0 F K V cap i lat

end Consensus.Comparison

end

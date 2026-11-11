module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ChainRepresentation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation

public section

/-! # Unconditional honest-read chain edges

All rows are UNPROVED proposition contracts, not evidence. The same E1 map is reused for
the actual engine run. No cross-reader union, collision excuse or constant-fault condition
is available to these edges. They do not use `ReadRepresentation.ancestor_prefix`.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- The node state at the mapped cut of this engine reader, not a fresh simulation witness. -/
noncomputable abbrev mappedReadState (M : RunMap (A := A) rho payload)
    (v : V) (i : Nat) : NodeState A :=
  M.trace.state (M.validator.symm v) (M.cut i)

/-- UNPROVED actual-read suppliers. Read-time honesty is charged at `rho.cutTime i`,
never at the possibly later micro-cut time. Concrete source:
`Growing/Simulation/Endpoint/Outputs.lean:69,148,167`: freeze at the actual reader's
time (at the later read for growth), preserve both mapped states, then use local-store
reachability, cache membership, tree growth and finalized ancestry. The arbitrary-AC
suppliers are OPEN; a value of `RunMap` alone does not establish these invariants. -/
structure HonestChainReads (M : RunMap (A := A) rho payload) : Prop where
  /-- Output read transport: E1 `output_eq` and `state_eq`; concrete
  `Simulation/Chains.lean:31` and growing endpoint `Outputs.lean:160,182`.
  The output clock stays the actual engine read clock, with no equality to trace time. -/
  output_read : ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) → ∀ g,
    (chainTrace rho).read g v i =
      (M.chain (mappedReadState M v i)
        (M.tip g (mappedReadState M v i) (rho.cutTime i))).map M.header
  /-- Reachability of the store at each actual honest engine read. -/
  reachable : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    (mappedReadState M v i).fg.Reachable A.genesisPayload
  /-- Rank-ordered provided tips have ancestry in this one store, at its actual clock.
  Goldilocks source: growing endpoint `Outputs.lean:156–162` (frame rootedness and
  AC tips at the stored clock). Equal confirmed aliases require only reflexivity.
  This is local ancestry, not an assumption of the target chain-prefix claim. -/
  nested_tips : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) → ∀ c₁ c₂ g₁ g₂,
    c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
    (mappedReadState M v i).fg.Anc
      (M.tip g₁ (mappedReadState M v i) (rho.cutTime i))
      (M.tip g₂ (mappedReadState M v i) (rho.cutTime i))
  /-- Finalized cache membership at the old honest read, required by store growth. -/
  finalized_held : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    (mappedReadState M v i).fg.F ∈ (mappedReadState M v i).fg.tree
  /-- The E1 final-tip identity, separately from cross-reader representation laws.
  Source: `AsChainShape.lean:559` and `Simulation/Outputs.lean:29`. -/
  finalized_tip : ∀ g, O.output .final = some g → ∀ st t, M.tip g st t = st.fg.F
  /-- A reader still honest at the later actual engine cut has not lost held blocks.
  Source: growing endpoint `Outputs.lean:174–188`, on the later reader's prefix. -/
  tree_growth : rho.ExecutionValid → ∀ v i j, i ≤ j → j ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime j) →
    (mappedReadState M v i).fg.tree ⊆ (mappedReadState M v j).fg.tree
  /-- Finalized cache ancestry is inside the later store; no union coherence is needed.
  Source: growing endpoint `Outputs.lean:189`; generic FG `FinalMonotone` is node-clock
  indexed, so its actual-read/prefix adapter remains an explicit supplier obligation. -/
  finalized_ancestry : rho.ExecutionValid → ∀ v i j, i ≤ j → j ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime j) →
    (mappedReadState M v j).fg.Anc
      (mappedReadState M v i).fg.F (mappedReadState M v j).fg.F

/-- UNPROVED nesting edge, at every bounded honest read, without a regime or excuse.
Consumer: `ShapeClaimsAt.nested` (`Spec/Shape/Claims.lean:50`). -/
def NestedChainEdge (M : RunMap (A := A) rho payload) : Prop :=
  ChainRepresentation A M.chain M.header → HonestChainReads M → rho.ExecutionValid →
    ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
      (chainTrace rho).Nested g₁ g₂

/-- UNPROVED monotonicity edge. The E1 final-tip identity identifies the cache;
growth preserves the old cache chain, then same-store ancestry gives the prefix.
Consumer: `ShapeClaimsAt.finalMonotone` (`Spec/Shape/Claims.lean:53`). -/
def FinalMonotoneChainEdge (M : RunMap (A := A) rho payload) : Prop :=
  ChainRepresentation A M.chain M.header → HonestChainReads M →
    rho.ExecutionValid → ∀ g, O.output .final = some g → (chainTrace rho).Monotone g 0

/-- UNPROVED system-level nesting assembly with the original `HoldsAlways` wrapper.
One binding supplies one map per valid run, reused for every output and read. -/
def NestedChainsAlways (B : EngineBinding (A := A) (F := F) (V := V) payload) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    ChainRepresentation A (B.map E rho hv).chain (B.map E rho hv).header ∧
      HonestChainReads (B.map E rho hv)) →
    ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
      (Sys F V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂

/-- UNPROVED system-level final monotonicity assembly. The wrapper has no collision
escape, constant-fault restriction or new regime antecedent. -/
def FinalChainsAlways (B : EngineBinding (A := A) (F := F) (V := V) payload) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    ChainRepresentation A (B.map E rho hv).chain (B.map E rho hv).header ∧
      HonestChainReads (B.map E rho hv)) →
    ∀ g, O.output .final = some g →
      (Sys F V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0

end Consensus.Goldilocks.Generic

end

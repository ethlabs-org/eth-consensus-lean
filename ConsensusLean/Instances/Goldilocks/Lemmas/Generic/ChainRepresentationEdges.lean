module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ChainRepresentation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation

public section

/-! # Unconditional honest-read chain edges

The actual-read suppliers are UNPROVED proposition contracts, not evidence. The nesting and
final-monotonicity edges and their system-level assemblies are proved from them and the
representation laws (section "Chain edge proofs"). The same E1 map is reused for the actual
engine run. No cross-reader union, collision excuse or constant-fault condition
is available to these edges. They do not use `ReadRepresentation.ancestor_prefix`.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}
  {sg : A.Msg → Fin P.n} {runs : ACRun A sg}

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
  The output clock is the protocol's stored clock, not the observation or trace time. -/
  output_read : ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) → ∀ g,
    (chainTrace rho).read g v i =
      (M.chain (mappedReadState M v i)
        (M.tip g (mappedReadState M v i)
          (M.clock (rho.stateBefore i v).st.1))).map M.header
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
      (M.tip g₁ (mappedReadState M v i) (M.clock (rho.stateBefore i v).st.1))
      (M.tip g₂ (mappedReadState M v i) (M.clock (rho.stateBefore i v).st.1))
  /-- Finalized cache membership at the old honest read, required by store growth. -/
  finalized_held : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    rho.point.HonestAt v (rho.cutTime i) →
    (mappedReadState M v i).fg.F ∈ (mappedReadState M v i).fg.tree
  /-- The E1 final-tip identity, separately from cross-reader representation laws.
  Source: `AsChainShape.lean:559` and `Simulation/Outputs.lean:28`. -/
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

/-- Nesting edge, at every bounded honest read, without a regime or excuse.
Consumer: `ShapeClaimsAt.nested` (`Spec/Shape/Claims.lean:50`). Proved by `nestedChainEdge`. -/
def NestedChainEdge (M : RunMap (A := A) rho payload) : Prop :=
  ChainRepresentation A M.chain M.header → HonestChainReads M → rho.ExecutionValid →
    ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
      (chainTrace rho).Nested g₁ g₂

/-- Monotonicity edge. The E1 final-tip identity identifies the cache;
growth preserves the old cache chain, then same-store ancestry gives the prefix.
Consumer: `ShapeClaimsAt.finalMonotone` (`Spec/Shape/Claims.lean:53`).
Proved by `finalMonotoneChainEdge`. -/
def FinalMonotoneChainEdge (M : RunMap (A := A) rho payload) : Prop :=
  ChainRepresentation A M.chain M.header → HonestChainReads M →
    rho.ExecutionValid → ∀ g, O.output .final = some g → (chainTrace rho).Monotone g 0

/-- System-level nesting assembly at fixed public parameters, without an excuse.
One binding supplies one map per valid run, reused for every output and read.
Proved by `nestedChainsAlways`. -/
def NestedChainsAlways {pub : Model.Public}
    (B : EngineBinding (F := F) (V := V) pub payload sg runs) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    ChainRepresentation A (B.map E hE rho hv).chain (B.map E hE rho hv).header ∧
      HonestChainReads (B.map E hE rho hv)) →
    ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ → O.output c₂ = some g₂ →
      (Sys F V).HoldsAlways fun r => Model.pubOf r.1 = pub → (chainTrace r.2).Nested g₁ g₂

/-- System-level final monotonicity assembly. The wrapper has no collision
escape or constant-fault restriction; the binding fixes only public parameters.
Proved by `finalChainsAlways`. -/
def FinalChainsAlways {pub : Model.Public}
    (B : EngineBinding (F := F) (V := V) pub payload sg runs) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    ChainRepresentation A (B.map E hE rho hv).chain (B.map E hE rho hv).header ∧
      HonestChainReads (B.map E hE rho hv)) →
    ∀ g, O.output .final = some g →
      (Sys F V).HoldsAlways fun r => Model.pubOf r.1 = pub → (chainTrace r.2).Monotone g 0

section ChainEdgeProofs

/-- Nesting at every honest read: both reads are chains in the reader's mapped store
(`HonestChainReads.output_read`), whose tips are ordered by local ancestry (`nested_tips`) in a
reachable store, so the lower-rank chain is a prefix (`ChainRepresentation.same_store_prefix`). -/
theorem nestedChainEdge (M : RunMap (A := A) rho payload) : NestedChainEdge M := by
  intro hrep hreads hv c₁ c₂ g₁ g₂ hc h₁ h₂ v i hi hh
  rw [hreads.output_read v i hi hh g₁, hreads.output_read v i hi hh g₂]
  exact hrep.same_store_prefix _ (hreads.reachable hv v i hi hh) _ _
    (hreads.nested_tips hv v i hi hh c₁ c₂ g₁ g₂ hc h₁ h₂)

/-- Final monotonicity: a final read is the chain of the store's finalized cache
(`finalized_tip`). The later store holds the earlier one's blocks (`tree_growth`), so the earlier
cache keeps its chain (`store_growth`), and it is a local ancestor of the later cache
(`finalized_ancestry`), so its chain is a prefix (`same_store_prefix`). -/
theorem finalMonotoneChainEdge (M : RunMap (A := A) rho payload) :
    FinalMonotoneChainEdge M := by
  intro hrep hreads hv g hg v i j hi hij hj hhi hhj
  rw [hreads.output_read v i hi.1 hhi g, hreads.output_read v j hj.1 hhj g,
    hreads.finalized_tip g hg, hreads.finalized_tip g hg,
    hrep.store_growth _ _ (hreads.reachable hv v i hi.1 hhi)
      (hreads.tree_growth hv v i j hij hj.1 hhj) _ (hreads.finalized_held hv v i hi.1 hhi)]
  exact hrep.same_store_prefix _ (hreads.reachable hv v j hj.1 hhj) _ _
    (hreads.finalized_ancestry hv v i j hij hj.1 hhj)

/-- System-level nesting at fixed public parameters, from `nestedChainEdge` on the binding's
map of each valid run. -/
theorem nestedChainsAlways {pub : Model.Public}
    (B : EngineBinding (F := F) (V := V) pub payload sg runs) : NestedChainsAlways B := by
  intro h c₁ c₂ g₁ g₂ hc h₁ h₂ r hv hpub
  obtain ⟨E, rho⟩ := r
  exact nestedChainEdge (B.map E hpub rho hv) (h E hpub rho hv).1 (h E hpub rho hv).2 hv
    c₁ c₂ g₁ g₂ hc h₁ h₂

/-- System-level final monotonicity at fixed public parameters, from
`finalMonotoneChainEdge` on the binding's map of each valid run. -/
theorem finalChainsAlways {pub : Model.Public}
    (B : EngineBinding (F := F) (V := V) pub payload sg runs) : FinalChainsAlways B := by
  intro h g hg r hv hpub
  obtain ⟨E, rho⟩ := r
  exact finalMonotoneChainEdge (B.map E hpub rho hv) (h E hpub rho hv).1 (h E hpub rho hv).2
    hv g hg

end ChainEdgeProofs

end Consensus.Goldilocks.Generic

end

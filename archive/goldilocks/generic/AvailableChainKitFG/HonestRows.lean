module
public import AvailableChainSimplexFG.Client
public import AvailableChainSimplexFG.Evidence

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Honest-row facts for one row pool `A` and fault set `faulty`
(GLY G29/G30 and §C.2; step-2 ruling B08).

`M` is an explicit cap on the height pairs of honest rows in this pool.
Emission and client safety alone do not give a cap at an arbitrary `M`.
The run layer supplies all three fields at the read in question. For a
comparison of two chains, `A` must contain the rows of both chains.
This predicate makes no claim about the weight of `faulty`. -/
structure HonestRows (E : Electorate V) (cfg : FGConfig)
    (A : Finset (Row V)) (faulty : Finset V) (M : Height) : Prop where
  /-- The `hemit` premise of `Provenance.lean:80–81`. -/
  emit : ∀ a ∈ A, a.signer ∉ faulty →
    ∃ Λ src Hd, a = (createRow E cfg Λ a.signer src (HeadFields.ofBlock E cfg Hd)).1
  /-- The `hhonest` premise of `CrossingNoFinal.lean:98`, restricted to
  the two chain row sets by their inclusion in `A`. -/
  noSlash : ∀ a ∈ A, ∀ b ∈ A, a.signer ∉ faulty → ¬ Slashable a b
  /-- The `hrows` premise of `CausalCap.lean:27–28`, restricted to the
  chain row set by its inclusion in `A`. -/
  height_le : ∀ a ∈ A, a.signer ∉ faulty →
    ∀ h T t, a.height_pair = .vote h T t → h ≤ M

end AvailableChain.KitFG
end

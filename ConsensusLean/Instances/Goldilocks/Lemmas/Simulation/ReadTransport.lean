module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # Steps of the R.7/R.8 engine read transport

The steps of R.8 output validity and of R.7 compatible reads used by the growing-fault
`engine_outputValid_at` (`Growing/Simulation/Endpoint/Outputs`) and `compatible_reads_at`
(`Growing/Simulation/Endpoint/Accountable`). The caller supplies the reachable stores, root
facts, view and coherent block set.

* `chainTo_compatible`: two reachable stores inside one coherent block set have prefix-related
  header chains at two of their blocks that are compatible in that set (`chainTo_prefix_of_anc`);
* `parentRef_root_of_rootOk`: a block with a parent whose root is its tagged digest is
  referenced by the engine hash of its header;
* `reader_chains_valid`: in a reachable store whose held non-genesis blocks have their digests as
  roots and a parent, the header chain of every held block is linked and has increasing
  positions; it has proposal-role provenance in an engine view that contains the held
  non-genesis blocks. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape
open Consensus.Model (pubOf)

/-- **Compatible held blocks have prefix-related header chains.** For two reachable stores whose
trees lie in a coherent set `U`, blocks `B` and `C` held by the first and second store that are
compatible in `U` have header chains of which one is a prefix of the other. -/
theorem chainTo_compatible {sp : SA.SAParams} {acp₀ : SA.Payload sp.n}
    {st st' : Store sp.toParams (SA.Payload sp.n)} (hr : st.Reachable acp₀)
    (hr' : st'.Reachable acp₀) {U : Set (Blk sp)} (hU : Coherent U) (hs : st.tree ⊆ U)
    (hs' : st'.tree ⊆ U) {B C : Blk sp} (hB : B ∈ st.tree) (hC : C ∈ st'.tree)
    (hc : Compatible U B C) :
    Consensus.Compatible (chainTo st.blocks (B.slot + 1) B)
      (chainTo st'.blocks (C.slot + 1) C) := by
  rcases hc with hc | hc
  · exact .inl (chainTo_prefix_of_anc hr hr' hU hs hs' hB hC hc)
  · exact .inr (chainTo_prefix_of_anc hr' hr hU hs' hs hC hB hc)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- A block with a parent whose root is its tagged digest is referenced by the engine hash of its
header. -/
theorem parentRef_root_of_rootOk {X : Blk (S.params (pubOf E) hn)}
    (hroot : X.RootOk (digestOf S rho))
    (hpar : ∃ P : Blk (S.params (pubOf E) hn), X.parent = some P.root) :
    parentRef (S.params (pubOf E) hn).genesisRoot (some X.root) =
      .digest (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
  obtain ⟨P, hpar⟩ := hpar
  have he : X.root = taggedRoot S.genesisRoot
      (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
    simp only [Block.RootOk, digestOf_eq] at hroot
    simpa [headerOf_eq, hpar] using hroot.trans (dgOf_eq _ _ _ _ _ _ _)
  simp only [parentRef_eq, he, rawRoot_taggedRoot, taggedRoot_ne, ite_false]

/-- **The header chains of a reader's held blocks are valid outputs.** For a reachable store of the
reader at cut `k` of a trace `T` whose held non-genesis blocks have their digests as roots and a
parent (`hroot`), the chain of every held block is linked, has increasing positions and
proposal-role provenance in the engine view `rho.ViewIdx v i`, given that this view contains the
held non-genesis blocks (`hheld`). -/
theorem reader_chains_valid {T : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)}
    {v : V} (k i : Nat)
    (hr : (T.state (rho.ownKey v) k).fg.Reachable
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload)
    (hroot : ∀ X ∈ (T.state (rho.ownKey v) k).fg.tree,
      X.root ≠ (S.params (pubOf E) hn).genesisRoot →
      X.RootOk (digestOf S rho) ∧ ∃ P : Blk (S.params (pubOf E) hn), X.parent = some P.root)
    (hheld : ∀ X ∈ (T.state (rho.ownKey v) k).fg.tree,
      X.root ≠ (S.params (pubOf E) hn).genesisRoot →
      blockObj (S.params (pubOf E) hn) X ∈ rho.ViewIdx v i) :
    ∀ B ∈ (T.state (rho.ownKey v) k).fg.tree,
      Chain.Linked rho.hash (chainTo (T.state (rho.ownKey v) k).fg.blocks (B.slot + 1) B) ∧
      Chain.PosIncreasing (chainTo (T.state (rho.ownKey v) k).fg.blocks (B.slot + 1) B) ∧
      Chain.Provenant (rho.ViewIdx v i) ProposalRole
        (chainTo (T.state (rho.ownKey v) k).fg.blocks (B.slot + 1) B) := by
  intro B hB
  have hstruct := chainTo_append_valid hr rho.hash
    (fun X hX hg => parentRef_root_of_rootOk S rho hn (hroot X hX hg).1 (hroot X hX hg).2) hB
    (Nat.lt_succ_self _) [] trivial trivial
  simp only [List.append_nil] at hstruct
  refine ⟨hstruct.1, hstruct.2, ?_⟩
  intro h hh
  obtain ⟨X, hX, _, hg, rfl⟩ := mem_chainTo hr hB hh
  exact ⟨X.proposer, .proposer X.slot, _, rfl, hheld X hX hg⟩

end Consensus.Goldilocks.Simulation

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # Shared steps of the R.7/R.8 engine read transport

The steps of R.8 output validity and of R.7 compatible reads shared by the constant-fault
`engine_outputValid` and `compatible_reads` (`Simulation/Transport`) and the growing-fault
`engine_outputValid_at` (`Growing/Simulation/Endpoint/Outputs`) and `compatible_reads_at`
(`Growing/Simulation/Endpoint/Accountable`). Each fault model supplies its own reachable stores,
root facts, view and coherent block set.

* `chainTo_compatible`: two reachable stores inside one coherent block set have prefix-related
  header chains at two of their blocks that are compatible in that set;
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
  · left
    have ha := anc_in_store hr' hU hs' hc hC
    have hm : B ∈ st'.tree := by
      by_cases he : B = C
      · exact he ▸ hC
      · exact (Anc.mem ha he).1
    rw [chainTo_agree hr hr' hU hs hs' hB hm]
    exact chainTo_prefix hr' ha
  · right
    have ha := anc_in_store hr hU hs hc hB
    have hm : C ∈ st.tree := by
      by_cases he : C = B
      · exact he ▸ hB
      · exact (Anc.mem ha he).1
    rw [chainTo_agree hr' hr hU hs' hs hC hm]
    exact chainTo_prefix hr ha

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

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
  have hhash : ∀ X ∈ (T.state (rho.ownKey v) k).fg.tree,
      X.root ≠ (S.params (pubOf E) hn).genesisRoot →
      parentRef (S.params (pubOf E) hn).genesisRoot (some X.root) =
        .digest (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
    intro X hX hg
    obtain ⟨hroot, P, hpar⟩ := hroot X hX hg
    have he : X.root = taggedRoot S.genesisRoot
        (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
      simp only [Block.RootOk, digestOf_eq] at hroot
      erw [dgOf_eq] at hroot
      simpa [headerOf, hpar] using hroot
    simp only [parentRef, he, rawRoot_taggedRoot, taggedRoot_ne, ite_false]
  intro B hB
  have hstruct := chainTo_append_valid hr rho.hash hhash hB (Nat.lt_succ_self _) []
    trivial trivial
  simp only [List.append_nil] at hstruct
  refine ⟨hstruct.1, hstruct.2, ?_⟩
  intro h hh
  obtain ⟨X, hX, _, hg, rfl⟩ := mem_chainTo hr hB hh
  exact ⟨X.proposer, .proposer X.slot, _, rfl, hheld X hX hg⟩

end Consensus.Goldilocks.Simulation

end

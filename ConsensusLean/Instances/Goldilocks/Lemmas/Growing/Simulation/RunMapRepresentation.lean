module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.EngineBinding
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReadTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks chain representation and honest-read transport

The canonical run map supplies the generic representation contracts at every vote binding.
The chain laws retain the held-tip and reachable-store premises of `ReadRepresentation`.
The suppliers do not show that an honest reader's output tip, read at the stored clock `M.clock`,
is held: that membership is the open obligation of `OutputValidityEdge` (ledger row "actual tip
held / payload ancestry").
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : BoundSetup) {E : Env V}
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
  (hv : rho.ExecutionValid)

/-- The canonical chain map satisfies the generic held-tip representation laws. -/
theorem goldilocksRunMap_readRepresentation :
    Generic.ReadRepresentation (goldilocksRunMap S rho hn hv) where
  chain_held st tip hr ht B hB := by
    rw [goldilocksRunMap_chain] at hB
    exact (mem_blocksTo hr ht hB).1
  linked st tip hr ht hroot := by
    rw [goldilocksRunMap_digest] at hroot
    rw [goldilocksRunMap_chain, goldilocksRunMap_header, blocksTo_map]
    have hhash : ∀ X ∈ st.fg.tree, X.root ≠ (S.params (pubOf E) hn).genesisRoot →
        parentRef (S.params (pubOf E) hn).genesisRoot (some X.root) =
          .digest (rho.hash (headerOf (S.params (pubOf E) hn) X)) := by
      intro X hX hg
      obtain he | ⟨P, _, e⟩ :=
        (Relation.ReflTransGen.cases_tail_iff _ _ _).1
          ((Store.accepted_tree _ _ _ _ hr).2.2.2 X hX)
      · exact (hg (congrArg Block.root he)).elim
      exact parentRef_root_of_rootOk S rho hn (hroot X hX) ⟨P, e.2.2⟩
    simpa only [List.append_nil] using
      (chainTo_append_valid hr rho.hash hhash ht (Nat.lt_succ_self _) [] trivial trivial).1
  increasing st tip hr ht := by
    rw [goldilocksRunMap_chain, goldilocksRunMap_header, blocksTo_map]
    simpa only [List.append_nil] using chainTo_append_pos hr ht (Nat.lt_succ_self _) [] trivial
  ancestor_prefix _ _ _ _ _ _ _ _ := by
    intro st st' hr hr' _ _ hU hs hs' B B' hB hB' ha
    rw [goldilocksRunMap_chain, goldilocksRunMap_chain, goldilocksRunMap_header, blocksTo_map,
      blocksTo_map]
    exact chainTo_prefix_of_anc hr hr' hU hs hs' hB hB' ha
  tip_in_chain st B _ hg := by
    rw [goldilocksRunMap_chain, goldilocksRunMap_header]
    refine List.mem_map.2 ⟨B, ?_, rfl⟩
    rw [blocksTo_succ, ite_eq_right hg]
    exact List.mem_append_right _ (List.mem_singleton_self B)
  confirmed_tip g hg st t := by
    obtain rfl : Out.confirmed = g := Option.some.inj hg
    rw [goldilocksRunMap_tip]
    exact outTip_confirmed _ _ st t
  finalized_tip g hg st t := by
    obtain rfl : Out.finalized = g := Option.some.inj hg
    rw [goldilocksRunMap_tip]
    exact outTip_finalized _ _ st t

/-- Honest engine reads transport their reachable stores, roots and held objects. -/
theorem goldilocksRunMap_honestReadTransport :
    Generic.HonestReadTransport (goldilocksRunMap S rho hn hv) where
  reachable hv' v i hi hh := by
    simp only [goldilocksRunMap_trace, goldilocksRunMap_validator, goldilocksRunMap_cut]
    exact (held_tree_at S rho hn hv' hi hh).1
  roots hv' v i hi hh B hB := by
    simp only [goldilocksRunMap_trace, goldilocksRunMap_validator, goldilocksRunMap_cut] at hB
    rw [goldilocksRunMap_digest]
    obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv' hi hh
    rw [← hs] at hB
    rcases Compose.tree_cases hrun.toLocalRun hy hB with hgen | ⟨k, -, hacc⟩
    · exact hgen ▸ simTrace_genesis_root_ok S rho hn
    · exact (Compose.accept_facts hrun.toLocalRun hy hacc).1
  held_view hv' v i hi hh B hB hg := by
    simp only [goldilocksRunMap_trace, goldilocksRunMap_validator, goldilocksRunMap_cut] at hB
    rw [goldilocksRunMap_proposalObject]
    exact held_in_view_at S rho hn hv' hi hh hB hg
  chain_nonroot st tip B hB := by
    rw [goldilocksRunMap_chain] at hB
    exact blocksTo_nonroot _ _ _ _ hB
  held_att_view hv' v i hi hh B hB a ha := by
    simp only [goldilocksRunMap_trace, goldilocksRunMap_validator, goldilocksRunMap_cut] at hB
    rw [goldilocksRunMap_attObject]
    exact held_att_in_view_at S rho hn hv' hi hh hB ha
  chain_att_view hv' v i hi hh X a ha := by
    obtain ⟨Y, hY, -, haY⟩ := ha
    simp only [goldilocksRunMap_trace, goldilocksRunMap_validator, goldilocksRunMap_cut] at hY
    rw [goldilocksRunMap_attObject]
    exact held_att_in_view_at S rho hn hv' hi hh hY haY

/-- The public-indexed binding supplies both chain representation contracts. -/
theorem goldilocksEngineBinding_readTransport (pub : Model.Public) (hn : 1 ≤ pub.n)
    (E : Env V) (hE : pubOf E = pub)
    (rho : Model.Run (compiled (goldilocksWith S)) E) (hv : rho.ExecutionValid) :
    let M := (goldilocksEngineBinding S pub hn).map E hE rho hv
    Generic.ReadRepresentation M ∧ Generic.HonestReadTransport M := by
  subst pub
  rw [goldilocksEngineBinding_map]
  exact ⟨goldilocksRunMap_readRepresentation S rho hn hv,
    goldilocksRunMap_honestReadTransport S rho hn hv⟩

end Consensus.Goldilocks.Simulation

end

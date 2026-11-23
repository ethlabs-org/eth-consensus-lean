module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.EngineBinding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReadTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State

public section

/-! # Goldilocks chain representation and honest-read transport

The canonical run map supplies the generic representation contracts at every vote binding:
`ReadRepresentation`, `HonestReadTransport`, `ChainRepresentation`, `HonestChainReads`, the
resilience tip, honest-store coherence on collision-free runs, and `OutputValidityEdge`
(from `engine_outputValid_at`). The chain laws retain the held-tip and reachable-store premises
of `ReadRepresentation`.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
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

/-- The canonical chain map represents same-store ancestry by prefixes and survives store growth. -/
theorem goldilocks_chainRepresentation (sp : AC.ACParams)
    (ro : AC.ReplayOrder sp (List (FG.Att sp.n))) :
    Generic.ChainRepresentation (goldilocksNode sp ro)
      (fun st B => blocksTo st.fg.blocks (B.slot + 1) B) (headerOf sp) where
  same_store_prefix st hr B C h := by
    rw [blocksTo_map, blocksTo_map]
    exact chainTo_prefix hr h
  store_growth st st' hr hsub B hB := by
    rw [blocksTo_map, blocksTo_map]
    exact chainTo_mono hr hsub hB _

/-- Engine reads are the mapped chains at the stored clock, with the store laws of honest reads. -/
theorem goldilocksRunMap_honestChainReads :
    Generic.HonestChainReads (goldilocksRunMap S rho hn hv) where
  output_read v i hi hh g := by
    change (goldilocks S (pubOf E)).out g (rho.stateBefore i v).st.1 = _
    rw [(goldilocksRunMap S rho hn hv).output_eq g v i hi,
      (goldilocksRunMap S rho hn hv).state_eq v i hi hh]
  reachable hv' v i hi hh := by
    simp only [Generic.mappedReadState, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut]
    exact (held_tree_at S rho hn hv' hi hh).1
  nested_tips hv' v i hi hh c₁ c₂ g₁ g₂ hr h₁ h₂ := by
    simp only [Generic.mappedReadState, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut, goldilocksRunMap_tip]
    have hR := (held_tree_at S rho hn hv' hi hh).1
    cases c₁ <;> cases c₂ <;> simp only [Capability.rank] at hr <;> try omega
    all_goals have he₁ := Option.some.inj h₁
    all_goals have he₂ := Option.some.inj h₂
    all_goals cases he₁; cases he₂
    · exact .refl
    all_goals
      rw [outTip_finalized, outTip_confirmed]
      have hΦ := (Store.frame_realization _ _ _ _ hR).1
      have ha := hΦ.rooted.2 _ (Regimes.ac_tips (A := (((simTraceAt S rho hn).state
        (rho.ownKey v) (cutMap S rho hn i))).ac) hΦ
        ((goldilocksRunMap S rho hn hv).clock (rho.stateBefore i v).st.1)).1
      exact Anc.mono (fun _ hX => hX.1) ha
  finalized_held hv' v i hi hh := by
    simp only [Generic.mappedReadState, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut]
    exact (Store.cache_invariants _ _ _ _ (held_tree_at S rho hn hv' hi hh).1).1
  finalized_tip g hg st t := by
    obtain rfl : Out.finalized = g := Option.some.inj hg
    rw [goldilocksRunMap_tip]
    exact outTip_finalized _ _ st t
  tree_growth hv' v i j hij hj hh := by
    simp only [Generic.mappedReadState, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut]
    obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv' hj hh
    have hsi := upTo_state_cutMap S rho hn hv' hij hj (rho.ownKey v)
    have h := Compose.tree_mono hrun.toLocalRun hy (cutMap_mono S rho hn hij)
    rw [hsi, hs] at h
    exact h
  finalized_ancestry hv' v i j hij hj hh := by
    simp only [Generic.mappedReadState, goldilocksRunMap_trace, goldilocksRunMap_validator,
      goldilocksRunMap_cut]
    obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv' hj hh
    have hsi := upTo_state_cutMap S rho hn hv' hij hj (rho.ownKey v)
    have h := Regimes.finalized_monotone_from hrun hy (cutMap_mono S rho hn hij)
    simp only [RunTrace.finalizedAt] at h
    rw [hsi, hs] at h
    exact h

/-- The resilience target of the stable output is the confirmed tip. -/
theorem goldilocksRunMap_resilienceTipTransport :
    Generic.ResilienceTipTransport (goldilocksRunMap S rho hn hv) := by
  intro g hg st t
  obtain rfl : Out.confirmed = g := Option.some.inj hg
  rw [goldilocksRunMap_tip]
  exact outTip_confirmed _ _ st t

/-- The blocks held while honest are coherent on a collision-free run. -/
theorem goldilocksRunMap_coherent (hc : ¬ rho.HashCollision) :
    Coherent ((goldilocksRunMap S rho hn hv).trace.HonestBlocksAt
      (goldilocksRunMap S rho hn hv).honest) := by
  rw [goldilocksRunMap_trace, goldilocksRunMap_honest]
  exact Compose.Growing.honest_blocks_coherent (simTraceAt_goldilocksRun S rho hn hv)
    (noCollRun_simTraceAt S rho hn hv hc)

/-- Engine outputs are valid at every vote binding (`engine_outputValid_at`). -/
theorem goldilocksRunMap_outputValidity :
    Generic.OutputValidityEdge (goldilocksRunMap S rho hn hv) :=
  (Generic.outputValidityEdge_iff _).mpr fun _ _ hv' g => engine_outputValid_at S rho hv' g

/-- Actual-read accountability for every Goldilocks run supplier whose runs are Goldilocks runs
from some start: the shared FG argument at both readers' own read points
(`finalAccountable_readPoint`). -/
theorem goldilocks_actualReadAccountability {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] {F : ChainShapeFamily O Info} {E : Env V}
    {rho : Model.Run (compiled F) E} {payload : AC.Blk sp.n (List (FG.Att sp.n)) → Set Nat}
    (M : Generic.RunMap (A := goldilocksNode sp ro) rho payload)
    (runs : Generic.ACRun (goldilocksNode sp ro) M.signer)
    (hruns : ∀ cm proposer dg H tr, runs.Run cm proposer dg H tr →
      ∃ ini, Growing.GoldilocksRun proposer dg H tr ini) :
    Generic.ActualReadAccountability M runs := by
  intro hrun hnc y z i j t u hy hz hne
  obtain ⟨ini, hg⟩ := hruns _ _ _ _ _ hrun
  exact finalAccountable_readPoint hg hnc hy.2.2.1 hy.2.1.1 hy.1 hz.2.2.1 hz.2.1.1 hz.1 hne

end Consensus.Goldilocks.Simulation

end

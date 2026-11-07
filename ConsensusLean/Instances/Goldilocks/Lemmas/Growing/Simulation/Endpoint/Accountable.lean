module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Pending
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Always
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Engine final accountability under growing faults

The growing-fault form of the static R.7 engine transport (`compatible_reads`,
`final_accountable_of_noColl` and the arithmetic of `shape_finalAccountable`), without a
constant-fault premise. Each reader is honest at its own engine cut and read at its mapped trace
cut, which is a read point of the prefix through its engine cut time; compatibility is read inside
the blocks held while honest.

* `finalAccountable_readPoint`: the node-level G1.3 argument for two readers, each honest at a
  time `t ≥ 0` no earlier than every cut before its read: each reader's finalized chain comes from
  the static FG store on its own prefix run, with the blocks held while honest as the common
  coherent universe;
* `read_finalized_at`: the finalized engine read is the chain of the trace state's finalized tip;
* `compatible_reads_at`: compatible tips inside the blocks held while honest give prefix-related
  finalized reads;
* `engine_finalAccountable_at`: the fourth `ShapeClaimsAt` field for every `α ≤ 1/3`, with the
  hash-collision escape.

The collision transport `noCollRun_simTraceAt` is still a stand-in (`Endpoint/Pending`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Consensus.Model (pubOf)

section Node

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The FG projection of the prefix through `d ≥ 0` is a static FG run for the keys honest at `d`,
over the blocks held while honest in the whole run. -/
private theorem fg_run_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload (H d) (tr.HonestBlocksAt H)
      (tr.upTo d).projFG := by
  have hr := hrun.upTo hd
  have hq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  have h := Compose.fg_projection _ _ dg (H d) _ (tr.upTo d) proposer
    ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hr.genesis_root_ok hr.toLocalRun (hnc.upTo d)
  exact { h with
    coherent := Compose.Growing.honest_blocks_coherent hrun hnc
    tree_subset := fun y hy i => (h.tree_subset y hy i).trans
      (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd) }

/-- The FG store of a node honest at `d ≥ 0`, before a cut whose predecessors are at times `≤ d`,
is its state's FG part in the run. -/
private theorem store_upTo (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {d : Time} (hd : 0 ≤ d) {y : Fin sp.n} (hy : y ∈ H d) {i : Nat}
    (hi : ∀ k < i, tr.time k ≤ d) : (tr.upTo d).projFG.store y i = (tr.state y i).fg := by
  change ((tr.upTo d).projFG.state y i).1 = _
  rw [Compose.projFG_state (hrun.upTo hd).toLocalRun hy i, Trace.upTo_state _ y hi]

/-- **Final accountability at read points under growing faults.** If the finalized tips of two
nodes, each honest at a time `t ≥ 0` no earlier than every cut before its read, conflict inside
the blocks held while honest, at least `2q − n` validators each have a slashable pair among the
attestations included on two chains the two readers hold. No fault bound. -/
theorem finalAccountable_readPoint
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i j : Nat} {t t' : Time}
    (ht : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t)
    (ht' : 0 ≤ t') (hj : ∀ k < j, tr.time k ≤ t') (hz : z ∈ H t')
    (hne : ¬ Compatible (tr.HonestBlocksAt H) (tr.finalizedAt y i) (tr.finalizedAt z j)) :
    ∃ X₁ ∈ (tr.state y i).fg.tree, ∃ X₂ ∈ (tr.state z j).fg.tree,
      ∃ W : Finset (Fin sp.n), 2 * sp.toParams.q - sp.n ≤ W.card ∧
        ∀ v ∈ W, ∃ a ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂,
          ∃ b ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂,
            a.val = v ∧ FG.slashable a b := by
  obtain ⟨c₁, σ₁, h₁, hF₁, hU₁, hc₁, -, X₁, hX₁, hb₁⟩ :=
    Store.finalized_chain (fg_run_upTo hrun hnc ht) hy i
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, -, X₂, hX₂, hb₂⟩ :=
    Store.finalized_chain (fg_run_upTo hrun hnc ht') hz j
  rw [store_upTo hrun ht hy hi] at hF₁ hU₁ hc₁ hX₁ hb₁
  rw [store_upTo hrun ht' hz hj] at hF₂ hU₂ hc₂ hX₂ hb₂
  obtain ⟨W, hW, hWv⟩ := FG.accountable_safety sp.toParams.fg c₁ c₂ σ₁ σ₂ h₁ h₂
    (fun h => hne (hc₂ _ hU₁ (hF₁ ▸ h))) (fun h => hne (hc₁ _ hU₂ (hF₂ ▸ h)).symm)
  have hmem : ∀ a ∈ sp.toParams.fg.chainAtts c₁ ++ sp.toParams.fg.chainAtts c₂,
      a ∈ Regimes.ChainAtts tr y i X₁ ∪ Regimes.ChainAtts tr z j X₂ := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₁ a ha
      exact Or.inl ⟨Y, hY, hYX, haY⟩
    · obtain ⟨Y, hY, hYX, haY⟩ := hb₂ a ha
      exact Or.inr ⟨Y, hY, hYX, haY⟩
  refine ⟨X₁, hX₁, X₂, hX₂, W, hW, fun v hv => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hab⟩ := hWv v hv
  exact ⟨a, hmem a ha, b, hmem b hb, hav, hab⟩

end Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The finalized engine read at a bounded cut is the chain of the trace state's finalized tip
at the mapped cut. -/
theorem read_finalized_at (hv : rho.ExecutionValid) (v : V) {i : Nat}
    (hi : i ≤ rho.events.length) :
    (chainTrace rho).read .finalized v i =
      chainTo ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.blocks
        (((simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn i)).slot + 1)
        ((simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn i)) := by
  rw [read_eq_out S rho hn, outOf, simTraceAt_state_all S rho hn hv v i hi]
  rfl

/-- The tree of a node honest at its engine cut is reachable at the mapped cut and inside the
blocks held while honest. -/
theorem held_tree_at (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hh : v ∉ rho.faultyAt (rho.cutTime i)) :
    ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.Reachable
        (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload ∧
      ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)).fg.tree ⊆
        (simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho) := by
  obtain ⟨hrun, hy, hs⟩ := prefix_reader_at S rho hn hv hi hh
  refine ⟨hs _ ▸ Compose.fg_reachable hrun.toLocalRun hy (cutMap S rho hn i), fun B hB => ?_⟩
  exact ⟨_, _, _, (cutTime_bounds S rho hv hi).1, cutMap_time_le S rho hn hv hi, hy, hB⟩

/-- **Compatible held tips give prefix-related finalized reads.** For two nodes each honest at its
engine cut, compatibility of their finalized tips inside the blocks held while honest makes one
finalized engine read a prefix of the other. -/
theorem compatible_reads_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {u v : V} {i j : Nat} (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length)
    (hu : u ∉ rho.faultyAt (rho.cutTime i)) (hv' : v ∉ rho.faultyAt (rho.cutTime j))
    (hc : Compatible ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i))
      ((simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j))) :
    Consensus.Compatible ((chainTrace rho).read .finalized u i)
      ((chainTrace rho).read .finalized v j) := by
  obtain ⟨hri, hsi⟩ := held_tree_at S rho hn hv hi hu
  obtain ⟨hrj, hsj⟩ := held_tree_at S rho hn hv hj hv'
  have hU := Compose.Growing.honest_blocks_coherent (simTraceAt_goldilocksRun S rho hn hv) hnc
  have hFi := (Store.cache_invariants _ _ _ _ hri).1
  have hFj := (Store.cache_invariants _ _ _ _ hrj).1
  rw [read_finalized_at S rho hn hv u hi, read_finalized_at S rho hn hv v hj]
  rcases hc with hc | hc
  · left
    have ha := anc_in_store hrj hU hsj hc hFj
    have hm : (simTraceAt S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i) ∈
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn j)).fg.tree := by
      by_cases he : (simTraceAt S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i) =
          (simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j)
      · exact he ▸ hFj
      · exact (Anc.mem ha he).1
    simp only [RunTrace.finalizedAt]
    rw [chainTo_agree hri hrj hU hsi hsj hFi hm]
    exact chainTo_prefix hrj ha
  · right
    have ha := anc_in_store hri hU hsi hc hFi
    have hm : (simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j) ∈
        ((simTraceAt S rho hn).state (rho.ownKey u) (cutMap S rho hn i)).fg.tree := by
      by_cases he : (simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j) =
          (simTraceAt S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i)
      · exact he ▸ hFi
      · exact (Anc.mem ha he).1
    simp only [RunTrace.finalizedAt]
    rw [chainTo_agree hrj hri hU hsj hsi hFj hm]
    exact chainTo_prefix hri ha

/-- Two finalized reads of nodes each honest at its own engine cut are prefix-related, or their
two views convict `2q − n` validators. -/
theorem final_accountable_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {u v : V} {i j : Nat} (hi : i ≤ rho.events.length) (hj : j ≤ rho.events.length)
    (hu : u ∉ rho.faultyAt (rho.cutTime i)) (hv' : v ∉ rho.faultyAt (rho.cutTime j)) :
    Consensus.Compatible ((chainTrace rho).read .finalized u i)
        ((chainTrace rho).read .finalized v j) ∨
      2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V ≤
        (convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card := by
  classical
  by_cases hc : Compatible ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      ((simTraceAt S rho hn).finalizedAt (rho.ownKey u) (cutMap S rho hn i))
      ((simTraceAt S rho hn).finalizedAt (rho.ownKey v) (cutMap S rho hn j))
  · exact Or.inl (compatible_reads_at S rho hn hv hnc hi hj hu hv' hc)
  · right
    obtain ⟨-, hyu, -⟩ := prefix_reader_at S rho hn hv hi hu
    obtain ⟨-, hyv, -⟩ := prefix_reader_at S rho hn hv hj hv'
    obtain ⟨X, _, Y, _, W, hW, hw⟩ := finalAccountable_readPoint
      (simTraceAt_goldilocksRun S rho hn hv) hnc (cutTime_bounds S rho hv hi).1
      (cutMap_time_le S rho hn hv hi) hyu (cutTime_bounds S rho hv hj).1
      (cutMap_time_le S rho hn hv hj) hyv hc
    have hmem : ∀ a ∈ Regimes.ChainAtts (simTraceAt S rho hn) (rho.ownKey u)
        (cutMap S rho hn i) X ∪ Regimes.ChainAtts (simTraceAt S rho hn) (rho.ownKey v)
        (cutMap S rho hn j) Y, attObj a ∈ rho.ViewIdx u i ∪ rho.ViewIdx v j := by
      intro a ha
      rcases ha with ⟨B, hB, _, ha⟩ | ⟨B, hB, _, ha⟩
      · exact Or.inl (held_att_in_view_at S rho hn hv hi hu hB ha)
      · exact Or.inr (held_att_in_view_at S rho hn hv hj hv' hB ha)
    refine hW.trans (convicted_count S rho W ?_)
    intro k hk
    obtain ⟨a, ha, b, hb, hak, hab⟩ := hw k hk
    exact ⟨a, b, hmem a ha, hmem b hb, hak, hab⟩

/-- **R.7 final accountability under growing faults**, the fourth `ShapeClaimsAt` field for every
`α ≤ 1/3`: two finalized reads of nodes each honest at its own engine cut are compatible, or the
union of their views convicts `nα` validators; the only escape is an observed hash collision. -/
theorem engine_finalAccountable_at (hv : rho.ExecutionValid) {α : ℚ} (hα : α ≤ 1 / 3) :
    (chainTrace rho).AccountablySafe rho.ViewIdx rho.Slashable α .finalized 0 ∨
      rho.HashCollision := by
  by_cases hc : rho.HashCollision
  · exact Or.inr hc
  left
  intro u v i j hi hj hu hv'
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  rcases final_accountable_at S rho hn hv (noCollRun_simTraceAt S rho hn hv hc)
      hi.1 hj.1 hu hv' with h | h
  · exact Or.inl h
  right
  have hq : Fintype.card V ≤
      3 * (2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V) := by
    simp only [Params.q]
    omega
  have hq' : (Fintype.card V : ℚ) ≤
      3 * ((2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V : Nat) : ℚ) := by
    exact_mod_cast hq
  have h' : ((2 * (S.params (pubOf E) hn).toParams.q - Fintype.card V : Nat) : ℚ) ≤
      (convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j)).card := by
    exact_mod_cast h
  have hα' := mul_le_mul_of_nonneg_left hα (show (0 : ℚ) ≤ Fintype.card V by positivity)
  linarith

end Consensus.Goldilocks.Simulation

end

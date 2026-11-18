module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks under `Sleepy`: the origin chain

Blocks on the ancestor closure of the origin chain within a horizon `b` (`OnOriginChainWithin`)
are pairwise compatible once the origins within `b` are (S1): an ancestor of an origin is
compatible with every ancestor of a compatible origin, and genesis is below every honest block
(`OnOriginChainWithin.compatible`, `OnOriginChainWithin.of_anc`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The honest blocks of a run are coherent. -/
theorem honest_coherent {ini} (hrun : GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) :
    Coherent (tr.HonestBlocks H) :=
  honest_blocks_coherent hrun.toLocalRun hnc

/-- Genesis is an honest block below every honest block. -/
theorem honest_genesis_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) :
    sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H)
        (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ :=
    Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- An honest block with the genesis root is genesis. -/
theorem honest_eq_genesis {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hU : Coherent (tr.HonestBlocks H))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
  hU.1 hB (honest_genesis_anc hrun hB).1 hr

/-- Genesis has no parent, so its only ancestor is itself. -/
private theorem anc_genesis {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc S A (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)) :
    A = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, -, hY⟩
  · exact heq.symm
  · exact absurd hY.2.2 (by simp [Params.genesisBlock])

/-- Blocks below tips that are pairwise compatible (`Q`, an origin predicate) or genesis are
compatible. -/
private theorem chain_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {Q : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    (hcomp : ∀ C s C' s', Q C s → Q C' s' → Compatible (tr.HonestBlocks H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hB' : B' ∈ tr.HonestBlocks H)
    (h : B.root = sp.genesisRoot ∨ ∃ C s, Q C s ∧ Anc (tr.HonestBlocks H) B C)
    (h' : B'.root = sp.genesisRoot ∨ ∃ C s, Q C s ∧ Anc (tr.HonestBlocks H) B' C) :
    Compatible (tr.HonestBlocks H) B B' := by
  have hU := honest_coherent hrun hnc
  rcases h with hg | ⟨C, s, hC, hBC⟩
  · rw [honest_eq_genesis hrun hU hB hg]
    exact Or.inl (honest_genesis_anc hrun hB').2
  rcases h' with hg' | ⟨C', s', hC', hBC'⟩
  · rw [honest_eq_genesis hrun hU hB' hg']
    exact Or.inr (honest_genesis_anc hrun hB).2
  rcases hcomp C s C' s' hC hC' with hCC | hCC
  · exact Anc.total hU (hBC.trans hCC) hBC'
  · exact Anc.total hU hBC (hBC'.trans hCC)

/-- An ancestor of a block that is genesis or below a tip `Q` is genesis or below it. -/
private theorem chain_of_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {Q : SA.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B)
    (h : B.root = sp.genesisRoot ∨ ∃ C s, Q C s ∧ Anc (tr.HonestBlocks H) B C) :
    A.root = sp.genesisRoot ∨ ∃ C s, Q C s ∧ Anc (tr.HonestBlocks H) A C := by
  rcases h with hg | ⟨C, s, hC, hBC⟩
  · have hBU : B ∈ tr.HonestBlocks H := by
      by_cases hne : A = B
      · exact hne ▸ hA
      · exact (hAB.mem hne).2
    rw [honest_eq_genesis hrun (honest_coherent hrun hnc) hBU hg] at hAB
    exact Or.inl (by rw [anc_genesis hAB]; rfl)
  · exact Or.inr ⟨C, s, hC, hAB.trans hBC⟩

/-- **Blocks on the chain of the origins within `b` are compatible** when those origins are
pairwise compatible. -/
theorem OnOriginChainWithin.compatible (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {b : Time} (hcomp : ∀ C s C' s', OriginWithin tr H C s b → OriginWithin tr H C' s' b →
      Compatible (tr.HonestBlocks H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hB' : B' ∈ tr.HonestBlocks H) (h : OnOriginChainWithin tr H B b)
    (h' : OnOriginChainWithin tr H B' b) : Compatible (tr.HonestBlocks H) B B' :=
  chain_compatible hrun hnc (Q := fun C s => OriginWithin tr H C s b) hcomp hB hB'
    (onOriginChainWithin_iff.1 h) (onOriginChainWithin_iff.1 h')

/-- **An ancestor of a block on the chain of the origins within `b` is on it.** -/
theorem OnOriginChainWithin.of_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {b : Time} {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B) (h : OnOriginChainWithin tr H B b) :
    OnOriginChainWithin tr H A b :=
  onOriginChainWithin_iff.2
    (chain_of_anc hrun hnc (Q := fun C s => OriginWithin tr H C s b) hA hAB
      (onOriginChainWithin_iff.1 h))

end Consensus.Goldilocks.Compose

end

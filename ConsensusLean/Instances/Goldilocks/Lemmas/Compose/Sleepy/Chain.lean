module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks under `Sleepy`: the origin chain

Genesis is below every honest block (`honest_genesis_anc`), and the ancestor closure of the origin
chain within a horizon `b` (`OnOriginChainWithin`) is closed under ancestors inside the honest
blocks (`OnOriginChainWithin.of_anc`). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n}

/-- The honest blocks of a run are coherent. -/
theorem honest_coherent {ini} (hrun : GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr) :
    Coherent (tr.HonestBlocks H) :=
  honest_blocks_coherent hrun.toLocalRun hnc

/-- Genesis is an honest block below every honest block. -/
theorem honest_genesis_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) :
    sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H)
        (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ :=
    Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- An honest block with the genesis root is genesis. -/
theorem honest_eq_genesis {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hU : Coherent (tr.HonestBlocks H))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload :=
  hU.1 hB (honest_genesis_anc hrun hB).1 hr

/-- Genesis has no parent, so its only ancestor is itself. -/
private theorem anc_genesis {S : Set (AC.Blk sp.n (List (FG.Att sp.n)))}
    {A : AC.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc S A (sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload)) :
    A = sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, -, hY⟩
  · exact heq.symm
  · exact absurd hY.2.2 (by simp [Params.genesisBlock])

/-- An ancestor of a block that is genesis or below a tip `Q` is genesis or below it. -/
private theorem chain_of_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {Q : AC.Blk sp.n (List (FG.Att sp.n)) → Nat → Prop}
    {A B : AC.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
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

/-- **An ancestor of a block on the chain of the origins within `b` is on it.** -/
theorem OnOriginChainWithin.of_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {b : Time} {A B : AC.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B) (h : OnOriginChainWithin tr H B b) :
    OnOriginChainWithin tr H A b :=
  onOriginChainWithin_iff.2
    (chain_of_anc hrun hnc (Q := fun C s => OriginWithin tr H C s b) hA hAB
      (onOriginChainWithin_iff.1 h))

end Consensus.Goldilocks.Compose

end

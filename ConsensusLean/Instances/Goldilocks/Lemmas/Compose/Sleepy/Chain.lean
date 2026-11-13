module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks under `Sleepy`: the origin chain

Blocks on the ancestor closure of the origin chain (`OnOriginChain`) are pairwise compatible once
the origins are (S1): an ancestor of an origin is compatible with every ancestor of a compatible
origin, and genesis is below every honest block. Hence R.1's safety part:
every honest `ac_confirmed` is an ancestor of the effective record (the record,
or `Σ.F` when the record is not in the frame), which is on the chain, so the honest confirmed
outputs are pairwise compatible, served or not. -/

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

/-- **Blocks on the origin chain are compatible** when the origins are pairwise compatible. -/
theorem OnOriginChain.compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hcomp : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
      Compatible (tr.HonestBlocks H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hB' : B' ∈ tr.HonestBlocks H) (h : OnOriginChain tr H B) (h' : OnOriginChain tr H B') :
    Compatible (tr.HonestBlocks H) B B' :=
  chain_compatible hrun hnc hcomp hB hB' (onOriginChain_iff.1 h) (onOriginChain_iff.1 h')

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

/-- **An ancestor of a block on the origin chain is on it.** -/
theorem OnOriginChain.of_anc (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B) (h : OnOriginChain tr H B) : OnOriginChain tr H A :=
  onOriginChain_iff.2 (chain_of_anc hrun hnc hA hAB (onOriginChain_iff.1 h))

/-- **An ancestor of a block on the chain of the origins within `b` is on it.** -/
theorem OnOriginChainWithin.of_anc {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {b : Time} {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B) (h : OnOriginChainWithin tr H B b) :
    OnOriginChainWithin tr H A b :=
  onOriginChainWithin_iff.2
    (chain_of_anc hrun hnc (Q := fun C s => OriginWithin tr H C s b) hA hAB
      (onOriginChainWithin_iff.1 h))

/-- An honest confirmed read is an honest block on a chain `Ch` closed under ancestors that
holds the record's block and `Σ.F`: it is an ancestor of the effective record (the record's
block, or `Σ.F` when the record is not in the frame), whatever the head. -/
private theorem confirmed_read_of (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {Ch : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hanc : ∀ {A B}, A ∈ tr.HonestBlocks H → Anc (tr.HonestBlocks H) A B → Ch B → Ch A)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) (t : Time)
    (hrec : ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧ Ch C)
    (hF : Ch (tr.state y i).fg.F) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t ∈
        tr.HonestBlocks H ∧
      Ch ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t) := by
  have hU := honest_coherent hrun hnc
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, i, hX.1⟩
  -- the effective record is on the chain
  have hCr : (SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (Node.frame (tr.state y i)).F ∈ (Node.frame (tr.state y i)).tree ∧
      Ch ((SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (Node.frame (tr.state y i)).F) := by
    rcases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
      _ | R
    · exact ⟨hΦ.rooted.1, hF⟩
    · obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
      obtain ⟨C, hC, hCr, hCc⟩ := hrec
      obtain rfl : R = C := hU.1 (hsub hR) ⟨y, hy, i, hC⟩ (hRr.trans hCr.symm)
      exact ⟨hR, hCc⟩
  -- the confirmed output is an ancestor of it in the frame
  have hX : ∀ X, X = (SA.deepest (Node.frame (tr.state y i))
      {X | X ∈ (Node.frame (tr.state y i)).tree ∧
        (Node.frame (tr.state y i)).Anc X ((SA.lookup (Node.frame (tr.state y i))
          (tr.state y i).ac.latestConfirmed).getD (Node.frame (tr.state y i)).F) ∧
        (Node.frame (tr.state y i)).Anc X (SA.acHead sp (tr.state y i).ac
          (Node.frame (tr.state y i)) t)}).getD (Node.frame (tr.state y i)).F →
      X ∈ (Node.frame (tr.state y i)).tree ∧ (Node.frame (tr.state y i)).Anc X
        ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
          (Node.frame (tr.state y i)).F) := by
    rintro X rfl
    rcases hd : SA.deepest (Node.frame (tr.state y i)) _ with _ | D
    · exact ⟨hΦ.rooted.1, hΦ.rooted.2 _ hCr.1⟩
    · obtain ⟨⟨hDt, hDC, -⟩, -⟩ := SA.deepest_mem hd
      exact ⟨hDt, hDC⟩
  replace hX := hX _ rfl
  exact ⟨hsub hX.1, hanc (hsub hX.1) (hX.2.mono hsub) hCr.2⟩

/-- An honest confirmed read, at the state before any cut and at any time, is an honest block on
the origin chain: it is an ancestor of the effective record (the record's block, or `Σ.F` when
the record is not in the frame), whatever the head. -/
theorem confirmed_read_on_chain (hinv : SleepyInvariant tr H)
    (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) (t : Time) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t ∈
        tr.HonestBlocks H ∧
      OnOriginChain tr H
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t) :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i
  confirmed_read_of hrun hnc (fun hA hAB h => OnOriginChain.of_anc hrun hnc hA hAB h) hy i t
    ⟨C, hC, hCr, onOriginChain_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    (hinv.caches y hy i).1

/-- **An honest confirmed read at a cut within `b`**, at any time, is an honest block on the
chain of the origins within `b`. -/
theorem confirmed_read_on_chain_upTo {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    (hi : ∀ k < i, tr.time k ≤ b) (t : Time) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t ∈
        tr.HonestBlocks H ∧
      OnOriginChainWithin tr H
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t) b :=
  have ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i hi
  confirmed_read_of hrun hnc (fun hA hAB h => OnOriginChainWithin.of_anc hrun hnc hA hAB h) hy
    i t ⟨C, hC, hCr, onOriginChainWithin_iff.2 (hgo.imp_right fun ⟨s, hs⟩ => ⟨C, s, hs, .refl⟩)⟩
    (hinv.caches y hy i hi).1

/-- **R.1 up to `b` from the invariant**: the confirmed reads of honest nodes at any two cuts
within `b`, at any times, are compatible (inside the honest blocks). -/
theorem SleepyInvariantUpTo.read_compatible {b : Time} (hinv : SleepyInvariantUpTo tr H b)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) {y y' : Fin sp.n} (hy : y ∈ H)
    (hy' : y' ∈ H) {i i' : Nat} (hi : ∀ k < i, tr.time k ≤ b) (hi' : ∀ k < i', tr.time k ≤ b)
    (t t' : Time) :
    Compatible (tr.HonestBlocks H)
      ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t)
      ((goldilocksNode sp ro).confirmed (tr.state y' i').ac (Node.frame (tr.state y' i')) t') :=
  have ⟨hB, hc⟩ := confirmed_read_on_chain_upTo hinv hrun hnc hy hi t
  have ⟨hB', hc'⟩ := confirmed_read_on_chain_upTo hinv hrun hnc hy' hi' t'
  OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible hB hB' hc hc'

end Consensus.Goldilocks.Compose

end

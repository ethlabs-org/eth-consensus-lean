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
origin, and genesis is below every honest block. Hence R.1's safety part
(workbench#11 §5): every honest `ac_confirmed` is an ancestor of the effective record (the record,
or `Σ.F` when the record is not in the frame), which is on the chain, so the honest confirmed
outputs are pairwise compatible, served or not. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

/-- The Goldilocks node's AC meets the interface requirements 1–5 (A0.6, A0.9). -/
private theorem requirements (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    (goldilocksNode sp ro).Requirements :=
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

/-- The honest blocks of a run are coherent. -/
private theorem honest_coherent (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) :
    Coherent (tr.HonestBlocks H) :=
  (ac_projection _ _ dg H _ tr (requirements sp ro) hrun.toLocalRun hnc).coherent

/-- Genesis is an honest block below every honest block. -/
private theorem genesis_anc (hrun : GoldilocksRun dg H tr) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H) :
    sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∈ tr.HonestBlocks H ∧
      Anc (tr.HonestBlocks H)
        (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) B := by
  obtain ⟨y, hy, i, hBt⟩ := hB
  obtain ⟨-, -, hg, hanc⟩ :=
    Store.accepted_tree _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  exact ⟨⟨y, hy, i, hg⟩, (hanc B hBt).mono fun X hX => ⟨y, hy, i, hX⟩⟩

/-- An honest block with the genesis root is genesis. -/
private theorem eq_genesis (hrun : GoldilocksRun dg H tr) (hU : Coherent (tr.HonestBlocks H))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hr : B.root = sp.genesisRoot) :
    B = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
  hU.1 hB (genesis_anc hrun hB).1 hr

/-- Genesis has no parent, so its only ancestor is itself. -/
private theorem anc_genesis {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {A : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc S A (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload)) :
    A = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, -, hY⟩
  · exact heq.symm
  · exact absurd hY.2.2 (by simp [Params.genesisBlock])

/-- **Blocks on the origin chain are compatible** when the origins are pairwise compatible. -/
theorem OnOriginChain.compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hcomp : ∀ C s C' s', Origin tr H C s → Origin tr H C' s' →
      Compatible (tr.HonestBlocks H) C C')
    {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hB' : B' ∈ tr.HonestBlocks H) (h : OnOriginChain tr H B) (h' : OnOriginChain tr H B') :
    Compatible (tr.HonestBlocks H) B B' := by
  have hU := honest_coherent hrun hnc
  rcases onOriginChain_iff.1 h with hg | ⟨C, s, hC, hBC⟩
  · rw [eq_genesis hrun hU hB hg]
    exact Or.inl (genesis_anc hrun hB').2
  rcases onOriginChain_iff.1 h' with hg' | ⟨C', s', hC', hBC'⟩
  · rw [eq_genesis hrun hU hB' hg']
    exact Or.inr (genesis_anc hrun hB).2
  rcases hcomp C s C' s' hC hC' with hCC | hCC
  · exact Anc.total hU (hBC.trans hCC) hBC'
  · exact Anc.total hU hBC (hBC'.trans hCC)

/-- **An ancestor of a block on the origin chain is on it.** -/
theorem OnOriginChain.of_anc (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {A B : SA.Blk sp.n (List (FG.Att sp.n))} (hA : A ∈ tr.HonestBlocks H)
    (hAB : Anc (tr.HonestBlocks H) A B) (h : OnOriginChain tr H B) : OnOriginChain tr H A := by
  rcases onOriginChain_iff.1 h with hg | ⟨C, s, hC, hBC⟩
  · have hBU : B ∈ tr.HonestBlocks H := by
      by_cases hne : A = B
      · exact hne ▸ hA
      · exact (hAB.mem hne).2
    rw [eq_genesis hrun (honest_coherent hrun hnc) hBU hg] at hAB
    exact onOriginChain_iff.2 (Or.inl (by rw [anc_genesis hAB]; rfl))
  · exact onOriginChain_iff.2 (Or.inr ⟨C, s, hC, hAB.trans hBC⟩)

/-- An honest confirmed read, at the state before any cut and at any time, is an honest block on
the origin chain: it is an ancestor of the effective record (the record's block, or `Σ.F` when
the record is not in the frame), whatever the head. -/
theorem confirmed_read_on_chain (hinv : SleepyInvariant tr H) (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) (t : Time) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t ∈
        tr.HonestBlocks H ∧
      OnOriginChain tr H
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) t) := by
  have hU := honest_coherent hrun hnc
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H :=
    fun X hX => ⟨y, hy, i, hX.1⟩
  -- the effective record is on the chain
  have hCr : (SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
        (Node.frame (tr.state y i)).F ∈ (Node.frame (tr.state y i)).tree ∧
      OnOriginChain tr H ((SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (Node.frame (tr.state y i)).F) := by
    rcases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
      _ | R
    · exact ⟨hΦ.rooted.1, (hinv.caches y hy i).1⟩
    · obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
      obtain ⟨C, hC, hCr, hgo⟩ := hinv.record y hy i
      obtain rfl : R = C := hU.1 (hsub hR) ⟨y, hy, i, hC⟩ (hRr.trans hCr.symm)
      refine ⟨hR, onOriginChain_iff.2 ?_⟩
      rcases hgo with hg | ⟨s, hs⟩
      · exact Or.inl hg
      · exact Or.inr ⟨R, s, hs, .refl⟩
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
  exact ⟨hsub hX.1, OnOriginChain.of_anc hrun hnc (hsub hX.1) (hX.2.mono hsub) hCr.2⟩

/-- **R.1 from the invariant**: the confirmed outputs of honest nodes at any two cuts are
compatible (inside the honest blocks). -/
theorem SleepyInvariant.confirmed_compatible (hinv : SleepyInvariant tr H)
    (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr) :
    ∀ y ∈ H, ∀ y' ∈ H, ∀ i i',
      Compatible (tr.HonestBlocks H) (tr.confirmedAt y i) (tr.confirmedAt y' i') := by
  intro y hy y' hy' i i'
  obtain ⟨hB, hc⟩ := confirmed_read_on_chain hinv hrun hnc hy i (tr.time i)
  obtain ⟨hB', hc'⟩ := confirmed_read_on_chain hinv hrun hnc hy' i' (tr.time i')
  exact OnOriginChain.compatible hrun hnc hinv.origins_compatible hB hB' hc hc'

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes

public section

/-! # Goldilocks SA: A1.8 for an ancestor of the result

A1.8 (`result_transfer`) with its hypotheses and conclusion about a block `D ⪯ C` of the result
`C` (a slow lock's block is on its result's path). The counted supporters of `C` support
`D`, and they are a strict majority of the writer's participants. -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable (sp : SAParams)

/-- `result_transfer_anc` with the unlock given. -/
theorem result_transfer_ancU
    {u : Nat → Set Lock} {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hrun : ACRunU wm u proposer tr H U) {s : Nat}
    {X y : Fin sp.n} {i₀ i : Nat} {C D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hX : X ∈ H)
    (hres : ResultAt tr X i₀ s C CV) (hDC : Anc U D C) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV)
    (hviab : ViableAtVote ℓ e (s + 1) D)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg D := by
  obtain ⟨-, -, -, hhead⟩ := castAt_specU hrun.localRun hy hc
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_ancU hrun.localRun (fun _ => voteStart_initial _) hy hc
  rw [hs] at hdomA
  have hDt : D ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hmaj := result_majority hres
  obtain ⟨ℓX, hupd, -, rfl⟩ := hres
  have hsupp := counted_supportersU hrun hX hy hupd.1 hc hs hDC hcarry hviab hd
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => voteDomain_subset_tree
        hB) hdomA hviab.voteDomain
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxD =>
      isBest_of_majority hΦ (merged_support_subsetU hrun.localRun hy hc (s + 1))
        (fun B hB => (voteDomain_subset_tree hB.1)) hsupp
          (merged_voters_subsetU hrun.localRun (fun _ => voteStart_initial _) hy hc hd)
          hmaj hCx hp hCxD
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : D = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hDt
  · exact (Anc.mem hcore he).2

/-- **A1.8 for a block `D ⪯ C` of the result `C`.** -/
theorem result_transfer_anc {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {proposer : Nat → Fin sp.n} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hrun : ACRun proposer tr H U) {s : Nat}
    {X y : Fin sp.n} {i₀ i : Nat} {C D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hX : X ∈ H)
    (hres : ResultAt tr X i₀ s C CV) (hDC : Anc U D C) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV)
    (hviab : ViableAtVote ℓ e (s + 1) D)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg D :=
  result_transfer_ancU (FGP := FGP) (ro := ro) (H := H) (proposer := proposer) (U := U) (tr := tr)
      (hrun := hrun.toU) (s := s) (X := X) (y := y) (i₀ := i₀) (i := i) (C := C) (D := D)
          (CV := CV) (ℓ := ℓ) (e := e) (hX := hX) (hres := hres) (hDC := hDC) (hy := hy)
              (hc := hc) (hs := hs) (hcarry := hcarry) (hviab := hviab) (hlocks := hlocks)
                  (hd := hd)

/-- A strict majority result has an earlier honest counted supporter when its
participants number at least twice the faulty validators. -/
theorem result_honest_supporter_of_participants {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U)
    {x : Fin sp.n} (hx : x ∈ H) {i s : Nat} {B C : Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hR : ResultAt tr x i s C CV) (hBC : Anc U B C)
    (hparticipants : 2 * Hᶜ.ncard ≤ (voters {v | v ∈ (tr.state x i).pool s}).ncard) :
    ∃ z ∈ H, ∃ q < i, ∃ e, VoteAt tr z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ VoteExtends U e.msg B := by
  have hmaj := result_majority hR
  obtain ⟨z, ⟨v, hv, hvz⟩, hz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := Hᶜ) (t := {w | ∃ v ∈ CV, v.val = w}) (by omega)
  have hzH : z ∈ H := not_not.mp hz
  obtain ⟨ℓ, hupd, _, hCV⟩ := hR
  have hv' := hv
  rw [hCV] at hv'
  obtain ⟨hvp, _, _, R, hRt, hroot, hCR⟩ := hv'
  have hvH : v.val ∈ H := hvz.symm ▸ hzH
  obtain ⟨q, hq, e, he, hmsg⟩ := hrun.honest.pool_vote x hx i s v hvp hvH
  have hslot := state_pool_slot sp hrun.localRun hx i s v hvp
  refine ⟨v.val, hvH, q, hq, e, he, hmsg.symm ▸ hv, ?_, ?_⟩
  · simpa only [hmsg] using hslot
  · rw [hmsg]
    have hΦU := (frameIn_of_callAt hrun.localRun hx hupd.1).2
    exact ⟨R, hΦU hRt, hroot, hBC.trans (Anc.mono hΦU hCR)⟩

end Consensus.Goldilocks.SA

end

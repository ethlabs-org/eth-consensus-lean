module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # An optimistic writer below a later honest proposal -/

namespace Consensus.Goldilocks.SA.Growing.ProposalSources

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {proposer : Nat → Fin sp.n} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {T : SATrace sp FGP ro}

theorem optimistic_first_proposal_anc_at
    (hrun : Growing.ACRun proposer T H U) {i : Nat}
    (hf : 2 * (H (T.time i))ᶜ.ncard < sp.n)
    {X : Fin sp.n} {i₀ σ : Nat} (hX : X ∈ H (T.time i₀))
    {D B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hopt : OptimisticLockAt T X i₀ σ D CV) (hBD : Anc U B D)
    {x : Fin sp.n} (hx : x ∈ H (T.time i))
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : T.CallAt x i ell)
    (hslot : sp.slot (T.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (T.state x i) ell.frame (T.time i)).2 = some (d, pay))
    (hV : B ∈ ell.frame.tree ∧
      (B ∈ ell.frame.viableTree ell.frame.tree ∨ ell.frame.Anc B ell.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (T.state x i) ell.frame σ v)
    (hhigh : HighLocksCompatible U (T.state x i) (T.time i) σ B) :
    Anc U B d.head := by
  have hm := hrun.localRun.time_mono
  have hU := hrun.localRun.coherent
  have hrx := hrun.upTo (hrun.localRun.time_nonneg i)
  have hrX := hrun.upTo (hrun.localRun.time_nonneg i₀)
  have hr := hrx.localRun
  have hc' := (Trace.upTo_callAt T).mpr ⟨le_rfl, hc⟩
  have hs : (T.upTo (T.time i)).state x i = T.state x i :=
    Trace.upTo_state T x (fun q hq => hm hq.le)
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc'
  obtain ⟨ellX, A, hpt, hslX, hsel, rfl⟩ := hopt
  have hpt' := (upTo_optimisticPoint hm).mpr ⟨le_rfl, hpt⟩
  obtain ⟨-, hΦXU⟩ := frameIn_of_callAt hrX.localRun hX hpt'.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel'
  obtain ⟨-, h34, -⟩ := (deepest_mem hsel').1
  rw [hrun.stock] at h34
  have hstock := hrun.stock
  rw [hslX] at h34
  set V := View.ofLists (voteViewList ((T.upTo (T.time i)).state x i) ell.frame σ ⊤)
  set SX := optimisticVoters sp A ellX.frame σ D
  have hcover : SX ⊆ supporters ell.frame V σ B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R', hR', hR'r, hDR'⟩
    have hvs := optimisticPoint_pool_slot hrX.localRun hX hpt' hv
    by_cases heq : v.val ∈ equivocators V.votes
    · exact Or.inr heq
    left
    obtain ⟨hheld, R, hR, hRr, hbs⟩ := heldAtProposal_iff.mp
      (hP v ⟨hv, R', hR', hR'r, hDR'⟩)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦXU hR') (hRr.trans hR'r.symm)
    have hheld : v ∈ (T.state x i).pool σ := hheld.resolve_right fun h =>
      heq (equivocators_mono (S := {u | u ∈ (T.state x i).pool σ})
        (fun u hu => (mem_proposalView_votes hr hx i σ ell.frame u).2
          (hs.symm ▸ hu)) h)
    have hRs : R.slot ≤ σ := by
      have := frame_slot_le sp hrX.localRun hX hpt'.1 R hR'
      change R.slot ≤ sp.slot (T.time i₀) at this
      rw [hslX] at this
      omega
    exact proposal_supporter hr hx hc' hvs (hs.symm ▸ hheld) hR hRr hRs
      (anc_tree_of_anc_U hU hΦ hΦU hV.1
        (hBD.trans (Anc.mono hΦXU hDR')) hR) (hs.symm ▸ hbs) heq
  have hE : (equivocators V.votes).ncard ≤ (H (T.time i))ᶜ.ncard :=
    Set.ncard_le_ncard fun w hw hwH =>
      honest_not_equivocator_proposal hrx hx i σ ell.frame hwH (by simpa only [V, hs] using hw)
  have hO : (voters V.votes \ SX).ncard + SX.ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ ((voters V.votes \ SX) ∪ SX))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_union_eq Set.disjoint_sdiff_left] at this
    exact this
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by omega
  have hprop' := hprop
  rw [← hs] at hprop'
  have hhigh' := hhigh
  rw [← hs] at hhigh'
  refine proposal_walk hr hx hc' hslot hprop' hV.2
    (unlocked_compatible hU hΦ hΦU hV.1 (Or.inl ⟨SX, fun w hw => ?_, by omega⟩)
      (fun l hl hlive hlσ Y hY hYr =>
        highLocksCompatible_iff.mp hhigh' l hl hlive (by exact_mod_cast hlσ) Y hY hYr)
      (locksWF_state hr hx i))
    fun Y Cx hCx hp hCxB => isBest_of_cover hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hcover h3 hCx hp hCxB
  rcases hcover hw with ⟨-, v, hv, hvw, hvs, hva⟩ | h
  · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
  · exact Or.inl h

end Consensus.Goldilocks.SA.Growing.ProposalSources

end

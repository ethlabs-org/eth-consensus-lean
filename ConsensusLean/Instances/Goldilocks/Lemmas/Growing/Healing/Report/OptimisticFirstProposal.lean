module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # The first proposal after an optimistic write, under growing faults

The writer is honest at its write and the proposer at its proposal call, independently. The
writer's pool and counted voters are read on the prefix through the write; the proposer's view,
equivocators and locks on the prefix through the proposal, over the validators honest there,
which is where the fault count is charged. -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- **The first proposal after an optimistic write**: with every counted vote of the write held at
the proposal, `B ⪯ D` in the frame, and the high locks compatible, `B` is an ancestor of the duty
head of an honest proposal of the next slot. -/
theorem optimistic_first_proposal_stored_at (hrun : ACRun proposer tr H U)
    {X : Fin sp.n} {i₀ σ : Nat} (hX : X ∈ H (tr.time i₀)) {D : Blk sp.n FGP}
    {CV : Set (Vote sp.n)} (hopt : OptimisticLockAt tr X i₀ σ D CV) {B : Blk sp.n FGP}
    (hBD : Anc U B D) {x : Fin sp.n} {i : Nat} (hx : x ∈ H (tr.time i))
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ)
    (hslot : sp.slot (tr.time i) = σ + 1) {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n}
    (hprop : (acProposal sp (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, pay))
    (hV : B ∈ ℓ.frame.tree ∧
      (B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot))
    (hP : ∀ v ∈ CV, HeldAtProposal (tr.state x i) ℓ.frame σ v)
    (hhigh : HighLocksCompatible U (tr.state x i) (tr.time i) σ B)
    (hstock : sp.committeeSize = sp.n) :
    Anc U B d.head := by
  have hU := hrun.localRun.coherent
  have htime := hrun.localRun.time_mono
  have hry := hrun.upTo (hrun.localRun.time_nonneg i)
  have hrx := hrun.upTo (hrun.localRun.time_nonneg i₀)
  have hr := hry.localRun
  have hst : (tr.upTo (tr.time i)).state x i = tr.state x i :=
    Trace.upTo_state tr x fun _ hk => htime hk.le
  have hc' : (tr.upTo (tr.time i)).CallAt x i ℓ := (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  have hprop' : (acProposal sp ((tr.upTo (tr.time i)).state x i) ℓ.frame
      ((tr.upTo (tr.time i)).time i)).2 = some (d, pay) := by rw [hst]; exact hprop
  have hP' : ∀ v ∈ CV, HeldAtProposal ((tr.upTo (tr.time i)).state x i) ℓ.frame σ v := by
    rw [hst]; exact hP
  have hhigh' : HighLocksCompatible U ((tr.upTo (tr.time i)).state x i)
      ((tr.upTo (tr.time i)).time i) σ B := by rw [hst]; exact hhigh
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc'
  obtain ⟨ℓX, A, hpt, hslX, hsel, rfl⟩ := id hopt
  have hpt' := (upTo_optimisticPoint htime).mpr ⟨le_rfl, hpt⟩
  obtain ⟨-, hΦXU⟩ := frameIn_of_callAt hrx.localRun hX hpt'.1
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel' with hcond
  obtain ⟨-, h34, -⟩ := (deepest_mem hsel').1
  rw [hslX] at h34
  set V := View.ofLists (voteViewList ((tr.upTo (tr.time i)).state x i) ℓ.frame σ ⊤) with hV'
  set SX := optimisticVoters sp A ℓX.frame σ D
  -- every optimistic voter supports `B` at the proposal, or equivocates there
  have hcover : SX ⊆ supporters ℓ.frame V σ B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R', hR', hR'r, hDR'⟩
    have hvs := optimisticPoint_pool_slot hrx.localRun hX hpt' hv
    by_cases heq : v.val ∈ equivocators V.votes
    · exact Or.inr heq
    left
    obtain ⟨hheld, R, hR, hRr, hbs⟩ := heldAtProposal_iff.mp (hP' v ⟨hv, R', hR', hR'r, hDR'⟩)
    obtain rfl : R = R' := hU.1 (hΦU hR) (hΦXU hR') (hRr.trans hR'r.symm)
    have hheld : v ∈ ((tr.upTo (tr.time i)).state x i).pool σ := hheld.resolve_right fun h =>
      heq (equivocators_mono (fun u hu => (mem_proposalView_votes hr hx i σ ℓ.frame u).2 hu) h)
    have hRs : R.slot ≤ σ := by
      have h := frame_slot_le sp hrx.localRun hX hpt'.1 R hR'
      change R.slot ≤ sp.slot (tr.time i₀) at h
      omega
    exact proposal_supporter hr hx hc' hvs hheld hR hRr hRs
      (anc_tree_of_anc_U hU hΦ hΦU hV.1 (hBD.trans (Anc.mono hΦXU hDR')) hR) hbs heq
  -- counting at the proposal: the equivocators are faulty there, the others are outside `SX`
  have hE : (equivocators V.votes).ncard ≤ (H (tr.time i))ᶜ.ncard := Set.ncard_le_ncard
    fun w hw hwH => honest_not_equivocator_proposal hry hx i σ ℓ.frame hwH hw
  have hO : (voters V.votes \ SX).ncard + SX.ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ ((voters V.votes \ SX) ∪ SX))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      Set.ncard_union_eq Set.disjoint_sdiff_left] at this
    exact this
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by omega
  -- the live locks after unlocking are compatible with `B`
  have hlocks : ∀ C ∈ liveLockBlocks sp (unlock sp ((tr.upTo (tr.time i)).state x i).locks
      ℓ.frame ((tr.upTo (tr.time i)).time i) σ V) ℓ.frame ((tr.upTo (tr.time i)).time i),
      Compatible U C B := by
    refine unlocked_compatible hr.coherent hΦ hΦU hV.1 ?_
      (fun l hl hlive hlσ X hX hXr =>
        highLocksCompatible_iff.mp hhigh' l hl hlive (by exact_mod_cast hlσ) X hX hXr)
      (locksWF_state hr hx i)
    refine Or.inl ⟨SX, fun w hw => ?_, by omega⟩
    rcases hcover hw with ⟨-, v, hv, hvw, hvs, hva⟩ | h
    · exact Or.inr ⟨v, hv, hvw, hvs, hva⟩
    · exact Or.inl h
  exact proposal_walk hr hx hc' hslot hprop' hV.2 hlocks
    fun X' Cx hCx hp hCxD => isBest_of_cover hΦ (ofLists_support_subset _ _ _ _)
      (fun _ h => h.1) hcover h3 hCx hp hCxD

end Consensus.Goldilocks.SA.Growing

end

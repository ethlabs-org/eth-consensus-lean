module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild

public section

/-! # Goldilocks SA: carried heads force the walk towards an anchor

Prior-slot honest heads (`honest_isBest_of_carry`, `honest_prefix_of_carry`) force the best child
towards an anchor once their batch is carried. Split out of `AC/Steps/Nodes`, so that a new carry
helper does not rebuild Nodes' cone. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- Prior-slot honest heads force the child toward a lock anchor once their
actual batch is carried. This is a local comparison, not current-slot unanimity. The voters
are members of the slot-`s` committee (T), fewer than a third of whose members are faulty. -/
theorem honest_isBest_of_carry {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    (hf : 3 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : Blk sp.n FGP}
    (hBt : B ∈ ℓ.frame.tree)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hex : ∀ x ∈ H, x ∈ K.committee s → ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s)
    (hcarry : CarryAt tr U y i e s
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    {X C : Blk sp.n FGP}
    (hC : C ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
    (hp : C.parent = some X.root) (hCB : ℓ.frame.Anc C B) :
    IsBest sp (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s)
      {Q | Q ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) ∧
        Q.parent = some X.root ∧
        goldfishEligible sp ℓ.frame (tr.time i) (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s Q}
      C := by
  have hr := hrun.localRun
  have hΦ := frameIn_of_callAt hr hy hc.1
  let V := mergedVoteView sp e.readPoint ℓ.frame (s + 1)
  have hcover : K.committee s ∩ H ⊆ supporters ℓ.frame V s B ∪ equivocators V.votes := by
    rintro x ⟨hxK, hx⟩
    obtain ⟨j, e', hv, hvs⟩ := hex x hx hxK
    obtain ⟨ℓx, hcx⟩ := hv
    have hvx := (castAt_spec hr hx hcx).1
    obtain ⟨R, hR, hRr, hRs⟩ := honest_head hrun hx ⟨ℓx, hcx⟩
    obtain ⟨R', hR', hR'r, hBR⟩ := hall x hx j e' ⟨ℓx, hcx⟩ hvs
    have heq : R' = R := hr.coherent.1 hR' hR (hR'r.trans hRr.symm)
    have hBR' : Anc U B R := heq ▸ hBR
    have h := carried_cover hrun hy hc hs hBt hcarry
      ⟨x, hx, j, e', ⟨ℓx, hcx⟩, rfl, hvs⟩ hvs
      ⟨R, hR, hRr, hvs ▸ hRs, hBR'⟩
    exact hvx ▸ h
  have hW : voters V.votes ⊆ K.committee s := by
    rintro u ⟨v, hv, rfl⟩
    have hK := hT y hy i ℓ e hc s v hv
    rwa [merged_vote_slot hr (fun _ => voteStart_initial _) hy hc v hv] at hK
  have hE : equivocators V.votes ⊆ K.committee s ∩ Hᶜ := by
    intro w hw
    refine ⟨?_, fun hwH => honest_not_equivocator hrun hy hc hwH hw⟩
    obtain ⟨a, ha, -, -, -, rfl, -⟩ := hw
    exact hW ⟨a, ha, rfl⟩
  have h3 := third_cover_count (K.committee s) hW hE (by rw [hsize s]; exact hf)
  exact isBest_of_cover hΦ.1 (merged_support_subset hr hy hc (s + 1)) (fun _ h =>
      voteDomain_subset_tree h.1)
    hcover h3 hC hp hCB

/-- A shallower voter walk reaches a lock anchor supported by all actual
prior-slot honest votes. Only the prefix is asserted. -/
theorem honest_prefix_of_carry {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) (K : CommitteeDict sp.n)
    (hT : CommitteeT K tr H) (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    (hf : 3 * (K.committee s ∩ Hᶜ).ncard < sp.committeeSize) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : Blk sp.n FGP}
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hex : ∀ x ∈ H, x ∈ K.committee s → ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s)
    (hcarry : CarryAt tr U y i e s
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hB : B ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
    (haB : ℓ.frame.Anc (getAnchor sp e.readPoint ℓ.frame (tr.time i)) B) :
    ℓ.frame.Anc B (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s) := by
  have hΦ := frameIn_of_callAt hrun.localRun hy hc.1
  have hVT : ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) ⊆ ℓ.frame.tree :=
    fun _ h => voteDomain_subset_tree h.1
  have hBt := hVT hB
  have hdomA := voteDomain_anc hrun.localRun hy hc
  rw [hs] at hdomA
  unfold getHead
  refine anc_ghost_of_best hΦ.1.coherent hVT (hΦ.1.finite.subset hVT) hBt _ haB
    (Set.ncard_le_ncard (fun _ h => hVT h.1) hΦ.1.finite) ?_
  intro X haX hXB hne
  obtain rfl | ⟨C, eC, hCB⟩ := Relation.ReflTransGen.cases_head_iff.1 hXB
  · exact (hne rfl).elim
  obtain ⟨_, _, Y, hY, hvY, hBY⟩ := hB
  have hCv : C ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) :=
    ⟨hdomA Y hY C (hCB.trans hBY),
      ((fcRoot_anc_getAnchor hΦ.1 e.readPoint (tr.time i)).trans haX).tail eC,
      Y, hY, hvY, hCB.trans hBY⟩
  exact ⟨C, honest_isBest_of_carry sp hrun K hT hsize hf hy hc hs hBt hall hex hcarry hCv eC.2.2
    hCB, hCB⟩

end Consensus.Goldilocks.SA

end

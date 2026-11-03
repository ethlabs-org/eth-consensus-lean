module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild

public section

/-! # Goldilocks SA: carried heads force the walk towards an anchor

Prior-slot honest heads (`honest_isBest_of_carry`, `honest_prefix_of_carry`) and the counted
votes of an optimistic lock (`optimistic_isBest_of_carry`, `optimistic_prefix_of_carry`) force
the best child towards an anchor once their batch is carried. Split out of `AC/Steps/Nodes`, so
that a new carry helper does not rebuild Nodes' cone. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- Prior-slot honest heads force the child toward a lock anchor once their
actual batch is carried. This is a local comparison, not current-slot unanimity. -/
theorem honest_isBest_of_carry {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) {s : Nat}
    (hf : 3 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : Blk sp.n FGP}
    (hBt : B ∈ ℓ.frame.tree)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hex : ∀ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s)
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
  have hcover : H ⊆ supporters ℓ.frame V s B ∪ equivocators V.votes := by
    intro x hx
    obtain ⟨j, e', hv, hvs⟩ := hex x hx
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
  have hE : (equivocators V.votes).ncard ≤ Hᶜ.ncard :=
    Set.ncard_le_ncard fun w hw hwH => honest_not_equivocator hrun hy hc hwH hw
  have hcompl : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hout : (voters V.votes \ H).ncard ≤ Hᶜ.ncard :=
    Set.ncard_le_ncard fun _ h => h.2
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ H).ncard < H.ncard := by omega
  exact isBest_of_cover hΦ.1 (merged_support_subset hr hy hc (s + 1)) (fun _ h =>
      voteDomain_subset_tree h.1)
    hcover h3 hC hp hCB

/-- A shallower voter walk reaches a lock anchor supported by all actual
prior-slot honest votes. Only the prefix is asserted. -/
theorem honest_prefix_of_carry {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) {s : Nat}
    (hf : 3 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : Blk sp.n FGP}
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hex : ∀ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s)
    (hcarry : CarryAt tr U y i e s
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hB : B ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
    (haB : ℓ.frame.Anc (getAnchor sp e.readPoint ℓ.frame (tr.time i)) B) :
    ℓ.frame.Anc B (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s) := by
  have hΦ := frameIn_of_callAt hrun.localRun hy hc.1
  have hT : ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) ⊆ ℓ.frame.tree :=
    fun _ h => voteDomain_subset_tree h.1
  have hBt := hT hB
  have hdomA := voteDomain_anc hrun.localRun hy hc
  rw [hs] at hdomA
  unfold getHead
  refine anc_ghost_of_best hΦ.1.coherent hT (hΦ.1.finite.subset hT) hBt _ haB
    (Set.ncard_le_ncard (fun _ h => hT h.1) hΦ.1.finite) ?_
  intro X haX hXB hne
  obtain rfl | ⟨C, eC, hCB⟩ := Relation.ReflTransGen.cases_head_iff.1 hXB
  · exact (hne rfl).elim
  obtain ⟨_, _, Y, hY, hvY, hBY⟩ := hB
  have hCv : C ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) :=
    ⟨hdomA Y hY C (hCB.trans hBY),
      ((fcRoot_anc_getAnchor hΦ.1 e.readPoint (tr.time i)).trans haX).tail eC,
      Y, hY, hvY, hCB.trans hBY⟩
  exact ⟨C, honest_isBest_of_carry sp hrun hf hy hc hs hBt hall hex hcarry hCv eC.2.2 hCB, hCB⟩

/-- Actual optimistic CV dominance forces each child toward the stored block
in a receiving vote's frozen domain. This local comparison needs delivery,
but neither earlier-head induction nor prior-slot unanimity. -/
theorem optimistic_isBest_of_carry {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * Hᶜ.ncard < sp.n) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV) (hBt : B ∈ ℓ.frame.tree)
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
  obtain ⟨ℓx, A, hpt, hslx, hsel, rfl⟩ := hopt
  have hΦxU := (frameIn_of_callAt hr hx hpt.1).2
  let SX := optimisticVoters sp A ℓx.frame s D
  have h34 : 3 * sp.n ≤ 4 * SX.ncard := by
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h := (deepest_mem hsel).1.2.1
    rwa [hslx] at h
  let V := mergedVoteView sp e.readPoint ℓ.frame (s + 1)
  have hcover : SX ⊆ supporters ℓ.frame V s B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R, hR, hRr, hDR⟩
    exact carried_cover hrun hy hc hs hBt hcarry ⟨hv, R, hR, hRr, hDR⟩
      (optimisticPoint_pool_slot hr hx hpt hv) ⟨R, hΦxU hR, hRr,
        (frame_slot_le sp hr hx hpt.1 R hR).trans hslx.le, hBD.trans (Anc.mono hΦxU hDR)⟩
  have hE : (equivocators V.votes).ncard ≤ Hᶜ.ncard :=
    Set.ncard_le_ncard fun w hw hwH => honest_not_equivocator hrun hy hc hwH hw
  have hcompl : SX.ncard + SXᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hout : (voters V.votes \ SX).ncard ≤ SXᶜ.ncard :=
    Set.ncard_le_ncard fun _ h => h.2
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by
    omega
  exact isBest_of_cover hΦ.1 (merged_support_subset hr hy hc (s + 1)) (fun _ h =>
      voteDomain_subset_tree h.1)
    hcover h3 hC hp hCB

/-- CV dominance carries a shallower walk up to an optimistic anchor.
Unlike `optimistic_transfer_stored`, this prefix uses explicit anchor order,
not causal induction to establish compatibility with every lock. -/
theorem optimistic_prefix_of_carry {FGP : Type} {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    {proposer : Nat → Fin sp.n} (hrun : ACRun proposer tr H U) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hx : x ∈ H)
    (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * Hᶜ.ncard < sp.n) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV)
    (hB : B ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
    (haB : ℓ.frame.Anc (getAnchor sp e.readPoint ℓ.frame (tr.time i)) B) :
    ℓ.frame.Anc B (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s) := by
  have hΦ := frameIn_of_callAt hrun.localRun hy hc.1
  have hT : ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) ⊆ ℓ.frame.tree :=
    fun _ h => voteDomain_subset_tree h.1
  have hBt := hT hB
  have hdomA := voteDomain_anc hrun.localRun hy hc
  rw [hs] at hdomA
  unfold getHead
  refine anc_ghost_of_best hΦ.1.coherent hT (hΦ.1.finite.subset hT) (hT hB) _ haB
    (Set.ncard_le_ncard (fun _ h => hT h.1) hΦ.1.finite) ?_
  intro X haX hXB hne
  obtain rfl | ⟨C, eC, hCB⟩ := Relation.ReflTransGen.cases_head_iff.1 hXB
  · exact (hne rfl).elim
  obtain ⟨_, _, Y, hY, hvY, hBY⟩ := hB
  have hCv : C ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) :=
    ⟨hdomA Y hY C (hCB.trans hBY),
      ((fcRoot_anc_getAnchor hΦ.1 e.readPoint (tr.time i)).trans haX).tail eC,
      Y, hY, hvY, hCB.trans hBY⟩
  exact ⟨C, optimistic_isBest_of_carry sp hrun hx hopt hBD hf hy hc hs hcarry
    hBt hCv eC.2.2 hCB, hCB⟩

end Consensus.Goldilocks.SA

end

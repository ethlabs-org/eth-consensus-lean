module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CarryPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic prefix dominance with independently honest writer and reader

The writer pool is retained only at its write. Equivocation is charged at the
receiving cast; historical writers need not remain honest there.
-/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- Counted optimistic votes dominate each child towards the historical anchor. -/
theorem optimistic_isBest_of_carry_at (hrun : ACRun proposer tr H U) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hx : x ∈ H (tr.time i₀)) (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) (hy : y ∈ H (tr.time i))
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV) (hBt : B ∈ ℓ.frame.tree)
    {X C : Blk sp.n FGP}
    (hC : C ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
    (hp : C.parent = some X.root) (hCB : ℓ.frame.Anc C B) :
    IsBest sp (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s)
      {Q | Q ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) ∧
        Q.parent = some X.root ∧
        goldfishEligible sp ℓ.frame (tr.time i) (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s Q}
      C := by
  have hr := hrun.localRun
  have hry := hrun.upTo (hr.time_nonneg i)
  have hrx := hrun.upTo (hr.time_nonneg i₀)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hΦ := frameIn_of_callAt hry.localRun hy hc'.1
  obtain ⟨ℓx, A, hpt, hslx, hsel, rfl⟩ := hopt
  have hpt' := (upTo_optimisticPoint hr.time_mono).mpr ⟨le_rfl, hpt⟩
  have hΦxU := (frameIn_of_callAt hrx.localRun hx hpt'.1).2
  let SX := optimisticVoters sp A ℓx.frame s D
  have h34 : 3 * sp.n ≤ 4 * SX.ncard := by
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h := (deepest_mem hsel).1.2.1
    rwa [hslx] at h
  have hfreeze : sp.ts s + 3 * sp.Δ ≤ tr.time i := by
    have hsv := (castAt_spec hry.localRun hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at hsv
    have ht := (ts_le_iff_le_slot sp (hr.time_nonneg i) (s + 1 : Nat)).mpr
      (by rw [← hsv, hs])
    simp only [SAParams.ts] at ht ⊢
    push_cast at ht
    have hΔ := sp.toParams.hΔ
    nlinarith
  have hcarry' := carryAt_upTo (d := tr.time i) le_rfl hfreeze hcarry
  let V := mergedVoteView sp e.readPoint ℓ.frame (s + 1)
  have hcover : SX ⊆ supporters ℓ.frame V s B ∪ equivocators V.votes := by
    rintro w ⟨v, hv, rfl, R, hR, hRr, hDR⟩
    exact carried_cover hry hy hc' hs hBt hcarry' ⟨hv, R, hR, hRr, hDR⟩
      (optimisticPoint_pool_slot hrx.localRun hx hpt' hv)
      ⟨R, hΦxU hR, hRr, (frame_slot_le sp hrx.localRun hx hpt'.1 R hR).trans hslx.le,
        hBD.trans (Anc.mono hΦxU hDR)⟩
  have hE : (equivocators V.votes).ncard ≤ (H (tr.time i))ᶜ.ncard :=
    Set.ncard_le_ncard fun w hw hwH => honest_not_equivocator hry hy hc' hwH hw
  have hcompl : SX.ncard + SXᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hout : (voters V.votes \ SX).ncard ≤ SXᶜ.ncard :=
    Set.ncard_le_ncard fun _ h => h.2
  have h3 : (equivocators V.votes).ncard + (voters V.votes \ SX).ncard < SX.ncard := by
    omega
  exact isBest_of_cover hΦ.1 (merged_support_subset hry.localRun hy hc' (s + 1))
    (fun _ h => voteDomain_subset_tree h.1) hcover h3 hC hp hCB

/-- Explicit anchor order suffices for prefix reachability, without a prior-vote induction. -/
theorem optimistic_prefix_of_carry_at (hrun : ACRun proposer tr H U) {s : Nat}
    {x y : Fin sp.n} {i₀ i : Nat} {B D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hx : x ∈ H (tr.time i₀)) (hopt : OptimisticLockAt tr x i₀ s D CV) (hBD : Anc U B D)
    (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n) (hy : y ∈ H (tr.time i))
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : CarryAt tr U y i e s CV)
    (hB : B ∈ ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
    (haB : ℓ.frame.Anc (getAnchor sp e.readPoint ℓ.frame (tr.time i)) B) :
    ℓ.frame.Anc B (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s) := by
  have hry := hrun.upTo (hrun.localRun.time_nonneg i)
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hΦ := frameIn_of_callAt hry.localRun hy hc'.1
  have hT : ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)) ⊆ ℓ.frame.tree :=
    fun _ h => voteDomain_subset_tree h.1
  have hBt := hT hB
  have hdomA := voteDomain_anc hry.localRun hy hc'
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
  exact ⟨C, optimistic_isBest_of_carry_at hrun hx hopt hBD hf hy hc hs hcarry
    hBt hCv eC.2.2 hCB, hCB⟩

end Consensus.Goldilocks.SA.Growing

end

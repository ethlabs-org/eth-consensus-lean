module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core

public section

/-! # Goldilocks SA: the head walk below a finalized floor

Below a common finalized ancestor of all viable heads, the best-child step of the viable-domain
walk is forced by geometry alone (`isBest_of_viable_floor`), so the head extends that floor
(`finalized_floor_anc_getHead`). Split out of `AC/Steps/Core` so that a new floor/head helper
does not rebuild Core's cone. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- Below a common finalized ancestor of all viable heads, the viable-domain
path is forced by geometry alone. No supporter or score bound is needed. -/
theorem isBest_of_viable_floor {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    {F X C : Blk sp.n FGP}
    (hfloor : ∀ Q ∈ Φ.viableHeads, Φ.Anc F Q)
    (hXF : Φ.Anc X F) (hne : X ≠ F)
    (hC : C ∈ Φ.viableTree dom) (hp : C.parent = some X.root)
    (hCF : Φ.Anc C F) (V : View sp.n) (t : Time) (σ : Int) :
    IsBest sp (goldfishScore sp Φ V σ)
      {B | B ∈ Φ.viableTree dom ∧ B.parent = some X.root ∧
        goldfishEligible sp Φ t V σ B} C := by
  have hCt := hdom hC.1
  have hXt : X ∈ Φ.tree := (Anc.mem hXF hne).1
  have hel : goldfishEligible sp Φ t V σ C := by
    left
    rintro ⟨Q, hQ, hpar⟩
    have he : Q = X := hΦ.coherent.1 (hΦ.viableHeads_subset hQ) hXt
      (Option.some.inj (hpar.symm.trans hp))
    subst Q
    exact hne (Anc.antisymm hΦ.coherent hXF (hfloor X hQ))
  refine ⟨⟨hC, hp, hel⟩, fun D hD hDC => ?_⟩
  have hDt := hdom hD.1.1
  obtain ⟨Q, _, hQ, hDQ⟩ := hD.1.2.2
  have hcomp : Compatible Φ.tree D C := by
    rcases Anc.total hΦ.coherent hDQ (hfloor Q hQ) with hDF | hFD
    · exact Anc.total hΦ.coherent hDF hCF
    · exact Or.inr (hCF.trans hFD)
  have key : ∀ {B B' : Blk sp.n FGP}, B ∈ Φ.tree →
      B.parent = some X.root → B'.parent = some X.root → Φ.Anc B B' → B = B' := by
    intro B B' hB hpB hpB' hBB'
    by_contra hn
    rcases Relation.ReflTransGen.cases_tail hBB' with he | ⟨Y, hBY, e⟩
    · exact hn he.symm
    · have hYr : Y.root = X.root := Option.some.inj (e.2.2.symm.trans hpB')
      have hlt := hΦ.coherent.2 Y e.1 B hB
        (hpB.trans (congrArg some hYr.symm))
      have := (Anc.slot_le hΦ.coherent hBY).1
      omega
  exact (hDC (hcomp.elim (key hDt hD.2.1 hp)
    (fun h => (key hCt hp hD.2.1 h).symm))).elim

/-- If every viable head extends a common floor, a walk whose anchor is
below that floor reaches it regardless of scores. The witness is in the
actual walking domain, which may be frozen. -/
theorem finalized_floor_anc_getHead {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom)
    {F Y : Blk sp.n FGP} (hfloor : ∀ Q ∈ Φ.viableHeads, Φ.Anc F Q)
    (hY : Y ∈ dom) (hvY : Y ∈ Φ.viableHeads) (hFY : Φ.Anc F Y)
    (A : SAState sp.n) (t : Time) (V : View sp.n) (σ : Int)
    (hfa : Φ.Anc Φ.fcRoot (getAnchor sp A Φ t))
    (haF : Φ.Anc (getAnchor sp A Φ t) F) :
    Φ.Anc F (getHead sp A Φ t (Φ.viableTree dom) V σ) := by
  have hFt := mem_of_anc hFY (hdom hY)
  have hT : Φ.viableTree dom ⊆ Φ.tree := fun _ h => hdom h.1
  unfold getHead
  refine anc_ghost_of_best hΦ.coherent hT (hΦ.finite.subset hT) hFt _ haF
    (Set.ncard_le_ncard (fun _ h => hT h.1) hΦ.finite) ?_
  intro X haX hXF hne
  obtain rfl | ⟨C, e, hCF⟩ := Relation.ReflTransGen.cases_head_iff.1 hXF
  · exact (hne rfl).elim
  have hCv : C ∈ Φ.viableTree dom :=
    ⟨hdomA Y hY C (hCF.trans hFY),
      (hfa.trans haX).tail e, Y, hY, hvY, hCF.trans hFY⟩
  exact ⟨C, isBest_of_viable_floor hΦ hdom hfloor hXF hne hCv e.2.2 hCF V t σ, hCF⟩

end Consensus.Goldilocks.SA

end

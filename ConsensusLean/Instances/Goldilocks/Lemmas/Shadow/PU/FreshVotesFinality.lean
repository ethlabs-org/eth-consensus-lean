module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core

public section

/-! # Finalized observations below warm shadow vote heads -/

/-! ## The head walk below a finalized ancestor

Below a common finalized ancestor of all viable heads, the best-child step of the viable-domain
walk is forced by geometry alone (`isBest_of_viable_floor`), so the head extends that ancestor
(`finalized_floor_anc_getHead`). -/

section FinalizedHead

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams}

/-- Below a common finalized ancestor of all viable heads, the viable-domain
path is forced by geometry alone. No supporter or score bound is needed. -/
private theorem isBest_of_viable_floor {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    {F X C : Blk sp.n FGP}
    (hfloor : ∀ Q ∈ Φ.viableHeads, Φ.Anc F Q)
    (hXF : Φ.Anc X F) (hne : X ≠ F)
    (hC : C ∈ Φ.viableTree dom) (hp : C.parent = some X.root)
    (hCF : Φ.Anc C F) (V : View sp.n) (t : Time) (σ : Int) :
    IsBest sp (headScore sp Φ V σ)
      {B | B ∈ Φ.viableTree dom ∧ B.parent = some X.root ∧
        headEligible sp Φ t V σ B} C := by
  have hCt := hdom hC.1
  have hXt : X ∈ Φ.tree := (Anc.mem hXF hne).1
  have hel : headEligible sp Φ t V σ C := by
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
private theorem finalized_floor_anc_getHead {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom)
    {F Y : Blk sp.n FGP} (hfloor : ∀ Q ∈ Φ.viableHeads, Φ.Anc F Q)
    (hY : Y ∈ dom) (hvY : Y ∈ Φ.viableHeads) (hFY : Φ.Anc F Y)
    (A : ACState sp.n) (t : Time) (V : View sp.n) (σ : Int)
    (hfa : Φ.Anc Φ.F (getAnchor sp A Φ t))
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

end Consensus.Goldilocks.AC

end FinalizedHead

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- A primed viable witness puts a separate finalized observation below every viable head. -/
theorem finalized_anc_head_at_cast_at {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {z y : Fin sp.n} {c i : Nat}
    (hz : z ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    (hf : (H (max (tr.time c) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e)
    {Y : AC.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i))
      (tr.state z c).fg.F) :
    Anc (tr.HonestBlocksAt H) (tr.state z c).fg.F
      (AC.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hri := (hac.upTo (hrun.time_nonneg i)).localRun
  have hPhi := AC.frameIn_of_callAt hri hy hci
  have hfloor : ∀ Q ∈ ell.frame.viableHeads,
      ell.frame.Anc (tr.state z c).fg.F Q := by
    intro Q hQ
    have hwit := Consensus.Goldilocks.Shadow.PU.Growing.early_witness_viable
      hrun hframe hy hilo hihi hc.1 hQ
    have hQt : Q ∈ (tr.state y i).fg.tree := by
      have hv := hQ
      rw [Compose.Growing.frame_of_projAC_at hrun hy hc.1, Node.frame_eq,
        Store.toFrame_viableHeads] at hv
      exact hv.1
    have hFQ := hframe.finalized_below_descendant_at hrun hnc hz hy hy hf hclo hchi
      hQt hwit hQt .refl
    have hFt := AC.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2
      (hPhi.1.viableHeads_subset hQ) hFQ
      ((Anc.mono hPhi.2 (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))).trans haF)
    exact AC.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hFt hFQ
      (hPhi.1.viableHeads_subset hQ)
  have hFt := AC.mem_of_anc (hfloor Y hvY) (hPhi.1.viableHeads_subset hvY)
  have hat : AC.getAnchor sp e.readPoint ell.frame (tr.time i) ∈ ell.frame.tree := by
    by_cases he : ell.frame.F = AC.getAnchor sp e.readPoint ell.frame (tr.time i)
    · exact he ▸ hPhi.1.rooted.1
    · exact (Anc.mem (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)) he).2
  have hcast : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  exact Anc.mono hPhi.2 (AC.finalized_floor_anc_getHead hPhi.1 (fun _ h => h.1)
    (AC.voterBlockTree_ancU hri.toU hrun.vstart hy hcast) hfloor hY hvY (hfloor Y hvY)
    e.readPoint (tr.time i) _ _ (AC.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))
    (AC.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hat haF hFt))

/-- The primed frame root is F, so a separate root observation uses finalized ancestry. -/
theorem fcRoot_anc_head_at_cast_at {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {z y : Fin sp.n} {c i : Nat}
    (hz : z ∈ H (tr.time c)) (hy : y ∈ H (tr.time i))
    (hf : (H (max (tr.time c) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ellz ell : ACLabel (goldilocksNode sp)} (hcz : tr.projAC.CallAt z c ellz)
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y i ell e)
    {Y : AC.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i))
      ellz.frame.F) :
    Anc (tr.HonestBlocksAt H) ellz.frame.F
      (AC.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (AC.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hroot : ellz.frame.F = (tr.state z c).fg.F := by
    rw [Compose.Growing.frame_of_projAC_at hrun hz hcz,
      Node.frame_eq, Store.toFrame_F]
  rw [hroot] at haF ⊢
  exact finalized_anc_head_at_cast_at hframe hrun hnc hz hy hf hclo hchi hilo hihi hc
    hY hvY haF

end Consensus.Goldilocks.Healing.Growing.Shadow

end

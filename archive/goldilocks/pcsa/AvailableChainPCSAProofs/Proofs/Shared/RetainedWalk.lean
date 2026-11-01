module
public import AvailableChainPCSAProofs.Proofs.Shared.Walk

public section

/-! Retained PC-SA walks with separate view roots (pcsa34-r4.3 §§3.3, 5.3). -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- Retained walk premises use the actual PC view at each read. -/
structure PCSARetainedWalkGeometry (p : Params) (src dst : State p.n)
    (cs ct : Option (PC p.n)) (Ts Tt : List Block)
    (rs ss rt st : List (GridCO.Wire p.n .root)) (cut parent : Block) : Prop where
  source_cut : Block.Preceq (liveRoot p src cs) cut
  target_cut : Block.Preceq (liveRoot p dst ct) cut
  cut_parent : Block.Preceq cut parent
  target_prefix : BestAncestry (liveRoot p dst ct) cut Tt
    (GridCO.goldfishScore dst.base.blocks rt st) (eligible p dst rt st)
  persists : SuffixPersists cut parent Ts Tt
    (GridCO.goldfishScore src.base.blocks rs ss) (eligible p src rs ss) (eligible p dst rt st)
  reflects : SuffixReflects cut parent Ts Tt (eligible p src rs ss) (eligible p dst rt st)
  scores : SuffixScoresAgree cut parent Tt
    (GridCO.goldfishScore src.base.blocks rs ss) (GridCO.goldfishScore dst.base.blocks rt st)
    (eligible p dst rt st)

/-- A retained suffix transfers parent coverage between two PC-SA walks. -/
theorem pcsa_head_covers_of_retained_geometry
    (p : Params) (src dst : State p.n) (cs ct : Option (PC p.n)) (Ts Tt : List Block)
    (rs ss rt st : List (GridCO.Wire p.n .root)) (cut parent : Block)
    (hroot : ∀ A ∈ Tt, ∀ B ∈ Tt, A.root = B.root → A = B)
    (hsource : Block.Preceq parent (headInTree p src cs Ts rs ss))
    (h : PCSARetainedWalkGeometry p src dst cs ct Ts Tt rs ss rt st cut parent) :
    Block.Preceq parent (headInTree p dst ct Tt rt st) := by
  exact walk_covers_of_retained_transport (liveRoot p src cs) (liveRoot p dst ct)
    cut parent Ts Tt (GridCO.goldfishScore src.base.blocks rs ss)
    (GridCO.goldfishScore dst.base.blocks rt st) (eligible p src rs ss) (eligible p dst rt st)
    hroot hsource h.source_cut h.target_cut h.cut_parent h.target_prefix
    h.persists h.reflects h.scores

/-- Retained transport applies to the actual voter tree and vote merge. -/
theorem pcsa_headVote_covers_of_retained_geometry
    (p : Params) (src dst : State p.n) (s : Slot) (cut parent : Block)
    (hs : s ≠ 0)
    (hroot : ∀ A ∈ erasedList dst
        (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst s)),
      ∀ B ∈ erasedList dst
        (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst s)),
        A.root = B.root → A = B)
    (hsource : Block.Preceq parent
      (getHead p src (proposerPC p src) (proposerVotes src s) (proposerSupport src s)))
    (h : PCSARetainedWalkGeometry p src dst (proposerPC p src) (voterPC p dst s)
      (erasedList src (fullTree p src))
      (erasedList dst (KitFG.storeFrameView (FGSA.heightView p) dst.fg (voterBlocks p dst s)))
      (proposerVotes src s) (proposerSupport src s) (headVotes p dst s) (headSupport p dst s)
      cut parent) :
    Block.Preceq parent (headVote p dst s) := by
  unfold headVote
  rw [ite_eq_right hs]
  exact pcsa_head_covers_of_retained_geometry p src dst _ _ _ _ _ _ _ _ cut parent
    hroot hsource h

/-- A retained edge is best if it is the only child, or strictly beats all rivals. -/
theorem pcsa_retained_prefix_of_trunk_or_support
    (p : Params) (st : State p.n) (c : Option (PC p.n)) (tree : List Block)
    (raw sup : List (GridCO.Wire p.n .root)) (cut : Block)
    (hpath : ∀ X, Block.Preceq (liveRoot p st c) X → Block.Prec X cut →
      ∃ C, C.parent? = some X ∧ Block.Preceq C cut ∧ C ∈ tree ∧
        eligible p st raw sup C = true ∧
        ((∀ B ∈ tree, B.parent? = some X → B = C) ∨
          ∀ B ∈ tree, B.parent? = some X → eligible p st raw sup B = true →
            B ≠ C → GridCO.goldfishScore st.base.blocks raw sup B <
              GridCO.goldfishScore st.base.blocks raw sup C)) :
    BestAncestry (liveRoot p st c) cut tree
      (GridCO.goldfishScore st.base.blocks raw sup) (eligible p st raw sup) := by
  intro X hX hcut
  obtain ⟨C, hp, hc, hm, he, hr⟩ := hpath X hX hcut
  refine ⟨C, hp, hc, hm, he, ?_⟩
  intro B hB hpar hel
  rcases hr with hu | hd
  · obtain rfl := hu B hB hpar
    exact ⟨le_refl _, fun _ => le_refl _⟩
  · by_cases hBC : B = C
    · subst B
      exact ⟨le_refl _, fun _ => le_refl _⟩
    · have hlt := hd B hB hpar hel hBC
      exact ⟨Nat.le_of_lt hlt, fun heq => (Nat.ne_of_lt hlt heq).elim⟩

/-- A stored height witness keeps an ancestor in the filtered voter tree. -/
theorem pcsa_walk_domain_of_witness (p : Params) (st : State p.n)
    (V : Finset (SimplexFG.FGBlock (Fin p.n))) (C W : SimplexFG.FGBlock (Fin p.n))
    (hbase : ∀ B ∈ st.fg.TF, eraseFG B ∈ st.base.blocks)
    (hV : V ⊆ st.fg.TF) (hC : C ∈ V) (hW : W ∈ V)
    (hF : SimplexFG.FGBlock.Preceq st.fg.F C)
    (hZ : SimplexFG.FGBlock.Preceq (controls p st).Z C)
    (hCW : SimplexFG.FGBlock.Preceq C W)
    (hlo : (controls p st).lo ≤ (FGSA.heightView p W).h) :
    eraseFG C ∈ erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg V) := by
  apply List.mem_filter.mpr
  refine ⟨hbase C (hV hC), decide_eq_true ⟨C, ?_, rfl⟩⟩
  exact (KitFG.mem_filteredFromView (FGSA.heightView p) (controls p st) V C).2
    ⟨hC, hF, hZ, W, hW, hCW, hlo⟩

end AvailableChain.PCSA
end

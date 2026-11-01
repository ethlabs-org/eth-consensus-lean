module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAProofs.Proofs.Shared.RetainedWalk
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEvidence

public section

/-! Formation step 1 (pcsa34-r4.3b §5.3).
The first F4 clause gives a path from the base root to the proposer root.
The second clause bounds each voter root by the proposal parent.
The old release counterexample fails the first clause.
Retained input transport must use the actual voter tree and vote merge. -/

namespace AvailableChain.PCSA

/-- F4 bounds the live root using only the locks selected by the walk. -/
theorem pcsa_formation_root_below_parent (p : Params) (st : State p.n)
    (v : Option (PC p.n)) (P : Block)
    (hStart : Block.Preceq (walkBase p st v) P.parent)
    (hLocks : ∀ B, LiveLease st B → Block.Compatible B (walkBase p st v) →
      (walkBase p st v).depth < B.depth → Block.Preceq B P.parent) :
    Block.Preceq (liveRoot p st v) P.parent := by
  rcases pcsa_liveRoot_origin p st v with he | hm
  · exact he ▸ hStart
  · obtain ⟨row, hr, he, ht, _, hc, hd, _⟩ :=
      (pcsa_walkLocks_mem p st v _).mp hm
    exact hLocks _ ⟨row, hr, he, ht⟩ hc hd

/-- The first F4 clause permits the proposer walk to start at the base root.
The score and root order can include ties. -/
theorem pcsa_formation_base_walk_eq (p : Params) (st : State p.n)
    (pc : Option (PC p.n)) (raw support : List (GridCO.Wire p.n .root))
    (hroot : ∀ A ∈ erasedList st (fullTree p st),
      ∀ B ∈ erasedList st (fullTree p st), A.root = B.root → A = B)
    (hReach : Block.Preceq (liveRoot p st pc)
      (GridCO.ghost (walkBase p st pc) (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks raw support)
        (eligible p st raw support))) :
    GridCO.ghost (walkBase p st pc) (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks raw support)
      (eligible p st raw support) = getHead p st pc raw support := by
  exact Gen.Pure.walk_reanchor_of_best_ancestry _ _ _ _ _ hroot
    (pcsa_liveRoot_extends_base p st pc)
    (Gen.Pure.walk_best_ancestry_of_cover _ _ _ _ _ hReach)

/-- A voter root on the common base walk has the same continuation. -/
theorem pcsa_formation_walk_from_voter_root (p : Params) (src : State p.n)
    (pc : Option (PC p.n)) (raw support : List (GridCO.Wire p.n .root))
    (root parent : Block)
    (hroot : ∀ A ∈ erasedList src (fullTree p src),
      ∀ B ∈ erasedList src (fullTree p src), A.root = B.root → A = B)
    (hReach : Block.Preceq (liveRoot p src pc)
      (GridCO.ghost (walkBase p src pc) (erasedList src (fullTree p src))
        (GridCO.goldfishScore src.base.blocks raw support)
        (eligible p src raw support)))
    (hParent : getHead p src pc raw support = parent)
    (hBase : Block.Preceq (walkBase p src pc) root)
    (hBound : Block.Preceq root parent) :
    GridCO.ghost root (erasedList src (fullTree p src))
      (GridCO.goldfishScore src.base.blocks raw support)
      (eligible p src raw support) = parent := by
  have he := (pcsa_formation_base_walk_eq p src pc raw support hroot hReach).trans hParent
  have hc : Block.Preceq root
      (GridCO.ghost (walkBase p src pc) (erasedList src (fullTree p src))
        (GridCO.goldfishScore src.base.blocks raw support)
        (eligible p src raw support)) := he.symm ▸ hBound
  exact (Gen.Pure.walk_reanchor_of_best_ancestry _ _ _ _ _ hroot hBase
    (Gen.Pure.walk_best_ancestry_of_cover _ _ _ _ _ hc)).symm.trans he

/-- Corrected F4 and retained common inputs give voter coverage of the parent.
The retained inputs are read on the path from the common base root. -/
theorem pcsa_formation_parent_covers_of_inputs (p : Params) (src dst : State p.n)
    (pc vc : Option (PC p.n)) (Ts Tt : List Block)
    (rs ss rt st : List (GridCO.Wire p.n .root)) (H : Block)
    (hSrcTree : Ts = erasedList src (fullTree p src))
    (hSrcRoots : ∀ A ∈ Ts, ∀ B ∈ Ts, A.root = B.root → A = B)
    (hDstRoots : ∀ A ∈ Tt, ∀ B ∈ Tt, A.root = B.root → A = B)
    (hReach : Block.Preceq (liveRoot p src pc)
      (GridCO.ghost (walkBase p src pc) Ts
        (GridCO.goldfishScore src.base.blocks rs ss) (eligible p src rs ss)))
    (hParent : getHead p src pc rs ss = H)
    (hBase : walkBase p src pc = walkBase p dst vc)
    (hBound : Block.Preceq (liveRoot p dst vc) H)
    (hKeep : Gen.Pure.SuffixPersists (walkBase p src pc) H Ts Tt
      (GridCO.goldfishScore src.base.blocks rs ss) (eligible p src rs ss) (eligible p dst rt st))
    (hReflect : Gen.Pure.SuffixReflects (walkBase p src pc) H Ts Tt
      (eligible p src rs ss) (eligible p dst rt st))
    (hScores : Gen.Pure.SuffixScoresAgree (walkBase p src pc) H Tt
      (GridCO.goldfishScore src.base.blocks rs ss)
      (GridCO.goldfishScore dst.base.blocks rt st) (eligible p dst rt st)) :
    Block.Preceq H (headInTree p dst vc Tt rt st) := by
  have he : GridCO.ghost (walkBase p src pc) Ts
      (GridCO.goldfishScore src.base.blocks rs ss) (eligible p src rs ss) = H := by
    subst Ts
    exact (pcsa_formation_base_walk_eq p src pc rs ss hSrcRoots hReach).trans hParent
  have hb : Block.Preceq (walkBase p src pc) H := by
    rw [← he]
    exact @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _
  have hc := Gen.Pure.ghost_transfer_sfx (walkBase p src pc) H Ts Tt
    (GridCO.goldfishScore src.base.blocks rs ss) (GridCO.goldfishScore dst.base.blocks rt st)
    (eligible p src rs ss) (eligible p dst rt st) hb
    (he.symm ▸ Gen.Pure.block_preceq_refl H) hKeep hReflect hScores
  have hr : Block.Preceq (walkBase p src pc) (liveRoot p dst vc) := by
    rw [hBase]
    exact pcsa_liveRoot_extends_base p dst vc
  have hl := Gen.Pure.walk_reanchor_of_best_ancestry _ _ Tt
    (GridCO.goldfishScore dst.base.blocks rt st) (eligible p dst rt st) hDstRoots hr
    (Gen.Pure.walk_best_ancestry_of_cover _ _ _ _ _
      (Gen.Pure.block_preceq_trans hBound hc))
  change Block.Preceq H (GridCO.ghost (liveRoot p dst vc) Tt _ _)
  rw [← hl]
  exact hc

/-- The current-slot child is eligible even without majority support. -/
theorem pcsa_formation_current_eligible (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root)) (P : Block)
    (hSlot : P.slot = st.slot p) : eligible p st raw support P = true := by
  change (_ || _ || (P.slot == st.slot p)) = true
  rw [hSlot, BEq.rfl, Bool.or_true]

private theorem formation_child_depth (A C : Block) (h : C.parent? = some A) :
    C.depth = A.depth + 1 := by
  cases C with
  | genesis => cases h
  | node P s root body =>
    change some P = some A at h
    cases Option.some.inj h
    rfl

private theorem formation_parent_prefix (A C : Block) (h : C.parent? = some A) :
    Block.Preceq A C := by
  cases C with
  | genesis => cases h
  | node P s root body =>
    change some P = some A at h
    cases Option.some.inj h
    change (decide (_ = _) || Block.preceq _ _) = true
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_refl _))

private theorem formation_prec_iff (A B : Block) :
    Block.Prec A B ↔ A ≠ B ∧ Block.Preceq A B := by
  change ((!decide (A = B) && Block.preceq A B) = true ↔
    A ≠ B ∧ Block.preceq A B = true)
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]

/-- Parent coverage takes the unique current-slot child and stops there.
Equal-score root choices on the earlier path need no strict score premise. -/
theorem pcsa_formation_headVote_exact_of_parent (p : Params) (st : State p.n) (s : Slot)
    (P : Block) (hs : s ≠ 0)
    (hRoot : Block.Preceq (liveRoot p st (voterPC p st s)) P.parent)
    (hCover : Block.Preceq P.parent (headVote p st s))
    (hRoots : ∀ A ∈ erasedList st
        (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)),
      ∀ B ∈ erasedList st
        (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)),
        A.root = B.root → A = B)
    (hPar : P.parent? = some P.parent)
    (hP : P ∈ erasedList st
      (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
    (hSlot : P.slot = st.slot p)
    (hUnique : ∀ B ∈ erasedList st
        (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)),
      B.parent? = some P.parent →
      eligible p st (headVotes p st s) (headSupport p st s) B = true → B = P)
    (hStop : Gen.Pure.NoEligibleChild
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
      (eligible p st (headVotes p st s) (headSupport p st s)) P) :
    headVote p st s = P := by
  change (if s = 0 then Block.genesis else GridCO.ghost _ _ _ _) = P
  rw [ite_eq_right hs]
  change Block.Preceq P.parent (if s = 0 then Block.genesis else GridCO.ghost _ _ _ _) at hCover
  rw [ite_eq_right hs] at hCover
  rw [Gen.Pure.walk_reanchor_of_best_ancestry _ _ _ _ _ hRoots hRoot
    (Gen.Pure.walk_best_ancestry_of_cover _ _ _ _ _ hCover)]
  apply Gen.Pure.walk_exact_of_dominated_suffix _ _ _ _ _
    (formation_parent_prefix _ _ hPar) ?_ hStop
  intro C hPrec hCP
  obtain ⟨hne, hPC⟩ := (formation_prec_iff _ _).mp hPrec
  have hd : P.parent.depth < C.depth := by
    have hl := Gen.Pure.prefix_depth _ _ hPC
    by_contra hn
    exact hne (Gen.Pure.prefix_eq_of_depth _ _ hPC (Nat.le_of_not_gt hn))
  have hp := formation_child_depth _ _ hPar
  have he : C = P := Gen.Pure.prefix_eq_of_depth C P hCP (by omega)
  subst C
  refine ⟨hP, pcsa_formation_current_eligible p st _ _ P hSlot, ?_⟩
  intro B hB hpar hel hne
  exact (hne (hUnique B hB (hpar.trans hPar) hel)).elim

/-- The exact terminal path fixes the executable voter HEAD. -/
theorem pcsa_formation_headVote_exact (p : Params) (st : State p.n) (s : Slot)
    (P : Block) (hs : s ≠ 0)
    (hRoot : Block.Preceq (liveRoot p st (voterPC p st s)) P)
    (hPath : Gen.Pure.DominatedSuffix (liveRoot p st (voterPC p st s)) P
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
      (GridCO.goldfishScore st.base.blocks (headVotes p st s) (headSupport p st s))
      (eligible p st (headVotes p st s) (headSupport p st s)))
    (hStop : Gen.Pure.NoEligibleChild
      (erasedList st (KitFG.storeFrameView (FGSA.heightView p) st.fg (voterBlocks p st s)))
      (eligible p st (headVotes p st s) (headSupport p st s)) P) :
    headVote p st s = P := by
  change (if s = 0 then Block.genesis else _) = P
  rw [ite_eq_right hs]
  exact pcsa_headInTree_exact_path p st _ _ _ _ P hRoot hPath hStop

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

omit [Fintype V] in
/-- The named run premise makes each honest post-clock walk tree root-injective. -/
theorem pcsa_formation_read_root_injective (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (t : Time) (nd : Node p) (hx : x ∈ rho.honest)
    (hr : pcsa_postClock E rho x t = some nd)
    (tree : Finset (SimplexFG.FGBlock (Fin p.n))) :
    ∀ A ∈ erasedList nd.st tree, ∀ B ∈ erasedList nd.st tree,
      A.root = B.root → A = B := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hpre, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hpre
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hpre
  subst pre
  subst nd
  have hi := pcsa_clock_body_scope p _ _ t
    (pcsa_body_scope E rho k x hx)
  intro A hA B hB he
  rw [erasedList_def] at hA hB
  exact pcsa_scoped_root_eq E rho h.idealization A B
    (hi A (List.mem_filter.mp hA).1)
    (hi B (List.mem_filter.mp hB).1) he

/-- Corrected F4 reanchors the actual proposer walk at its common base root. -/
theorem pcsa_formation_proposer_base_walk (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (nd : Node p)
    (hr : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd) :
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    GridCO.ghost root (erasedList st (fullTree p st))
      (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
      (eligible p st (proposerVotes st s) (proposerSupport st s)) =
      getHead p st pc (proposerVotes st s) (proposerSupport st s) := by
  have hb : walkBase p nd.st (proposerPC p nd.st) =
      ((proposerPC p nd.st).map PC.target).getD (eraseFG (controls p nd.st).Z) := by
    cases hv : proposerPC p nd.st with
    | none => rfl
    | some C =>
      have hm : C ∈ nd.st.pcs.filter (frameActive p nd.st) := bestPC_mem _ C hv
      have ha := (List.mem_filter.mp hm).2
      change (if frameActive p nd.st C then C.target else _) = C.target
      rw [ite_eq_left ha]
  have hi := pcsa_formation_read_root_injective E rho h.base _ _ nd h.proposal.1 hr
    (fullTree p nd.st)
  have hReach := h.proposerRootReachable nd hr
  change Block.Preceq (liveRoot p nd.st (proposerPC p nd.st))
    (GridCO.ghost _ _ _ _) at hReach
  change GridCO.ghost _ _ _ _ = _
  rw [← hb] at hReach ⊢
  exact pcsa_formation_base_walk_eq p nd.st _ _ _ hi hReach

end AvailableChain.PCSA.Run
end

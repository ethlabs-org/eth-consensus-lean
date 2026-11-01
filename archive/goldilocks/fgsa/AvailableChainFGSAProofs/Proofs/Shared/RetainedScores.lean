module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalk
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalkStore
public import AvailableChainFGSAProofs.Proofs.Shared.ScoreRun

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:856–886 (design citation 728–758); spec 1350–1360.
Class (iii). DC: INTENTIONAL; the stored-parent band needs the same
immutable parent in both stores and equal floors at these two reads. -/
theorem fgsa_eligible_eq_of_same_floor
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n .root)) (C : Block) (P : FGBlock (Fin p.n))
    (hsrc : P ∈ src.fg.TF) (hdst : P ∈ dst.fg.TF) (hP : eraseFG P = C.parent)
    (hlo : (controls p src).lo = (controls p dst).lo)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C :=
  fgsa_eligible_eq_of_band_score p src dst raw sup raw' sup' C
    (fgsa_band_eq_of_same_floor p src dst C P hsrc hdst hP hlo) hcount hscore hslot

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.1:1558–1565, L2-W:2068–2088, L4-R:2250–2265,
H.17:2976–2985 (design 1422–1425,1937–1939,2112–2116,2836–2845);
spec 1350–1360. Class (iii). DC: INTENTIONAL; parent height witnesses
exclude the band arm separately at each read, without equal floors. -/
theorem fgsa_eligible_eq_of_parent_height
    (p : Params) (src dst : State p.n)
    (raw sup raw' sup' : List (GridCO.Wire p.n .root)) (C : Block)
    (hsrc : ∀ P ∈ src.fg.TF, eraseFG P = C.parent →
      (controls p src).lo ≤ (heightView p P).h)
    (hdst : ∀ P ∈ dst.fg.TF, eraseFG P = C.parent →
      (controls p dst).lo ≤ (heightView p P).h)
    (hcount : GridCO.voterCount raw = GridCO.voterCount raw')
    (hscore : GridCO.goldfishScore src.base.blocks raw sup C =
      GridCO.goldfishScore dst.base.blocks raw' sup' C)
    (hslot : src.slot p = dst.slot p) :
    eligible p src raw sup C = eligible p dst raw' sup' C := by
  have hs : ¬ ∃ P ∈ src.fg.TF, eraseFG P = C.parent ∧
      (heightView p P).h < (controls p src).lo := by
    rintro ⟨P, hm, he, hh⟩
    exact Nat.not_lt_of_ge (hsrc P hm he) hh
  have hd : ¬ ∃ P ∈ dst.fg.TF, eraseFG P = C.parent ∧
      (heightView p P).h < (controls p dst).lo := by
    rintro ⟨P, hm, he, hh⟩
    exact Nat.not_lt_of_ge (hdst P hm he) hh
  unfold eligible
  simp only [hs, hd, hcount, hscore, hslot]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:886–914, H.17:2987–3009; spec 1290–1297,1520–1523.
Class (iii). DC: INTENTIONAL; each common candidate supplies its own two
F bounds. Membership can come from fgsa_walk_domain_of_witness; the height
witness stays inside its duty view. No bound on a paper pivot is used. -/
theorem fgsa_score_geometry_of_domains
    (p : Params) (src dst : State p.n)
    (Vs Vt : Finset (FGBlock (Fin p.n))) (C : Block)
    (hsrc : C ∈ erasedList src (KitFG.storeFrameView (heightView p) src.fg Vs))
    (hdst : C ∈ erasedList dst (KitFG.storeFrameView (heightView p) dst.fg Vt)) :
    ScoreRunGeometry src dst C := by
  have floor (st : State p.n) (V : Finset (FGBlock (Fin p.n)))
      (hm : C ∈ erasedList st (KitFG.storeFrameView (heightView p) st.fg V)) :
      Block.Preceq (eraseFG st.fg.F) C := by
    obtain ⟨B, hB, he⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
    rw [← he]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p)
        (KitFG.storeControlsView (heightView p) st.fg) V B).mp hB).2.1
  exact ⟨floor src Vs hsrc, floor dst Vt hdst⟩

/-- The canonical source and voter domains supply their separate F bounds. -/
theorem fgsa_score_geometry_of_tree_domains
    (p : Params) (src dst : State p.n)
    (Vs Vt : Finset (FGBlock (Fin p.n))) (C : Block)
    (hsrc : C ∈ erasedList src (KitFG.treeStoreFrameView (heightView p) src.fg Vs))
    (hdst : C ∈ erasedList dst (KitFG.treeStoreFrameView (heightView p) dst.fg Vt)) :
    ScoreRunGeometry src dst C := by
  have floor (st : State p.n) (V : Finset (FGBlock (Fin p.n)))
      (hm : C ∈ erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg V)) :
      Block.Preceq (eraseFG st.fg.F) C := by
    obtain ⟨B, hB, he⟩ := of_decide_eq_true (List.mem_filter.mp hm).2
    rw [← he]
    exact eraseFG_preceq
      ((KitFG.mem_filteredFromView (heightView p)
        (KitFG.treeStoreControlsView (heightView p) st.fg) V B).mp hB).2.1
  exact ⟨floor src Vs hsrc, floor dst Vt hdst⟩

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:293–331; 21 H.5:886–914, H.17:2987–3009;
spec 1530–1538,1554–1577. Class (iii). DC: INTENTIONAL;
ProposalWalkTransportCore.lean:185 compares common candidates. The parent
instance supplies the count even for an empty candidate set. Each candidate
uses G25 at itself. Signed proposal metadata passes through unchanged. -/
theorem fgsa_score_eq_on_candidates_on_run
    (E) (rho)
    (hE : V2.D.ExecutionValid (V := V) (P := fgsa p c) E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks)
    (Candidates : Block → Prop)
    (hA : ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) N.erase.parent)
    (hCandidates : ∀ C, Candidates C → ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) C)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
    GridCO.voterCount (proposerVotes src s) = GridCO.voterCount (headVotes p dst s) ∧
      ∀ C, Candidates C → RetainedWalk.ss src s C = RetainedWalk.ts p dst s C := by
  have hFN := block_preceq_trans hA.target_floor (fgsa_parent_preceq N.erase)
  refine ⟨(fgsa_score_eq_on_run (hroots := hroots) E rho hE hN hDelta s hSync hx hy hip hih hseat
    N hem hadm hFN N.erase.parent hA).2.2.1, ?_⟩
  intro C hC
  exact (fgsa_score_eq_on_run (hroots := hroots) E rho hE hN hDelta s hSync hx hy hip hih hseat
    N hem hadm hFN C (hCandidates C hC)).2.2.2 C (block_preceq_refl C)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.5:886–914, H.17:2987–3009; spec 1330–1360.
Class (iii). DC: INTENTIONAL; selected retained children and reflected
eligible rivals use candidate-local G25. The inclusive candidate set also
serves old-child endpoint reflection. This supplies exactly the scores field
of RetainedWalkRunGeometry, with no assertion about a removed trunk. -/
theorem fgsa_retained_scores_of_candidates
    (p : Params) (src dst : State p.n) (s : Slot) (Kc A : Block)
    (hscore : ∀ C, (∃ X, Block.Preceq Kc X ∧ Block.Preceq X A ∧
      C ∈ RetainedWalk.T p dst s ∧ C.parent? = some X ∧
      RetainedWalk.et p dst s C = true ∧ (Block.Prec X A ∨ C.slot < s)) →
      RetainedWalk.ss src s C = RetainedWalk.ts p dst s C) :
    SuffixScoresAgree Kc A (RetainedWalk.T p dst s)
      (RetainedWalk.ss src s) (RetainedWalk.ts p dst s) (RetainedWalk.et p dst s) := by
  intro X C hK hX hm hp he
  exact (hscore C ⟨X, hK, (Bool.and_eq_true_iff.mp hX).2, hm, hp, he, Or.inl hX⟩).symm

/-- Receiver services for each candidate with valid endpoint floors.
Each retained object keeps its own ready anchor and history premise. -/
structure RetainedServiceScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ip ih : Nat) (x y : V) (s : Slot) (N : NamedProposal p.n) : Prop where
  proposal : Nonempty (ReceiverService E rho
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p)
    (SA.proposalTime p.toParams s) (SA.voteTime p.toParams s) y)
  scores : ∀ D, ScoreRunGeometry
    (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
    (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) D →
    ScoreServiceScope E rho ip ih x y s D

theorem fgsa_score_eq_on_candidates_on_run_on
    (E) (rho)
    (hE : V2.D.ExecutionValid (V := V) (P := fgsa p c) E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks)
    (Candidates : Block → Prop)
    (hA : ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) N.erase.parent)
    (hCandidates : ∀ C, Candidates C → ScoreRunGeometry
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) C)
    (hScope : RetainedServiceScope E rho ip ih x y s N)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
    GridCO.voterCount (proposerVotes src s) = GridCO.voterCount (headVotes p dst s) ∧
      ∀ C, Candidates C → RetainedWalk.ss src s C = RetainedWalk.ts p dst s C := by
  have hFN := block_preceq_trans hA.target_floor (fgsa_parent_preceq N.erase)
  refine ⟨(fgsa_score_eq_on_run_on (hroots := hroots) E rho hE s hx hy hip hih hseat
    N hem hadm hFN N.erase.parent hA (hScope.scores _ hA)).2.2.1, ?_⟩
  intro C hC
  exact (fgsa_score_eq_on_run_on (hroots := hroots) E rho hE s hx hy hip hih hseat
    N hem hadm hFN C (hCandidates C hC) (hScope.scores _ (hCandidates C hC))).2.2.2 C
      (block_preceq_refl C)

end AvailableChain.FGSA.Run
end

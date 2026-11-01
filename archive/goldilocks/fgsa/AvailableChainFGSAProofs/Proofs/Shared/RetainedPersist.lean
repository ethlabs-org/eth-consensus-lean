module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedReflect
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure
open RetainedWalk

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:942–953, H.17:2971–2984 (design 798–809,2832–2845); spec 1286–1293.
Class (iii). DC: INTENTIONAL; bridge the two FJ domain interfaces through
heightView_bridge, without reducing the active height view. -/
theorem fgsa_domainR_eq_treeStoreFrameView (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n))) :
    domainR p st Vw = KitFG.treeStoreFrameView (heightView p) st.fg Vw := by
  rw [domainR_def, frameR_def, KitFG.treeStoreFrameView_def]
  rfl

/-- Top retention permits comparison with the old store frame. -/
theorem fgsa_domainR_eq_storeFrameView_of_top_retained (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n)))
    (hTop : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    domainR p st Vw = KitFG.storeFrameView (heightView p) st.fg Vw := by
  rw [fgsa_domainR_eq_treeStoreFrameView,
    KitFG.treeStoreFrameView_eq (heightView p) st.fg Vw hTop]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:942–953, H.17:2971–2984 (design 798–809,2832–2845); spec 1286–1293.
Class (iii). DC: INTENTIONAL; S3 with a witness inside the target view.
The base premise is supplied by CStoreInv.baseTree. -/
theorem fgsa_walk_domain_of_witness_tree_view (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hbase : ∀ B ∈ st.fg.TF, eraseFG B ∈ st.base.blocks)
    (hV : Vw ⊆ st.fg.TF) (hC : C ∈ Vw) (hW : W ∈ Vw)
    (hF : FGBlock.Preceq st.fg.F C)
    (hZ : FGBlock.Preceq (controls p st).Z C)
    (hCW : FGBlock.Preceq C W) (hlo : (controls p st).lo ≤ (heightView p W).h) :
    eraseFG C ∈ erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg Vw) := by
  exact List.mem_filter.mpr ⟨hbase C (hV hC), decide_eq_true ⟨C,
    (KitFG.mem_filteredFromView (heightView p) (controls p st) Vw C).mpr
      ⟨hC, hF, hZ, W, hW, hCW, hlo⟩, rfl⟩⟩

/-- Top retention preserves the old-frame conclusion of the path witness helper. -/
theorem fgsa_walk_domain_of_witness_view_of_top_retained (p : Params) (st : State p.n)
    (Vw : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hTop : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W)
    (hbase : ∀ B ∈ st.fg.TF, eraseFG B ∈ st.base.blocks)
    (hV : Vw ⊆ st.fg.TF) (hC : C ∈ Vw) (hW : W ∈ Vw)
    (hF : FGBlock.Preceq st.fg.F C)
    (hZ : FGBlock.Preceq (controls p st).Z C)
    (hCW : FGBlock.Preceq C W) (hlo : (controls p st).lo ≤ (heightView p W).h) :
    eraseFG C ∈ erasedList st (KitFG.storeFrameView (heightView p) st.fg Vw) := by
  rw [← KitFG.treeStoreFrameView_eq (heightView p) st.fg Vw hTop]
  exact fgsa_walk_domain_of_witness_tree_view p st Vw C W hbase hV hC hW hF hZ hCW hlo

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:927–953, H.17:2986–3006 (design 783–809,2847–2867); spec 1286–1293, 1520–1523.
Class (iii). DC: INTENTIONAL; named hA supplier, review F3 route (ii).
Source F/Z and target F/liveRoot extend through the retained cut to A. -/
theorem fgsa_score_geometry_of_retained_cuts (p : Params) (src dst : State p.n)
    (hs : CStoreInv p src) (ht : CStoreInv p dst) (s : Slot)
    (D : FGBlock (Fin p.n)) (b Kc : Block)
    (h : RetainedReadPremises p src dst s D b Kc) : ScoreRunGeometry src dst b.parent :=
  ⟨block_preceq_trans (eraseFG_preceq (fgsa_F_preceq_Z p src hs))
      (block_preceq_trans h.source_cut h.cut_parent),
    block_preceq_trans (F_preceq_liveRoot p dst ht)
      (block_preceq_trans h.target_cut h.cut_parent)⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:935–953, HG.1:1518–1532, HG.8:2249–2259, HG.8:2079–2121, H.17:3008–3011
(design 791–809,1385–1399,2107–2117,1937–1979,2869–2872);
spec 1286–1293. Class (iii). DC: INTENTIONAL;
D2-1 permits source A or admitted target b as the height witness. Receipt
and closure put the path and b in the same duty view; S3 then filters it. -/
theorem fgsa_retained_path_mem (p : Params) (src dst : State p.n)
    (hbase : ∀ C, C ∈ dst.base.blocks ↔ ∃ B ∈ dst.fg.TF, eraseFG B = C)
    (hclosed : ∀ B ∈ dst.fg.TF, B.parent ∈ dst.fg.TF)
    (hfloor : Block.Preceq (eraseFG dst.fg.F) (ay p dst)) (s : Slot) (b C : Block)
    (hadm : b ∈ dst.base.blocks) (hslot : b.slot = s)
    (hstart : Block.Preceq (ay p dst) C) (hCb : Block.Preceq C b)
    (hw : ∃ W : FGBlock (Fin p.n),
      ((W ∈ src.fg.TF ∧ eraseFG W = b.parent) ∨ (W ∈ dst.fg.TF ∧ eraseFG W = b)) ∧
      (controls p dst).lo ≤ (heightView p W).h) : C ∈ T p dst s := by
  obtain ⟨B, hB, heB⟩ := (hbase b).mp hadm
  obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem hclosed hB (heB ▸ hCb)
  have hAB : FGBlock.Preceq A B := eraseFG_preceq_iff.mp (heA ▸ heB ▸ hCb)
  have hbslot : B.slot = s := by rw [← eraseFG_slot, heB, hslot]
  have hFA : FGBlock.Preceq dst.fg.F A :=
    eraseFG_preceq_iff.mp (heA ▸ block_preceq_trans hfloor hstart)
  have inView (Q : FGBlock (Fin p.n)) (hQ : Q ∈ dst.fg.TF)
      (hQB : FGBlock.Preceq Q B) (hFQ : FGBlock.Preceq dst.fg.F Q) :
      Q ∈ voterBlocks p dst s :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hQ, hFQ⟩, Bool.or_eq_true_iff.mpr
      (Or.inr (decide_eq_true ⟨B, Finset.mem_filter.mpr ⟨hB, KitFG.preceq_trans hFA hAB⟩,
        hbslot, hQB⟩))⟩
  have hlo : (controls p dst).lo ≤ (heightView p B).h := by
    obtain ⟨W, hw, hlo⟩ := hw
    have hWB : FGBlock.Preceq W B := by
      rcases hw with ⟨-, he⟩ | ⟨-, he⟩
      · exact eraseFG_preceq_iff.mp (he ▸ heB ▸ fgsa_parent_preceq b)
      · exact eraseFG_preceq_iff.mp (he ▸ heB ▸ block_preceq_refl b)
    apply hlo.trans
    rw [(KitFG.heightBridge_fields p.E p.cfg (heightView p) (heightView_bridge p) W).1,
      (KitFG.heightBridge_fields p.E p.cfg (heightView p) (heightView_bridge p) B).1]
    exact KitFG.h_mono p.E p.cfg hWB
  rw [← heA]
  exact fgsa_walk_domain_of_witness_tree_view p dst (voterBlocks p dst s) A B
    (fun Q hm => (hbase _).mpr ⟨Q, hm, rfl⟩)
    (fun _ hm => Next.tree_subset_TF p dst (Finset.mem_filter.mp hm).1)
    (inView A hA hAB hFA)
    (inView B hB (KitFG.preceq_refl _) (KitFG.preceq_trans hFA hAB)) hFA
    (eraseFG_preceq_iff.mp (heA ▸ block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) hstart)) hAB hlo

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:935–953, H.17:3008–3011 (design 791–809,2869–2872); spec 1286–1293.
Class (iii). DC: INTENTIONAL; exact E.proposal_mem after receipt, with
source A or admitted b as the witness. No source storage of new b is needed. -/
theorem fgsa_retained_proposal_mem (p : Params) (src dst : State p.n)
    (hbase : ∀ C, C ∈ dst.base.blocks ↔ ∃ B ∈ dst.fg.TF, eraseFG B = C)
    (hclosed : ∀ B ∈ dst.fg.TF, B.parent ∈ dst.fg.TF)
    (hfloor : Block.Preceq (eraseFG dst.fg.F) (ay p dst)) (s : Slot) (b : Block)
    (hadm : b ∈ dst.base.blocks) (hslot : b.slot = s)
    (hparent : Block.Preceq (ay p dst) b.parent)
    (hw : ∃ W : FGBlock (Fin p.n),
      ((W ∈ src.fg.TF ∧ eraseFG W = b.parent) ∨ (W ∈ dst.fg.TF ∧ eraseFG W = b)) ∧
      (controls p dst).lo ≤ (heightView p W).h) : b ∈ T p dst s :=
  fgsa_retained_path_mem p src dst hbase hclosed hfloor s b b hadm hslot
    (block_preceq_trans hparent (fgsa_parent_preceq b)) (block_preceq_refl _) hw

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:942–958, H.17:2986–3006 (design 798–814,2847–2867); spec 1330–1360.
Class (iii). DC: INTENTIONAL; store composition of S3 and full eligibility.
Only selected children inside the retained interval are compared. -/
theorem fgsa_retained_persists_of_path
    (p : Params) (src dst : State p.n) (s : Slot) (Kc A : Block)
    (hpath : ∀ X C, Block.Preceq Kc X → Block.Prec X A →
      C.parent? = some X → Block.Preceq C A → C ∈ T p dst s)
    (hel : ∀ X C, Block.Preceq Kc X → Block.Prec X A →
      C.parent? = some X → C ∈ S p src → C ∈ T p dst s →
      es p src s C = et p dst s C) :
    SuffixPersists Kc A (S p src) (T p dst s) (ss src s) (es p src s) (et p dst s) := by
  intro X C hK hX hstep hCA
  have hchild : C ∈ S p src ∧ C.parent? = some X ∧ es p src s C = true := by
    let children := (S p src).filter (fun B => B.parent? == some X && es p src s B)
    let select : Option Block → Block → Option Block := fun best B =>
      match best with
      | none => some B
      | some old =>
        if ss src s old < ss src s B || (ss src s old == ss src s B && old.root < B.root)
        then some B else best
    have hm : ∀ B, children.foldl select none = some B → B ∈ children := by
      apply List.foldlRecOn (motive := fun best => ∀ B, best = some B → B ∈ children)
      · intro B hb
        cases hb
      · intro best ih B hB C he
        cases best with
        | none => exact (Option.some.inj he) ▸ hB
        | some old =>
          dsimp only [select] at he
          split at he
          · exact (Option.some.inj he) ▸ hB
          · exact ih C he
    change (match children.foldl select none with
      | none => none
      | some B => if children.any (fun D => D != B && ss src s D == ss src s B && D.root == B.root)
          then none else some B) = some C at hstep
    cases hb : children.foldl select none with
    | none => rw [hb] at hstep; cases hstep
    | some B =>
      rw [hb] at hstep
      change (if children.any (fun D => D != B && ss src s D == ss src s B && D.root == B.root)
        then none else some B) = some C at hstep
      split at hstep
      · cases hstep
      · cases Option.some.inj hstep
        obtain ⟨ht, he⟩ := List.mem_filter.mp (hm C hb)
        obtain ⟨hp, hel⟩ := Bool.and_eq_true_iff.mp he
        exact ⟨ht, by simpa using hp, hel⟩
  obtain ⟨hm, hp, he⟩ := hchild
  have ht := hpath X C hK hX hp hCA
  exact ⟨ht, (hel X C hK hX hp hm ht).symm.trans he⟩

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:935–953, HG.1:1518–1532, HG.8:2249–2259, HG.8:2079–2121,
H.17:3008–3011
(design 791–809,1385–1399,2107–2117,1937–1979,2869–2872);
spec 1555–1581. Class (iii). DC: INTENTIONAL; S8
composes the existing R6-aware trigger-to-tick receipt and S3. The chain
uses fgsa_trigger_rowsValid and invalidForParent exclusion inside receipt. -/
theorem fgsa_retained_proposal_mem_on_run_epoch
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc)
    (hService : ReceiverService E rho
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p)
      (SA.proposalTime p.toParams s) (SA.voteTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    N.erase ∈ (rho.stateBefore E ih y).st.base.blocks ∧
      N.erase ∈ T p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hslot := (fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2).1
  obtain ⟨Y, hY, he⟩ := hService.proposal hE.toScheduleWellFormed hy hroots
  have hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ ih := by
    by_contra hn
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hE.toScheduleWellFormed hih _).mp
      (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ hlt).elim
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed] at hY
  have hY' := (fgsa_store_durable p c E rho hcut y).1 hY
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks :=
    ((cstoreInv_stateBefore E rho ih y).baseTree _).mpr ⟨Y, hY', he⟩
  refine ⟨hadm', fgsa_retained_proposal_mem p src dst ht.baseTree ht.fg.closed
    (F_preceq_liveRoot p dst ht) s N.erase ?_ hslot h.target_parent h.parent_height⟩
  simpa only [dst, clock_base_blocks] using hadm'

theorem fgsa_retained_proposal_mem_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D N.erase Kc)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    N.erase ∈ (rho.stateBefore E ih y).st.base.blocks ∧
      N.erase ∈ T p (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s)
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ s _).mp hm
  have hslot := (fgsa_scoreRun_proposal_pools p _ s _ N hp.2.2.2.2).1
  obtain ⟨dl, cut, hD, -, hlt, hb, -, hc, -⟩ := hSync
  have hd : dl (SA.proposalTime p.toParams s) ≤ SA.voteTime p.toParams s := by
    have hb := hb (SA.proposalTime p.toParams s)
    rw [max_eq_left (by linarith [p.deltaPos]), hDelta] at hb
    exact hb.trans (by unfold SA.proposalTime SA.voteTime; ring_nf; rfl)
  have hF : Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) N.erase := by
    have hf := block_preceq_trans (F_preceq_liveRoot p dst ht)
      (block_preceq_trans h.target_parent (fgsa_parent_preceq N.erase))
    change Block.Preceq (eraseFG (rho.stateBefore E ih y).st.fg.F) N.erase
    simpa only [dst, clock_fg] using hf
  have hadm := fgsa_gateReceipt_block_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD
    (SA.proposalTime p.toParams s)
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) N.erase rfl
    (Or.inl ⟨x, hx, ip, hip, hem⟩) (hlt _) (hd.trans hc) hy hih hd hF
  have hadm' : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks := hadm
  refine ⟨hadm', fgsa_retained_proposal_mem p src dst ht.baseTree ht.fg.closed
    (F_preceq_liveRoot p dst ht) s N.erase ?_ hslot h.target_parent h.parent_height⟩
  simpa only [dst, clock_base_blocks] using hadm'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:942–953, H.17:2971–3006 (design 798–809,2832–2867); spec
1286–1293,1330–1360.
Class (iii). DC: INTENTIONAL; exact W.persists. Target receipt and its
internal path witness give membership. Candidate-local G25 and the band
adapter then preserve all three eligibility arms. -/
theorem fgsa_retained_path_persists_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D N.erase Kc)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    SuffixPersists Kc N.erase.parent (S p src) (T p dst (s + 1))
      (ss src (s + 1)) (es p src (s + 1)) (et p dst (s + 1)) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hm
  have hbslot := (fgsa_scoreRun_proposal_pools p _ (s + 1) _ N hp.2.2.2.2).1
  have scores := fgsa_score_eq_on_candidates_on_run (hroots := hroots) E rho hE hN hDelta (s + 1)
    hScoreSync hx hy hip hih hseat N hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1))
    (fgsa_score_geometry_of_retained_cuts p src dst hs ht (s + 1) D N.erase Kc h)
    (fun C hm => fgsa_score_geometry_of_tree_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2)
  apply fgsa_retained_persists_of_path
  · intro X C hK _ hp hCA
    have hXC : Block.Preceq X C := by
      cases C with
      | genesis => cases hp
      | node P t root r =>
        have heq : P = X := Option.some.inj hp
        subst P
        exact fgsa_parent_preceq (.node X t root r)
    exact fgsa_retained_path_mem p src dst ht.baseTree ht.fg.closed
      (F_preceq_liveRoot p dst ht) (s + 1) N.erase C
      (by simpa only [dst, clock_base_blocks] using hadm) hbslot
      (block_preceq_trans h.target_cut (block_preceq_trans hK hXC))
      (block_preceq_trans hCA (fgsa_parent_preceq N.erase)) h.parent_height
  · intro X C hK hX hp hm htC
    have hold := (fgsa_stored_block_slots E rho hE.toScheduleWellFormed hip
      (Nat.succ_pos s)).2.1 C (List.mem_filter.mp hm).1
    exact fgsa_eligible_eq_of_retainedBand_score p src dst
      (proposerVotes src (s + 1)) (proposerSupport src (s + 1))
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) C
      (h.band_agrees X C hK (Bool.and_eq_true_iff.mp hX).2 hm htC hp hold)
      scores.1 (scores.2 C ⟨hm, htC⟩)
      ((fgsa_proposal_slot (c := c) _ (s + 1)).trans
        (fgsa_vote_slot (c := c) _ (s + 1)).symm)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.6:942–958, H.17:2986–3011 (design 798–814,2847–2872); spec
1555–1581,1330–1360.
Class (iii). DC: INTENTIONAL; job-5 strict-path assembly. The landed Gen
API takes atomic fields, so this constructs RetainedWalkRunGeometry and
returns the endpoint fields already supplied by jobs 5a/5b for job 6. -/
theorem fgsa_retainedWalk_geometry_on_run
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    (hWalkSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    (hScoreSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.voteTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D N.erase Kc)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    RetainedWalkRunGeometry p src dst (s + 1) D N.erase Kc ∧
      N.erase ∈ T p dst (s + 1) ∧
      (∀ C ∈ T p dst (s + 1), C.parent? = some N.erase.parent → C.slot < s + 1 →
        et p dst (s + 1) C = true → C ∈ S p src ∧ es p src (s + 1) C = true) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  obtain ⟨hadm, hmem⟩ := fgsa_retained_proposal_mem_on_run (hroots := hroots)
    E rho hE hN hDelta (s + 1)
    hScoreSync hx hy hip hih N hem D Kc h
  have hr := fgsa_retained_old_child_reflects_on_run (hroots := hroots) E rho hE hN hDelta s
    hWalkSync hScoreSync hx hy hip hih hseat N hem hadm D Kc h
  have hA := fgsa_score_geometry_of_retained_cuts p src dst hs ht (s + 1) D N.erase Kc h
  have scores := fgsa_score_eq_on_candidates_on_run (hroots := hroots) E rho hE hN hDelta (s + 1)
    hScoreSync hx hy hip hih hseat N hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1)) hA
    (fun C hm => fgsa_score_geometry_of_tree_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2)
  refine ⟨{
    pivot_parent := h.pivot_parent
    ordinary_start := fgsa_Z_preceq_liveRoot p src
    ordinary_prefix := h.ordinary_prefix
    target_parent := h.target_parent
    source_cut := h.source_cut
    target_cut := h.target_cut
    cut_parent := h.cut_parent
    target_prefix := h.target_prefix
    persists := fgsa_retained_path_persists_on_run (hroots := hroots) E rho hE hN hDelta s
      hScoreSync
      hx hy hip hih hseat N hem hadm D Kc h
    reflects := hr.1
    scores := ?_ }, hmem, hr.2⟩
  apply fgsa_retained_scores_of_candidates
  intro C hC
  obtain ⟨X, hK, hX, hm, hp, he, hcase⟩ := hC
  have hsrc : C ∈ S p src := by
    rcases hcase with hstrict | hold
    · exact (hr.1 X C hK hstrict hm hp he).1
    · exact fgsa_walkRun_reflected_old_child (hroots := hroots) E rho hE hN hDelta s hWalkSync
        hx hy hip hih hseat N hem Kc X C h.source_cut hK hX hp hold hm
        (h.reflected_witness X C hK hX hm hp hold he)
  exact scores.2 C ⟨hsrc, hm⟩

theorem fgsa_retained_path_persists_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hadm : N.erase ∈ (rho.stateBefore E ih y).st.base.blocks)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D N.erase Kc)
    (hScope : RetainedServiceScope E rho ip ih x y (s + 1) N)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    SuffixPersists Kc N.erase.parent (S p src) (T p dst (s + 1))
      (ss src (s + 1)) (es p src (s + 1)) (et p dst (s + 1)) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  have hm := hem
  rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
  have hp := (fgsa_emits_proposal E rho _ x _ (s + 1) _).mp hm
  have hbslot := (fgsa_scoreRun_proposal_pools p _ (s + 1) _ N hp.2.2.2.2).1
  have scores := fgsa_score_eq_on_candidates_on_run_on (hroots := hroots) E rho hE (s + 1) hx
    hy hip hih hseat N hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1))
    (fgsa_score_geometry_of_retained_cuts p src dst hs ht (s + 1) D N.erase Kc h)
    (fun C hm => fgsa_score_geometry_of_tree_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2) hScope
  apply fgsa_retained_persists_of_path
  · intro X C hK _ hp hCA
    have hXC : Block.Preceq X C := by
      cases C with
      | genesis => cases hp
      | node P t root r =>
        have heq : P = X := Option.some.inj hp
        subst P
        exact fgsa_parent_preceq (.node X t root r)
    exact fgsa_retained_path_mem p src dst ht.baseTree ht.fg.closed
      (F_preceq_liveRoot p dst ht) (s + 1) N.erase C
      (by simpa only [dst, clock_base_blocks] using hadm) hbslot
      (block_preceq_trans h.target_cut (block_preceq_trans hK hXC))
      (block_preceq_trans hCA (fgsa_parent_preceq N.erase)) h.parent_height
  · intro X C hK hX hp hm htC
    have hold := (fgsa_stored_block_slots E rho hE.toScheduleWellFormed hip
      (Nat.succ_pos s)).2.1 C (List.mem_filter.mp hm).1
    exact fgsa_eligible_eq_of_retainedBand_score p src dst
      (proposerVotes src (s + 1)) (proposerSupport src (s + 1))
      (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) C
      (h.band_agrees X C hK (Bool.and_eq_true_iff.mp hX).2 hm htC hp hold)
      scores.1 (scores.2 C ⟨hm, htC⟩)
      ((fgsa_proposal_slot (c := c) _ (s + 1)).trans
        (fgsa_vote_slot (c := c) _ (s + 1)).symm)

theorem fgsa_retainedWalk_geometry_on_run_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n)) (Kc : Block)
    (h : RetainedReadPremises p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) D N.erase Kc)
    (hScope : RetainedServiceScope E rho ip ih x y (s + 1) N)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
    RetainedWalkRunGeometry p src dst (s + 1) D N.erase Kc ∧
      N.erase ∈ T p dst (s + 1) ∧
      (∀ C ∈ T p dst (s + 1), C.parent? = some N.erase.parent → C.slot < s + 1 →
        et p dst (s + 1) C = true → C ∈ S p src ∧ es p src (s + 1) C = true) := by
  let src := clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))
  have hs : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip x) _
  have ht : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  obtain ⟨hadm, hmem⟩ := fgsa_retained_proposal_mem_on_run_epoch (hroots := hroots)
    E rho hE (s + 1) hy hip hih N hem D Kc h hScope.proposal.some
  have hr := fgsa_retained_old_child_reflects_on_run_on (hroots := hroots) E rho hE s
    hx hy hip hih hseat N hem hadm D Kc h hScope
  have hA := fgsa_score_geometry_of_retained_cuts p src dst hs ht (s + 1) D N.erase Kc h
  have scores := fgsa_score_eq_on_candidates_on_run_on (hroots := hroots) E rho hE (s + 1) hx
    hy hip hih hseat N hem hadm
    (fun C => C ∈ S p src ∧ C ∈ T p dst (s + 1)) hA
    (fun C hm => fgsa_score_geometry_of_tree_domains p src dst src.fg.TF
      (voterBlocks p dst (s + 1)) C hm.1 hm.2) hScope
  refine ⟨{
    pivot_parent := h.pivot_parent
    ordinary_start := fgsa_Z_preceq_liveRoot p src
    ordinary_prefix := h.ordinary_prefix
    target_parent := h.target_parent
    source_cut := h.source_cut
    target_cut := h.target_cut
    cut_parent := h.cut_parent
    target_prefix := h.target_prefix
    persists := fgsa_retained_path_persists_on_run_on (hroots := hroots) E rho hE s
      hx hy hip hih hseat N hem hadm D Kc h hScope
    reflects := hr.1
    scores := ?_ }, hmem, hr.2⟩
  apply fgsa_retained_scores_of_candidates
  intro C hC
  obtain ⟨X, hK, hX, hm, hp, he, hcase⟩ := hC
  have hsrc : C ∈ S p src := by
    rcases hcase with hstrict | hold
    · exact (hr.1 X C hK hstrict hm hp he).1
    · exact fgsa_walkRun_reflected_old_child_on (hroots := hroots) E rho hE s
        hx hy hip hih hseat N hem Kc X C h.source_cut hK hX hp hold hm
        (h.reflected_witness X C hK hX hm hp hold he) hScope
  exact scores.2 C ⟨hsrc, hm⟩

end AvailableChain.FGSA.Run
end

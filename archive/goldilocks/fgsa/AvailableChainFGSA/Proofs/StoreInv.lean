module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainFGSA.Statements.Store
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGSA.Proofs.Admission
public import AvailableChainFGSA.Proofs.Nesting
public import AvailableChainGeneric.Proofs.Pure.Fold

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The composite store invariant (K4 core; `bp.store.v1`, `bp.frame.v1`), F
monotone, K1 at a block step (`bp.reconcile.v1`), and the selector facts. -/

/-! ### Σ.T -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.carrier.v1; K5 local + DQ2] Σ.T satisfies `ViewRootInj`
with no hypothesis. -/
theorem viewRootInj_TF (p : Params) (st : State p.n) (h : CStoreInv p st) :
    ViewRootInj st.fg.TF :=
  viewRootInj_of_rootInj h.fg.closed h.rootInj

/-- [ROOT-DIGEST-2 W1; DC root HEAD] ROOT-DIGEST W1c: the body store inherits root uniqueness from
CStoreInv. -/
theorem baseBlocks_rootInj (p : Params) (st : State p.n) (h : CStoreInv p st) :
    ∀ A ∈ st.base.blocks, ∀ B ∈ st.base.blocks, A.root = B.root → A = B := by
  intro a ha b hb he
  obtain ⟨A, hA, rfl⟩ := (h.baseTree a).mp ha
  obtain ⟨B, hB, rfl⟩ := (h.baseTree b).mp hb
  have hr : A.root = B.root := by simpa only [eraseFG_root] using he
  exact congrArg eraseFG (h.rootInj A hA B hB hr)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] ROOT-DIGEST W1c: every erasedList walk uses a subset of the
body store. -/
theorem erasedList_rootInj (p : Params) (st : State p.n) (h : CStoreInv p st)
    (X : Finset (FGBlock (Fin p.n))) :
    ∀ A ∈ erasedList st X, ∀ B ∈ erasedList st X, A.root = B.root → A = B := by
  intro A hA B hB
  exact baseBlocks_rootInj p st h A (List.mem_filter.mp hA).1 B (List.mem_filter.mp hB).1

/-- [bp bp.frame.v1; K4] The live controls equal the old FJ controls with top retention. -/
theorem fgsa_storeControls_eq_of_top_retained (p : Params) (st : State p.n)
    (h : CStoreInv p st)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    controls p st = fjControls p.E p.cfg st.fg.F st.fg.TF := by
  rw [fgsa_controls_eq_of_top_retained p st hF,
    KitFG.storeControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p),
    KitFG.fjControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  exact KitFG.storeControlsView_eq_fjControlsView_of_inv
    (heightView p) (finalityView p) st.fg h.fg
    (KitFG.candidateJ_rootInj_of_viewRootInj p.E (heightView p)
      (fgCertificateLaws p).height st.fg.TF (viewRootInj_TF p st h))

/-- [bp bp.frame.v1; K4] The live controls are the guarded FJ controls of Σ.T. -/
theorem fgsa_storeControls_eq_tree (p : Params) (st : State p.n) (h : CStoreInv p st) :
    controls p st = KitFG.treeFjControlsView (heightView p) st.fg.F st.fg.TF := by
  have he := KitFG.storeControlsView_eq_fjControlsView_of_inv
    (heightView p) (finalityView p) st.fg h.fg
    (KitFG.candidateJ_rootInj_of_viewRootInj p.E (heightView p)
      (fgCertificateLaws p).height st.fg.TF (viewRootInj_TF p st h))
  have hH := congrArg Controls.H he
  have hj := congrArg Controls.j he
  have hJ := congrArg Controls.J he
  dsimp [KitFG.storeControlsView, KitFG.fjControlsView] at hH hj hJ
  unfold controls KitFG.treeStoreControlsView KitFG.treeFjControlsView
  simp only [← hH, ← hj, ← hJ]

/-- [bp bp.frame.v1; K4] The live full tree is the guarded FJ frame domain of Σ.T. -/
theorem fgsa_fullTree_eq_treeFrame (p : Params) (st : State p.n) (h : CStoreInv p st) :
    fullTree p st = (KitFG.treeFjFrameView (heightView p) st.fg.F st.fg.TF).D := by
  change KitFG.filteredFromView (heightView p) (controls p st) st.fg.TF = _
  rw [fgsa_storeControls_eq_tree p st h]
  rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1; K4] The live J is in Σ.T (the clause "F, J ∈
T"; `Fmem` of
`KitFG.FGStoreInvariant` gives F). -/
theorem J_mem (p : Params) (st : State p.n) (h : CStoreInv p st) : st.fg.J ∈ st.fg.TF := by
  obtain ⟨K, hK, _, _, hJ⟩ := h.fg.pair.1
  rw [hJ]
  exact KitFG.ancestor_closed_of_parent_closed _ h.fg.closed K hK _
    (KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry K)
      ((fgCertificateLaws p).height.entry_preceq K))

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The FG root `Z` of the live controls is in Σ.T. -/
theorem Z_mem (p : Params) (st : State p.n) (h : CStoreInv p st) :
    (controls p st).Z ∈ st.fg.TF := by
  unfold Controls.Z
  split
  · exact J_mem p st h
  · exact h.fg.Fmem

/-! ### Invariant transfer -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `savedGenuine` reads only `genuine`. -/
theorem savedGenuine_congr {n : Nat} {v w : GridCO.State n .root} (h : w.genuine = v.genuine) (r :
  Slot) :
    GridCO.savedGenuine w r = GridCO.savedGenuine v r := by
  unfold GridCO.savedGenuine
  rw [h]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `FastOrigin` reads only `fastWrite` and `genuine`. -/
theorem fastOrigin_congr {n : Nat} {st st' : State n} (F : Block)
    (hW : st'.fastWrite = st.fastWrite) (hG : st'.base.genuine = st.base.genuine)
    (h : FastOrigin F st) : FastOrigin F st' := by
  intro row hrow B hB
  rw [hW] at hrow
  rw [savedGenuine_congr hG]
  exact h row hrow B hB

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The invariant depends only on `fg`, the block list,
the leases, the
saved results, S and `fastWrite`; the leases may shrink. -/
theorem cstoreInv_of_sublist (p : Params) {st st' : State p.n} (h : CStoreInv p st)
    (hfg : st'.fg = st.fg) (hb : st'.base.blocks = st.base.blocks)
    (ho : st'.base.obligations.Sublist st.base.obligations)
    (hg : st'.base.genuine = st.base.genuine) (hS : st'.base.stableRecord = st.base.stableRecord)
    (hW : st'.fastWrite = st.fastWrite) : CStoreInv p st' := by
  have hsv := savedGenuine_congr hg
  refine ⟨hfg ▸ h.fg, hfg ▸ h.rootInj, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [hb, hfg]
    exact h.baseTree b
  · intro row hrow
    rw [hfg]
    exact h.saCompat.1 row (ho.subset hrow)
  · intro r C hC
    rw [hfg]
    rw [hg] at hC
    exact h.saCompat.2.1 r C hC
  · intro row hrow b hb'
    rw [hfg]
    rw [hW] at hrow
    exact h.saCompat.2.2 row hrow b hb'
  · rw [hS, hb]
    exact h.Smem
  · rw [hfg]
    exact fastOrigin_congr _ hW hg h.fastOrigin
  · rw [hW]
    refine ⟨h.fastDom.1, fun r hr => ?_⟩
    rw [hsv]
    exact h.fastDom.2 r hr
  · rw [hg]
    exact h.genuineKeys
  · exact ⟨(ho.map Prod.fst).nodup h.leaseKeys.1,
      fun row hrow => h.leaseKeys.2 row (ho.subset hrow)⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `normalizeS` keeps the invariant: the new S is
`eraseFG F`, which is
stored. -/
theorem cstoreInv_normalizeS (p : Params) (st : State p.n) (h : CStoreInv p st) :
    CStoreInv p (normalizeS st) := by
  rw [normalizeS_fields]
  split
  · exact cstoreInv_of_sublist p h rfl rfl (List.Sublist.refl _) rfl rfl rfl
  · refine ⟨h.fg, h.rootInj, h.baseTree, h.saCompat, ?_, h.fastOrigin, h.fastDom, h.genuineKeys,
      h.leaseKeys⟩
    exact (h.baseTree _).2 ⟨_, h.fg.Fmem, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1] -/
theorem cstoreInv_init (p : Params) : CStoreInv p (initial p.n) := by
  refine ⟨(fgStoreSafety p).initial_good, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX Y hY _
    have hx : X = .genesis := Finset.mem_singleton.mp hX
    have hy : Y = .genesis := Finset.mem_singleton.mp hY
    exact hx.trans hy.symm
  · intro b
    simp only [initial, GridCO.initial, Store.init, List.mem_singleton, Finset.mem_singleton,
      exists_eq_left, eraseFG]
    exact eq_comm
  · intro row hrow; simp [initial, GridCO.initial] at hrow
  · intro r C hC; simp [initial, GridCO.initial] at hC
  · intro row hrow; simp [initial] at hrow
  · simp [initial, GridCO.initial]
  · intro row hrow; simp [initial] at hrow
  · simp [initial]
  · simp [initial, GridCO.initial]
  · simp [initial, GridCO.initial]

/-- Ruling Y: the store invariant does not read the reset clock. -/
theorem cstoreInv_initialAt (p : Params) (t : Time) : CStoreInv p (initialAt p.n t) := by
  have h := cstoreInv_init p
  exact ⟨h.fg, h.rootInj, h.baseTree, h.saCompat, h.Smem, h.fastOrigin,
    h.fastDom, h.genuineKeys, h.leaseKeys⟩

/-- [Sleep v6; P24] Wipe keeps durable invariant fields and clears fast histories. -/
theorem cstoreInv_wipe (p : Params) (st : State p.n) (w : Time) (h : CStoreInv p st) :
    CStoreInv p (wipe p st w) := by
  refine ⟨h.fg, h.rootInj, h.baseTree, ⟨h.saCompat.1, ?_, ?_⟩, h.Smem, ?_, ?_, ?_,
    h.leaseKeys⟩
  · simp [wipe, GridCO.initial]
  · simp [wipe]
  · intro row hm
    exact False.elim (List.not_mem_nil hm)
  · simp [wipe]
  · simp [wipe, GridCO.initial]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] Admission proves
inserted-tree roots locally. -/
theorem storeStepRoots_of_blockAccepted (p : Params) (st : State p.n) (h : CStoreInv p st)
    (s : Slot) (N : NamedProposal p.n) (P : FGBlock (Fin p.n)) (hP : parentFG st N.erase = some P)
    (hacc : blockAccepted p st s N P = true) :
    KitFG.StoreStepRoots st.fg (fgBlock P N.erase N.rows) := by
  have hparent := ((parentFG_spec st N.erase P).1 hP).1
  have hfresh := (blockAccepted_facts hacc).2.2.1
  apply viewRootInj_of_rootInj
  · intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX
    · exact Finset.mem_insert_of_mem hparent
    · exact Finset.mem_insert_of_mem (h.fg.closed X hX)
  · intro X hX Y hY hr
    rcases Finset.mem_insert.mp hX with rfl | hX <;>
      rcases Finset.mem_insert.mp hY with rfl | hY
    · rfl
    · exact False.elim (hfresh ⟨Y, hY, hr.symm⟩)
    · exact False.elim (hfresh ⟨X, hX, hr⟩)
    · exact h.rootInj X hX Y hY hr

/-! ### Delivery -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The pre-reconcile state of an accepted block keeps the
invariant
fields that do not read F, and the origin invariant for the old F. -/
theorem cstoreInv_accepted_pre (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true) :
    let st1 : State p.n := { st with
      base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
        N.support) N.erase
        (N.raw.map baseHead)
      fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
      proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
    KitFG.FGStoreInvariant (heightView p) (finalityView p) st1.fg ∧
      (∀ X ∈ st1.fg.TF, ∀ Y ∈ st1.fg.TF, X.root = Y.root → X = Y) ∧
      (∀ c, c ∈ st1.base.blocks ↔ ∃ B ∈ st1.fg.TF, eraseFG B = c) ∧
      st1.base.obligations = st.base.obligations ∧ st1.base.genuine = st.base.genuine ∧
      st1.base.stableRecord = st.base.stableRecord ∧ st1.fastWrite = st.fastWrite ∧
      st.base.blocks ⊆ st1.base.blocks ∧ FGBlock.Preceq st.fg.F st1.fg.F := by
  intro st1
  have h0 : Inv0 p st := h.toInv0
  obtain ⟨hg, -, -, hFB, -, -⟩ := blockAccepted_facts hacc
  obtain ⟨hPT, hPe, -, -⟩ := accepted_base_facts p st h0 hP hacc
  obtain ⟨hbl, -, -, hob, hgen, hstab, -⟩ :=
    base_admitProposal_accepts p st h0 s N P hP hacc
  have hTF : st1.fg.TF = insert (fgBlock P N.erase N.rows) st.fg.TF := by
    change (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF = _
    rw [fg_on_block_accepts p st s N P hP hacc, Window.window_update_finality_TF]
  have hok := blockAccepted_rowsOk hacc
  have hStep := storeStepRoots_of_blockAccepted p st h s N P hP hacc
  refine ⟨?_, ?_, ?_, hob, hgen, hstab, rfl, ?_, Window.window_on_block_F_mono p p.K_W st.fg _⟩
  · exact (fgStoreSafety p).invariant _ ((fgStoreSafety p).step_good st.fg _ h.fg hStep)
  · intro X hX Y hY hr
    rw [hTF] at hX hY
    exact hStep X Y ⟨X, hX, KitFG.preceq_refl X⟩ ⟨Y, hY, KitFG.preceq_refl Y⟩ hr
  · intro c
    change c ∈ (GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
      N.support) N.erase
      (N.raw.map baseHead)).blocks ↔ _
    rw [hbl, hTF, List.mem_append, List.mem_singleton, h.baseTree c]
    constructor
    · rintro (⟨B, hB, rfl⟩ | rfl)
      · exact ⟨B, Finset.mem_insert_of_mem hB, rfl⟩
      · exact ⟨_, Finset.mem_insert_self _ _, eraseFG_fgBlock hg hPe N.rows hok⟩
    · rintro ⟨B, hB, rfl⟩
      rw [Finset.mem_insert] at hB
      rcases hB with rfl | hB
      · exact Or.inr (eraseFG_fgBlock hg hPe N.rows hok)
      · exact Or.inl ⟨B, hB, rfl⟩
  · intro c hc
    change c ∈ (GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
      N.support) N.erase
      (N.raw.map baseHead)).blocks
    rw [hbl]
    exact List.mem_append_left _ hc

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] An accepted block keeps the invariant. -/
theorem cstoreInv_admitBlock (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (N : NamedProposal p.n) :
    CStoreInv p (admitBlock p st s N) := by
  by_cases hNamed : namedParentHeld st N = true
  swap
  · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
    exact h
  cases hP : parentFG st N.erase with
  | none =>
      rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
      exact h
  | some P =>
      cases hacc : blockAccepted p st s N P with
      | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))]
          exact h
      | true =>
          obtain ⟨pool, heq, -⟩ := admitBlock_accepted_eq p st s N P hNamed hP hacc
          rw [heq]
          obtain ⟨hfg, hri, hbt, hob, hgen, hstab, hW, hsub, hmono⟩ :=
            cstoreInv_accepted_pre p st h s N P hP hacc
          dsimp only at hfg hri hbt hob hgen hstab hW hsub hmono ⊢
          have hsv := savedGenuine_congr hgen
          split
          · next hc =>
            refine ⟨hfg, hri, hbt, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
            · intro row hrow; rw [hc]; rw [hob] at hrow; exact h.saCompat.1 row hrow
            · intro r C hC; rw [hc]; rw [hgen] at hC; exact h.saCompat.2.1 r C hC
            · intro row hrow; rw [hc]; exact h.saCompat.2.2 row hrow
            · rw [hstab]; exact hsub h.Smem
            · rw [hc]; exact fastOrigin_congr (st := st) _ rfl hgen h.fastOrigin
            · exact ⟨h.fastDom.1, fun r hr => by rw [hsv]; exact h.fastDom.2 r hr⟩
            · rw [hgen]; exact h.genuineKeys
            · rw [hob]; exact h.leaseKeys
          · next hc =>
            refine ⟨by rw [reconcile_fg]; exact hfg, by rw [reconcile_fg]; exact hri,
              by rw [reconcile_fg, (reconcile_frame _).2.2.2.1]; exact hbt,
              by have := reconcile_saCompat
                  { st with
                    base := GridCO.admitProposal p.toParams.engine st.base
                      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                    fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
                 exact this, ?_, ?_, ?_, ?_, ?_⟩
            · rw [reconcile_stable, (reconcile_frame _).2.2.2.1]
              split
              · rw [hstab]; exact hsub h.Smem
              · exact (hbt _).2 ⟨_, hfg.Fmem, rfl⟩
            · rw [reconcile_fg]
              exact reconcile_fastOrigin _ (eraseFG st.fg.F)
                (fastOrigin_congr (st := st) _ rfl hgen h.fastOrigin) (eraseFG_preceq hmono)
            · rw [reconcile_fastWrite]
              refine ⟨by rw [List.map_map]; exact h.fastDom.1, fun r hr => ?_⟩
              rw [List.map_map] at hr
              rw [reconcile_savedGenuine, hsv]
              simpa using h.fastDom.2 r hr
            · rw [reconcile_genuine, List.map_map, hgen]
              exact h.genuineKeys
            · rw [reconcile_obligations, hob]
              exact ⟨((List.filter_sublist (l := st.base.obligations)).map Prod.fst).nodup
                h.leaseKeys.1,
                fun row hrow => h.leaseKeys.2 row (List.mem_filter.1 hrow).1⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1] A delivery keeps the invariant. -/
theorem cstoreInv_process (p : Params) (st : State p.n) (h : CStoreInv p st) (o : Wire p.n) :
    CStoreInv p (process p st o) := by
  unfold process
  split
  · exact cstoreInv_of_sublist p h rfl (admitHead_base_blocks ..)
      (by rw [admitHead_obligations]) (admitHead_genuine ..) (admitHead_base_stable ..) rfl
  · rcases admitRow_eq p st ⟨o.auth, _⟩ with he | he <;> rw [he]
    · exact h
    · exact cstoreInv_of_sublist p h rfl rfl (List.Sublist.refl _) rfl rfl rfl
  · exact cstoreInv_admitBlock p st h _ _
  · exact h

/-! ### The tick -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate only deletes leases. -/
theorem clockPre_obligations_sublist (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.obligations.Sublist st.base.obligations := by
  unfold clockPre
  dsimp only
  split_ifs <;>
    first
    | exact List.filter_sublist
    | exact List.filter_sublist.trans List.filter_sublist

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate keeps the invariant. -/
theorem cstoreInv_clockPre (p : Params) (st : State p.n) (h : CStoreInv p st) (t : Time) :
    CStoreInv p (clockPre p st t) :=
  cstoreInv_of_sublist p h (clockPre_fg p st t) (clockPre_fields p st t).2.1
    (clockPre_obligations_sublist p st t) (clockPre_genuine p st t) (clockPre_stable p st t)
    (clockPre_fastWrite p st t)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] One lease write keeps one row per target at the one SA
level. -/
theorem writeObligation_keys {n : Nat} (v : GridCO.State n .root) (b : Block) (g : Nat) (d : Time)
    (τ : Nat) (hN : (v.obligations.map Prod.fst).Nodup) (hL : ∀ row ∈ v.obligations, row.2.1 = τ)
    (hg : g = τ) :
    ((GridCO.writeObligation v b g d).obligations.map Prod.fst).Nodup ∧
      ∀ row ∈ (GridCO.writeObligation v b g d).obligations, row.2.1 = τ := by
  simp only [GridCO.writeObligation]
  constructor
  · rw [List.map_append, List.nodup_append]
    refine ⟨(List.filter_sublist.map Prod.fst).nodup hN, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst hy
    intro hxb
    subst hxb
    obtain ⟨row, hrow, hr⟩ := List.mem_map.1 hx
    rw [List.mem_filter] at hrow
    have hl := hL row hrow.1
    obtain ⟨t, l, dd⟩ := row
    simp only at hr hl
    subst hr
    simp [hl, hg] at hrow
  · intro row hrow
    rw [List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hrow | rfl
    · exact hL row (List.mem_filter.1 hrow).1
    · exact hg

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A sequence of lease writes at the one SA level keeps
one row per
target, and writes no S. -/
theorem writeKeys_keys {n : Nat} (v : GridCO.State n .root) (keys : List (Block × Nat)) (d : Time)
    (τ : Nat) (hN : (v.obligations.map Prod.fst).Nodup) (hL : ∀ row ∈ v.obligations, row.2.1 = τ)
    (hk : ∀ key ∈ keys, key.2 = τ) :
    ((GridCO.writeKeys v keys d).obligations.map Prod.fst).Nodup ∧
      (∀ row ∈ (GridCO.writeKeys v keys d).obligations, row.2.1 = τ) ∧
      (GridCO.writeKeys v keys d).stableRecord = v.stableRecord ∧
      (GridCO.writeKeys v keys d).genuine = v.genuine := by
  induction keys generalizing v with
  | nil => exact ⟨hN, hL, rfl, rfl⟩
  | cons key keys ih =>
      simp only [GridCO.writeKeys, List.foldl_cons]
      obtain ⟨hN', hL'⟩ := writeObligation_keys v key.1 key.2 d τ hN hL
        (hk key List.mem_cons_self)
      exact ih _ hN' hL' (fun k hk' => hk k (List.mem_cons_of_mem _ hk'))

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Every key that the SA gate writes has the one SA
level. -/
theorem saGateWriteKeys_level (p : SA.Params) {n : Nat} (v : GridCO.State n .root) (s : Slot)
    (C : Block) :
    ∀ key ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.engine n v s C,
      key.2 = SA.releaseThreshold p := by
  intro key hkey
  simp only [GridCO.gateWriteKeys, List.mem_flatMap, List.mem_map] at hkey
  obtain ⟨b, -, g, hgl, rfl⟩ := hkey
  simp only [GridCO.admissionLevels] at hgl
  split at hgl
  · split at hgl
    · simp only [List.mem_singleton] at hgl
      exact hgl
    · simp at hgl
  · exact absurd rfl ‹_›

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA gate with the walk from `a` on a view: an empty
or vetoed gate
writes no lease and no S; otherwise S := advance(S, C) and the leases keep one row
per target at the one SA level. -/
theorem saGate_cases (p : SA.Params) {n : Nat} (a : Block) (v : GridCO.State n .root) (s : Slot)
    (hN : (v.obligations.map Prod.fst).Nodup)
    (hL : ∀ row ∈ v.obligations, row.2.1 = SA.releaseThreshold p) :
    ((SA.Root.gateFrom p a v s).obligations.map Prod.fst).Nodup ∧
      (∀ row ∈ (SA.Root.gateFrom p a v s).obligations, row.2.1 = SA.releaseThreshold p) ∧
      ((SA.Root.gateFrom p a v s).stableRecord = v.stableRecord ∨
        ∃ C, SA.Root.confirmationFrom p a v s = some C ∧
          (SA.Root.gateFrom p a v s).stableRecord = GridCO.advance v.stableRecord C) := by
  cases hc : SA.Root.confirmationFrom p a v s with
  | none =>
      have he : SA.Root.gateFrom p a v s = { v with
          genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s none } := by
        simp only [SA.Root.gateFrom, GridCO.gateFrom]
        rw [show GridCO.confirmationFrom p.engine a v s = none from hc]
      rw [he]
      exact ⟨hN, hL, Or.inl rfl⟩
  | some C =>
      cases hg : v.obligations.any (fun (target, _, _) => !Block.compatible target C) with
      | true =>
          have he : SA.Root.gateFrom p a v s = { v with
              goldfishRecord := GridCO.advance v.goldfishRecord C
              genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some C) } := by
            simp only [SA.Root.gateFrom, GridCO.gateFrom]
            rw [show GridCO.confirmationFrom p.engine a v s = some C from hc]
            simp only [hg, ite_true]
          rw [he]
          exact ⟨hN, hL, Or.inl rfl⟩
      | false =>
          have he := @GridCO.gateFrom_eq_writeKeys GridCO.slowLeasePolicy .root
            p.engine n a v s C hc hg
          change SA.Root.gateFrom p a v s = _ at he
          obtain ⟨h1, h2, h3, -⟩ := writeKeys_keys
            { v with
              goldfishRecord := GridCO.advance v.goldfishRecord C
              genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some C)
              stableRecord := GridCO.advance v.stableRecord C }
            (@GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.engine n v s C)
            (GridCO.gateTime p.engine s + GridCO.lifetime p.engine) (SA.releaseThreshold p) hN hL
            (saGateWriteKeys_level p v s C)
          rw [he]
          exact ⟨h1, h2, Or.inr ⟨C, rfl, h3⟩⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A saved label is not a fresh label. -/
theorem ne_of_saved {n : Nat} {v : GridCO.State n .root} {r s : Slot}
    (hr : (GridCO.savedGenuine v r).isSome) (hs : GridCO.savedGenuine v s = none) : r ≠ s := by
  rintro rfl
  rw [hs] at hr
  exact absurd hr (by simp)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] An unsaved label is not a key of `genuine`. -/
theorem notMem_keys_of_unsaved {n : Nat} {v : GridCO.State n .root} {s : Slot}
    (hs : GridCO.savedGenuine v s = none) : s ∉ v.genuine.map Prod.fst := by
  unfold GridCO.savedGenuine at hs
  rw [Option.map_eq_none_iff, List.find?_eq_none] at hs
  intro hm
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hm
  exact hs row hrow (by simp)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The result of the walk from F on the active view is
compatible with
F and stored: F itself or an active result, and every prefix of it. -/
theorem compat_of_confirmation (p : Params) (st : State p.n) (h : CStoreInv p st) {s : Slot}
    {C : Block}
    (hc : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s = some C) :
    Block.Compatible C (eraseFG st.fg.F) ∧ C ∈ st.base.blocks := by
  rcases GridCO.confirmationFrom_mem p.toParams.engine (eraseFG st.fg.F) (actView st) s C hc
    with rfl | hm
  · exact ⟨block_compatible_of_preceq (block_preceq_refl _),
      ((actView_blocks st _).1 (actView_genesis_F p st h).2).1⟩
  · exact ⟨((actView_blocks st C).1 hm).2, ((actView_blocks st C).1 hm).1⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A fresh gate (before `S := F`) keeps the invariant. -/
theorem cstoreInv_gateFresh (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (hnew : GridCO.savedGenuine st.base s = none) :
    CStoreInv p { onView (fun v => SA.Root.gateFrom p.toParams (eraseFG st.fg.F) v s) st with
      fastWrite := st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] } := by
  have hv : GridCO.savedGenuine (actView st) s = none := hnew
  have hgen := saGate_genuine p.toParams (eraseFG st.fg.F) (actView st) s hv
  have hsv : ∀ r, GridCO.savedGenuine
      (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s) r =
        if r = s then some (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s)
        else GridCO.savedGenuine st.base r := by
    intro r
    have := savedGenuine_append (actView st) s
      (SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) hv r
    exact (savedGenuine_congr hgen r).trans this
  obtain ⟨hN, hL, hS⟩ :=
    saGate_cases p.toParams (eraseFG st.fg.F) (actView st) s h.leaseKeys.1 h.leaseKeys.2
  refine ⟨h.fg, h.rootInj, h.baseTree, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨hN, hL⟩⟩
  · rintro ⟨B, g, d⟩ hrow
    rcases @GridCO.gateFrom_target_origin GridCO.slowLeasePolicy .root p.toParams.engine _
      (eraseFG st.fg.F) (actView st) s B g
      d hrow with ⟨k, dl, hold⟩ | ⟨C, hc, hBC⟩
    · exact h.saCompat.1 (B, k, dl) hold
    · exact block_compatible_of_preceq_compatible hBC (compat_of_confirmation p st h hc).1
  · intro r C hC
    change (r, some C) ∈
      (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).genuine at hC
    rw [hgen, List.mem_append, List.mem_singleton] at hC
    rcases hC with hC | hC
    · exact h.saCompat.2.1 r C hC
    · rw [Prod.mk.injEq] at hC
      exact (compat_of_confirmation p st h hC.2.symm).1
  · intro row hrow B hB
    rw [List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hrow | rfl
    · exact h.saCompat.2.2 row hrow B hB
    · obtain ⟨-, -, -, hm, -⟩ := fastSet_prefix p (eraseFG st.fg.F) (actView st) s hB
      exact ((actView_blocks st B).1 hm).2
  · change (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).stableRecord ∈
      st.base.blocks
    rcases hS with hS | ⟨C, hc, hS⟩
    · rw [hS]; exact h.Smem
    · rw [hS]
      unfold GridCO.advance
      split
      · exact h.Smem
      · exact (compat_of_confirmation p st h hc).2
  · intro row hrow B hB
    change (∃ C, GridCO.savedGenuine (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s)
      row.1 = some (some C) ∧ Block.Preceq B C) ∨ Block.Preceq B (eraseFG st.fg.F)
    rw [List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hrow | rfl
    · have hne : row.1 ≠ s := ne_of_saved (h.fastDom.2 row.1 (List.mem_map_of_mem hrow)) hnew
      rw [hsv, ite_eq_right hne]
      exact h.fastOrigin row hrow B hB
    · obtain ⟨C, hc, hBC, -, -⟩ := fastSet_prefix p (eraseFG st.fg.F) (actView st) s hB
      left
      refine ⟨C, ?_, hBC⟩
      rw [hsv, ite_eq_left rfl, hc]
  · change ((st.fastWrite ++
        [(s, fastSet p (eraseFG st.fg.F) (actView st) s)]).map Prod.fst).Nodup ∧
      ∀ r ∈ (st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)]).map Prod.fst,
        (GridCO.savedGenuine (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s)
          r).isSome
    rw [List.map_append]
    refine ⟨List.nodup_append.2 ⟨h.fastDom.1, List.nodup_singleton _, ?_⟩, ?_⟩
    · intro x hx y hy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy
      exact ne_of_saved (h.fastDom.2 x hx) hnew
    · intro r hr
      rw [hsv]
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · rw [ite_eq_right (ne_of_saved (h.fastDom.2 r hr) hnew)]
        exact h.fastDom.2 r hr
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        rw [ite_eq_left hr]
        rfl
  · change ((SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).genuine.map
    Prod.fst).Nodup
    rw [hgen, List.map_append, List.nodup_append]
    refine ⟨h.genuineKeys, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst hy
    rintro rfl
    exact notMem_keys_of_unsaved hv hx

/-- [Sleep v6; plan §14.3] The suppressed fresh gate keeps all store invariants. -/
theorem cstoreInv_gateUnjoined (p : Params) (st : State p.n) (h : CStoreInv p st)
    (s : Slot) (hnew : GridCO.savedGenuine st.base s = none) :
    CStoreInv p
      { onView (fun v => { v with genuine := v.genuine ++ [(s, none)] }) st with
        fastWrite := st.fastWrite ++ [(s, [])] } := by
  have hsv := savedGenuine_append (actView st) s none hnew
  refine ⟨h.fg, h.rootInj, h.baseTree, ⟨h.saCompat.1, ?_, ?_⟩, h.Smem, ?_, ?_, ?_,
    h.leaseKeys⟩
  · intro r C hm
    change (r, some C) ∈ st.base.genuine ++ [(s, none)] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.saCompat.2.1 r C hm
    · simp at hm
  · intro row hm B hb
    rcases List.mem_append.mp hm with hm | hm
    · exact h.saCompat.2.2 row hm B hb
    · have he := List.mem_singleton.mp hm
      subst row
      exact False.elim (List.not_mem_nil hb)
  · intro row hm B hb
    rcases List.mem_append.mp hm with hm | hm
    · have hn := ne_of_saved (h.fastDom.2 row.1 (List.mem_map_of_mem hm)) hnew
      change (∃ C, GridCO.savedGenuine
        { (actView st) with genuine := (actView st).genuine ++ [(s, none)] }
        row.1 = some (some C) ∧ Block.Preceq B C) ∨ Block.Preceq B (eraseFG st.fg.F)
      rw [hsv, ite_eq_right hn]
      exact h.fastOrigin row hm B hb
    · have he := List.mem_singleton.mp hm
      subst row
      exact False.elim (List.not_mem_nil hb)
  · change ((st.fastWrite ++ [(s, [])]).map Prod.fst).Nodup ∧ _
    rw [List.map_append]
    refine ⟨List.nodup_append.2 ⟨h.fastDom.1, List.nodup_singleton _, ?_⟩, ?_⟩
    · intro x hx y hy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst y
      exact ne_of_saved (h.fastDom.2 x hx) hnew
    · intro r hr
      change (GridCO.savedGenuine
        { (actView st) with genuine := (actView st).genuine ++ [(s, none)] } r).isSome
      rw [hsv]
      rcases List.mem_append.mp hr with hr | hr
      · rw [ite_eq_right (ne_of_saved (h.fastDom.2 r hr) hnew)]
        exact h.fastDom.2 r hr
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        rw [ite_eq_left hr]
        rfl
  · change ((st.base.genuine ++ [(s, none)]).map Prod.fst).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨h.genuineKeys, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst y
    rintro rfl
    exact notMem_keys_of_unsaved hnew hx

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate keeps the invariant. -/
theorem cstoreInv_gateStep (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot) :
    CStoreInv p (gateStep p st s) := by
  by_cases hs : (GridCO.savedGenuine st.base s).isSome
  · rw [gateStep_saved p st s hs]
    exact cstoreInv_normalizeS p st h
  · have hnew : GridCO.savedGenuine st.base s = none := by simpa using hs
    unfold gateStep
    dsimp only
    rw [ite_eq_right hs]
    split
    · exact cstoreInv_normalizeS p _ (cstoreInv_gateUnjoined p st h s hnew)
    · exact cstoreInv_normalizeS p _ (cstoreInv_gateFresh p st h s hnew)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] The gate keeps every SA target compatible
with F. -/
theorem saCompat_gateStep (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot) :
    SACompat (gateStep p st s) :=
  (cstoreInv_gateStep p st h s).saCompat

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.leaseOrigins.v1] A fresh gate keeps the fast-write
origins. -/
theorem fastOrigin_gateStep (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot) :
    FastOrigin (eraseFG st.fg.F) (gateStep p st s) := by
  have := (cstoreInv_gateStep p st h s).fastOrigin
  rwa [gateStep_fg] at this

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1] A tick keeps the invariant. -/
theorem cstoreInv_clock (p : Params) (st : State p.n) (h : CStoreInv p st) (t : Time) :
    CStoreInv p (clock p st t) := by
  unfold clock
  dsimp only
  split
  · exact cstoreInv_gateStep p _ (cstoreInv_clockPre p st h t) _
  · exact cstoreInv_clockPre p st h t

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1; K4 core] -/
theorem storeInvariant (p : Params) : StoreInvariant p := by
  intro st hst
  induction hst with
  | init => exact cstoreInv_init p
  | restart w _ ih => exact cstoreInv_wipe p _ w ih
  | tick t _ ih => exact cstoreInv_clock p _ ih t
  | deliver o _ ih => exact cstoreInv_process p _ ih o

/-! ### F, `h_max` and the pair are monotone -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.frame.v1] The FG projection stutters or takes one FG
`on_block` step. -/
theorem fg_step_cases (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).fg = st.fg ∨ ∃ B, (process p st o).fg = Window.on_block p p.K_W st.fg B := by
  unfold process
  split
  · exact Or.inl rfl
  · rcases admitRow_eq p st ⟨o.auth, _⟩ with he | he <;> rw [he] <;> exact Or.inl rfl
  · rename_i s N _
    by_cases hNamed : namedParentHeld st N = true
    swap
    · left
      rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
    cases hP : parentFG st N.erase with
    | none =>
        left
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
    | some P =>
        cases hacc : blockAccepted p st s N P with
        | false =>
            left
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))]
        | true =>
            right
            refine ⟨fgBlock P N.erase N.rows, ?_⟩
            obtain ⟨pool, heq, -⟩ := admitBlock_accepted_eq p st s N P hNamed hP hacc
            rw [heq]
            dsimp only
            split
            · rfl
            · rw [reconcile_fg]
  · exact Or.inl rfl

/-- [bp bp.frame.v1] A new FG block comes only from an accepted proposal wire. -/
theorem process_TF_new (p : Params) (st : State p.n) (w : Wire p.n) (B : FGBlock (Fin p.n))
    (hB : B ∈ (process p st w).fg.TF) (hn : B ∉ st.fg.TF) :
    ∃ s N P, w = ⟨.proposer s, .proposal N⟩ ∧ parentFG st N.erase = some P ∧
      blockAccepted p st s N P = true ∧ B = fgBlock P N.erase N.rows := by
  unfold process at hB
  split at hB
  · exact absurd hB hn
  · rcases admitRow_eq p st ⟨w.auth, _⟩ with he | he <;> rw [he] at hB <;> exact absurd hB hn
  · rename_i s N hd
    have hw : w = ⟨.proposer s, .proposal N⟩ := by
      clear hB hn
      obtain ⟨a, m⟩ := w
      rcases a with ⟨(_ | _), _⟩ | _ | _ <;> cases m <;> simp_all [Wire.decode]
    by_cases hNamed : namedParentHeld st N = true
    swap
    · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))] at hB
      exact absurd hB hn
    cases hP : parentFG st N.erase with
    | none =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))] at hB
        exact absurd hB hn
    | some P =>
        cases hacc : blockAccepted p st s N P with
        | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))] at hB
            exact absurd hB hn
        | true =>
            refine ⟨s, N, P, hw, hP, hacc, ?_⟩
            have hTF : (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF =
                insert (fgBlock P N.erase N.rows) st.fg.TF := by
              rw [fg_on_block_accepts p st s N P hP hacc, Window.window_update_finality_TF]
            obtain ⟨pool, heq, -⟩ := admitBlock_accepted_eq p st s N P hNamed hP hacc
            rw [heq] at hB
            dsimp only at hB
            split at hB
            · rw [hTF] at hB
              exact (Finset.mem_insert.mp hB).resolve_right hn
            · rw [reconcile_fg, hTF] at hB
              exact (Finset.mem_insert.mp hB).resolve_right hn
  · exact absurd hB hn

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1; K4] -/
theorem fMonotone (p : Params) : FMonotone p := by
  intro st
  refine ⟨fun o => ?_, fun t => by rw [clock_fg]⟩
  rcases fg_step_cases p st o with he | ⟨B, he⟩ <;> rw [he]
  · exact KitFG.preceq_refl _
  · exact Window.window_on_block_F_mono p p.K_W st.fg B

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1; K4; G11 m1] A delivery moves F only to a
descendant. -/
theorem process_F_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    FGBlock.Preceq st.fg.F (process p st o).fg.F :=
  (fMonotone p st).1 o

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1; K4; G11 m1] A tick does not change F. -/
theorem clock_F_eq (p : Params) (st : State p.n) (t : Time) : (clock p st t).fg.F = st.fg.F :=
  (fMonotone p st).2 t

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.frame.v1] `h_max` never decreases. -/
theorem process_hmax_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.h_max ≤ (process p st o).fg.h_max := by
  rcases fg_step_cases p st o with he | ⟨B, he⟩ <;> rw [he]
  by_cases hc : B ∈ st.fg.TF ∨ B.parent ∉ st.fg.TF ∨ FGBlock.preceq st.fg.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [Window.window_on_block_of_refused p p.K_W st.fg B hc]
  · rw [Window.window_on_block_of_accepted p p.K_W st.fg B hc, Window.window_update_finality_h_max]
    exact le_max_left _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.frame.v1] The lex pair `(h_j, J)` never decreases. -/
theorem process_pair_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    lexKey (st.fg.h_j, st.fg.J) ≤ lexKey ((process p st o).fg.h_j, (process p st o).fg.J) := by
  rcases fg_step_cases p st o with he | ⟨B, he⟩ <;> rw [he]
  by_cases hc : B ∈ st.fg.TF ∨ B.parent ∉ st.fg.TF ∨ FGBlock.preceq st.fg.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [Window.window_on_block_of_refused p p.K_W st.fg B hc]
  · rw [Window.window_on_block_of_accepted p p.K_W st.fg B hc]
    have hp := Window.window_update_finality_pair p p.K_W { st.fg with TF := insert B st.fg.TF } B
    split at hp
    · next hcond =>
      rw [hp]
      exact le_of_lt hcond.2
    · rw [hp]

/-! ### The active view, K1 at a block step -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.activeView.v1] The erased active view is the image of
the FG active view. -/
theorem actView_eq_image (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block) :
    b ∈ (actView st).blocks ↔ ∃ B ∈ activeView st.fg, eraseFG B = b := by
  have hinj := viewRootInj_TF p st h
  rw [actView_blocks, h.baseTree]
  simp only [activeView, Finset.mem_filter]
  constructor
  · rintro ⟨⟨B, hB, rfl⟩, hc⟩
    refine ⟨B, ⟨hB, ?_⟩, rfl⟩
    rw [compatible_iff_eraseFG hinj ⟨B, hB, KitFG.preceq_refl _⟩
      ⟨_, h.fg.Fmem, KitFG.preceq_refl _⟩]
    exact hc
  · rintro ⟨B, ⟨hB, hc⟩, rfl⟩
    refine ⟨⟨B, hB, rfl⟩, ?_⟩
    rw [compatible_iff_eraseFG hinj ⟨B, hB, KitFG.preceq_refl _⟩
      ⟨_, h.fg.Fmem, KitFG.preceq_refl _⟩] at hc
    exact hc

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.reconcile.v1; K1] K1 at a block step, blueprint form: at
an accepted
block that moves F, if the new F is compatible with every live lease (every row
of `obligations`, due leases included; G9 m2), every saved nonempty result and S
of the state before the step, then reconcile
deletes no lease, no body and no fastWrite member, and only extends S. No
fastWrite premise: `FastOrigin` comes from `CStoreInv`. -/
theorem admitBlock_reconcile_harmless (p : Params) (st : State p.n) (h : CStoreInv p st)
    (s : Slot) (N : NamedProposal p.n) (P : FGBlock (Fin p.n)) (hNamed : namedParentHeld st N =
      true)
    (hP : parentFG st N.erase = some P)
    (hacc : blockAccepted p st s N P = true)
    (hL : ∀ row ∈ st.base.obligations,
      Block.Compatible row.1 (eraseFG (admitBlock p st s N).fg.F))
    (hG : ∀ r C, (r, some C) ∈ st.base.genuine →
      Block.Compatible C (eraseFG (admitBlock p st s N).fg.F))
    (hS : Block.Compatible st.base.stableRecord
      (eraseFG (admitBlock p st s N).fg.F)) :
    (admitBlock p st s N).base.obligations = st.base.obligations ∧
    (admitBlock p st s N).base.genuine = st.base.genuine ∧
    (admitBlock p st s N).fastWrite = st.fastWrite ∧
    Block.Preceq st.base.stableRecord (admitBlock p st s N).base.stableRecord := by
  obtain ⟨pool, heq, -⟩ := admitBlock_accepted_eq p st s N P hNamed hP hacc
  obtain ⟨-, -, -, hob, hgen, hstab, -, -, hmono⟩ :=
    cstoreInv_accepted_pre p st h s N P hP hacc
  rw [heq] at hL hG hS ⊢
  dsimp only at hL hG hS hob hgen hstab hmono ⊢
  by_cases hc : (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).F = st.fg.F
  · rw [ite_eq_left hc]
    exact ⟨hob, hgen, rfl, by rw [hstab]; exact block_preceq_refl _⟩
  · rw [ite_eq_right hc] at hL hG hS ⊢
    rw [reconcile_fg] at hL hG hS
    obtain ⟨he, hpre⟩ := reconcile_harmless_origin
      { st with
        base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
          N.support) N.erase
          (N.raw.map baseHead)
        fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
        proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
      (eraseFG st.fg.F)
      (fastOrigin_congr (st := st) _ rfl hgen h.fastOrigin) (eraseFG_preceq hmono)
      (by rw [hob]; exact hL) (by rw [hgen]; exact hG) (by rw [hstab]; exact hS)
    refine ⟨by rw [he]; exact hob, by rw [he]; exact hgen, by rw [he], ?_⟩
    rw [← hstab]
    exact hpre

/-! ### Selector facts -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [DQ13; audit N2] The stored FG block of an erased block is
exact. -/
theorem fgBlockOf_spec (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block)
    (B : FGBlock (Fin p.n)) : fgBlockOf st b = some B ↔ B ∈ st.fg.TF ∧ eraseFG B = b := by
  constructor
  · intro hB
    have := pickPair_some_spec _ _ hB
    exact ⟨this.1, by simpa using this.2⟩
  · rintro ⟨hB, he⟩
    unfold fgBlockOf
    apply KitFG.pickPair_eq_of_unique _ _ B hB (by simpa using he)
    intro B' hB' he'
    simp only [decide_eq_true_eq] at he'
    apply h.rootInj B' hB' B hB
    rw [← eraseFG_root B', ← eraseFG_root B, he, he']

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [DQ13; audit N2] A nonempty subset of Σ.T has a deepest member
(tie: the
greater root). -/
theorem deepest_spec (p : Params) (st : State p.n) (h : CStoreInv p st)
    (X : Finset (FGBlock (Fin p.n))) (hX : X ⊆ st.fg.TF) (hne : X.Nonempty) :
    ∃ B, deepest X = some B ∧ B ∈ X ∧ ∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
      ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value) := by
  let key : FGBlock (Fin p.n) → ℕ ×ₗ ℕ := fun B => toLex ((eraseFG B).depth, B.root.value)
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image X key hne
  have hq : ∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
      ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value) := by
    intro C hC
    have := hmax C hC
    rcases Prod.Lex.toLex_le_toLex.1 this with hlt | ⟨heq, hle⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, hle⟩
  refine ⟨B, ?_, hB, hq⟩
  unfold deepest
  apply KitFG.pickPair_eq_of_unique _ _ B hB (by simpa using hq)
  intro B' hB' hq'
  simp only [decide_eq_true_eq] at hq'
  have h1 := hq' B hB
  have h2 := hq B' hB'
  have hdep : (eraseFG B').depth = (eraseFG B).depth := by omega
  have hroot : B'.root.value = B.root.value := by
    rcases h1 with h1 | ⟨-, h1⟩ <;> rcases h2 with h2 | ⟨-, h2⟩ <;> omega
  apply h.rootInj B' (hX hB') B (hX hB)
  cases hr' : B'.root
  cases hr : B.root
  rw [hr', hr] at hroot
  simp only at hroot
  rw [hroot]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [spec 648–655; T7.W] The live root is stored: it is the erasure
of Z or a
lease target in the full filtered tree. `fgHead_stored` and the walk wrappers
use this proof. -/
theorem liveRoot_stored (p : Params) (st : State p.n) (h : CStoreInv p st) :
    liveRoot p st ∈ st.base.blocks := by
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · rw [he]
    exact (h.baseTree _).2 ⟨_, Z_mem p st h, rfl⟩
  · obtain ⟨row, -, hrow⟩ := List.mem_filterMap.1 hm
    split at hrow
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨B, hB, hBe⟩ := hc.2
      rw [← Option.some.inj hrow, ← hBe]
      exact (h.baseTree _).2 ⟨B, (Finset.filter_subset _ _) hB, rfl⟩
    · exact absurd hrow (by simp)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [DQ13; audit N2] The finality head is stored; so the fallback
head fields
of `fgInputs` are unreachable. -/
theorem fgHead_stored (p : Params) (st : State p.n) (h : CStoreInv p st) :
    fgHead p st ∈ st.base.blocks := by
  unfold fgHead getHead headInTree GridCO.ghost
  dsimp only
  rcases @GridCO.ghostWalk_mem GridCO.slowLeasePolicy _ _ _ _ (liveRoot p st) with he | hm
  · rw [he]
    exact liveRoot_stored p st h
  · have hm2 := List.mem_eraseDups.1 hm
    exact (List.mem_filter.1 hm2).1

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [DQ2; Opus m4] The base list satisfies GridCO's local root
premise. -/
theorem rootInjectiveBelow_base (p : Params) (st : State p.n) (h : CStoreInv p st) :
    GridCO.RootInjectiveBelow st.base.blocks := by
  rintro A C ⟨BA, hBA, hA⟩ ⟨BC, hBC, hC⟩ hr
  obtain ⟨FA, hFA, rfl⟩ := (h.baseTree _).1 hBA
  obtain ⟨FC, hFC, rfl⟩ := (h.baseTree _).1 hBC
  obtain ⟨A', hA', rfl⟩ := eraseFG_ancestor_mem h.fg.closed hFA hA
  obtain ⟨C', hC', rfl⟩ := eraseFG_ancestor_mem h.fg.closed hFC hC
  rw [eraseFG_root, eraseFG_root] at hr
  rw [h.rootInj A' hA' C' hC' hr]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper; G3 minor 3] The composite lease read is SA's lease
read at its one
level. -/
theorem leaseOf_eq_deadlineOf (p : Params) (st : State p.n) (h : CStoreInv p st) (b : Block) :
    leaseOf st b = GridCO.deadlineOf st.base b (SA.releaseThreshold p.toParams) := by
  unfold leaseOf GridCO.deadlineOf
  congr 1
  apply Gen.Pure.find?_congr_mem
  rintro ⟨t, l, d⟩ hrow
  have hl : l = SA.releaseThreshold p.toParams := h.leaseKeys.2 _ hrow
  simp [hl]

end AvailableChain.FGSA
end

module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainFGSA.Proofs.RowValidity
public import AvailableChainFGSA.Proofs.NamedStore

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! The metadata invariant (K4 metadata; `bp.store.v1`, `bp.frame.v1`): the
stored wires, the block stamps and the row pool. -/

/-! ### Stamps -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A vote admission keeps the blocks and the block
stamps, and only
appends to the vote stamps. -/
theorem admitVote_stamps (q : GridCO.Params) {n : Nat} (v : GridCO.State n .root) (o : GridCO.Wire n
  .root) :
    (GridCO.admitVote q v o).blocks = v.blocks ∧
      (GridCO.admitVote q v o).blockStamp = v.blockStamp ∧
      v.voteStamp <+: (GridCO.admitVote q v o).voteStamp := by
  simp only [GridCO.admitVote]
  split
  · split_ifs
    · exact ⟨rfl, rfl, List.prefix_refl _⟩
    · exact ⟨rfl, rfl, List.prefix_append _ _⟩
  · exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The carried-vote fold keeps the block stamps and only
appends to
the vote stamps. -/
theorem foldVotes_stamps (q : GridCO.Params) {n : Nat} (raw : List (GridCO.HeadWire n .root))
    (v : GridCO.State n .root) :
    (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) v).blockStamp =
        v.blockStamp ∧
      v.voteStamp <+:
        (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) v).voteStamp := by
  induction raw generalizing v with
  | nil => exact ⟨rfl, List.prefix_refl _⟩
  | cons x xs ih =>
      simp only [List.foldl_cons]
      obtain ⟨-, h1, h2⟩ := admitVote_stamps q v (GridCO.fromHead x)
      obtain ⟨h3, h4⟩ := ih (GridCO.admitVote q v (GridCO.fromHead x))
      exact ⟨h3.trans h1, h2.trans h4⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Lease writes keep both stamp lists. -/
theorem writeKeys_stamps {n : Nat} (v : GridCO.State n .root) (keys : List (Block × Nat)) (d : Time)
  :
    (GridCO.writeKeys v keys d).blockStamp = v.blockStamp ∧
      (GridCO.writeKeys v keys d).voteStamp = v.voteStamp := by
  induction keys generalizing v with
  | nil => exact ⟨rfl, rfl⟩
  | cons key keys ih =>
      simp only [GridCO.writeKeys, List.foldl_cons]
      exact ih _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA gate with the walk from `a` keeps both stamp
lists. -/
theorem saGate_stamps (p : SA.Params) {n : Nat} (a : Block) (v : GridCO.State n .root) (s : Slot) :
    (SA.Root.gateFrom p a v s).blockStamp = v.blockStamp ∧
      (SA.Root.gateFrom p a v s).voteStamp = v.voteStamp := by
  cases hc : SA.Root.confirmationFrom p a v s with
  | none =>
      simp only [SA.Root.gateFrom, GridCO.gateFrom]
      rw [show GridCO.confirmationFrom p.engine a v s = none from hc]
      exact ⟨rfl, rfl⟩
  | some C =>
      cases hg : v.obligations.any (fun (target, _, _) => !Block.compatible target C) with
      | true =>
          simp only [SA.Root.gateFrom, GridCO.gateFrom]
          rw [show GridCO.confirmationFrom p.engine a v s = some C from hc]
          simp only [hg, ite_true]
          exact ⟨trivial, trivial⟩
      | false =>
          have he := @GridCO.gateFrom_eq_writeKeys GridCO.slowLeasePolicy .root
            p.engine n a v s C hc hg
          change SA.Root.gateFrom p a v s = _ at he
          rw [he]
          exact writeKeys_stamps _ _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The gate keeps both stamp lists. -/
theorem gateStep_stamps (p : Params) (st : State p.n) (s : Slot) :
    (gateStep p st s).base.blockStamp = st.base.blockStamp ∧
      (gateStep p st s).base.voteStamp = st.base.voteStamp := by
  unfold gateStep
  rw [normalizeS_fields]
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · exact saGate_stamps p.toParams (eraseFG st.fg.F) (actView st) s

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The tick before the gate keeps both stamp lists. -/
theorem clockPre_stamps (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.blockStamp = st.base.blockStamp ∧
      (clockPre p st t).base.voteStamp = st.base.voteStamp := by
  unfold clockPre
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1] A tick changes no tree, stamp, wire or pool.
-/
theorem clock_cumulative (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).fg.TF = st.fg.TF ∧ (clock p st t).base.blocks = st.base.blocks ∧
    (clock p st t).base.blockStamp = st.base.blockStamp ∧
    (clock p st t).base.voteStamp = st.base.voteStamp ∧
    (clock p st t).proposals = st.proposals ∧ (clock p st t).rowPool = st.rowPool := by
  refine ⟨by rw [clock_fg], clock_base_blocks p st t, ?_, ?_, clock_proposals p st t,
    clock_rowPool p st t⟩
  · unfold clock
    dsimp only
    split
    · rw [(gateStep_stamps _ _ _).1, (clockPre_stamps _ _ _).1]
    · exact (clockPre_stamps _ _ _).1
  · unfold clock
    dsimp only
    split
    · rw [(gateStep_stamps _ _ _).2, (clockPre_stamps _ _ _).2]
    · exact (clockPre_stamps _ _ _).2

/-! ### The accepted step -/

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The state before the row fold of an accepted block:
one more wire,
one more FG block, one more base block with its stamp; the vote stamps only
grow, and the row pool is unchanged. -/
theorem accepted_st2 (p : Params) (st : State p.n) (h : CStoreInv p st) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hP : parentFG st N.erase = some P) (hacc : blockAccepted p st s N P = true) :
    let st1 : State p.n := { st with
      base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
        N.support) N.erase
        (N.raw.map baseHead)
      fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
      proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
    let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
    st2.proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩] ∧
      st2.fg.TF = insert (fgBlock P N.erase N.rows) st.fg.TF ∧
      st2.base.blocks = st.base.blocks ++ [N.erase] ∧
      st2.base.blockStamp = st.base.blockStamp ++ [(N.erase, st.base.now)] ∧
      st.base.voteStamp <+: st2.base.voteStamp ∧ st2.rowPool = st.rowPool := by
  have h0 : Inv0 p st := h.toInv0
  obtain ⟨hbl, hbs, -, -, -, -, -⟩ :=
    base_admitProposal_accepts p st h0 s N P hP hacc
  obtain ⟨hB, -, -⟩ := admitProposal_base_view p st h0 s N P hP hacc
  have hvs : st.base.voteStamp <+: (GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).voteStamp := by
    rw [hB]
    exact (foldVotes_stamps p.toParams.engine (N.raw.map baseHead)
      { st.base with
        blocks := st.base.blocks ++ [N.erase]
        blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
        proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }).2
  have hTF : (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF =
      insert (fgBlock P N.erase N.rows) st.fg.TF := by
    rw [fg_on_block_accepts p st s N P hP hacc, Window.window_update_finality_TF]
  dsimp only
  by_cases hc : (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).F = st.fg.F
  · rw [ite_eq_left hc]
    exact ⟨rfl, hTF, hbl, hbs, hvs, rfl⟩
  · rw [ite_eq_right hc]
    obtain ⟨h1, h2, h3, h4, h5, -, h7, -⟩ := reconcile_frame
      { st with
        base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
          N.support) N.erase
          (N.raw.map baseHead)
        fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
        proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
    rw [h1, h2, h3, h4, h5, h7]
    exact ⟨rfl, hTF, hbl, hbs, hvs, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The SA block admission only appends to the blocks and
both stamp
lists, also when it refuses. -/
theorem admitProposal_prefix (q : GridCO.Params) {n : Nat} (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root)) :
    v.blocks <+: (GridCO.admitProposal q v o b raw).blocks ∧
      v.blockStamp <+: (GridCO.admitProposal q v o b raw).blockStamp ∧
      v.voteStamp <+: (GridCO.admitProposal q v o b raw).voteStamp := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩
  · have h1 := (foldVotes_fields q raw { v with
      blocks := v.blocks ++ [b]
      blockStamp := v.blockStamp ++ [(b, v.now)]
      proposals := v.proposals ++ [o] }).1
    have h2 := foldVotes_stamps q raw { v with
      blocks := v.blocks ++ [b]
      blockStamp := v.blockStamp ++ [(b, v.now)]
      proposals := v.proposals ++ [o] }
    refine ⟨?_, ?_, h2.2⟩
    · rw [h1]; exact List.prefix_append _ _
    · rw [h2.1]; exact List.prefix_append _ _

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1] A delivery only appends: Σ.T and the base list
grow; old
block stamps, vote stamps, stored wires and pool rows stay, in order. -/
theorem process_cumulative (p : Params) (st : State p.n) (o : Wire p.n) :
    st.fg.TF ⊆ (process p st o).fg.TF ∧
    st.base.blocks <+: (process p st o).base.blocks ∧
    st.base.blockStamp <+: (process p st o).base.blockStamp ∧
    st.base.voteStamp <+: (process p st o).base.voteStamp ∧
    st.proposals <+: (process p st o).proposals ∧
    st.rowPool <+: (process p st o).rowPool := by
  have refl6 : st.fg.TF ⊆ st.fg.TF ∧ st.base.blocks <+: st.base.blocks ∧
      st.base.blockStamp <+: st.base.blockStamp ∧ st.base.voteStamp <+: st.base.voteStamp ∧
      st.proposals <+: st.proposals ∧ st.rowPool <+: st.rowPool :=
    ⟨subset_rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
      List.prefix_refl _⟩
  unfold process
  split
  · obtain ⟨h1, h2, h3⟩ := admitVote_stamps p.toParams.engine st.base
      ⟨.seat _ _, .head _⟩
    refine ⟨subset_rfl, ?_, ?_, h3, List.prefix_refl _, List.prefix_refl _⟩
    · change st.base.blocks <+: (GridCO.admitVote _ _ _).blocks
      rw [h1]
    · change st.base.blockStamp <+: (GridCO.admitVote _ _ _).blockStamp
      rw [h2]
  · rcases admitRow_eq p st ⟨o.auth, _⟩ with he | he <;> rw [he]
    · exact refl6
    · exact ⟨subset_rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
        List.prefix_refl _, List.prefix_append _ _⟩
  · rename_i s N _
    by_cases hNamed : namedParentHeld st N = true
    swap
    · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
      exact refl6
    cases hP : parentFG st N.erase with
    | none =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
        exact refl6
    | some P =>
        cases hacc : blockAccepted p st s N P with
        | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))]
            exact refl6
        | true =>
            obtain ⟨pool, heq, hpre⟩ := admitBlock_accepted_eq p st s N P hNamed hP hacc
            rw [heq]
            obtain ⟨b1, b2, b3⟩ := admitProposal_prefix p.toParams.engine st.base
              (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
            have hsub := Window.window_on_block_TF_subset p p.K_W st.fg (fgBlock P N.erase N.rows)
            dsimp only at hpre ⊢
            by_cases hc : (Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).F = st.fg.F
            · rw [ite_eq_left hc] at hpre ⊢
              exact ⟨hsub, b1, b2, b3, List.prefix_append _ _, hpre⟩
            · rw [ite_eq_right hc] at hpre ⊢
              obtain ⟨h1, h2, h3, h4, h5, -, h7, -⟩ := reconcile_frame
                { st with
                  base := GridCO.admitProposal p.toParams.engine st.base
                    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
                  fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
              rw [h3] at hpre
              refine ⟨by rw [h1]; exact hsub, by rw [h4]; exact b1, by rw [h5]; exact b2,
                by rw [h7]; exact b3, by rw [h2]; exact List.prefix_append _ _, hpre⟩
  · exact refl6

/-! ### The metadata invariant -/

theorem metaInv_init (p : Params) : MetaInv p (initial p.n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho; simp [initial] at ho
  · intro B hB hg
    simp only [initial, Store.init, Finset.mem_singleton] at hB
    exact absurd hB hg
  · simp [initial]
  · simp [initial, GridCO.initial]
  · simp [initial, GridCO.initial]
  · intro a ha; simp [initial] at ha
  · simp [initial]
  · intro o ho; simp [initial] at ho

/-- Ruling Y: reset metadata does not read the retained clock. -/
theorem metaInv_initialAt (p : Params) (t : Time) : MetaInv p (initialAt p.n t) := by
  have h := metaInv_init p
  exact ⟨h.wireTree, h.treeWire, h.proposalsNodup, h.stampKeys, h.blocksNodup,
    h.poolDecodes, h.poolNodup, h.noGenesisWire⟩

/-- [Sleep v6; P24] Wipe rebuilds the stamp keys in the stored block order. -/
theorem metaInv_wipe (p : Params) (st : State p.n) (w : Time) (h : MetaInv p st) :
    MetaInv p (wipe p st w) := by
  refine ⟨h.wireTree, h.treeWire, h.proposalsNodup, ?_, h.blocksNodup,
    h.poolDecodes, h.poolNodup, h.noGenesisWire⟩
  simp [wipe, List.map_map, Function.comp_def]

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] `Wire.block?` of a proposal wire. -/
theorem block?_proposal {n : Nat} (s : Slot) (N : NamedProposal n) :
    Wire.block? (n := n) ⟨.proposer s, .proposal N⟩ = some N.erase := rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A row admission keeps the metadata invariant. -/
theorem metaInv_admitRow (p : Params) (st : State p.n) (m : MetaInv p st) (a : RowWire p.n) :
    MetaInv p (admitRow p st a) := by
  unfold admitRow
  cases hd : a.decode? with
  | none => exact m
  | some val =>
      dsimp only
      split
      · exact m
      · next hnot =>
        refine ⟨m.wireTree, m.treeWire, m.proposalsNodup, m.stampKeys, m.blocksNodup,
          ?_, ?_, m.noGenesisWire⟩
        · intro c hc
          rw [List.mem_append, List.mem_singleton] at hc
          rcases hc with hc | rfl
          · exact m.poolDecodes c hc
          · rw [hd]; rfl
        · rw [List.nodup_append]
          refine ⟨m.poolNodup, List.nodup_singleton _, ?_⟩
          intro x hx y hy
          rw [List.mem_singleton] at hy
          subst hy
          rintro rfl
          exact hnot hx

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] A row fold keeps the metadata invariant. -/
theorem metaInv_foldl_admitRow (p : Params) (rows : List (RowWire p.n)) (X : State p.n)
    (m : MetaInv p X) : MetaInv p (rows.foldl (admitRow p) X) := by
  induction rows generalizing X with
  | nil => exact m
  | cons a rows ih => exact ih _ (metaInv_admitRow p X m a)

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The block of a stored wire is in the base list. -/
theorem wire_block_mem (p : Params) (st : State p.n) (h : CStoreInv p st) (m : MetaInv p st)
    {o : Wire p.n} (ho : o ∈ st.proposals) {c : Block} (hc : Wire.block? o = some c) :
    c ∈ st.base.blocks := by
  obtain ⟨s, N, rfl, -, -, -, B, hB, hBe, -⟩ := m.wireTree o ho
  rw [block?_proposal, Option.some.injEq] at hc
  subst hc
  exact (h.baseTree _).2 ⟨B, hB, hBe⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] Every row of an accepted block decodes (DQ12). -/
theorem accepted_rows_decode {p : Params} {st : State p.n} {s
  : Slot} {N : NamedProposal p.n}
    {P : FGBlock (Fin p.n)} (hacc : blockAccepted p st s N P = true) : ∀ a ∈ N.rows,
      (RowWire.decode?
      a).isSome := by
  have hv : rowsValidForParent p P N.erase.slot N.rows = true := by
    simp only [blockAccepted, Bool.and_eq_true] at hacc
    exact hacc.1.2
  intro a ha
  obtain ⟨N.erase, hb⟩ := Window.rowValidW_decodes _ a
    ((rowsValidForParent_iff p P _ N.rows).mp hv a ha)
  cases hd : a.decode? with
  | none => simp [RowWire.toRow?, hd] at hb
  | some x => rfl

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The state before the row fold of an accepted block
keeps the
metadata invariant. -/
theorem metaInv_accepted (p : Params) (st : State p.n) (h : CStoreInv p st) (m : MetaInv p st)
    (s : Slot) (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (X : State p.n)
    (hX1 : X.proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩])
    (hX2 : X.fg.TF = insert (fgBlock P N.erase N.rows) st.fg.TF)
    (hX3 : X.base.blocks = st.base.blocks ++ [N.erase])
    (hX4 : X.base.blockStamp = st.base.blockStamp ++ [(N.erase, st.base.now)])
    (hX6 : X.rowPool = st.rowPool)
    (hparent : N.parent ∈ st.namedBodies)
    (hg : N.erase ≠ .genesis) (hPe : eraseFG P = N.erase.parent) (hb : N.erase ∉ st.base.blocks)
    (hdec : ∀ a ∈ N.rows, (RowWire.decode? a).isSome) (hcontent : contentOk p N.erase N.raw
      N.support N.rows =
      true) :
    MetaInv p X := by
  have hrows := contentOk_rowsOk hcontent
  have hwb : ∀ {o : Wire p.n}, o ∈ st.proposals → ∀ {c : Block}, Wire.block? o = some c →
      c ∈ st.base.blocks := fun ho _ hc => wire_block_mem p st h m ho hc
  have hnamed : st.namedBodies ⊆ X.namedBodies := by
    intro M hm
    rcases (mem_namedBodies st M).mp hm with rfl | ⟨t, ht⟩
    · exact (mem_namedBodies X _).mpr (Or.inl rfl)
    · apply (mem_namedBodies X M).mpr
      exact Or.inr ⟨t, by rw [hX1]; exact List.mem_append_left _ ht⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho
    rw [hX1, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · obtain ⟨s', M, ho', hk', hp', hd', B, hB, hBe, hBr⟩ := m.wireTree o ho
      exact ⟨s', M, ho', hk', hnamed hp', hd', B,
        by rw [hX2]; exact Finset.mem_insert_of_mem hB, hBe, hBr⟩
    · exact ⟨s, N, rfl, hcontent, hnamed hparent, hdec, fgBlock P N.erase N.rows,
        by rw [hX2]; exact Finset.mem_insert_self _ _,
        eraseFG_fgBlock hg hPe N.rows hrows, rfl⟩
  · intro B hB hBg
    rw [hX2, Finset.mem_insert] at hB
    rw [hX1]
    rcases hB with rfl | hB
    · rw [eraseFG_fgBlock hg hPe N.rows hrows]
      refine ⟨⟨.proposer s, .proposal N⟩,
        ⟨List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, ?_⟩
      rintro o ⟨ho, hob⟩
      rw [List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | ho
      · exact absurd (hwb ho hob) hb
      · exact ho
    · obtain ⟨o, ⟨ho, hob⟩, hu⟩ := m.treeWire B hB hBg
      have hne : eraseFG B ≠ N.erase := fun he => hb (he ▸ (h.baseTree _).2 ⟨B, hB, rfl⟩)
      refine ⟨o, ⟨List.mem_append_left _ ho, hob⟩, ?_⟩
      rintro o' ⟨ho', hob'⟩
      rw [List.mem_append, List.mem_singleton] at ho'
      rcases ho' with ho' | rfl
      · exact hu o' ⟨ho', hob'⟩
      · rw [block?_proposal, Option.some.injEq] at hob'
        exact absurd hob'.symm hne
  · rw [hX1, List.nodup_append]
    refine ⟨m.proposalsNodup, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    rintro rfl
    exact hb (hwb hx (block?_proposal _ _))
  · rw [hX4, hX3, List.map_append, m.stampKeys]
    rfl
  · rw [hX3, List.nodup_append]
    refine ⟨m.blocksNodup, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    rintro rfl
    exact hb hx
  · rw [hX6]; exact m.poolDecodes
  · rw [hX6]; exact m.poolNodup
  · intro o ho
    rw [hX1, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact m.noGenesisWire o ho
    · rw [block?_proposal, ne_eq, Option.some.injEq]
      exact hg

theorem metaInv_process (p : Params) (st : State p.n) (h : CStoreInv p st) (m : MetaInv p st)
    (o : Wire p.n) : MetaInv p (process p st o) := by
  unfold process
  split
  · rename_i s i b _
    have hv := admitVote_stamps p.toParams.engine st.base ⟨.seat s i, .head b⟩
    refine ⟨m.wireTree, m.treeWire, m.proposalsNodup, ?_, ?_, m.poolDecodes, m.poolNodup,
      m.noGenesisWire⟩
    · change (GridCO.admitVote _ _ _).blockStamp.map Prod.fst = (GridCO.admitVote _ _ _).blocks
      rw [hv.1, hv.2.1]; exact m.stampKeys
    · change (GridCO.admitVote _ _ _).blocks.Nodup
      rw [hv.1]; exact m.blocksNodup
  · exact metaInv_admitRow p st m _
  · rename_i s N _
    by_cases hNamed : namedParentHeld st N = true
    swap
    · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
      exact m
    cases hP : parentFG st N.erase with
    | none =>
        rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
        exact m
    | some P =>
        cases hacc : blockAccepted p st s N P with
        | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, hacc⟩))]
            exact m
        | true =>
            have h0 : Inv0 p st := h.toInv0
            obtain ⟨hg, -, -, -, -, -⟩ := blockAccepted_facts hacc
            obtain ⟨-, hPe, -, hb⟩ := accepted_base_facts p st h0 hP hacc
            have key := accepted_st2 p st h s N P hP hacc
            dsimp only at key
            obtain ⟨k1, k2, k3, k4, -, k6⟩ := key
            unfold admitBlock
            rw [hP]
            simp only [hNamed, Bool.not_true, Bool.false_eq_true, ite_false, hacc, ite_true]
            exact metaInv_foldl_admitRow p N.rows _
              (metaInv_accepted p st h m s N P _ k1 k2 k3 k4 k6 (of_decide_eq_true hNamed) hg hPe hb
                (accepted_rows_decode hacc) (blockAccepted_contentOk hacc))
  · exact m

theorem metaInv_clock (p : Params) (st : State p.n) (m : MetaInv p st) (t : Time) :
    MetaInv p (clock p st t) := by
  obtain ⟨c1, c2, c3, -, c5, c6⟩ := clock_cumulative p st t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold State.namedBodies
    rw [c5, c1]; exact m.wireTree
  · rw [c5, c1]; exact m.treeWire
  · rw [c5]; exact m.proposalsNodup
  · rw [c3, c2]; exact m.stampKeys
  · rw [c2]; exact m.blocksNodup
  · rw [c6]; exact m.poolDecodes
  · rw [c6]; exact m.poolNodup
  · rw [c5]; exact m.noGenesisWire

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [bp bp.store.v1; K4 metadata] -/
theorem metadataInvariant (p : Params) : MetadataInvariant p := by
  intro st hst
  induction hst with
  | init => exact metaInv_init p
  | restart w _ ih => exact metaInv_wipe p _ w ih
  | tick t _ ih => exact metaInv_clock p _ ih t
  | deliver o hst' ih => exact metaInv_process p _ (storeInvariant p _ hst') ih o

/-- [ROOT-DIGEST-2 W1; DC root HEAD] A held parent lookup persists in a cumulative store. Its exact
content
cannot change, because the stored FG representation is unique. -/
theorem fgBlockOf_mono (p : Params) {st st' : State p.n}
    (h : CStoreInv p st) (h' : CStoreInv p st') (hsub : st.fg.TF ⊆ st'.fg.TF)
    {b : Block} {P : FGBlock (Fin p.n)} (hP : fgBlockOf st b = some P) :
    fgBlockOf st' b = some P := by
  obtain ⟨hm, he⟩ := (fgBlockOf_spec p st h b P).mp hP
  exact (fgBlockOf_spec p st' h' b P).mpr ⟨hsub hm, he⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [R6] A block admission preserves the separate stored-row
obligation. -/
theorem rowsValidStored_admitBlock (p : Params) (st : State p.n)
    (h : CStoreInv p st) (hv : RowsValidStored p st) (s : Slot) (N : NamedProposal p.n)
    :
    RowsValidStored p (admitBlock p st s N) := by
  by_cases hNamed : namedParentHeld st N = true
  swap
  · rw [admitBlock_refused p st s N (Or.inl (Bool.eq_false_iff.mpr hNamed))]
    exact hv
  cases hP : parentFG st N.erase with
  | none =>
      rw [admitBlock_refused p st s N (Or.inr (Or.inl hP))]
      exact hv
  | some P =>
      cases ha : blockAccepted p st s N P with
      | false =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hP, ha⟩))]
          exact hv
      | true =>
          have hn := cstoreInv_admitBlock p st h s N
          have hsub : st.fg.TF ⊆ (admitBlock p st s N).fg.TF :=
            (process_cumulative p st ⟨.proposer s, .proposal N⟩).1
          have hprops : (admitBlock p st s N).proposals =
              st.proposals ++ [⟨.proposer s, .proposal N⟩] := by
            obtain ⟨pool, heq, _⟩ := admitBlock_accepted_eq p st s N P hNamed hP ha
            rw [heq]
            exact (accepted_st2 p st h s N P hP ha).1
          intro o ho t M hd
          rw [hprops, List.mem_append, List.mem_singleton] at ho
          rcases ho with ho | rfl
          · obtain ⟨Q, hQ, hvQ⟩ := hv o ho t M hd
            exact ⟨Q, fgBlockOf_mono p h hn hsub hQ, hvQ⟩
          · simp only [Wire.decode, Option.some.injEq, Input.block.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            obtain ⟨hm, he⟩ := (parentFG_spec st N.erase P).mp hP
            exact ⟨P, by simpa only [named_erase_parent] using
              (fgBlockOf_spec p _ hn N.erase.parent P).mpr ⟨hsub hm, he⟩,
              blockAccepted_rowsValid ha⟩

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [R6] A delivery preserves validity of every stored proposal's
rows. -/
theorem rowsValidStored_process (p : Params) (st : State p.n)
    (h : CStoreInv p st) (hv : RowsValidStored p st) (o : Wire p.n) :
    RowsValidStored p (process p st o) := by
  unfold process
  split
  · exact hv
  · rcases admitRow_eq p st ⟨o.auth, _⟩ with he | he <;> rw [he] <;> exact hv
  · exact rowsValidStored_admitBlock p st h hv _ _
  · exact hv

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [R6] Clock changes cannot change stored parent content or
carried rows. -/
theorem rowsValidStored_clock (p : Params) (st : State p.n)
    (hv : RowsValidStored p st) (t : Time) : RowsValidStored p (clock p st t) := by
  dsimp only [RowsValidStored, fgBlockOf] at hv ⊢
  simpa only [clock_proposals, clock_fg] using hv

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [R6] Every reachable store satisfies the separate stored-row
obligation. -/
theorem rowsValidStored_reachable (p : Params) {st : State p.n} (hr : Reachable p st) :
    RowsValidStored p st := by
  induction hr with
  | init => exact rowsValidStored_initial p
  | restart w _ ih => exact ih
  | tick t _ ih => exact rowsValidStored_clock p _ ih t
  | deliver o hr ih => exact rowsValidStored_process p _ (storeInvariant p _ hr) ih o

/-- [ROOT-DIGEST-2 W1; DC root HEAD] [helper] The one stored wire of a stored non-genesis FG block,
with its rows. -/
theorem stored_wire_of_block (p : Params) (st : State p.n) (h : CStoreInv p st)
    (m : MetaInv p st) {B : FGBlock (Fin p.n)} (hB : B ∈ st.fg.TF) (hg : B ≠ .genesis) :
    ∃ s N, (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals ∧
      N.erase = eraseFG B ∧ B.rows = N.rows.filterMap RowWire.toRow? := by
  obtain ⟨o, ⟨ho, hob⟩, -⟩ := m.treeWire B hB hg
  obtain ⟨s, N, rfl, -, -, -, B', hB', hBe, hBr⟩ := m.wireTree o ho
  rw [block?_proposal, Option.some.injEq] at hob
  have hBB : B' = B := h.rootInj B' hB' B hB
    (by rw [← eraseFG_root B', ← eraseFG_root B, hBe, hob])
  subst B'
  exact ⟨s, N, ho, hob, hBr⟩

end AvailableChain.FGSA
end

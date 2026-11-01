module
public import AvailableChainPCSAProofs.Proofs.Shared.BodyPersistence
public import AvailableChainPCSAProofs.Proofs.Shared.BodyAdmission
public import AvailableChainPCSAProofs.Proofs.Shared.BodyScope
public import AvailableChainPCSAProofs.Proofs.Shared.Clock
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainPCSAProofs.Proofs.Shared.Relay

public section

/-! C3 exact body origin, insertion, and relay before the freeze. -/

namespace AvailableChain.PCSA
open SimplexFG
private theorem pcsa_receipt_fg_erasure {n : Nat} (P : FGBlock (Fin n)) (b : Block)
    (rows : List (RowWire n)) (hne : b ≠ .genesis) (hp : eraseFG P = b.parent)
    (hr : rowsOk b rows = true) : eraseFG (fgBlock P b rows) = b := by
  cases b with
  | genesis => exact (hne rfl).elim
  | node parent slot root body =>
    have hb : body = packBody (appOf body) rows := beq_iff_eq.mp hr
    change Block.node (eraseFG P) slot root (packBody (appOf body) rows) = _
    rw [hp, ← hb]
    rfl

/-- Accepted body insertion writes the body and its exact FG projection. -/
theorem pcsa_body_insert_data (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hParent : parentFG st N.erase = some P)
    (hAcc : blockAccepted p st s N P = true) :
(GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks =
        st.base.blocks ++ [N.erase] ∧
      (FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF =
        insert (fgBlock P N.erase N.rows) st.fg.TF := by
  have hLook : P ∈ st.fg.TF ∧ eraseFG P = N.erase.parent := by
    have hm := FGSA.pickPair_some_spec st.fg.TF _ hParent
    exact ⟨hm.1, of_decide_eq_true hm.2⟩
  have hf := hAcc
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at hf
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hGen, hSlot⟩, hFresh⟩, hF⟩, hPS⟩, hS⟩, _⟩, _⟩, hContent⟩ := hf
  have hRows : rowsOk N.erase N.rows = true := by
    change (_ && _) = true at hContent
    exact (Bool.and_eq_true_iff.mp hContent).1
  have hErase := pcsa_receipt_fg_erasure P N.erase N.rows hGen hLook.2 hRows
  have hNot : N.erase ∉ st.base.blocks := by
    intro hb
    obtain ⟨B, hB, he⟩ := (hTree _).mp hb
    apply hFresh
    exact ⟨B, hB, by rw [← he]; cases B <;> rfl⟩
  have hBase := FGSA.admitProposal_of_accept p.toParams.engine st.base s
    (.proposal N.erase (N.raw.map baseHead) (N.support.map baseHead)) N.erase
    (N.raw.map baseHead) hSlot ((hTree _).mpr ⟨P, hLook.1, hLook.2⟩)
    hNot hPS hS
  have hBlocks := (FGSA.foldVotes_fields p.toParams.engine (N.raw.map baseHead)
    { st.base with
      blocks := st.base.blocks ++ [N.erase]
      blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
      proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }).1
  have hBaseBlocks : (GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks =
      st.base.blocks ++ [N.erase] :=
    (congrArg (fun v : GridCO.State p.n .root => v.blocks) hBase).trans hBlocks
  have hFG : (FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF =
      insert (fgBlock P N.erase N.rows) st.fg.TF := by
    rw [FGSA.Window.window_on_block_of_accepted p p.K_W st.fg _]
    · exact FGSA.Window.window_update_finality_TF p p.K_W _ _
    · simp only [not_or, Bool.not_eq_false, not_le]
      refine ⟨?_, fun hm => hm hLook.1, hF, ?_⟩
      · intro hm
        apply hFresh
        refine ⟨fgBlock P N.erase N.rows, hm, ?_⟩
        rw [← hErase]
        cases N.erase <;> rfl
      · have hs : (eraseFG P).slot = P.slot := by cases P <;> rfl
        change P.slot < N.erase.slot
        rw [← hs, hLook.2]
        exact hPS
  exact ⟨hBaseBlocks, hFG⟩

private theorem pcsa_body_row_blocks (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.blocks = st.base.blocks := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v =>
    dsimp only
    split <;> rfl
private theorem pcsa_body_norm_blocks {n : Nat} (st : State n) :
    (normalizeS st).base.blocks = st.base.blocks := by
  delta normalizeS
  split <;> rfl
private theorem pcsa_body_reconcile_blocks {n : Nat} (st : State n) :
    (reconcile st).base.blocks = st.base.blocks := by
  delta reconcile
  rw [pcsa_body_norm_blocks]

/-- A body that passes admission is in the completed delivery state. -/
theorem pcsa_admitBlock_body_mem (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hNamed : namedParentHeld st N = true) (hParent : parentFG st N.erase = some P)
    (hAcc : blockAccepted p st s N P = true) :
    N.erase ∈ (admitBlock p st s N).base.blocks := by
  have hb := (pcsa_body_insert_data p st s N P hTree hParent hAcc).1
  have hm : N.erase ∈ (GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks := by
    rw [hb]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : N.erase ∈ st.base.blocks) :
      N.erase ∈ (as.foldl poolAckRaw st).base.blocks := by
    apply List.foldlRecOn (motive := fun acc : State p.n => N.erase ∈ acc.base.blocks)
    · exact h
    · intro acc hh a _
      rw [(poolAckRaw_frame acc a).2.2.1]
      exact hh
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : N.erase ∈ st.base.blocks) :
      N.erase ∈ (as.foldl (admitRow p) st).base.blocks := by
    apply List.foldlRecOn (motive := fun acc : State p.n => N.erase ∈ acc.base.blocks)
    · exact h
    · intro acc hh a _
      rw [pcsa_body_row_blocks]
      exact hh
  delta admitBlock
  split
  · rename_i hBad
    rw [hNamed] at hBad
    cases hBad
  · cases hLookup : parentFG st N.erase with
    | none => rw [hParent] at hLookup; cases hLookup
    | some Q =>
      have he : Q = P := Option.some.inj (hLookup.symm.trans hParent)
      subst Q
      dsimp only
      split
      · apply hr
        rw [(collectPCs_frame _).2.1]
        apply ha
        cases N.pc <;> dsimp only
        all_goals split_ifs <;> first
          | exact hm
          | (rw [pcsa_body_reconcile_blocks]; exact hm)
      · rename_i hBad
        exact (hBad hAcc).elim

end AvailableChain.PCSA
namespace AvailableChain.PCSA
private def C3BodyScope {n : Nat} (B : Block → Prop) (st : State n) : Prop :=
  ∀ b ∈ st.base.blocks, B b

private theorem pcsa_c3_grid_vote_scope {n : Nat} (q : GridCO.Params)
    (B : Block → Prop) (v : GridCO.State n .root) (o : GridCO.Wire n .root)
    (h : ∀ b ∈ v.blocks, B b) : ∀ b ∈ (GridCO.admitVote q v o).blocks, B b := by
  rw [GridCO.admitVote_blocks]
  exact h

private theorem pcsa_c3_grid_proposal_scope {n : Nat} (q : GridCO.Params)
    (B : Block → Prop) (v : GridCO.State n .root) (o : GridCO.Wire n .root)
    (b : Block) (raw : List (GridCO.HeadWire n .root))
    (h : ∀ a ∈ v.blocks, B a) (hb : B b) :
    ∀ a ∈ (GridCO.admitProposal q v o b raw).blocks, B a := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
  | exact h
  | apply List.foldlRecOn (motive := fun acc : GridCO.State n .root => ∀ a ∈ acc.blocks, B a)
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h a ha
      · exact List.mem_singleton.mp ha ▸ hb
    · intro acc ha row _
      exact pcsa_c3_grid_vote_scope q B acc _ ha

private theorem pcsa_c3_normalize_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : C3BodyScope B st) : C3BodyScope B (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem pcsa_c3_reconcile_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : C3BodyScope B st) : C3BodyScope B (reconcile st) := by
  apply pcsa_c3_normalize_scope
  exact h

private theorem pcsa_c3_collect_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : C3BodyScope B st) : C3BodyScope B (collectPCs st) := by
  change ∀ b ∈ (collectPCs st).base.blocks, B b
  rw [(collectPCs_frame st).2.1]
  exact h

private theorem pcsa_c3_row_scope (p : Params) (B : Block → Prop) (st : State p.n)
    (a : RowWire p.n) (h : C3BodyScope B st) :
    C3BodyScope B (admitRow p st a) := by
  delta admitRow
  cases a.decode? <;> dsimp only <;> first | exact h | split <;> exact h

private theorem pcsa_c3_raw_ack_scope {n : Nat} (B : Block → Prop) (st : State n)
    (a : AckWire n) (h : C3BodyScope B st) : C3BodyScope B (poolAckRaw st a) := by
  change ∀ b ∈ (poolAckRaw st a).base.blocks, B b
  rw [(poolAckRaw_frame st a).2.2.1]
  exact h

theorem pcsa_c3_process_body_pred (p : Params) (B : Block → Prop) (st : State p.n)
    (o : Wire p.n) (h : ∀ b ∈ st.base.blocks, B b)
    (ho : ∀ s N P, o.decode = some (.block s N) →
      parentFG st N.erase = some P → blockAccepted p st s N P = true → B N.erase) :
    ∀ b ∈ (process p st o).base.blocks, B b := by
  change C3BodyScope B (process p st o)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : C3BodyScope B st) :
      C3BodyScope B (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc ha a _ => pcsa_c3_raw_ack_scope B acc a ha)
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : C3BodyScope B st) :
      C3BodyScope B (as.foldl (admitRow p) st) :=
    List.foldlRecOn as (admitRow p) h (fun acc ha a _ => pcsa_c3_row_scope p B acc a ha)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact pcsa_c3_grid_vote_scope p.toParams.engine B st.base _ h
    | row i body => exact pcsa_c3_row_scope p B st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hParent : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · rename_i hAcc
            have hb := ho s N P hd hParent hAcc
            apply hr
            apply pcsa_c3_collect_scope
            apply ha
            have hbase := pcsa_c3_grid_proposal_scope p.toParams.engine B st.base
              (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) h hb
            cases N.pc <;> dsimp only
            all_goals repeat first
              | exact hbase
              | (apply pcsa_c3_reconcile_scope; exact hbase)
              | split
          · exact h
    | ack s i r =>
      apply pcsa_c3_collect_scope
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc C =>
      dsimp only
      delta admitPC
      split
      · exact pcsa_c3_collect_scope B _ (ha _ _ h)
      · exact h


/-- A newly stored body comes from a proposal that passed the exact handler tests. -/
theorem pcsa_process_new_body (p : Params) (st : State p.n) (o : Wire p.n)
    (B : Block) (hn : B ∉ st.base.blocks) (hm : B ∈ (process p st o).base.blocks) :
    ∃ s N P, o.decode = some (.block s N) ∧ parentFG st N.erase = some P ∧
      blockAccepted p st s N P = true ∧ N.erase = B := by
  have h := pcsa_c3_process_body_pred p
    (fun b => b ∈ st.base.blocks ∨ ∃ s N P, o.decode = some (.block s N) ∧
      parentFG st N.erase = some P ∧ blockAccepted p st s N P = true ∧ N.erase = b)
    st o (fun b hb => Or.inl hb)
    (fun s N P hd hp ha => Or.inr ⟨s, N, P, hd, hp, ha, rfl⟩) B hm
  exact h.resolve_left hn
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Each held non-genesis body has an earlier accepting proposal delivery. -/
theorem pcsa_body_receipt_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (x : V) (B : Block) (hg : B ≠ .genesis)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    ∃ j < k, ∃ (t : Time) (o : Obj p) (s : Slot) (N : NamedProposal p.n)
      (P : SimplexFG.FGBlock (Fin p.n)),
      rho.events[j]? = some (.deliver x o t) ∧
      (toWire p o).decode = some (.block s N) ∧ N.erase = B ∧
      parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P ∧
      blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true ∧
      V2.D.Run.acceptsAt E rho j x o t := by
  induction k with
  | zero =>
    change B ∈ [Block.genesis] at hm
    exact (hg (List.mem_singleton.mp hm)).elim
  | succ k ih =>
    by_cases hold : B ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks
    · obtain ⟨j, hj, rest⟩ := ih hold
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    · cases hk : rho.events[k]? with
      | none =>
        have he : V2.D.Run.stateBefore E rho (k + 1) = V2.D.Run.stateBefore E rho k := by
          delta V2.D.Run.stateBefore
          rw [List.take_add_one, hk]
          simp only [Option.toList_none, List.append_nil]
        exact (hold (he ▸ hm)).elim
      | some e =>
        have hpost := V2.D.Run.stateBefore_succ E rho hk
        rw [hpost] at hm
        by_cases hx : e.node = x
        · cases e with
          | restart y t =>
            change y = x at hx
            subst y
            change B ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blocks at hm
            rw [Function.update_self] at hm
            change B ∈ [Block.genesis] at hm
            exact (hg (List.mem_singleton.mp hm)).elim
          | tick y t =>
            change y = x at hx
            subst y
            change B ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blocks at hm
            rw [Function.update_self] at hm
            have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
            rw [ht] at hm
            have hb := pcsa_clock_body_scope p
              (fun b => b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks)
              (V2.D.Run.stateBefore E rho k x).st t (fun _ h => h) B hm
            exact (hold hb).elim
          | deliver y o t =>
            change y = x at hx
            subst y
            change B ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.blocks at hm
            rw [Function.update_self] at hm
            obtain ⟨s, N, P, hd, hp, ha, hB⟩ :=
              pcsa_process_new_body p (V2.D.Run.stateBefore E rho k x).st (toWire p o) B hold hm
            refine ⟨k, Nat.lt_succ_self k, t, o, s, N, P, hk, hd, hB, hp, ha, ?_⟩
            refine ⟨⟨o, hk, Or.inl rfl⟩, hv.fresh k x o t hk, ?_⟩
            rw [hpost]
            change processedS p (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st o = true
            rw [Function.update_self]
            change processedS p
              (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)) o = true
            delta processedS
            rw [hd]
            apply decide_eq_true
            obtain ⟨D, hD, he⟩ := (pcsa_tree_correspondence p _
              (Reachable.deliver (toWire p o) (pcsa_reachable_stateBefore E rho k x)) B).mp hm
            refine ⟨D, hD, ?_⟩
            have er : (eraseFG D).root = D.root := by cases D <;> rfl
            have nr : N.erase.root = N.root := by cases N <;> rfl
            rw [← er, he, ← hB, nr]
        · have he := V2.D.World.step_apply_of_node_ne E rho (V2.D.Run.stateBefore E rho k) hx
          exact (hold (he ▸ hm)).elim
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem pcsa_c3_decoded_wire (o : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (h : o.decode = some (.block s N)) : o = ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at h <;> cases h
  | proposer k =>
    cases payload <;> delta Wire.decode at h <;> cases h
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at h <;> cases h
private theorem pcsa_c3_decoded_object (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) :
    o = ofWire p ⟨.proposer s, .proposal N⟩ :=
  ((toWireEquiv p).left_inv o).symm.trans
    (congrArg (ofWire p) (pcsa_c3_decoded_wire (toWire p o) s N h))

/-- A full proposal body is handled only by its direct delivery. -/
theorem pcsa_body_handles_direct (st : State p.n) (parent : Obj p)
    (s : Slot) (N : NamedProposal p.n)
    (h : handlesS p st parent (ofWire p ⟨.proposer s, .proposal N⟩)) :
    parent = ofWire p ⟨.proposer s, .proposal N⟩ := by
  rcases h with h | h | h
  · exact h
  · cases hd : (toWire p parent).decode with
    | none => rw [hd] at h; exact h.elim
    | some msg => cases msg with
      | vote a i r => rw [hd] at h; exact h.elim
      | row i body => rw [hd] at h; exact h.elim
      | ack a i r => rw [hd] at h; exact h.elim
      | pc C =>
        rw [hd] at h
        obtain ⟨a, _, he⟩ := List.mem_map.mp h
        have hp := congrArg (fun o : Obj p => o.payload) he
        change Msg.ack a.payload = Msg.proposal N at hp
        cases hp
      | block a M =>
        rw [hd] at h
        rcases h.2 with h | h | h
        all_goals obtain ⟨a, _, he⟩ := List.mem_map.mp h
        all_goals have hp := congrArg (fun o : Obj p => o.payload) he
        all_goals cases hp
  · obtain ⟨_, C, he, _, _⟩ := h
    have hp := congrArg (fun o : Obj p => o.payload) he
    cases hp

private theorem pcsa_c3_accept_rows (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n)) (h : blockAccepted p st s N P = true) :
    N.erase.slot ≤ st.slot p ∧ rowsValidForParent p P N.slot N.rows = true := by
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at h
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hSlot⟩, _⟩, _⟩, _⟩, _⟩, hRows⟩, _⟩, _⟩ := h
  have he : N.slot = N.erase.slot := by cases N <;> rfl
  exact ⟨hSlot, by simpa only [he] using hRows⟩

/-- An accepted exact body is admitted at every honest receiver by a deadline
`d`, given the relay step to `d` (the lane delivery premise supplies it). -/
theorem pcsa_body_relay_admitted (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho)
    (j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (t : Time) (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (hj : rho.events[j]? = some (.deliver x o t))
    (hd : (toWire p o).decode = some (.block s N))
    (hp : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P)
    (ha : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true)
    (d : Time) (htd0 : t < d)
    (hRelay : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (j + 1) y) o = false →
      (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho d y) o = false →
      ∃ t', t ≤ t' ∧ t' < d ∧ ∃ k, V2.D.Run.handlesAt E rho k y o t') :
    N.erase ∈ (V2.D.Run.stateBeforeTime E rho d y).st.base.blocks := by
  have hS := h.valid.toScheduleWellFormed
  have hShape := pcsa_c3_decoded_object o s N hd
  have hTree := pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho j x)
  have hdeps := h.valid.deps j x o t hj
  rw [hShape] at hdeps
  change (namedParentHeld (V2.D.Run.stateBefore E rho j x).st N && _ ) = true at hdeps
  have hSrc := pcsa_admitBlock_body_mem p _ s N P hTree
    (Bool.and_eq_true_iff.mp hdeps).1 hp ha
  have hSrc' : N.erase ∈ (V2.D.Run.stateBefore E rho (j + 1) x).st.base.blocks := by
    rw [V2.D.Run.stateBefore_succ E rho hj]
    change N.erase ∈ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.base.blocks
    rw [Function.update_self]
    change N.erase ∈ (process p (V2.D.Run.stateBefore E rho j x).st (toWire p o)).base.blocks
    delta process
    rw [hd]
    exact hSrc
  have hScope := pcsa_body_scope E rho (j + 1) x hx N.erase hSrc'
  have hparent := FGSA.pickPair_some_spec (V2.D.Run.stateBefore E rho j x).st.fg.TF _ hp
  have hGeom : eraseFG P = N.erase.parent := of_decide_eq_true hparent.2
  obtain ⟨hSlot, hRows⟩ := pcsa_c3_accept_rows _ s N P ha
  have hidx : j + 1 ≤ V2.D.Run.idxBefore rho d :=
    Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hS hj _).mpr
      htd0)
  by_cases hNeed : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (j + 1) y) o = true
  · change processedS p (V2.D.Run.stateBefore E rho (j + 1) y).st o = true at hNeed
    delta processedS at hNeed
    rw [hd] at hNeed
    obtain ⟨D, hDmem, hr⟩ := of_decide_eq_true hNeed
    have hB := (pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho (j + 1) y)
      (eraseFG D)).mpr ⟨D, hDmem, rfl⟩
    have hDscope := pcsa_body_scope E rho (j + 1) y hy (eraseFG D) hB
    have er : (eraseFG D).root = D.root := by cases D <;> rfl
    have nr : N.erase.root = N.root := by cases N <;> rfl
    have he := pcsa_scoped_root_eq E rho h.idealization (eraseFG D) N.erase hDscope
      hScope (er.trans (hr.trans nr.symm))
    have hm := pcsa_body_stateBefore_mono E rho h.noRestart y hidx (he ▸ hB)
    rwa [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm
  · have hNX : (pcsaWith m p c).excludes
        (V2.D.Run.stateBeforeTime E rho d y) o = false := by
      have hf := (hF y hy (V2.D.Run.idxBefore rho d)).1
      rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hf
      have he := pcsa_body_not_excluded p _ s N P hf hGeom hRows
      change excludesS p (V2.D.Run.stateBeforeTime E rho d y).st o = false
      delta excludesS
      rw [hd]
      exact he
    obtain ⟨t', htt, htd, k, parent, hk, hh⟩ := hRelay (Bool.eq_false_iff.mpr hNeed) hNX
    have hpobj := pcsa_body_handles_direct (V2.D.Run.stateBefore E rho k y).st parent s N
      (hShape ▸ hh)
    have hko : rho.events[k]? = some (.deliver y o t') := by rwa [hpobj, ← hShape] at hk
    have hDep := h.valid.deps k y o t' hko
    have hFresh := h.valid.fresh k y o t' hko
    have hWF := h.valid.wire k y o t' hko
    rw [hShape] at hDep hFresh hWF
    have hnowj := pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)
    have hnowk := pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho k y)
    have htPublic : V2.PublicTime E (V2.D.Run.stateBefore E rho j x).st.base.now := by
      rcases V2.D.Engine.stateBefore_now_source_noRestart (pcsaClock p c) E rho h.noRestart j x
        with hz | ⟨l, _, hl⟩
      · rw [hnowj] at hz
        exact ⟨0, by simpa using hz⟩
      · rw [hnowj] at hl
        exact hS.tick_public _ _ (List.mem_of_getElem? hl)
    have ht0 : 0 ≤ (V2.D.Run.stateBefore E rho j x).st.base.now := by
      obtain ⟨a, he⟩ := htPublic
      rw [he]
      exact mul_nonneg (Int.natCast_nonneg a) (le_of_lt E.Δ_pos)
    have htSource := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c)
      E rho hS h.noRestart hj x
    rw [hnowj] at htSource
    have htReceiver := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hS h.noRestart
      hko htPublic ht0 (htSource.trans htt)
    rw [hnowk] at htReceiver
    have hSlot' : N.erase.slot ≤ (V2.D.Run.stateBefore E rho k y).st.slot p :=
      hSlot.trans (Int.toNat_le_toNat (Int.ediv_le_ediv
        (by have := p.deltaPos; positivity) htReceiver))
    have hf := (hF y hy k).1
    obtain ⟨hNamed, Q, hQ, hAcc⟩ :=
      pcsa_body_accepted p _ s N P hf hGeom hRows hWF hDep hFresh hSlot'
    have hb := pcsa_admitBlock_body_mem p _ s N Q
      (pcsa_tree_correspondence p _ (pcsa_reachable_stateBefore E rho k y)) hNamed hQ hAcc
    have hb' : N.erase ∈ (V2.D.Run.stateBefore E rho (k + 1) y).st.base.blocks := by
      rw [V2.D.Run.stateBefore_succ E rho hko]
      change N.erase ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.base.blocks
      rw [Function.update_self]
      change N.erase ∈ (process p (V2.D.Run.stateBefore E rho k y).st (toWire p o)).base.blocks
      delta process
      rw [hd]
      exact hb
    have hkd := Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hS hko _).mpr htd)
    have hm := pcsa_body_stateBefore_mono E rho h.noRestart y hkd hb'
    rwa [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm

/-- An accepted exact body reaches every honest receiver before a window deadline
`d ≤ max t T₀ + Δ`, with `d = t + Δ` from the floor `T₀`. -/
theorem pcsa_body_relay_from (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time} (hD : StrictFrom E rho T₀ cut)
    (j : Nat) (x : V) (hx : x ∈ rho.honest)
    (t : Time) (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (hj : rho.events[j]? = some (.deliver x o t))
    (hd : (toWire p o).decode = some (.block s N))
    (hp : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P)
    (ha : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true)
    (hAccept : V2.D.Run.acceptsAt E rho j x o t) :
    ∃ d, t < d ∧ d ≤ max t T₀ + E.Δ ∧ (T₀ ≤ t → d = t + E.Δ) ∧
      ∀ y ∈ rho.honest, d ≤ cut →
        N.erase ∈ (V2.D.Run.stateBeforeTime E rho d y).st.base.blocks := by
  have hShape := pcsa_c3_decoded_object o s N hd
  have hn : ∀ body, o.payload ≠ .row body := by
    rw [hShape]
    intro body he
    cases he
  obtain ⟨d, htd, hle, hex, hrel⟩ := pcsa_strict_relay_from E rho hD o hn x j t hx hAccept
  exact ⟨d, htd, hle, hex, fun y hy hc => pcsa_body_relay_admitted E rho h hF j x y hx hy t o s
    N P hj hd hp ha d htd (fun hNeed hNX => hrel y hy hNeed hc hNX)⟩

/-- An accepted exact body reaches every honest receiver before its relay deadline. -/
theorem pcsa_body_relay_before_deadline (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (j : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (t : Time) (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (P : SimplexFG.FGBlock (Fin p.n))
    (hj : rho.events[j]? = some (.deliver x o t))
    (hd : (toWire p o).decode = some (.block s N))
    (hp : parentFG (V2.D.Run.stateBefore E rho j x).st N.erase = some P)
    (ha : blockAccepted p (V2.D.Run.stateBefore E rho j x).st s N P = true)
    (hAccept : V2.D.Run.acceptsAt E rho j x o t) (hc : t + E.Δ ≤ cut) :
    N.erase ∈ (V2.D.Run.stateBeforeTime E rho (t + E.Δ) y).st.base.blocks := by
  -- Floor `T₀ = t`, not `0`: the statement has no `0 ≤ t`, and healthy delivery is
  -- strict from every floor.
  obtain ⟨d, _, _, hex, hrecv⟩ := pcsa_body_relay_from E rho h hF
    (pcsa_strictFrom_of_healthy E rho hD t) j x hx t o s N P hj hd hp ha hAccept
  rw [hex (le_refl t)] at hrecv
  exact hrecv y hy hc
end AvailableChain.PCSA.Run

end

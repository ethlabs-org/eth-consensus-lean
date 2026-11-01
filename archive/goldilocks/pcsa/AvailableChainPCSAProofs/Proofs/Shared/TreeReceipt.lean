module
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainFGSA.Proofs.Admission
public import AvailableChainFGSA.Proofs.WindowStore

public section

/-! Stored tree correspondence for C3 receipt. -/

namespace AvailableChain.PCSA
open AvailableChain.SimplexFG

private def PCSACleanTreeCorr {n : Nat} (st : State n) : Prop :=
  ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b

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

private theorem pcsa_receipt_accepted_trees (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hTree : PCSACleanTreeCorr st) (hParent : parentFG st N.erase = some P)
    (hAcc : blockAccepted p st s N P = true) :
    PCSACleanTreeCorr { st with
      base := GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
      fg := FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) } := by
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
  change ∀ b, b ∈ (GridCO.admitProposal p.toParams.engine st.base
    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks ↔
    ∃ B ∈ (FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF, eraseFG B = b
  rw [hBaseBlocks, hFG]
  intro b
  rw [List.mem_append, List.mem_singleton]
  constructor
  · rintro (hb | rfl)
    · obtain ⟨B, hB, he⟩ := (hTree b).mp hb
      exact ⟨B, Finset.mem_insert_of_mem hB, he⟩
    · exact ⟨_, Finset.mem_insert_self _ _, hErase⟩
  · rintro ⟨B, hB, he⟩
    rcases Finset.mem_insert.mp hB with hB | hB
    · subst B
      exact Or.inr (he.symm.trans hErase)
    · exact Or.inl ((hTree b).mpr ⟨B, hB, he⟩)

private theorem pcsa_receipt_normalize_tree {n : Nat} (st : State n) (h : PCSACleanTreeCorr st) :
    PCSACleanTreeCorr (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem pcsa_receipt_reconcile_tree {n : Nat} (st : State n) (h : PCSACleanTreeCorr st) :
    PCSACleanTreeCorr (reconcile st) := by
  apply pcsa_receipt_normalize_tree
  exact h

private theorem pcsa_receipt_collect_tree {n : Nat} (st : State n) (h : PCSACleanTreeCorr st) :
    PCSACleanTreeCorr (collectPCs st) := by
  change ∀ b, b ∈ (collectPCs st).base.blocks ↔ ∃ B ∈ (collectPCs st).fg.TF, eraseFG B = b
  rw [(collectPCs_frame st).2.1, (collectPCs_frame st).2.2.2.2]
  exact h

private theorem pcsa_receipt_row_tree (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : PCSACleanTreeCorr st) : PCSACleanTreeCorr (admitRow p st a) := by
  delta admitRow
  cases a.decode? <;> dsimp only <;> first | exact h | split <;> exact h

private theorem pcsa_receipt_raw_ack_tree {n : Nat} (st : State n) (a : AckWire n)
    (h : PCSACleanTreeCorr st) : PCSACleanTreeCorr (poolAckRaw st a) := by
  change ∀ b, b ∈ (poolAckRaw st a).base.blocks ↔ ∃ B ∈ (poolAckRaw st a).fg.TF, eraseFG B = b
  rw [(poolAckRaw_frame st a).2.2.1, (poolAckRaw_frame st a).2.2.2]
  exact h

private theorem pcsa_receipt_process_tree (p : Params) (st : State p.n) (o : Wire p.n)
    (h : PCSACleanTreeCorr st) : PCSACleanTreeCorr (process p st o) := by
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : PCSACleanTreeCorr st) :
      PCSACleanTreeCorr (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc ha a _ => pcsa_receipt_raw_ack_tree acc a ha)
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : PCSACleanTreeCorr st) :
      PCSACleanTreeCorr (as.foldl (admitRow p) st) :=
    List.foldlRecOn as (admitRow p) h (fun acc ha a _ => pcsa_receipt_row_tree p acc a ha)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      change ∀ b, b ∈ (GridCO.admitVote p.toParams.engine st.base _).blocks ↔
        ∃ B ∈ st.fg.TF, eraseFG B = b
      rw [GridCO.admitVote_blocks]
      exact h
    | row i body => exact pcsa_receipt_row_tree p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hP : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · rename_i hAcc
            apply hr
            apply pcsa_receipt_collect_tree
            apply ha
            have hi := pcsa_receipt_accepted_trees p st s N P h hP hAcc
            cases N.pc <;> dsimp only
            all_goals repeat first
              | exact hi
              | (apply pcsa_receipt_reconcile_tree; exact hi)
              | split
          · exact h
    | ack s i r =>
      apply pcsa_receipt_collect_tree
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
      · exact pcsa_receipt_collect_tree _ (ha _ _ h)
      · exact h

private theorem pcsa_receipt_gate_tree (p : Params) {n : Nat} (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (h : PCSACleanTreeCorr st) :
    PCSACleanTreeCorr (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s <;> dsimp only
  · exact h
  · split
    · exact h
    · apply List.foldlRecOn (motive := PCSACleanTreeCorr)
      · exact h
      · intro acc ha b _
        apply List.foldlRecOn (motive := PCSACleanTreeCorr)
        · exact ha
        · intro acc' ha' g _
          change ∀ C, C ∈ (writeLease acc' b g
            (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine)
            rank).base.blocks ↔ ∃ B ∈ (writeLease acc' b g
              (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine) rank).fg.TF,
                eraseFG B = C
          rw [(writeLease_frame acc' b g _ rank).2.2.2.2.1,
            (writeLease_frame acc' b g _ rank).2.2.2.2.2]
          exact ha'

private theorem pcsa_receipt_clock_tree (p : Params) (st : State p.n) (t : Time)
    (h : PCSACleanTreeCorr st) : PCSACleanTreeCorr (clock p st t) := by
  have hc : PCSACleanTreeCorr (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply pcsa_receipt_normalize_tree
    split
    · exact hc
    · exact pcsa_receipt_gate_tree p _ _ _ _ _ hc
  · exact hc

/-- Every reachable store has the same base and FG block domain. -/
theorem pcsa_tree_correspondence (p : Params) (st : State p.n)
    (h : Reachable p st) : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b := by
  change PCSACleanTreeCorr st
  induction h with
  | init =>
    change ∀ b, b ∈ [Block.genesis] ↔ ∃ B ∈ ({FGBlock.genesis} : Finset _), eraseFG B = b
    simp only [List.mem_singleton, Finset.mem_singleton]
    intro b
    constructor
    · intro hb; subst b; exact ⟨_, rfl, rfl⟩
    · rintro ⟨B, rfl, he⟩; exact he.symm
  | tick t _ ih => exact pcsa_receipt_clock_tree p _ t ih
  | deliver o _ ih => exact pcsa_receipt_process_tree p _ o ih

/-- In stage 1 the full frame filter retains every stored FG block. -/
theorem pcsa_fullTree_of_frame (p : Params) (st : State p.n)
    (h : Run.FrameVacuous p st) : fullTree p st = st.fg.TF := by
  apply Finset.ext
  intro B
  rw [fullTree_def]
  change B ∈ KitFG.filteredFromView (FGSA.heightView p) (controls p st) st.fg.TF ↔ B ∈ st.fg.TF
  rw [KitFG.mem_filteredFromView]
  constructor
  · exact fun hb => hb.1
  · intro hb
    have hF : (controls p st).F = FGBlock.genesis := h.1
    rw [hF, h.2.1, h.2.2]
    exact ⟨hb, KitFG.genesis_preceq B, KitFG.genesis_preceq B,
      B, hb, KitFG.preceq_refl B, Nat.zero_le _⟩

end AvailableChain.PCSA

end

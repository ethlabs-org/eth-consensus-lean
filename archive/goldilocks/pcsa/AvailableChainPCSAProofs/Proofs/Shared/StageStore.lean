module
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotKeys
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainFGSA.Proofs.WindowStore
public import AvailableChainFGSA.Proofs.Admission

public section

/-! Store facts of the Outage lane (pcsa34-r4.3 §5.4.1 step 1, stage 1). With a
vacuous frame the full tree is `Σ.T` and F-compatibility removes nothing. The
held PC targets and the stored blocks have FG lifts in `Σ.T`, and the frozen
PCs are held PCs. -/

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG Gen.Pure

variable {n : Nat}

/-! ### A vacuous frame -/

/-- Every block is compatible with genesis. -/
theorem pcsa_compatible_genesis (b : Block) : Block.compatible b .genesis = true := by
  change (Block.preceq b .genesis || Block.preceq .genesis b) = true
  rw [show Block.preceq .genesis b = true from block_genesis_preceq b, Bool.or_true]

/-- With `F = genesis`, every block is in `act(Σ)`. -/
theorem pcsa_activeCompatible_genesis (st : State n) (hF : st.fg.F = .genesis) (b : Block) :
    activeCompatible st b = true := by
  change Block.compatible b (eraseFG st.fg.F) = true
  rw [hF]
  exact pcsa_compatible_genesis b

/-- With a vacuous frame the full filtered tree is `Σ.T`. -/
theorem pcsa_fullTree_vacuous (p : Params) (st : State p.n) (h : Run.FrameVacuous p st) :
    fullTree p st = st.fg.TF := by
  rw [Run.FrameVacuous_def] at h
  obtain ⟨hF, hZ, hlo⟩ := h
  ext B
  rw [fullTree_def, KitFG.storeFrameView_def, KitFG.mem_filteredFromView, ← controls_def]
  constructor
  · exact fun hB => hB.1
  · intro hB
    have hF' : (controls p st).F = .genesis := hF
    rw [hF', hZ, hlo]
    exact ⟨hB, KitFG.genesis_preceq B, KitFG.genesis_preceq B, B, hB, KitFG.preceq_refl B,
      Nat.zero_le _⟩

/-- With a vacuous frame a PC is frame-active iff its target has a lift in `Σ.T`. -/
theorem pcsa_frameActive_vacuous (p : Params) (st : State p.n) (h : Run.FrameVacuous p st)
    (c : PC p.n) : frameActive p st c = true ↔ ∃ B ∈ st.fg.TF, eraseFG B = c.target := by
  rw [frameActive_def, pcsa_fullTree_vacuous p st h, decide_eq_true_iff]

/-! ### Step frames -/

/-- Normalization writes only `S`. -/
theorem pcsa_normalizeS_frame (st : State n) :
    (normalizeS st).pcs = st.pcs ∧ (normalizeS st).pcSnapshot = st.pcSnapshot ∧
    (normalizeS st).ackPool = st.ackPool ∧ (normalizeS st).proposals = st.proposals ∧
    (normalizeS st).fg = st.fg ∧ (normalizeS st).base.blocks = st.base.blocks := by
  unfold normalizeS
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reconciliation filters the held and frozen PCs by `act(Σ)` and keeps the
tree, pools, proposals and FG state. -/
theorem pcsa_reconcile_frame (st : State n) :
    (reconcile st).pcs = st.pcs.filter (fun c => activeCompatible st c.target) ∧
    (reconcile st).pcSnapshot = st.pcSnapshot.map
      (fun row => (row.1, row.2.filter (fun c => activeCompatible st c.target))) ∧
    (reconcile st).ackPool = st.ackPool ∧ (reconcile st).proposals = st.proposals ∧
    (reconcile st).fg = st.fg ∧ (reconcile st).base.blocks = st.base.blocks := by
  delta reconcile
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pcsa_normalizeS_frame
    ({ st with
      base := { st.base with
        obligations := st.base.obligations.filter (fun row => activeCompatible st row.1)
        genuine := st.base.genuine.map (fun row => (row.1, row.2.filter (activeCompatible st))) }
      pcs := st.pcs.filter (fun c => activeCompatible st c.target)
      pcSnapshot := st.pcSnapshot.map
        (fun row => (row.1, row.2.filter (fun c => activeCompatible st c.target))) } : State n)
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- With `F = genesis`, reconciliation keeps every held and frozen PC. -/
theorem pcsa_reconcile_genesis (st : State n) (hF : st.fg.F = .genesis) :
    (reconcile st).pcs = st.pcs ∧ (reconcile st).pcSnapshot = st.pcSnapshot := by
  obtain ⟨h1, h2, -⟩ := pcsa_reconcile_frame st
  have hk : ∀ c : PC n, activeCompatible st c.target = true :=
    fun c => pcsa_activeCompatible_genesis st hF c.target
  refine ⟨h1.trans (List.filter_eq_self.mpr (fun c _ => hk c)), h2.trans ?_⟩
  conv_rhs => rw [← List.map_id st.pcSnapshot]
  apply List.map_congr_left
  intro row _
  rw [List.filter_eq_self.mpr (fun c _ => hk c)]
  rfl

/-- Row admission writes only the row pool. -/
theorem pcsa_admitRow_frame (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcs = st.pcs ∧ (admitRow p st a).pcSnapshot = st.pcSnapshot ∧
    (admitRow p st a).ackPool = st.ackPool ∧ (admitRow p st a).proposals = st.proposals ∧
    (admitRow p st a).fg = st.fg ∧ (admitRow p st a).base = st.base := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A row batch writes only the row pool. -/
theorem pcsa_fold_admitRow_frame (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).pcs = st.pcs ∧
    (as.foldl (admitRow p) st).pcSnapshot = st.pcSnapshot ∧
    (as.foldl (admitRow p) st).ackPool = st.ackPool ∧
    (as.foldl (admitRow p) st).proposals = st.proposals ∧
    (as.foldl (admitRow p) st).fg = st.fg ∧ (as.foldl (admitRow p) st).base = st.base := by
  induction as generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a as ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pcsa_admitRow_frame p st a
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (admitRow p st a)
    rw [List.foldl_cons]
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4, g5.trans h5, g6.trans h6⟩

/-- Raw ack pooling writes only the ack pool. -/
theorem pcsa_poolAckRaw_frame (st : State n) (a : AckWire n) :
    (poolAckRaw st a).pcs = st.pcs ∧ (poolAckRaw st a).pcSnapshot = st.pcSnapshot ∧
    (poolAckRaw st a).proposals = st.proposals ∧
    (poolAckRaw st a).fg = st.fg ∧ (poolAckRaw st a).base = st.base := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A raw ack batch writes only the ack pool, and pools every decoded ack. -/
theorem pcsa_fold_poolAckRaw_frame (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).pcs = st.pcs ∧
    (as.foldl poolAckRaw st).pcSnapshot = st.pcSnapshot ∧
    (as.foldl poolAckRaw st).proposals = st.proposals ∧
    (as.foldl poolAckRaw st).fg = st.fg ∧ (as.foldl poolAckRaw st).base = st.base ∧
    st.ackPool ⊆ (as.foldl poolAckRaw st).ackPool ∧
    (∀ a ∈ as, (a.decode?).isSome → a ∈ (as.foldl poolAckRaw st).ackPool) := by
  induction as generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, List.Subset.refl _, by simp⟩
  | cons a as ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := pcsa_poolAckRaw_frame st a
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := ih (poolAckRaw st a)
    rw [List.foldl_cons]
    refine ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4, g5.trans h5,
      List.Subset.trans (poolAckRaw_mono st a) g6, ?_⟩
    intro b hb hd
    rcases List.mem_cons.mp hb with rfl | hb
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd
      rcases v with ⟨s, i, r⟩
      exact g6 (poolAckRaw_mem st b s i r hv)
    · exact g7 b hb hd

/-- PC collection keeps the proposals. -/
theorem pcsa_collectPCs_proposals (st : State n) :
    (collectPCs st).proposals = st.proposals :=
  collectPCs_preserves State.proposals (fun s c => by
    unfold installPC deleteConflictingLeases
    split <;> rfl) st

/-! ### The clock -/

/-- A gate writes no held or frozen PC, pool, proposal, tree, or FG field. -/
theorem pcsa_gateFrom_frame (p : Params) (a : Block) (cs : List (PC n)) (ρ : Option PCRank)
    (st : State n) (s : Slot) :
    (gateFrom p a cs ρ st s).pcs = st.pcs ∧
    (gateFrom p a cs ρ st s).pcSnapshot = st.pcSnapshot ∧
    (gateFrom p a cs ρ st s).ackPool = st.ackPool ∧
    (gateFrom p a cs ρ st s).proposals = st.proposals ∧
    (gateFrom p a cs ρ st s).fg = st.fg ∧
    (gateFrom p a cs ρ st s).base.blocks = st.base.blocks := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · apply List.foldlRecOn (motive := fun a : State n => a.pcs = st.pcs ∧
        a.pcSnapshot = st.pcSnapshot ∧ a.ackPool = st.ackPool ∧ a.proposals = st.proposals ∧
        a.fg = st.fg ∧ a.base.blocks = st.base.blocks)
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun a : State n => a.pcs = st.pcs ∧
          a.pcSnapshot = st.pcSnapshot ∧ a.ackPool = st.ackPool ∧ a.proposals = st.proposals ∧
          a.fg = st.fg ∧ a.base.blocks = st.base.blocks)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- The pre-gate clock writes no held PC, pool, proposal, tree, or FG field. -/
theorem pcsa_clockPre_frame (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).pcs = st.pcs ∧ (clockPre p st t).ackPool = st.ackPool ∧
    (clockPre p st t).proposals = st.proposals ∧ (clockPre p st t).fg = st.fg ∧
    (clockPre p st t).base.blocks = st.base.blocks := by
  unfold clockPre
  dsimp only
  split <;> split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The clock writes no held PC, pool, proposal, tree, or FG field. -/
theorem pcsa_clock_frame (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).pcs = st.pcs ∧ (clock p st t).ackPool = st.ackPool ∧
    (clock p st t).proposals = st.proposals ∧ (clock p st t).fg = st.fg ∧
    (clock p st t).base.blocks = st.base.blocks := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pcsa_clockPre_frame p st t
  unfold clock
  dsimp only
  split
  · unfold gateStep
    dsimp only
    obtain ⟨n1, -, n3, n4, n5, n6⟩ := pcsa_normalizeS_frame
      (if (GridCO.savedGenuine (clockPre p st t).base
          ((t - 6 * p.Δ) / (4 * p.Δ)).toNat).isSome then clockPre p st t else
        gateFrom p (eraseFG (clockPre p st t).fg.F) (clockPre p st t).pcs
          (gateRank p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)
          (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)
    rw [n1, n3, n4, n5, n6]
    split
    · exact ⟨h1, h2, h3, h4, h5⟩
    · obtain ⟨g1, -, g3, g4, g5, g6⟩ := pcsa_gateFrom_frame p (eraseFG (clockPre p st t).fg.F)
        (clockPre p st t).pcs
        (gateRank p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat)
        (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
      exact ⟨g1.trans h1, g3.trans h2, g4.trans h3, g5.trans h4, g6.trans h5⟩
  · exact ⟨h1, h2, h3, h4, h5⟩

/-- The clock keeps every stored frozen row and adds at most one row, of the
current held PCs. -/
theorem pcsa_clock_snapshot (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).pcSnapshot = st.pcSnapshot ∨
      ∃ k, (clock p st t).pcSnapshot = st.pcSnapshot ++ [(k, st.pcs)] ∧
        st.pcSnapshot.find? (fun row => row.1 == k) = none := by
  have he : (clock p st t).pcSnapshot = (clockPre p st t).pcSnapshot := by
    unfold clock
    dsimp only
    split
    · exact gateStep_snapshot _ _ _
    · rfl
  rw [he, clockPre_snapshot]
  dsimp only
  split
  · split
    · exact Or.inl rfl
    · rename_i hs
      refine Or.inr ⟨_, rfl, ?_⟩
      cases hf : st.pcSnapshot.find? (fun row => row.1 == ((t - 3 * p.Δ) / (4 * p.Δ)).toNat)
      · rfl
      · rw [hf] at hs
        exact absurd rfl hs
  · exact Or.inl rfl

/-! ### Block admission facts -/

/-- Vote admission keeps the block list. -/
theorem pcsa_admitVote_blocks (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) : (GridCO.admitVote q v o).blocks = v.blocks := by
  delta GridCO.admitVote
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> dsimp only
  split_ifs <;> rfl

/-- The carried-vote fold keeps the block list. -/
theorem pcsa_foldVotes_blocks (q : GridCO.Params) (raw : List (GridCO.HeadWire n .root))
    (w : GridCO.State n .root) :
    (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) w).blocks =
      w.blocks := by
  induction raw generalizing w with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, pcsa_admitVote_blocks]

/-- Proposal admission adds at most its own block. -/
theorem pcsa_admitProposal_blocks (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root)) (x : Block)
    (hx : x ∈ (GridCO.admitProposal q v o b raw).blocks) : x ∈ v.blocks ∨ x = b := by
  delta GridCO.admitProposal at hx
  dsimp only at hx
  split_ifs at hx
  · exact Or.inl hx
  · rw [pcsa_foldVotes_blocks] at hx
    simpa only [List.mem_append, List.mem_singleton] using hx

/-- Proposal admission keeps every stored block. -/
theorem pcsa_admitProposal_blocks_mono (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (b : Block) (raw : List (GridCO.HeadWire n .root)) :
    v.blocks ⊆ (GridCO.admitProposal q v o b raw).blocks := by
  delta GridCO.admitProposal
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · rw [pcsa_foldVotes_blocks]
    exact List.subset_append_left _ _

/-- The acceptance facts that the Outage lane reads. -/
theorem pcsa_blockAccepted_facts (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (h : blockAccepted p st s N P = true) :
    N.erase ≠ .genesis ∧ FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) = true ∧
      N.erase.parent.slot < N.erase.slot ∧ rowsOk N.erase N.rows = true := by
  delta blockAccepted at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, -⟩, -⟩, hF⟩, hps⟩, -⟩, -⟩, -⟩, hc⟩ := h
  refine ⟨hg, hF, hps, ?_⟩
  change (rowsOk N.erase N.rows && _) = true at hc
  exact (Bool.and_eq_true_iff.mp hc).1

/-- The FG block of an accepted wire block erases to it. -/
theorem pcsa_eraseFG_fgBlock {P : FGBlock (Fin n)} {b : Block} (hb : b ≠ .genesis)
    (hP : eraseFG P = b.parent) (rows : List (RowWire n)) (hrows : rowsOk b rows = true) :
    eraseFG (fgBlock P b rows) = b := by
  cases b with
  | genesis => exact absurd rfl hb
  | node q s r x =>
    have hx : x = packBody (appOf x) rows := beq_iff_eq.mp hrows
    change Block.node (eraseFG P) s r (packBody (appOf x) rows) = Block.node q s r x
    have hq : eraseFG P = q := hP
    rw [hq, ← hx]

/-- The FG window inserts an accepted block. -/
theorem pcsa_on_block_TF (p : Params) (st : SimplexFG.Store (Fin p.n)) (B : FGBlock (Fin p.n))
    (hP : B.parent ∈ st.TF) (hF : FGBlock.preceq st.F B = true)
    (hs : B.parent.slot < B.slot) :
    (FGSA.Window.on_block p p.K_W st B).TF = insert B st.TF := by
  rw [FGSA.Window.on_block_def]
  split
  · rename_i hc
    rcases hc with hc | hc | hc | hc
    · exact (Finset.insert_eq_of_mem hc).symm
    · exact absurd hP hc
    · rw [hF] at hc; exact absurd hc (by simp)
    · exact absurd hc (Nat.not_le.mpr hs)
  · exact FGSA.Window.window_update_finality_TF _ _ _ _

/-- The FG window never removes a block of `Σ.T`. -/
theorem pcsa_on_block_TF_mono (p : Params) (st : SimplexFG.Store (Fin p.n))
    (B : FGBlock (Fin p.n)) : st.TF ⊆ (FGSA.Window.on_block p p.K_W st B).TF := by
  rw [FGSA.Window.on_block_def]
  split
  · exact Finset.Subset.refl _
  · rw [FGSA.Window.window_update_finality_TF]
    exact Finset.subset_insert _ _

/-! ### The Outage store invariant -/

/-- [pcsa34-r4.3 §5.4.1] Store facts of the Outage lane at one node: each
stored block has an FG lift in `Σ.T`; each block of `Σ.T` erases to a block
with the run property `R`; each held PC target is stored; each frozen PC is
held; each decoded ack of a stored proposal's PC is pooled. -/
structure OutageStore (R : Block → Prop) (st : State n) : Prop where
  lift : ∀ b ∈ st.base.blocks, ∃ B ∈ st.fg.TF, eraseFG B = b
  tf : ∀ B ∈ st.fg.TF, R (eraseFG B)
  pcBlocks : ∀ d ∈ st.pcs, d.target ∈ st.base.blocks
  snapSub : ∀ row ∈ st.pcSnapshot, ∀ d ∈ row.2, d ∈ st.pcs
  carried : ∀ o ∈ st.proposals, ∀ s (N : NamedProposal n), o.decode = some (.block s N) →
    ∀ a ∈ N.pcAcks, (a.decode?).isSome → a ∈ st.ackPool

/-- The initial store satisfies the invariant when genesis has the run property. -/
theorem pcsa_initial_outageStore (R : Block → Prop) (hg : R .genesis) :
    OutageStore R (initial n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hbl : (initial n).base.blocks = [.genesis] := rfl
    rw [hbl, List.mem_singleton] at hb
    exact ⟨.genesis, Finset.mem_singleton_self _, hb.symm⟩
  · intro B hB
    have hTF : (initial n).fg.TF = {.genesis} := rfl
    rw [hTF, Finset.mem_singleton] at hB
    subst hB
    exact hg
  · intro d hd
    exact absurd hd List.not_mem_nil
  · intro row hr
    exact absurd hr List.not_mem_nil
  · intro o ho
    exact absurd ho List.not_mem_nil

/-- PC installation keeps the invariant. -/
theorem pcsa_installPC_outageStore (R : Block → Prop) (st : State n) (c : PC n)
    (h : OutageStore R st) (hv : pcValid st c = true) : OutageStore R (installPC st c) := by
  obtain ⟨hn, hb, ha, hs, hf⟩ := installPC_frame st c
  have hp : (installPC st c).proposals = st.proposals := by
    unfold installPC deleteConflictingLeases
    split <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, hf]; exact h.lift
  · rw [hf]; exact h.tf
  · intro d hd
    rw [hb]
    rcases mem_installPC_pcs st c d hd with hd | rfl
    · exact h.pcBlocks d hd
    · exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
  · rw [hs]
    intro row hr d hd
    exact installPC_pcs_mono st c (h.snapSub row hr d hd)
  · rw [hp, ha]; exact h.carried

/-- PC collection keeps the invariant. -/
theorem pcsa_collectPCs_outageStore (R : Block → Prop) (st : State n)
    (h : OutageStore R st) : OutageStore R (collectPCs st) :=
  collectPCs_invariant (OutageStore R) (pcsa_installPC_outageStore R) st h

/-- A row batch keeps the invariant. -/
theorem pcsa_fold_admitRow_outageStore (p : Params) (R : Block → Prop) (st : State p.n)
    (as : List (RowWire p.n)) (h : OutageStore R st) :
    OutageStore R (as.foldl (admitRow p) st) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pcsa_fold_admitRow_frame p st as
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h6, h5]; exact h.lift
  · rw [h5]; exact h.tf
  · rw [h1, h6]; exact h.pcBlocks
  · rw [h2, h1]; exact h.snapSub
  · rw [h4, h3]; exact h.carried

/-- A raw ack batch keeps the invariant. -/
theorem pcsa_fold_poolAckRaw_outageStore (R : Block → Prop) (st : State n)
    (as : List (AckWire n)) (h : OutageStore R st) :
    OutageStore R (as.foldl poolAckRaw st) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := pcsa_fold_poolAckRaw_frame st as
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h5, h4]; exact h.lift
  · rw [h4]; exact h.tf
  · rw [h1, h5]; exact h.pcBlocks
  · rw [h2, h1]; exact h.snapSub
  · rw [h3]
    intro o ho s N hd a ha hda
    exact h6 (h.carried o ho s N hd a ha hda)

/-- The admission tail (reconcile, carried acks, collection, carried rows)
keeps the invariant once the new wire's acks are pooled. -/
theorem pcsa_admitBlock_tail (p : Params) (R : Block → Prop) (st st1 : State p.n)
    (w : Wire p.n) (s : Slot) (N : NamedProposal p.n) (C : Prop) [Decidable C]
    (hlift : ∀ b ∈ st1.base.blocks, ∃ B ∈ st1.fg.TF, eraseFG B = b)
    (htf : ∀ B ∈ st1.fg.TF, R (eraseFG B))
    (hpc : ∀ d ∈ st1.pcs, d.target ∈ st1.base.blocks)
    (hsnap : ∀ row ∈ st1.pcSnapshot, ∀ d ∈ row.2, d ∈ st1.pcs)
    (hprop : st1.proposals = st.proposals ++ [w]) (hw : w.decode = some (.block s N))
    (hcar : ∀ o ∈ st.proposals, ∀ s' (N' : NamedProposal p.n), o.decode = some (.block s' N') →
      ∀ a ∈ N'.pcAcks, (a.decode?).isSome → a ∈ st1.ackPool) :
    OutageStore R (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))) := by
  apply pcsa_fold_admitRow_outageStore
  apply pcsa_collectPCs_outageStore
  have h2 : (∀ b ∈ (if C then st1 else reconcile st1).base.blocks,
        ∃ B ∈ (if C then st1 else reconcile st1).fg.TF, eraseFG B = b) ∧
      (∀ B ∈ (if C then st1 else reconcile st1).fg.TF, R (eraseFG B)) ∧
      (∀ d ∈ (if C then st1 else reconcile st1).pcs,
        d.target ∈ (if C then st1 else reconcile st1).base.blocks) ∧
      (∀ row ∈ (if C then st1 else reconcile st1).pcSnapshot, ∀ d ∈ row.2,
        d ∈ (if C then st1 else reconcile st1).pcs) ∧
      (if C then st1 else reconcile st1).proposals = st.proposals ++ [w] ∧
      (if C then st1 else reconcile st1).ackPool = st1.ackPool := by
    split
    · exact ⟨hlift, htf, hpc, hsnap, hprop, rfl⟩
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := pcsa_reconcile_frame st1
      rw [r1, r2, r3, r4, r5, r6]
      refine ⟨hlift, htf, ?_, ?_, hprop, rfl⟩
      · intro d hd
        exact hpc d (List.mem_filter.mp hd).1
      · intro row hr d hd
        obtain ⟨row', hr', rfl⟩ := List.mem_map.mp hr
        have hd' := List.mem_filter.mp hd
        exact List.mem_filter.mpr ⟨hsnap row' hr' d hd'.1, hd'.2⟩
  generalize (if C then st1 else reconcile st1) = st2 at h2
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h2
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := pcsa_fold_poolAckRaw_frame st2 N.pcAcks
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f5, f4]; exact g1
  · rw [f4]; exact g2
  · rw [f1, f5]; exact g3
  · rw [f2, f1]; exact g4
  · rw [f3, g5]
    intro o ho s' N' hd a ha hda
    rcases List.mem_append.mp ho with ho | ho
    · exact f6 (g6 ▸ hcar o ho s' N' hd a ha hda)
    · rw [List.mem_singleton.mp ho, hw] at hd
      have hN : N = N' := by
        have := Option.some.inj hd
        injection this
      subst hN
      exact f7 a ha hda

/-- Block admission keeps the invariant when the offered block has the run property. -/
theorem pcsa_admitBlock_outageStore (p : Params) (R : Block → Prop) (st : State p.n)
    (s : Slot) (N : NamedProposal p.n) (h : OutageStore R st) (hR : R N.erase) :
    OutageStore R (admitBlock p st s N) := by
  delta admitBlock
  split
  · exact h
  · cases hP : parentFG st N.erase with
    | none => exact h
    | some P =>
      dsimp only
      split
      · rename_i hacc
        obtain ⟨hg, hF, hps, hrows⟩ := pcsa_blockAccepted_facts p st s N P hacc
        obtain ⟨hPT, hPe⟩ := FGSA.pickPair_some_spec _ _ hP
        have hPe' : eraseFG P = N.erase.parent := of_decide_eq_true hPe
        have hTF : (FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF =
            insert (fgBlock P N.erase N.rows) st.fg.TF := by
          apply pcsa_on_block_TF p st.fg (fgBlock P N.erase N.rows)
            (show (fgBlock P N.erase N.rows).parent ∈ st.fg.TF from hPT) hF
          change P.slot < N.erase.slot
          have : (eraseFG P).slot = P.slot := by
            rw [pcsa_eraseFG_eq]; exact FGSA.eraseFG_slot P
          rw [← this, hPe']
          exact hps
        have hE := pcsa_eraseFG_fgBlock hg hPe' N.rows hrows
        refine pcsa_admitBlock_tail p R st _ ⟨.proposer s, .proposal N⟩ s N _ ?_ ?_ ?_ ?_ ?_ rfl ?_
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try simp only [deleteConflictingLeases_def])
          all_goals
            rw [hTF]
            intro b hb
            rcases pcsa_admitProposal_blocks _ _ _ _ _ b hb with hb | rfl
            · obtain ⟨B, hB, he⟩ := h.lift b hb
              exact ⟨B, Finset.mem_insert_of_mem hB, he⟩
            · exact ⟨_, Finset.mem_insert_self _ _, hE⟩
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try simp only [deleteConflictingLeases_def])
          all_goals
            rw [hTF]
            intro B hB
            rcases Finset.mem_insert.mp hB with rfl | hB
            · rw [hE]; exact hR
            · exact h.tf B hB
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try simp only [deleteConflictingLeases_def])
          all_goals
            intro d hd
            exact pcsa_admitProposal_blocks_mono _ _ _ _ _ (h.pcBlocks d hd)
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try simp only [deleteConflictingLeases_def])
          all_goals exact h.snapSub
        · rfl
        · cases N.pc <;> dsimp only <;> (try split_ifs) <;>
            (try simp only [deleteConflictingLeases_def])
          all_goals exact h.carried
      · exact h

/-- Checked ack pooling writes only the ack pool. -/
theorem pcsa_poolAck_frame (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).pcs = st.pcs ∧ (poolAck p st a).pcSnapshot = st.pcSnapshot ∧
    (poolAck p st a).proposals = st.proposals ∧
    (poolAck p st a).fg = st.fg ∧ (poolAck p st a).base = st.base := by
  delta poolAck
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · rename_i v
    rcases v with ⟨_, _, _⟩
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A delivery keeps the invariant when every offered block has the run property. -/
theorem pcsa_process_outageStore (p : Params) (R : Block → Prop) (st : State p.n)
    (o : Wire p.n) (h : OutageStore R st)
    (hR : ∀ s N, o.decode = some (.block s N) → R N.erase) :
    OutageStore R (process p st o) := by
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      delta admitHead
      refine ⟨?_, h.tf, ?_, h.snapSub, h.carried⟩
      · change ∀ b ∈ (GridCO.admitVote _ st.base _).blocks, _
        rw [pcsa_admitVote_blocks]
        exact h.lift
      · change ∀ d ∈ st.pcs, d.target ∈ (GridCO.admitVote _ st.base _).blocks
        rw [pcsa_admitVote_blocks]
        exact h.pcBlocks
    | row i body =>
      dsimp only
      exact pcsa_fold_admitRow_outageStore p R st [_] h
    | block s N =>
      dsimp only
      exact pcsa_admitBlock_outageStore p R st s N h (hR s N hd)
    | ack s i r =>
      dsimp only
      delta admitAck
      apply pcsa_collectPCs_outageStore
      obtain ⟨h1, h2, h3, h4, h5⟩ := pcsa_poolAck_frame p st ⟨o.auth, r⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [h5, h4]; exact h.lift
      · rw [h4]; exact h.tf
      · rw [h1, h5]; exact h.pcBlocks
      · rw [h2, h1]; exact h.snapSub
      · rw [h3]
        intro o ho s N hd a ha hda
        exact poolAck_mono p st _ (h.carried o ho s N hd a ha hda)
    | pc d =>
      dsimp only
      delta admitPC
      split
      · exact pcsa_collectPCs_outageStore R _ (pcsa_fold_poolAckRaw_outageStore R st _ h)
      · exact h
  | none => exact h

/-- The clock keeps the invariant. -/
theorem pcsa_clock_outageStore (p : Params) (R : Block → Prop) (st : State p.n) (t : Time)
    (h : OutageStore R st) : OutageStore R (clock p st t) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pcsa_clock_frame p st t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h5, h4]; exact h.lift
  · rw [h4]; exact h.tf
  · rw [h1, h5]; exact h.pcBlocks
  · rw [h1]
    rcases pcsa_clock_snapshot p st t with hs | ⟨k, hs, -⟩
    · rw [hs]; exact h.snapSub
    · rw [hs]
      intro row hr d hd
      rcases List.mem_append.mp hr with hr | hr
      · exact h.snapSub row hr d hd
      · rw [List.mem_singleton.mp hr] at hd
        exact hd
  · rw [h3, h2]; exact h.carried

/-! ### Stage-1 monotonicity -/

/-- The admission tail keeps every held and frozen PC when its final `F` is genesis. -/
theorem pcsa_admitBlock_tail_genesis (p : Params) (st st1 : State p.n) (C : Prop) [Decidable C]
    (rows : List (RowWire p.n)) (acks : List (AckWire p.n))
    (hpcs : st1.pcs = st.pcs) (hsnap : st1.pcSnapshot = st.pcSnapshot)
    (hF : (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).fg.F = .genesis) :
    st.pcs ⊆ (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).pcs ∧
    (rows.foldl (admitRow p) (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1)))).pcSnapshot = st.pcSnapshot := by
  obtain ⟨r1, r2, -, -, r5, -⟩ := pcsa_fold_admitRow_frame p (collectPCs (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1))) rows
  obtain ⟨-, -, -, c4, c5⟩ := collectPCs_frame (acks.foldl poolAckRaw
      (if C then st1 else reconcile st1))
  obtain ⟨a1, a2, -, a4, -⟩ := pcsa_fold_poolAckRaw_frame (if C then st1 else reconcile st1) acks
  rw [r5, c5, a4] at hF
  rw [r1, r2, c4, a2, ← hpcs, ← hsnap]
  have hm := collectPCs_pcs_mono (acks.foldl poolAckRaw (if C then st1 else reconcile st1))
  rw [a1] at hm
  by_cases hc : C
  · rw [ite_eq_left hc] at hm ⊢
    exact ⟨hm, rfl⟩
  · rw [ite_eq_right hc] at hm hF ⊢
    rw [(pcsa_reconcile_frame st1).2.2.2.2.1] at hF
    obtain ⟨g1, g2⟩ := pcsa_reconcile_genesis st1 hF
    rw [g1] at hm
    exact ⟨hm, g2⟩

/-- In a stage-1 step (`F` genesis after the delivery), a delivery keeps every
held PC and the frozen PC rows. -/
theorem pcsa_process_stageOne (p : Params) (st : State p.n) (o : Wire p.n)
    (hF : (process p st o).fg.F = .genesis) :
    st.pcs ⊆ (process p st o).pcs ∧ (process p st o).pcSnapshot = st.pcSnapshot := by
  revert hF
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      intro _
      exact ⟨List.Subset.refl _, rfl⟩
    | row i body =>
      intro _
      dsimp only
      obtain ⟨h1, h2, -⟩ := pcsa_admitRow_frame p st ⟨o.auth, body⟩
      rw [h1, h2]
      exact ⟨List.Subset.refl _, rfl⟩
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · intro _; exact ⟨List.Subset.refl _, rfl⟩
      · cases hP : parentFG st N.erase with
        | none => intro _; exact ⟨List.Subset.refl _, rfl⟩
        | some P =>
          dsimp only
          split
          · intro hF
            refine pcsa_admitBlock_tail_genesis p st _ _ N.rows N.pcAcks ?_ ?_ hF
            · cases N.pc <;> dsimp only; split_ifs <;> rfl
            · cases N.pc <;> dsimp only; split_ifs <;> rfl
          · intro _; exact ⟨List.Subset.refl _, rfl⟩
    | ack s i r =>
      intro _
      dsimp only
      delta admitAck
      obtain ⟨h1, h2, -⟩ := pcsa_poolAck_frame p st ⟨o.auth, r⟩
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact collectPCs_pcs_mono _
      · rw [(collectPCs_frame _).2.2.2.1, h2]
    | pc d =>
      intro _
      dsimp only
      delta admitPC
      split
      · obtain ⟨h1, h2, -⟩ := pcsa_fold_poolAckRaw_frame st d.acks
        refine ⟨?_, ?_⟩
        · rw [← h1]; exact collectPCs_pcs_mono _
        · rw [(collectPCs_frame _).2.2.2.1, h2]
      · exact ⟨List.Subset.refl _, rfl⟩
  | none => intro _; exact ⟨List.Subset.refl _, rfl⟩

/-- A stored frozen row keeps its PCs through the clock. -/
theorem pcsa_clock_pcSnapshotAt (p : Params) (st : State p.n) (t : Time) (k : Slot)
    (hk : (st.pcSnapshot.find? (fun row => row.1 == k)).isSome) :
    pcSnapshotAt (clock p st t) k = pcSnapshotAt st k ∧
      ((clock p st t).pcSnapshot.find? (fun row => row.1 == k)).isSome := by
  rcases pcsa_clock_snapshot p st t with hs | ⟨k', hs, -⟩
  · rw [pcSnapshotAt_eq_of_list_eq _ _ k hs, hs]
    exact ⟨rfl, hk⟩
  · obtain ⟨row, hrow⟩ := Option.isSome_iff_exists.mp hk
    have hf : (clock p st t).pcSnapshot.find? (fun row => row.1 == k) = some row := by
      rw [hs, List.find?_append, hrow]
      rfl
    refine ⟨?_, by rw [hf]; rfl⟩
    dsimp only [pcSnapshotAt]
    rw [hf, hrow]

end AvailableChain.PCSA
end

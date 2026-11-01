module
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotKeys
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainFGSA.Proofs.WindowStore
public import AvailableChainFGSA.Proofs.Admission

public section

/-! C6 RelayFrames: concrete receipt and count support. -/
namespace AvailableChain.PCSA.CleanPCRelay
open AvailableChain.SimplexFG Gen.Pure
variable {n : Nat}

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

end AvailableChain.PCSA.CleanPCRelay

end

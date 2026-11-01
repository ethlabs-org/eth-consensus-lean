module
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks

public section

/-! Body scope for honest ack checks and target receipt. -/

namespace AvailableChain.PCSA

private def CleanBodyScope {n : Nat} (B : Block → Prop) (st : State n) : Prop :=
  ∀ b ∈ st.base.blocks, B b

private theorem pcsa_clean_grid_vote_scope {n : Nat} (q : GridCO.Params)
    (B : Block → Prop) (v : GridCO.State n .root) (o : GridCO.Wire n .root)
    (h : ∀ b ∈ v.blocks, B b) : ∀ b ∈ (GridCO.admitVote q v o).blocks, B b := by
  rw [GridCO.admitVote_blocks]
  exact h

private theorem pcsa_clean_grid_proposal_scope {n : Nat} (q : GridCO.Params)
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
      exact pcsa_clean_grid_vote_scope q B acc _ ha

private theorem pcsa_clean_normalize_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : CleanBodyScope B st) : CleanBodyScope B (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem pcsa_clean_reconcile_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : CleanBodyScope B st) : CleanBodyScope B (reconcile st) := by
  apply pcsa_clean_normalize_scope
  exact h

private theorem pcsa_clean_collect_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : CleanBodyScope B st) : CleanBodyScope B (collectPCs st) := by
  change ∀ b ∈ (collectPCs st).base.blocks, B b
  rw [(collectPCs_frame st).2.1]
  exact h

private theorem pcsa_clean_row_scope (p : Params) (B : Block → Prop) (st : State p.n)
    (a : RowWire p.n) (h : CleanBodyScope B st) :
    CleanBodyScope B (admitRow p st a) := by
  delta admitRow
  cases a.decode? <;> dsimp only <;> first | exact h | split <;> exact h

private theorem pcsa_clean_raw_ack_scope {n : Nat} (B : Block → Prop) (st : State n)
    (a : AckWire n) (h : CleanBodyScope B st) : CleanBodyScope B (poolAckRaw st a) := by
  change ∀ b ∈ (poolAckRaw st a).base.blocks, B b
  rw [(poolAckRaw_frame st a).2.2.1]
  exact h

private theorem pcsa_clean_process_scope (p : Params) (B : Block → Prop) (st : State p.n)
    (o : Wire p.n) (h : CleanBodyScope B st)
    (ho : ∀ s N, o.decode = some (.block s N) → B N.erase) :
    CleanBodyScope B (process p st o) := by
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : CleanBodyScope B st) :
      CleanBodyScope B (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc ha a _ => pcsa_clean_raw_ack_scope B acc a ha)
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : CleanBodyScope B st) :
      CleanBodyScope B (as.foldl (admitRow p) st) :=
    List.foldlRecOn as (admitRow p) h (fun acc ha a _ => pcsa_clean_row_scope p B acc a ha)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact pcsa_clean_grid_vote_scope p.toParams.engine B st.base _ h
    | row i body => exact pcsa_clean_row_scope p B st _ h
    | block s N =>
      have hb := ho s N hd
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply hr
            apply pcsa_clean_collect_scope
            apply ha
            have hbase := pcsa_clean_grid_proposal_scope p.toParams.engine B st.base
              (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) h hb
            cases N.pc <;> dsimp only
            all_goals repeat first
              | exact hbase
              | (apply pcsa_clean_reconcile_scope; exact hbase)
              | split
          · exact h
    | ack s i r =>
      apply pcsa_clean_collect_scope
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
      · exact pcsa_clean_collect_scope B _ (ha _ _ h)
      · exact h

private theorem pcsa_clean_gate_scope (p : Params) {n : Nat} (B : Block → Prop)
    (st : State n) (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot)
    (h : CleanBodyScope B st) : CleanBodyScope B (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s <;> dsimp only
  · exact h
  · split
    · exact h
    · apply List.foldlRecOn (motive := CleanBodyScope B)
      · exact h
      · intro acc ha b _
        apply List.foldlRecOn (motive := CleanBodyScope B)
        · exact ha
        · intro acc' ha' g _
          change ∀ C ∈ (writeLease acc' b g
            (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine)
            rank).base.blocks, B C
          rw [(writeLease_frame acc' b g _ rank).2.2.2.2.1]
          exact ha'

/-- Clock steps keep every stored body within its original scope. -/
theorem pcsa_clock_body_scope (p : Params) (B : Block → Prop)
    (st : State p.n) (t : Time) (h : ∀ b ∈ st.base.blocks, B b) :
    ∀ b ∈ (clock p st t).base.blocks, B b := by
  have hc : CleanBodyScope B (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply pcsa_clean_normalize_scope
    split
    · exact hc
    · exact pcsa_clean_gate_scope p B _ _ _ _ _ hc
  · exact hc

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem pcsa_clean_named_refl (N : NamedProposal p.n) : NamedProposal.Preceq N N := by
  cases N with
  | genesis => rfl
  | node P s root body raw support rows pc =>
    change (decide (NamedProposal.node P s root body raw support rows pc =
      NamedProposal.node P s root body raw support rows pc) ||
      NamedProposal.preceq (.node P s root body raw support rows pc) P) = true
    exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true rfl))

private theorem pcsa_clean_decode_proposal (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta toWire toAuth Wire.decode at h <;> cases h
  | seat l i =>
    cases l with
    | prop k =>
      cases payload <;> delta toWire toAuth Wire.decode at h
      all_goals cases h <;> rfl
    | base l =>
      cases l <;> cases payload <;> delta toWire toAuth Wire.decode Label.ackSlot? at h <;> cases h

/-- Every stored body in an honest run state is in the named collision scope. -/
theorem pcsa_body_scope (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (x : V) (hx : x ∈ rho.honest) :
    ∀ b ∈ (V2.D.Run.stateBefore E rho j x).st.base.blocks, RootBlockInRun p c E rho b := by
  have hg : RootBlockInRun p c E rho .genesis := by
    refine ⟨.genesis, ⟨.genesis, Or.inr ⟨x, hx, 0, ?_⟩, pcsa_clean_named_refl _⟩, rfl⟩
    change (NamedProposal.genesis : NamedProposal p.n) ∈ [NamedProposal.genesis]
    exact List.mem_singleton_self _
  have hz : CleanBodyScope (RootBlockInRun p c E rho) (initial p.n) := by
    change ∀ b ∈ [Block.genesis], RootBlockInRun p c E rho b
    intro b hb
    exact List.mem_singleton.mp hb ▸ hg
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => CleanBodyScope (RootBlockInRun p c E rho) nd.st)
    (Nat.zero_le j) x ?_ hz
  intro k e _ _ he hn h
  cases e with
  | restart y t =>
    change y = x at hn
    subst y
    change CleanBodyScope _ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    exact hz
  | tick y t =>
    change y = x at hn
    subst y
    change CleanBodyScope _ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    have hf : CleanBodyScope (RootBlockInRun p c E rho)
        (clock p (V2.D.Run.stateBefore E rho k x).st t) :=
      pcsa_clock_body_scope p _ _ t h
    exact ht.symm ▸ hf
  | deliver y o t =>
    change y = x at hn
    subst y
    change CleanBodyScope _ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    apply pcsa_clean_process_scope p _ _ (toWire p o) h
    intro s N hd
    exact ⟨N, ⟨N, Or.inl ⟨x, o, t, List.mem_of_getElem? he,
      pcsa_clean_decode_proposal o s N hd⟩, pcsa_clean_named_refl N⟩, rfl⟩

/-- The collision premise identifies equal roots of scoped blocks. -/
theorem pcsa_scoped_root_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : NamedRootCollisionFree p c E rho)
    (A B : Block) (hA : RootBlockInRun p c E rho A) (hB : RootBlockInRun p c E rho B)
    (he : A.root = B.root) : A = B := by
  obtain ⟨N, hN, rfl⟩ := hA
  obtain ⟨M, hM, rfl⟩ := hB
  have hr : N.root = M.root := by
    have er (P : NamedProposal p.n) : P.erase.root = P.root := by cases P <;> rfl
    simpa only [er] using he
  have hn := h.root_injective N M hN hM N M
    (Or.inl (pcsa_clean_named_refl N)) (Or.inr (pcsa_clean_named_refl M)) hr
  exact congrArg NamedProposal.erase hn

end AvailableChain.PCSA.Run
end

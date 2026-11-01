module
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSA.Model.Frame

public section

/-! The stored proposal wires (FG finality safety, step P5). The list only
grows. A delivery appends at most its own proposal wire. A clock keeps it. -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- A wire that decodes to a proposal is that proposal wire. -/
theorem pcsa_wire_decode_block (w : Wire n) (s : Slot) (N : NamedProposal n)
    (h : w.decode = some (.block s N)) : w = ⟨.proposer s, .proposal N⟩ := by
  rcases w with ⟨auth, payload⟩
  cases auth with
  | seat l i => cases l <;> cases payload <;> simp [Wire.decode] at h
  | proposer k =>
      cases payload <;> simp [Wire.decode] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      rfl
  | none => cases payload <;> simp [Wire.decode] at h

/-- A wire with a named payload is that proposal wire. -/
theorem pcsa_wire_proposal_some (w : Wire n) (N : NamedProposal n)
    (h : w.proposal? = some N) : ∃ s, w = ⟨.proposer s, .proposal N⟩ := by
  rw [Wire.proposal?] at h
  cases hd : w.decode with
  | none =>
      rw [hd] at h
      cases h
  | some x =>
      rw [hd] at h
      cases x with
      | block s M =>
          have hMN : M = N := Option.some.inj h
          subst hMN
          exact ⟨s, pcsa_wire_decode_block w s M hd⟩
      | vote s i b => cases h
      | row i body => cases h
      | ack s i b => cases h
      | pc d => cases h

/-- Normalization keeps the proposal wires. -/
theorem pcsa_normalizeS_proposals (st : State n) :
    (normalizeS st).proposals = st.proposals := by
  unfold normalizeS
  split <;> rfl

/-- Reconciliation keeps the proposal wires. -/
theorem pcsa_reconcile_proposals (st : State n) :
    (reconcile st).proposals = st.proposals := by
  unfold reconcile
  rw [pcsa_normalizeS_proposals]

/-- PC installation keeps the proposal wires. -/
theorem pcsa_installPC_proposals (st : State n) (d : PC n) :
    (installPC st d).proposals = st.proposals := by
  rw [installPC_def]
  split <;> rfl

/-- PC collection keeps the proposal wires. -/
theorem pcsa_collectPCs_keeps_proposals (st : State n) :
    (collectPCs st).proposals = st.proposals :=
  collectPCs_preserves State.proposals pcsa_installPC_proposals st

/-- Ack pooling keeps the proposal wires. -/
theorem pcsa_poolAckRaw_proposals (st : State n) (a : AckWire n) :
    (poolAckRaw st a).proposals = st.proposals := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  split <;> rfl

/-- An ack batch keeps the proposal wires. -/
theorem pcsa_fold_poolAckRaw_proposals (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).proposals = st.proposals := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, pcsa_poolAckRaw_proposals]

/-- Checked ack pooling keeps the proposal wires. -/
theorem pcsa_poolAck_proposals (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).proposals = st.proposals := by
  delta poolAck
  cases hdecode : a.decode? <;> dsimp only
  rename_i v
  rcases v with ⟨_, _, _⟩
  split
  · rfl
  · split <;> rfl

/-- Row admission keeps the proposal wires. -/
theorem pcsa_admitRow_proposals (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).proposals = st.proposals := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  split <;> rfl

/-- A row batch keeps the proposal wires. -/
theorem pcsa_fold_admitRow_proposals (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).proposals = st.proposals := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, pcsa_admitRow_proposals]

/-- Block admission keeps the wires, or appends its own proposal wire. -/
theorem pcsa_admitBlock_proposals (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) :
    (admitBlock p st s N).proposals = st.proposals ∨
      (admitBlock p st s N).proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩] := by
  have key : ∃ L : List (Wire p.n), (L = [] ∨ L = [⟨.proposer s, .proposal N⟩]) ∧
      (admitBlock p st s N).proposals = st.proposals ++ L := by
    delta admitBlock
    split
    · exact ⟨[], Or.inl rfl, (List.append_nil _).symm⟩
    · cases hP : parentFG st N.erase
      · exact ⟨[], Or.inl rfl, (List.append_nil _).symm⟩
      · dsimp only
        split
        · refine ⟨[⟨.proposer s, .proposal N⟩], Or.inr rfl, ?_⟩
          rw [pcsa_fold_admitRow_proposals, pcsa_collectPCs_keeps_proposals,
            pcsa_fold_poolAckRaw_proposals]
          split_ifs
          · rfl
          · rw [pcsa_reconcile_proposals]
        · exact ⟨[], Or.inl rfl, (List.append_nil _).symm⟩
  obtain ⟨L, hL | hL, h⟩ := key <;> subst hL
  · rw [List.append_nil] at h
    exact Or.inl h
  · exact Or.inr h

/-- A delivery keeps the wires, or appends the delivered proposal wire. -/
theorem pcsa_process_proposals (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).proposals = st.proposals ∨
      (∃ s N, o.decode = some (.block s N) ∧
        (process p st o).proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩]) := by
  delta process
  cases hd : o.decode with
  | none => exact Or.inl rfl
  | some x =>
    cases x with
    | vote s i b => exact Or.inl rfl
    | row i body => exact Or.inl (pcsa_admitRow_proposals p st _)
    | block s N =>
        rcases pcsa_admitBlock_proposals p st s N with h | h
        · exact Or.inl h
        · exact Or.inr ⟨s, N, rfl, h⟩
    | ack s i b =>
        left
        change (collectPCs (poolAck p st ⟨o.auth, b⟩)).proposals = _
        rw [pcsa_collectPCs_keeps_proposals, pcsa_poolAck_proposals]
    | pc d =>
        left
        change (admitPC st d).proposals = _
        unfold admitPC
        split
        · rw [pcsa_collectPCs_keeps_proposals, pcsa_fold_poolAckRaw_proposals]
        · rfl

/-- A delivery keeps every stored proposal wire. -/
theorem pcsa_process_proposals_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.proposals ⊆ (process p st o).proposals := by
  intro a ha
  rcases pcsa_process_proposals p st o with h | ⟨_, _, _, h⟩
  · rw [h]
    exact ha
  · rw [h]
    exact List.mem_append_left _ ha

/-- The pre-gate clock keeps the proposal wires. -/
theorem pcsa_clockPre_proposals (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).proposals = st.proposals := by
  unfold clockPre
  dsimp only
  split <;> split <;> split <;> rfl

/-- The gate keeps the proposal wires. -/
theorem pcsa_gateFrom_proposals (p : Params) (a : Block) (cs : List (PC n))
    (ρ : Option PCRank) (st : State n) (s : Slot) :
    (gateFrom p a cs ρ st s).proposals = st.proposals := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · rfl
  · dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun a : State n => a.proposals = st.proposals)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun a : State n => a.proposals = st.proposals)
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- A clock keeps the proposal wires. -/
theorem pcsa_clock_proposals (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  unfold clock
  dsimp only
  split
  · unfold gateStep
    rw [pcsa_normalizeS_proposals]
    split
    · exact pcsa_clockPre_proposals p st t
    · rw [pcsa_gateFrom_proposals]
      exact pcsa_clockPre_proposals p st t
  · exact pcsa_clockPre_proposals p st t

/-- A clock keeps the named bodies. -/
theorem pcsa_clock_namedBodies (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).namedBodies = st.namedBodies := by
  rw [State.namedBodies, State.namedBodies, pcsa_clock_proposals]

/-- A unique named match is a stored body with that geometry. -/
theorem pcsa_namedByErase_sound (st : State n) (H : Block) (N : NamedProposal n)
    (h : namedByErase? st H = some N) : N ∈ st.namedBodies ∧ N.erase = H := by
  rw [namedByErase?] at h
  generalize hl : (st.namedBodies.filter (fun M => M.erase == H)).eraseDups = l at h
  match l, hl, h with
  | [], _, h => cases h
  | [M], hl, h =>
      have hMN : M = N := Option.some.inj h
      subst hMN
      have hm : M ∈ (st.namedBodies.filter (fun M => M.erase == H)).eraseDups := by
        rw [hl]
        exact List.mem_singleton_self M
      simpa using hm
  | _ :: _ :: _, _, h => cases h

end AvailableChain.PCSA
end

module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run

public section

/-! Body and HEAD evidence in the store (pcsa34-r4.3 §5.1; proof plan C1). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Evidence for stored bodies, PC targets, and HEADs. -/
def StoreEvidence (B : Block → Prop) (H : GridCO.Wire n .root → Prop) (st : State n) : Prop :=
  (∀ b ∈ st.base.blocks, B b) ∧ (∀ d ∈ st.pcs, B d.target) ∧ ∀ o ∈ st.base.votes, H o

theorem StoreEvidence_def (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (st : State n) : StoreEvidence B H st =
      ((∀ b ∈ st.base.blocks, B b) ∧ (∀ d ∈ st.pcs, B d.target) ∧
        ∀ o ∈ st.base.votes, H o) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- Vote admission keeps body evidence and adds only the offered HEAD. -/
theorem grid_admitVote_evidence (q : GridCO.Params) (B : Block → Prop)
    (H : GridCO.Wire n .root → Prop) (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    (hb : ∀ b ∈ st.blocks, B b) (hh : ∀ a ∈ st.votes, H a) (ho : H o) :
    (∀ b ∈ (GridCO.admitVote q st o).blocks, B b) ∧
      ∀ a ∈ (GridCO.admitVote q st o).votes, H a := by
  cases o with | mk auth payload =>
    cases auth <;> cases payload <;> dsimp only [GridCO.admitVote]
    all_goals first | exact ⟨hb, hh⟩ | skip
    split
    · exact ⟨hb, hh⟩
    · refine ⟨hb, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hh a ha
      · simpa only [List.mem_singleton.mp ha] using ho

/-- Proposal admission uses only its new body and carried HEADs. -/
theorem grid_admitProposal_evidence (q : GridCO.Params) (B : Block → Prop)
    (H : GridCO.Wire n .root → Prop) (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    (b : Block) (raw : List (GridCO.HeadWire n .root))
    (hb : ∀ b ∈ st.blocks, B b) (hh : ∀ a ∈ st.votes, H a) (hnew : B b)
    (hraw : ∀ a ∈ raw, H (GridCO.fromHead a)) :
    (∀ k ∈ (GridCO.admitProposal q st o b raw).blocks, B k) ∧
      ∀ a ∈ (GridCO.admitProposal q st o b raw).votes, H a := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only <;> split
  all_goals first
  | exact ⟨hb, hh⟩
  | apply List.foldlRecOn (motive := fun acc : GridCO.State n .root =>
      (∀ k ∈ acc.blocks, B k) ∧ ∀ a ∈ acc.votes, H a)
    · refine ⟨?_, hh⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hb a ha
      · simpa only [List.mem_singleton.mp ha] using hnew
    · intro acc h a ha
      exact grid_admitVote_evidence q B H acc _ h.1 h.2 (hraw a ha)

/-- Normalization keeps body and HEAD evidence. -/
theorem normalizeS_evidence (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (st : State n) (h : StoreEvidence B H st) : StoreEvidence B H (normalizeS st) := by
  unfold normalizeS
  split <;> exact h

/-- Reconciliation keeps evidence for every retained PC. -/
theorem reconcile_evidence (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (st : State n) (h : StoreEvidence B H st) : StoreEvidence B H (reconcile st) := by
  apply normalizeS_evidence
  exact ⟨h.1, fun d hd => h.2.1 d (List.mem_filter.mp hd).1, h.2.2⟩

/-- Valid PC installation resolves its target in the evidenced body store. -/
theorem installPC_evidence (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (st : State n) (d : PC n) (h : StoreEvidence B H st) (hv : pcValid st d = true) :
    StoreEvidence B H (installPC st d) := by
  unfold installPC deleteConflictingLeases
  split
  · exact h
  · refine ⟨h.1, ?_, h.2.2⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h.2.1 a ha
    · have he := List.mem_singleton.mp ha
      subst a
      exact h.1 d.target (of_decide_eq_true (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp hv).1).2)

/-- PC collection keeps body and HEAD evidence. -/
theorem collectPCs_evidence (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (st : State n) (h : StoreEvidence B H st) : StoreEvidence B H (collectPCs st) :=
  collectPCs_invariant (StoreEvidence B H) (installPC_evidence B H) st h

/-- Ack pooling changes no body, PC target, or HEAD. -/
theorem poolAckRaw_evidence (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (st : State n) (a : AckWire n) (h : StoreEvidence B H st) :
    StoreEvidence B H (poolAckRaw st a) := by
  delta poolAckRaw
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact h
  · exact h

/-- Row admission changes no body, PC target, or HEAD. -/
theorem admitRow_evidence (p : Params) (B : Block → Prop) (H : GridCO.Wire p.n .root → Prop)
    (st : State p.n) (a : RowWire p.n) (h : StoreEvidence B H st) :
    StoreEvidence B H (admitRow p st a) := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact h
  · exact h

/-- Deliveries use only the offered body and direct or carried HEADs. -/
theorem process_evidence (p : Params) (B : Block → Prop) (H : GridCO.Wire p.n .root → Prop)
    (st : State p.n) (o : Wire p.n) (h : StoreEvidence B H st)
    (hv : ∀ s i r, o.decode = some (.vote s i r) → H ⟨.seat s i, .head r⟩)
    (hb : ∀ s N, o.decode = some (.block s N) →
      B N.erase ∧ ∀ a ∈ N.raw, H (GridCO.fromHead (baseHead a))) :
    StoreEvidence B H (process p st o) := by
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : StoreEvidence B H st) :
      StoreEvidence B H (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc h a _ => poolAckRaw_evidence B H acc a h)
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      obtain ⟨hB, hH⟩ := grid_admitVote_evidence p.toParams.engine B H st.base _
        h.1 h.2.2 (hv s i r hd)
      exact ⟨hB, h.2.1, hH⟩
    | row i body =>
      dsimp only
      exact admitRow_evidence p B H st _ h
    | block s N =>
      dsimp only
      have hn := hb s N hd
      have hbase := grid_admitProposal_evidence p.toParams.engine B H st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) h.1 h.2.2 hn.1
        (by
          intro a ham
          obtain ⟨a', ha', heq⟩ := List.mem_map.mp ham
          subst a
          exact hn.2 a' ha')
      delta admitBlock
      split
      · exact h
      · cases hP : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply List.foldlRecOn
            · apply collectPCs_evidence
              apply ha
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply reconcile_evidence; exact ⟨hbase.1, h.2.1, hbase.2⟩)
                | exact ⟨hbase.1, h.2.1, hbase.2⟩
            · intro acc h a _
              exact admitRow_evidence p B H acc a h
          · exact h
    | ack s i r =>
      dsimp only
      unfold admitAck
      apply collectPCs_evidence
      delta poolAck
      cases hdecode : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      rotate_left
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · exact h
        · split <;> exact h
      · exact h
    | pc d =>
      dsimp only
      unfold admitPC
      split
      · exact collectPCs_evidence B H _ (ha st _ h)
      · exact h
  | none =>
    exact h

/-- Gates change none of the three evidence domains. -/
theorem gateFrom_evidence (p : Params) (B : Block → Prop) (H : GridCO.Wire n .root → Prop)
    (a : Block) (cs : List (PC n)) (ρ : Option PCRank) (st : State n) (s : Slot)
    (h : StoreEvidence B H st) : StoreEvidence B H (gateFrom p a cs ρ st s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact h
  · dsimp only
    split
    · exact h
    · apply List.foldlRecOn
      · exact h
      · intro acc ha b _
        apply List.foldlRecOn
        · exact ha
        · intro acc' ha' g _
          exact ha'

/-- Ticks keep body and HEAD evidence. -/
theorem clock_evidence (p : Params) (B : Block → Prop) (H : GridCO.Wire p.n .root → Prop)
    (st : State p.n) (t : Time) (h : StoreEvidence B H st) :
    StoreEvidence B H (clock p st t) := by
  have hc : StoreEvidence B H (clockPre p st t) := by
    unfold clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  unfold clock
  dsimp only
  split
  · unfold gateStep
    apply normalizeS_evidence
    split
    · exact hc
    · exact gateFrom_evidence p B H _ _ _ _ _ hc
  · exact hc

end AvailableChain.PCSA
end

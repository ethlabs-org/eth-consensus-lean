module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run

public section

/-! Held-PC validity and ack provenance (pcsa34-r4.3 §3.6; proof plan C1). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Seat selection only removes acks. -/
theorem pcsa_firstPerSeat_subset (as : List (AckWire n)) : firstPerSeat as ⊆ as := by
  unfold firstPerSeat
  suffices ∀ acc : List (AckWire n), acc ⊆ as →
      (as.foldl (fun acc a => if acc.any (fun old => old.seat? == a.seat?) then acc
        else acc ++ [a]) acc) ⊆ as from this [] (by simp)
  intro acc h
  apply List.foldlRecOn (motive := fun acc => acc ⊆ as)
  · exact h
  · intro acc ha a hm
    split
    · exact ha
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ha hb
      · simpa only [List.mem_singleton.mp hb] using hm

/-- Every ack in an assembled PC is in the pool used for assembly. -/
theorem assemblePC_acks (st : State n) (s : Slot) (b : Block) (d : PC n)
    (h : assemblePC st s b = some d) : d.acks ⊆ st.ackPool := by
  obtain ⟨rfl, _⟩ := (assemblePC_some_iff st s b d).mp h
  exact List.Subset.trans (pcsa_firstPerSeat_subset _) (acksOn_subset st s b.root)

/-- The pool and all held certificates have ack provenance. -/
def CertSafe (Q : AckWire n → Prop) (st : State n) : Prop :=
  (∀ a ∈ st.ackPool, Q a) ∧ ∀ d ∈ st.pcs, d.wellFormed = true ∧ ∀ a ∈ d.acks, Q a

theorem CertSafe_def (Q : AckWire n → Prop) (st : State n) : CertSafe Q st =
    ((∀ a ∈ st.ackPool, Q a) ∧ ∀ d ∈ st.pcs,
      d.wellFormed = true ∧ ∀ a ∈ d.acks, Q a) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- Collection uses valid certificates and takes their acks from its pool. -/
theorem collectPCs_certSafe (Q : AckWire n → Prop) (st : State n) (h : CertSafe Q st) :
    CertSafe Q (collectPCs st) := by
  delta collectPCs
  apply List.foldlRecOn
  · exact h
  · intro acc ha sr _
    cases hb : acc.base.blocks.find? (fun b => b.root == sr.2) with
    | none => exact ha
    | some b =>
      dsimp only
      cases hc : assemblePC acc sr.1 b <;> dsimp only
      · exact ha
      · rename_i d
        have hd := hc
        have hv := pcsa_assemblePC_valid acc sr.1 _ d hd
        refine ⟨?_, ?_⟩
        · simpa only [(installPC_frame acc d).2.2.1] using ha.1
        · intro c hc
          rcases mem_installPC_pcs acc d c hc with hc | rfl
          · exact ha.2 c hc
          · exact ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1,
              fun a hm => ha.1 a (assemblePC_acks acc sr.1 _ c hd hm)⟩

/-- Raw pooling preserves certificate provenance when its input has provenance. -/
theorem poolAckRaw_certSafe (Q : AckWire n → Prop) (st : State n) (a : AckWire n)
    (h : CertSafe Q st) (ha : Q a) : CertSafe Q (poolAckRaw st a) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rcases mem_poolAckRaw st a b hb with hb | rfl
    · exact h.1 b hb
    · exact ha
  · simpa only [(poolAckRaw_frame st a).1] using h.2

/-- Normalization keeps certificate evidence. -/
theorem normalizeS_certSafe (Q : AckWire n → Prop) (st : State n) (h : CertSafe Q st) :
    CertSafe Q (normalizeS st) := by
  unfold normalizeS
  split <;> exact h

/-- Reconciliation keeps provenance for the PCs that remain held. -/
theorem reconcile_certSafe (Q : AckWire n → Prop) (st : State n) (h : CertSafe Q st) :
    CertSafe Q (reconcile st) := by
  apply normalizeS_certSafe
  exact ⟨h.1, fun d hd => h.2 d (List.mem_filter.mp hd).1⟩

/-- Row admission changes neither the ack pool nor held certificates. -/
theorem admitRow_certSafe (p : Params) (Q : AckWire p.n → Prop) (st : State p.n)
    (a : RowWire p.n) (h : CertSafe Q st) : CertSafe Q (admitRow p st a) := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact h
  · exact h

/-- Delivery preserves validity and provenance from its direct or carried acks. -/
theorem process_certSafe (p : Params) (Q : AckWire p.n → Prop) (st : State p.n)
    (o : Wire p.n) (h : CertSafe Q st)
    (ha : ∀ s i r, o.decode = some (.ack s i r) → Q ⟨o.auth, r⟩)
    (hb : ∀ s N, o.decode = some (.block s N) → ∀ a ∈ N.pcAcks, Q a)
    (hp : ∀ d, o.decode = some (.pc d) → ∀ a ∈ d.acks, Q a) :
    CertSafe Q (process p st o) := by
  have foldA (st : State p.n) (as : List (AckWire p.n)) (h : CertSafe Q st)
      (hs : ∀ a ∈ as, Q a) : CertSafe Q (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc h a hm => poolAckRaw_certSafe Q acc a h (hs a hm))
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      exact h
    | row i body =>
      dsimp only
      exact admitRow_certSafe p Q st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hP : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply List.foldlRecOn
            · apply collectPCs_certSafe
              apply foldA _ _ _ (hb s N hd)
              cases N.pc <;> dsimp only <;> split_ifs <;>
                first | apply reconcile_certSafe; exact h | exact h
            · intro acc h a _
              exact admitRow_certSafe p Q acc a h
          · exact h
    | ack s i r =>
      dsimp only
      unfold admitAck
      apply collectPCs_certSafe
      refine ⟨?_, ?_⟩
      · intro b hb'
        rcases mem_poolAck p st _ b hb' with hb' | rfl
        · exact h.1 b hb'
        · exact ha s i r hd
      · delta poolAck
        cases hdecode : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
        rotate_left
        · rename_i v
          rcases v with ⟨_, _, _⟩
          split
          · exact h.2
          · split <;> exact h.2
        · exact h.2
    | pc d =>
      dsimp only
      unfold admitPC
      split
      · exact collectPCs_certSafe Q _ (foldA st d.acks h (hp d hd))
      · exact h
  | none =>
    exact h

/-- Gate steps change no certificate evidence. -/
theorem gateFrom_certSafe (p : Params) (Q : AckWire n → Prop) (a : Block)
    (cs : List (PC n)) (ρ : Option PCRank) (st : State n) (s : Slot) (h : CertSafe Q st) :
    CertSafe Q (gateFrom p a cs ρ st s) := by
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

/-- Ticks keep certificate validity and provenance. -/
theorem clock_certSafe (p : Params) (Q : AckWire p.n → Prop) (st : State p.n) (t : Time)
    (h : CertSafe Q st) : CertSafe Q (clock p st t) := by
  have hc : CertSafe Q (clockPre p st t) := by
    unfold clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  unfold clock
  dsimp only
  split
  · unfold gateStep
    apply normalizeS_certSafe
    split
    · exact hc
    · exact gateFrom_certSafe p Q _ _ _ _ _ hc
  · exact hc

end AvailableChain.PCSA
end

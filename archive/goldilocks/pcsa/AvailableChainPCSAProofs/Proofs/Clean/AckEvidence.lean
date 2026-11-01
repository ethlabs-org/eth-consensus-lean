module
public import AvailableChainPCSAProofs.Proofs.Clean.AckRun
public import AvailableChainPCSAClaims.Statements.Regimes

public section

/-! Honest signatures in the ack pool, without a PC-lane dependency. -/

namespace AvailableChain.PCSA
variable {n : Nat}
private theorem pcsa_poolRaw_pred (Q : AckWire n → Prop) (st : State n) (a : AckWire n)
    (h : ∀ b ∈ st.ackPool, Q b) (ha : Q a) : ∀ b ∈ (poolAckRaw st a).ackPool, Q b := by
  intro b hb
  rcases mem_poolAckRaw st a b hb with hb | rfl
  · exact h b hb
  · exact ha
private theorem pcsa_poolChecked_pred (p : Params) (Q : AckWire p.n → Prop)
    (st : State p.n) (a : AckWire p.n) (h : ∀ b ∈ st.ackPool, Q b) (ha : Q a) :
    ∀ b ∈ (poolAck p st a).ackPool, Q b := by
  intro b hb
  rcases mem_poolAck p st a b hb with hb | rfl
  · exact h b hb
  · exact ha
private theorem pcsa_row_pool_pred (p : Params) (Q : AckWire p.n → Prop)
    (st : State p.n) (a : RowWire p.n) (h : ∀ b ∈ st.ackPool, Q b) :
    ∀ b ∈ (admitRow p st a).ackPool, Q b := by
  delta admitRow
  cases a.decode? <;> dsimp only <;> first | exact h | split <;> exact h
private theorem pcsa_normalize_pool_pred (Q : AckWire n → Prop) (st : State n)
    (h : ∀ b ∈ st.ackPool, Q b) : ∀ b ∈ (normalizeS st).ackPool, Q b := by
  delta normalizeS
  split <;> exact h
private theorem pcsa_reconcile_pool_pred (Q : AckWire n → Prop) (st : State n)
    (h : ∀ b ∈ st.ackPool, Q b) : ∀ b ∈ (reconcile st).ackPool, Q b := by
  apply pcsa_normalize_pool_pred
  exact h
/-- Each delivery preserves pool evidence and adds only signed input acks. -/
theorem pcsa_process_pool_pred (p : Params) (Q : AckWire p.n → Prop)
    (st : State p.n) (o : Wire p.n) (h : ∀ a ∈ st.ackPool, Q a)
    (hack : ∀ s i r, o.decode = some (.ack s i r) → Q ⟨o.auth, r⟩)
    (hblock : ∀ s N, o.decode = some (.block s N) → ∀ a ∈ N.pcAcks, Q a)
    (hpc : ∀ C, o.decode = some (.pc C) → ∀ a ∈ C.acks, Q a) :
    ∀ a ∈ (process p st o).ackPool, Q a := by
  have hraw (st : State p.n) (as : List (AckWire p.n))
      (h : ∀ a ∈ st.ackPool, Q a) (ha : ∀ a ∈ as, Q a) :
      ∀ a ∈ (as.foldl poolAckRaw st).ackPool, Q a :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a hm => pcsa_poolRaw_pred Q acc a hh (ha a hm))
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r => exact h
    | row i body => exact pcsa_row_pool_pred p Q st _ h
    | ack s i r =>
      change ∀ a ∈ (collectPCs (poolAck p st _)).ackPool, Q a
      rw [(collectPCs_frame _).2.2.1]
      exact pcsa_poolChecked_pred p Q st _ h (hack s i r hd)
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.1]
        exact hraw st C.acks h (hpc C hd)
      · exact h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
              (motive := fun acc : State p.n => ∀ a ∈ acc.ackPool, Q a)
            · rw [(collectPCs_frame _).2.2.1]
              apply hraw _ _ _ (hblock s N hd)
              cases N.pc <;> dsimp only
              all_goals repeat first
                | exact h
                | (apply pcsa_reconcile_pool_pred; exact h)
                | split
            · intro acc hh a _
              exact pcsa_row_pool_pred p Q acc a hh
          · exact h
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem pcsa_decoded_ack_object (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : (toWire p o).decode = some (.ack s i r)) :
    ofAck p ⟨(toWire p o).auth, r⟩ = o := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
  | seat l j =>
    cases l with
    | prop k => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] at h <;> simp at h
    | base l =>
      cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
private theorem pcsa_decoded_ack_exact (a : AckWire p.n) (s : Slot) (i : Fin p.n)
    (r : BlockId) (h : a.decode? = some (s, i, r)) : ofAck p a = ackObj p s i r := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => cases h
  | proposer k => cases h
  | seat l j =>
    cases l <;> dsimp only [AckWire.decode?, Label.ackSlot?] at h <;> simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
private theorem pcsa_pool_decoded_payloads (o : Obj p) :
    (∀ s N, (toWire p o).decode = some (.block s N) → o.payload = .proposal N) ∧
    (∀ C, (toWire p o).decode = some (.pc C) → o.payload = .pc C) := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] <;> simp
  | seat l j =>
    cases l with
    | prop k => cases payload <;> dsimp only [toWire, toAuth, Wire.decode] <;> simp
    | base l => cases l <;> cases payload <;>
      dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] <;> simp

/-- Each pooled honest-seat ack has an emission with the same slot and root. -/
theorem pcsa_pool_honest_emits (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.UnforgeableSignatures E rho)
    (j : Nat) (y : V) (a : AckWire p.n) (ha : a ∈ (V2.D.Run.stateBefore E rho j y).st.ackPool)
    (s : Slot) (i : Fin p.n) (r : BlockId) (hd : a.decode? = some (s, i, r))
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest) :
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r) t := by
  let Q := fun a : AckWire p.n => ∀ s i r, a.decode? = some (s, i, r) →
    rho.seatOf (.base (.ack s)) i ∈ rho.honest →
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r) t
  have hz : ∀ a ∈ (initial p.n).ackPool, Q a := by
    intro a ha
    exact (List.not_mem_nil ha).elim
  have hall : ∀ a ∈ (V2.D.Run.stateBefore E rho j y).st.ackPool, Q a := by
    refine V2.D.Engine.stateBefore_step_induction E rho
      (fun nd : Node p => ∀ a ∈ nd.st.ackPool, Q a) (Nat.zero_le j) y ?_ hz
    intro k e _ _ he hy h
    cases e with
    | restart x t =>
      change x = y at hy
      subst x
      change ∀ a ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool, Q a
      rw [Function.update_self]
      exact hz
    | tick x t =>
      change x = y at hy
      subst x
      change ∀ a ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool, Q a
      rw [Function.update_self]
      have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
      rw [ht, pcsa_clock_ackPool]
      exact h
    | deliver x o t =>
      change x = y at hy
      subst x
      change ∀ a ∈ (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool, Q a
      rw [Function.update_self]
      apply pcsa_process_pool_pred p Q _ (toWire p o) h
      · intro ss ii rr hh s i r hd hi
        have ho := pcsa_decoded_ack_object o ss ii rr hh
        have hobj := pcsa_decoded_ack_exact _ s i r hd
        have heq := hobj.symm.trans ho
        rw [← heq] at he
        obtain ⟨tt, _, ht⟩ := hv.unforgeable y _ t ⟨k, he⟩ _ hi rfl
        exact ⟨tt, ht⟩
      · intro ss N hh a ha s i r hd hi
        have hp := (pcsa_pool_decoded_payloads o).1 ss N hh
        have hc : (pcsaWith m p c).carries o (ofAck p a) := by
          change carriesS p o (ofAck p a)
          delta carriesS
          left
          rw [hp]
          exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩)))
        rw [pcsa_decoded_ack_exact a s i r hd] at hc
        obtain ⟨tt, _, ht⟩ := hv.carried y o t ⟨k, he⟩ _ hc _ hi rfl
        exact ⟨tt, ht⟩
      · intro C hh a ha s i r hd hi
        have hp := (pcsa_pool_decoded_payloads o).2 C hh
        have hc : (pcsaWith m p c).carries o (ofAck p a) := by
          change carriesS p o (ofAck p a)
          delta carriesS
          left
          rw [hp]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        rw [pcsa_decoded_ack_exact a s i r hd] at hc
        obtain ⟨tt, _, ht⟩ := hv.carried y o t ⟨k, he⟩ _ hc _ hi rfl
        exact ⟨tt, ht⟩
  exact hall a ha s i r hd hi
end AvailableChain.PCSA.Run
end

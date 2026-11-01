module
public import AvailableChainPCSAProofs.Proofs.Shared.Certificates
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainGeneric.Proofs.Pure.PCQuorum

public section

/-! Authentic ack origins for held PCs (pcsa34-r4.3 §5.1; proof plan C1). -/

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A pooled ack was delivered directly or carried by a delivered object. -/
def AckOrigin (_E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (a : AckWire p.n) : Prop :=
  ∃ x o t, V2.D.Run.processes rho x o t ∧
    (ofAck p a = o ∨ carriesS p o (ofAck p a))

omit [DecidableEq V] in
theorem AckOrigin_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (a : AckWire p.n) : AckOrigin E rho a =
      (∃ x o t, V2.D.Run.processes rho x o t ∧
        (ofAck p a = o ∨ carriesS p o (ofAck p a))) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

private theorem decoded_ack (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : (toWire p o).decode = some (.ack s i r)) :
    ofAck p ⟨(toWire p o).auth, r⟩ = o := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
  | seat l j =>
    cases l with
    | prop k => cases payload <;> simp [toWire, toAuth, Wire.decode] at h
    | base l =>
      cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] at h <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl

private theorem decoded_payloads (o : Obj p) :
    (∀ s N, (toWire p o).decode = some (.block s N) → o.payload = .proposal N) ∧
    (∀ d, (toWire p o).decode = some (.pc d) → o.payload = .pc d) := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> simp [toWire, toAuth, Wire.decode]
  | seat l j =>
    cases l with
    | prop k => cases payload <;> simp [toWire, toAuth, Wire.decode]
    | base l => cases l <;> cases payload <;>
        dsimp only [toWire, toAuth, Wire.decode, Label.ackSlot?] <;> simp

/-- Every indexed store has well-formed PCs with authentic ack origins. -/
theorem certSafe_stateBefore (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (j : Nat) (v : V) : CertSafe (AckOrigin E rho) (V2.D.Run.stateBefore E rho j v).st := by
  have hz : CertSafe (AckOrigin E rho) (initial p.n) := by
    dsimp only [initial]
    simp [CertSafe_def]
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => CertSafe (AckOrigin E rho) nd.st) (Nat.zero_le j) v ?_ hz
  intro k e _ _ he hn h
  cases e with
  | restart u t =>
    change u = v at hn
    subst u
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    exact hz
  | tick u t =>
    change u = v at hn
    subst u
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k v) v t
    rw [ht]
    exact clock_certSafe p _ _ t h
  | deliver u o t =>
    change u = v at hn
    subst u
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho k) v _ v).st
    rw [Function.update_self]
    apply process_certSafe p _ _ (toWire p o) h
    · intro s i r hd
      exact ⟨v, o, t, ⟨k, he⟩, Or.inl (decoded_ack o s i r hd)⟩
    · intro s N hd a ha
      refine ⟨v, o, t, ⟨k, he⟩, Or.inr ?_⟩
      unfold carriesS
      rw [(decoded_payloads o).1 s N hd]
      exact Or.inl (Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))))
    · intro d hd a ha
      refine ⟨v, o, t, ⟨k, he⟩, Or.inr ?_⟩
      unfold carriesS
      rw [(decoded_payloads o).2 d hd]
      exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- The inclusive reader has the same certificate evidence as its event prefix. -/
theorem certSafe_storeAt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.ScheduleWellFormed E rho) (v : V) (t : Time) :
    CertSafe (AckOrigin E rho) (storeAt p c E rho v t) := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore hv]
  exact certSafe_stateBefore E rho _ v

/-- Unforgeability turns an honest held ack into an actual emission. -/
theorem ackOrigin_emits (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hv : V2.D.UnforgeableSignatures E rho) (a : AckWire p.n) (s : Slot)
    (i : Fin p.n) (r : BlockId) (ha : AckOrigin E rho a)
    (hd : a.decode? = some (s, i, r)) (hh : rho.seatOf (.base (.ack s)) i ∈ rho.honest) :
    ∃ t, V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r) t := by
  have heq : ofAck p a = ackObj p s i r := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => dsimp only [AckWire.decode?] at hd; contradiction
    | proposer k => dsimp only [AckWire.decode?] at hd; contradiction
    | seat l j =>
      cases l <;> dsimp only [AckWire.decode?, Label.ackSlot?] at hd <;> simp at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      rfl
  obtain ⟨x, o, t, hp, ho⟩ := ha
  rw [heq] at ho
  rcases ho with ho | ho
  · subst o
    obtain ⟨t', _, he⟩ := hv.unforgeable x _ t hp _ hh rfl
    exact ⟨t', he⟩
  · obtain ⟨t', _, he⟩ := hv.carried x o t hp _ ho _ hh rfl
    exact ⟨t', he⟩


/-- A fresh committee has at most as many faulty seats as faulty nodes. -/
theorem fresh_faulty_card [Fintype V] (rho : V2.D.Run V (pcsaWith m p c))
    (hc : V2.D.CStar (pcsaFamilies p c).fresh rho) (l : Label)
    (hl : (pcsaFamilies (m := m) p c).fresh (.base l)) (F : Finset (Fin p.n))
    (hF : ∀ i ∈ F, rho.seatOf (.base l) i ∉ rho.honest) :
    F.card ≤ (Gen.V2.Duty.faulty rho).card := by
  classical
  rw [← Finset.card_image_of_injective F (hc (.base l) hl).1]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  simpa only [Gen.V2.Duty.faulty_def, Finset.mem_sdiff, Finset.mem_univ, true_and] using hF i hi

/-- A held PC has an honest ack emission under the PC fault bound. -/
theorem held_pc_honest_ack [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hf : FaultsBelowQA p c rho) (x : V) (t : Time) (d : PC p.n)
    (hd : d ∈ (storeAt p c E rho x t).pcs) :
    ∃ i : Fin p.n, rho.seatOf (.base (.ack d.slot)) i ∈ rho.honest ∧
      ∃ a, V2.D.Run.emits E rho (rho.seatOf (.base (.ack d.slot)) i)
        (ackObj p d.slot i d.target.root) a := by
  classical
  have hs := certSafe_storeAt E rho h.valid.toScheduleWellFormed x t
  rw [CertSafe_def] at hs
  obtain ⟨hw, ho⟩ := hs.2 d hd
  have hw' := hw
  dsimp only [PC.wellFormed] at hw'
  simp (config := { iota := false }) only [ Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw'
  let F : Finset (Fin p.n) := Finset.univ.filter
    (fun i => rho.seatOf (.base (.ack d.slot)) i ∉ rho.honest)
  have hbound := fresh_faulty_card rho h.cstar (.ack d.slot) trivial F
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hF : F.card < Gen.Pure.qA p.n := lt_of_le_of_lt hbound hf
  have hsize : Gen.Pure.qA p.n ≤ d.seats.toFinset.card := by
    rw [List.toFinset_card_of_nodup (show d.seats.Nodup from List.nodup_dedup _)]
    exact hw'.1.2 ▸ hw'.1.1.2
  obtain ⟨i, hi, hn⟩ := Gen.Pure.qA_honest hF hsize
  have hh : rho.seatOf (.base (.ack d.slot)) i ∈ rho.honest := by
    simpa [F] using hn
  have hi' : i ∈ d.acks.filterMap AckWire.seat? := by
    dsimp only [PC.seats] at hi
    simpa using hi
  obtain ⟨a, ha, hai⟩ := List.mem_filterMap.mp hi'
  have had := List.all_eq_true.mp hw'.2 a ha
  cases he : a.decode? with
  | none => rw [he] at had; contradiction
  | some v =>
    rcases v with ⟨s, j, r⟩
    have hij : j = i := by
      dsimp only [AckWire.seat?] at hai
      simpa [he] using hai
    have hsr : s = d.slot ∧ r = d.target.root := by
      rw [he] at had
      dsimp only at had
      simpa using had
    rcases hsr with ⟨rfl, rfl⟩
    subst j
    exact ⟨i, hh, ackOrigin_emits E rho h.valid.toUnforgeableSignatures a _ i _
      (ho a ha) he hh⟩

end AvailableChain.PCSA.Run
end

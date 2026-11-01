module
public import AvailableChainPCSAProofs.Proofs.Clean.PCPool
public import AvailableChainPCSAProofs.Proofs.Clean.AckAdmit
public import AvailableChainPCSAProofs.Proofs.Shared.HonestQuorum

public section

/-! C6 AckOrigins: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
open AvailableChain.PCSA.CleanPCPool
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private def AckBefore (_E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (bound : Time) (a : AckWire p.n) : Prop :=
  ∃ (j : Nat) (x : V) (o : Obj p) (t : Time),
    rho.events[j]? = some (V2.Event.deliver x o t) ∧ t < bound ∧
    (ofAck p a = o ∨ carriesS p o (ofAck p a))
private theorem ack_before_direct (o : Obj p) (s : Slot) (i : Fin p.n) (r : BlockId)
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
private theorem ack_before_payloads (o : Obj p) :
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
private theorem cert_before_cut (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (k : Nat) (x : V) (bound : Time) (hk : k ≤ V2.D.Run.idxBefore rho bound) :
    CertSafe (AckBefore E rho bound) (V2.D.Run.stateBefore E rho k x).st := by
  have hz : CertSafe (AckBefore E rho bound) (initial p.n) := by
    rw [CertSafe_def]
    exact ⟨by intro a ha; exact (List.not_mem_nil ha).elim,
      by intro C hc; exact (List.not_mem_nil hc).elim⟩
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => CertSafe (AckBefore E rho bound) nd.st) (Nat.zero_le k) x ?_ hz
  intro j e _ hjk he hy ih
  cases e with
  | restart y t =>
    change y = x at hy
    subst y
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st
    rw [Function.update_self]
    exact hz
  | tick y t =>
    change y = x at hy
    subst y
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t
    rw [ht]
    exact clock_certSafe p _ _ t ih
  | deliver y o t =>
    change y = x at hy
    subst y
    change CertSafe _ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st
    rw [Function.update_self]
    have ht : t < bound :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hs he bound).mp (lt_of_lt_of_le hjk hk)
    apply process_certSafe p _ _ (toWire p o) ih
    · intro s i r hd
      exact ⟨j, x, o, t, he, ht, Or.inl (ack_before_direct o s i r hd)⟩
    · intro s N hd a ha
      refine ⟨j, x, o, t, he, ht, Or.inr ?_⟩
      delta carriesS
      left
      rw [(ack_before_payloads o).1 s N hd]
      exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩)))
    · intro C hd a ha
      refine ⟨j, x, o, t, he, ht, Or.inr ?_⟩
      delta carriesS
      left
      rw [(ack_before_payloads o).2 C hd]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
private theorem ack_before_emits (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hu : V2.D.UnforgeableSignatures E rho)
    (bound : Time) (a : AckWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (ha : AckBefore E rho bound a) (hd : a.decode? = some (s, i, r))
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest) :
    ∃ t, t < bound ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r) t := by
  have heq : ofAck p a = ackObj p s i r := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => cases hd
    | proposer k => cases hd
    | seat l j =>
      cases l <;> dsimp only [AckWire.decode?, Label.ackSlot?] at hd <;> simp at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      rfl
  obtain ⟨j, x, o, t, he, ht, hcar⟩ := ha
  rw [heq] at hcar
  rcases hcar with hdir | hcar
  · subst o
    obtain ⟨t', hle, hem⟩ := hu.unforgeable x _ t ⟨j, he⟩ _ hi rfl
    exact ⟨t', lt_of_le_of_lt hle ht, hem⟩
  · obtain ⟨t', hle, hem⟩ := hu.carried x o t ⟨j, he⟩ _ hcar _ hi rfl
    exact ⟨t', lt_of_le_of_lt hle ht, hem⟩
/-- A PC held before a cut is well formed and has an honest ack emitted before that cut. -/
theorem pcsa_pc_honest_emission_before [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (bound : Time)
    (hk : k ≤ V2.D.Run.idxBefore rho bound) (C : PC p.n)
    (hC : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs) :
    C.wellFormed = true ∧ ∃ i, rho.seatOf (.base (.ack C.slot)) i ∈ rho.honest ∧
      ∃ t, t < bound ∧ V2.D.Run.emits E rho (rho.seatOf (.base (.ack C.slot)) i)
        (ackObj p C.slot i C.target.root) t := by
  have hs := cert_before_cut E rho h.valid.toScheduleWellFormed k x bound hk
  rw [CertSafe_def] at hs
  obtain ⟨hw, hsource⟩ := hs.2 C hC
  obtain ⟨i, hi, a, ha, hd⟩ := pcsa_pc_honest_ack rho h.cstar hFault C hw
  exact ⟨hw, i, hi, ack_before_emits E rho h.valid.toUnforgeableSignatures bound a
    C.slot i C.target.root (hsource a ha) hd hi⟩
/-- The ack duty of any PC held before a cut is strictly before that cut. -/
theorem pcsa_pc_early_before [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hFault : FaultsBelowQA p c rho) (k : Nat) (x : V) (bound : Time)
    (hk : k ≤ V2.D.Run.idxBefore rho bound) (C : PC p.n)
    (hC : C ∈ (V2.D.Run.stateBefore E rho k x).st.pcs) :
    C.wellFormed = true ∧ SA.earlyTime p.toParams C.slot < bound := by
  obtain ⟨hw, i, _, t, ht, j, hj, ho⟩ := pcsa_pc_honest_emission_before E rho h hFault k x bound
    hk C hC
  have he := (ack_emission_duty p c m E rho _ C.slot i C.target.root t j hj ho).1
  exact ⟨hw, he ▸ ht⟩
end AvailableChain.PCSA.Run

end

module
public import AvailableChainPCSAProofs.Proofs.Shared.Count
public import AvailableChainPCSAClaims.Statements.Regimes

public section

/-! Honest seats for fresh HEAD and ack counts (pcsa34-r4.3 §5.1).
PC uniqueness uses an honest ack in each PC, not an intersection of PCs. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- An injective committee has no more faulty seats than faulty nodes. -/
theorem pcsa_faulty_seats_card (rho : V2.D.Run V (pcsaWith m p c))
    (label : (pcsaWith m p c).Label) (hinj : Function.Injective (rho.seatOf label)) :
    (Finset.univ.filter (fun i => rho.seatOf label i ∉ rho.honest)).card ≤
      (Gen.V2.Duty.faulty rho).card := by
  apply Finset.card_le_card_of_injOn (rho.seatOf label)
  · intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ he
    exact hinj he

/-- Every PC quorum in an injective committee contains an honest seat. -/
theorem pcsa_quorum_honest (rho : V2.D.Run V (pcsaWith m p c))
    (label : (pcsaWith m p c).Label) (hinj : Function.Injective (rho.seatOf label))
    (hf : FaultsBelowQA p c rho) (Q : Finset (Fin ((pcsaWith m p c).seats label)))
    (hn : (pcsaWith m p c).seats label = p.n) (hQ : pcQuorum p.n ≤ Q.card) :
    ∃ i ∈ Q, rho.seatOf label i ∈ rho.honest := by
  classical
  have hcard := pcsa_faulty_seats_card rho label hinj
  have hF : (Finset.univ.filter (fun i => rho.seatOf label i ∉ rho.honest)).card <
      Gen.Pure.qA ((pcsaWith m p c).seats label) := by
    calc
      _ ≤ (Gen.V2.Duty.faulty rho).card := hcard
      _ < pcQuorum p.n := hf
      _ = Gen.Pure.qA ((pcsaWith m p c).seats label) := (congrArg Gen.Pure.qA hn).symm
  have hQ' : Gen.Pure.qA ((pcsaWith m p c).seats label) ≤ Q.card := by
    calc
      Gen.Pure.qA ((pcsaWith m p c).seats label) = pcQuorum p.n := congrArg Gen.Pure.qA hn
      _ ≤ Q.card := hQ
  obtain ⟨i, hi, hhon⟩ := Gen.Pure.qA_honest hF hQ'
  refine ⟨i, hi, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hhon

/-- A fresh ack count of PC size contains an honest acker. -/
theorem pcsa_ack_quorum_honest (rho : V2.D.Run V (pcsaWith m p c))
    (hC : V2.D.CStar (pcsaFamilies p c).fresh rho) (hf : FaultsBelowQA p c rho)
    (s : Slot) (Q : Finset (Fin p.n)) (hQ : pcQuorum p.n ≤ Q.card) :
    ∃ i ∈ Q, rho.seatOf (.base (.ack s)) i ∈ rho.honest :=
  pcsa_quorum_honest rho (.base (.ack s))
    (hC (.base (.ack s)) trivial).injective hf Q rfl hQ

/-- Two fresh N counts share an honest HEAD seat. -/
theorem pcsa_n_inter_honest (rho : V2.D.Run V (pcsaWith m p c))
    (hC : V2.D.CStar (pcsaFamilies p c).fresh rho) (hf : FaultsBelowQA p c rho)
    (s : Slot) (Q Q' : Finset (Fin p.n))
    (hQ : nQuorum p.n ≤ Q.card) (hQ' : nQuorum p.n ≤ Q'.card) :
    ∃ i ∈ Q ∩ Q', rho.seatOf (.base (.head s)) i ∈ rho.honest :=
  pcsa_quorum_honest rho (.base (.head s))
    (hC (.base (.head s)) trivial).injective hf (Q ∩ Q') rfl
    (pcsa_n_inter_card hQ hQ')

omit [DecidableEq V] [Fintype V] in
/-- Honest count witnesses give a lower bound for any seat multiset. -/
theorem pcsa_honest_seat_count {n : Nat} (holder : Fin n → V) (honest : Finset V)
    (seats H : Finset (Fin n)) (hH : ∀ i ∈ H, holder i ∈ honest ∧ i ∈ seats) :
    H.card ≤ (@Finset.filter (Fin n) (fun i => holder i ∈ honest)
      (fun i => Classical.propDecidable (holder i ∈ honest)) seats).card := by
  apply Finset.card_le_card
  intro i hi
  exact (@Finset.mem_filter (Fin n) (fun i => holder i ∈ honest)
    (fun i => Classical.propDecidable (holder i ∈ honest)) seats i).mpr
    ⟨(hH i hi).2, (hH i hi).1⟩

omit [DecidableEq V] [Fintype V] in
/-- The honest HEAD count contains every supplied honest seat witness.
Repeated objects and faulty entries cannot increase this honest count. -/
theorem pcsa_honest_head_count (rho : V2.D.Run V (pcsaWith m p c))
    (s : Slot) (heads : List (GridCO.Wire p.n .root)) (H : Finset (Fin p.n))
    (hH : ∀ i ∈ H, rho.seatOf (.base (.head s)) i ∈ rho.honest ∧
      ∃ o ∈ heads, GridCO.headSeat? o = some i) :
    H.card ≤ (@Finset.filter (Fin p.n)
      (fun i => rho.seatOf (.base (.head s)) i ∈ rho.honest)
      (fun i => Classical.propDecidable (rho.seatOf (.base (.head s)) i ∈ rho.honest))
      (GridCO.seats p.n heads).toFinset).card := by
  apply pcsa_honest_seat_count
  intro i hi
  exact ⟨(hH i hi).1, (Gen.AC.Root.vote_pool_mem_seats heads i).mpr (hH i hi).2⟩

omit [DecidableEq V] [Fintype V] in
/-- The honest ack count contains every supplied honest seat witness. -/
theorem pcsa_honest_ack_count (rho : V2.D.Run V (pcsaWith m p c))
    (s : Slot) (acks : List (AckWire p.n)) (H : Finset (Fin p.n))
    (hH : ∀ i ∈ H, rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
      ∃ a ∈ acks, a.seat? = some i) :
    H.card ≤ (@Finset.filter (Fin p.n)
      (fun i => rho.seatOf (.base (.ack s)) i ∈ rho.honest)
      (fun i => Classical.propDecidable (rho.seatOf (.base (.ack s)) i ∈ rho.honest))
      (acks.filterMap AckWire.seat?).toFinset).card := by
  apply pcsa_honest_seat_count
  intro i hi
  exact ⟨(hH i hi).1, (pcsa_ack_count_witness acks i).mpr (hH i hi).2⟩

/-- CL4's score bound follows from the Generic N intersection inequality.
Here `e` counts equivocating seats and is bounded by faulty nodes. -/
theorem pcsa_n_score_bound (rho : V2.D.Run V (pcsaWith m p c))
    (hf : FaultsBelowQA p c rho) (e : Nat)
    (he : e ≤ (Gen.V2.Duty.faulty rho).card) : p.n + e < 2 * nQuorum p.n := by
  have hq := Gen.Pure.qA_add_le_two_mul_qN p.n
  have hlt : e < Gen.Pure.qA p.n := lt_of_le_of_lt he hf
  change p.n + e < 2 * Gen.Pure.qN p.n
  omega

/-- A well-formed PC has at least a PC quorum of distinct ack seats. -/
theorem pcsa_pc_ack_card (C : PC p.n) (hw : C.wellFormed = true) :
    pcQuorum p.n ≤ (C.acks.filterMap AckWire.seat?).toFinset.card := by
  dsimp only [PC.wellFormed] at hw
  simp (config := { iota := false }) only
    [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
  rw [← pcsa_pc_seats_card]
  omega

/-- Each well-formed PC has an honest ack witness. -/
theorem pcsa_pc_honest_ack (rho : V2.D.Run V (pcsaWith m p c))
    (hC : V2.D.CStar (pcsaFamilies p c).fresh rho) (hf : FaultsBelowQA p c rho)
    (C : PC p.n) (hw : C.wellFormed = true) :
    ∃ i, rho.seatOf (.base (.ack C.slot)) i ∈ rho.honest ∧
      ∃ a ∈ C.acks, a.decode? = some (C.slot, i, C.target.root) := by
  obtain ⟨i, hi, hh⟩ := pcsa_ack_quorum_honest rho hC hf C.slot _
    (pcsa_pc_ack_card C hw)
  obtain ⟨a, ha, hs⟩ := (pcsa_ack_count_witness C.acks i).mp hi
  dsimp only [PC.wellFormed] at hw
  have hall := (Bool.and_eq_true_iff.mp hw).2
  have hd := List.all_eq_true.mp hall a ha
  unfold AckWire.seat? at hs
  cases he : a.decode? with
  | none => simp only [he, Option.map_none, reduceCtorEq] at hs
  | some v =>
    rcases v with ⟨s, j, r⟩
    simp only [he, Option.map_some, Option.some.injEq] at hs
    rw [he] at hd
    dsimp only at hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hd
    rcases hd with ⟨rfl, rfl⟩
    subst j
    exact ⟨i, hh, a, ha, he⟩

/-- PC targets have one root if every honest ack names the unique N root.
Run provenance and digest collision freedom are separate inputs. -/
theorem pcsa_pc_root_unique (rho : V2.D.Run V (pcsaWith m p c))
    (hC : V2.D.CStar (pcsaFamilies p c).fresh rho) (hf : FaultsBelowQA p c rho)
    (C C' : PC p.n) (hw : C.wellFormed = true) (hw' : C'.wellFormed = true)
    (hslot : C.slot = C'.slot) (r : BlockId)
    (hroot : ∀ i, rho.seatOf (.base (.ack C.slot)) i ∈ rho.honest →
      ∀ a ∈ C.acks ++ C'.acks, ∀ r', a.decode? = some (C.slot, i, r') → r' = r) :
    C.target.root = C'.target.root := by
  obtain ⟨i, hi, a, ha, hd⟩ := pcsa_pc_honest_ack rho hC hf C hw
  obtain ⟨j, hj, b, hb, hd'⟩ := pcsa_pc_honest_ack rho hC hf C' hw'
  rw [← hslot] at hj hd'
  exact (hroot i hi a (List.mem_append_left _ ha) _ hd).trans
    (hroot j hj b (List.mem_append_right _ hb) _ hd').symm

end AvailableChain.PCSA.Run
end

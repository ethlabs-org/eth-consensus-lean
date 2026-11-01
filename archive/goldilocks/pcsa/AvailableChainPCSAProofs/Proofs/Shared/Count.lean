module
public import AvailableChainPCSA.Model.PC
public import AvailableChainGeneric.Proofs.Pure.PCQuorum
public import AvailableChainGeneric.Proofs.Pure.SupportCounts
public import AvailableChainFGSAProofs.Proofs.Shared.Relay

public section

/-! Seat counts for CL1 and CL4 (pcsa34-r4.3 §5.1–5.2).
The lists are count multisets. No receipt-pool equality is required. -/

namespace AvailableChain.PCSA

/-- The model N threshold is the Generic threshold. -/
theorem pcsa_nQuorum_eq_qN (n : Nat) : nQuorum n = Gen.Pure.qN n := rfl

/-- The model PC threshold is the Generic threshold. -/
theorem pcsa_pcQuorum_eq_qA (n : Nat) : pcQuorum n = Gen.Pure.qA n := rfl

/-- [N-ARITH] Two N counts share at least a PC quorum of seats. -/
theorem pcsa_n_inter_card {n : Nat} {Q Q' : Finset (Fin n)}
    (hQ : nQuorum n ≤ Q.card) (hQ' : nQuorum n ≤ Q'.card) :
    pcQuorum n ≤ (Q ∩ Q').card :=
  Gen.Pure.qN_inter_card hQ hQ'

/-- N uniqueness uses the Generic exact-HEAD contract. -/
theorem pcsa_n_target_unique {n : Nat} {B : Type} (sent : Fin n → B → Prop)
    (F Q Q' : Finset (Fin n)) (b b' : B)
    (hone : ∀ i, i ∉ F → ∀ x y, sent i x → sent i y → x = y)
    (hF : F.card < pcQuorum n) (hQ : ∀ i ∈ Q, sent i b)
    (hQ' : ∀ i ∈ Q', sent i b')
    (hcQ : nQuorum n ≤ Q.card) (hcQ' : nQuorum n ≤ Q'.card) : b = b' :=
  Gen.Pure.qN_head_unique sent F Q Q' b b' hone hF hQ hQ' hcQ hcQ'

/-- The N count counts each exact HEAD seat once. -/
theorem pcsa_nCount_card (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (b : Block) : nCount p v s b =
      (GridCO.seats p.n ((timelyHeads p v s).filter
        (fun o => GridCO.resolvedHead? v o == some b))).toFinset.card :=
  Gen.AC.Root.vote_pool_voterCount_card _

/-- A PC counts each ack seat once. -/
theorem pcsa_pc_seats_card {n : Nat} (C : PC n) :
    C.seats.length = (C.acks.filterMap AckWire.seat?).toFinset.card := by
  unfold PC.seats
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _)]
  simp only [List.toFinset_dedup]

/-- A counted ack seat has an ack witness in the count multiset. -/
theorem pcsa_ack_count_witness {n : Nat} (acks : List (AckWire n)) (i : Fin n) :
    i ∈ (acks.filterMap AckWire.seat?).toFinset ↔
      ∃ a ∈ acks, a.seat? = some i := by
  simp only [List.mem_toFinset, List.mem_filterMap]

/-- Receipt order does not change the ack seat count. -/
theorem pcsa_ack_count_perm {n : Nat} {acks acks' : List (AckWire n)}
    (h : acks.Perm acks') :
    (acks.filterMap AckWire.seat?).toFinset =
      (acks'.filterMap AckWire.seat?).toFinset := by
  ext i
  simp only [pcsa_ack_count_witness]
  exact exists_congr (fun a => and_congr (h.mem_iff) Iff.rfl)

/-- CL1: relayed count sets with strict majorities share a seat. -/
theorem pcsa_majority_count_inter {n : Nat} {P Q D D' : Finset (Fin n)}
    (hD : P ∪ Q ⊆ D) (hD' : P ∪ Q ⊆ D')
    (hP : D.card < 2 * P.card) (hQ : D'.card < 2 * Q.card) :
    (P ∩ Q).Nonempty :=
  Gen.Pure.two_majorities_intersect hD hD' hP hQ

/-- CL1: common resolved heads lock compatibility of two majority results. -/
theorem pcsa_majority_count_compatible {n : Nat} {P Q D D' : Finset (Fin n)}
    (B C : Block) (heads : Fin n → Block) (hD : P ∪ Q ⊆ D) (hD' : P ∪ Q ⊆ D')
    (hP : D.card < 2 * P.card) (hQ : D'.card < 2 * Q.card)
    (hheadsB : ∀ i ∈ P, Block.Preceq B (heads i))
    (hheadsC : ∀ i ∈ Q, Block.Preceq C (heads i)) : Block.Compatible B C := by
  obtain ⟨i, hi⟩ := pcsa_majority_count_inter hD hD' hP hQ
  obtain ⟨hPi, hQi⟩ := Finset.mem_inter.mp hi
  exact Gen.Pure.block_compatible_of_common (hheadsB i hPi) (hheadsC i hQi)

/-- CL2/CL3 count boundary: forward and backward relay preserve a majority
and give strict score dominance over every conflicting block.
The two stores can have different receipt pools and different trees. -/
theorem pcsa_majority_count_transfer (p : Params) (st st' : State p.n)
    (P L U V : List (GridCO.Wire p.n .root)) (B : Block)
    (hPL : P ⊆ L)
    (hclean : ∀ o ∈ P, ∀ i, GridCO.headSeat? o = some i → GridCO.equivocates L i = false)
    (hforward : ∀ o ∈ P, ∀ i, GridCO.headSeat? o = some i →
      Gen.AC.Root.voteSupports st.base.blocks B o = true →
      (o ∈ V ∧ Gen.AC.Root.voteSupports st'.base.blocks B o = true) ∨
        GridCO.equivocates U i = true)
    (hbackward : ∀ o ∈ U, ∀ i, GridCO.headSeat? o = some i →
      o ∈ L ∨ GridCO.equivocates L i = true)
    (hsupport : V ⊆ U)
    (hmajority : GridCO.voterCount L < 2 * GridCO.goldfishScore st.base.blocks P P B) :
    Gen.AC.Root.TransferBounds (Gen.AC.Root.plainSupporters st.base.blocks P P B)
      L st'.base.blocks U V B :=
  Gen.AC.Root.transfer st.base.blocks st'.base.blocks P L U V B
    hPL hclean hforward hbackward hsupport hmajority

/-- A clean support seat stays non-equivocating in the late count.
This GridCO statement is imported from FG-SA Shared/Relay. -/
theorem pcsa_clean_support_seat (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s)
    (i : Fin p.n) (hi : GridCO.headSeat? o = some i) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) i = false :=
  FGSA.Run.fgsa_cleanSupport_seat_clean_late p v s o ho i hi

end AvailableChain.PCSA
end

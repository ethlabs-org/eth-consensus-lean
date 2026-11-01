module
public import AvailableChainPCSAProofs.Proofs.Clean.NCounts
public import AvailableChainPCSAProofs.Proofs.Clean.HonestSupport
public import AvailableChainPCSAProofs.Proofs.Clean.BackwardInputs

public section

/-! C6 NWalkCounts: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- With fewer than q_A capped seats, an N-sized score is a strict majority and beats conflicts. -/
theorem pcsa_N_score_dominance {n : Nat} (tree : List Block)
    (raw sup : List (GridCO.Wire n .root)) (B : Block) (F : Finset (Fin n))
    (hsub : sup ⊆ raw) (hF : F.card < pcQuorum n)
    (hcaps : ∀ i, GridCO.equivocates raw i = true → i ∈ F)
    (hN : nQuorum n ≤ GridCO.goldfishScore tree raw sup B) :
    GridCO.voterCount raw < 2 * GridCO.goldfishScore tree raw sup B ∧
    ∀ C, Block.compatible B C = false →
      GridCO.goldfishScore tree raw sup C < GridCO.goldfishScore tree raw sup B := by
  classical
  let seats := (GridCO.seats n raw).toFinset
  let scoreSeats := fun X => seats.filter
    (fun i => (GridCO.equivocates raw i || Gen.AC.Root.poolSupports tree sup i X) = true)
  have hscore (X : Block) : GridCO.goldfishScore tree raw sup X = (scoreSeats X).card :=
    Gen.AC.Root.vote_pool_score_card tree raw sup X
  have hcount : GridCO.voterCount raw ≤ n := by
    rw [Gen.AC.Root.vote_pool_voterCount_card]
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ seats
  have hn : n < 2 * nQuorum n := by
    have hq := Gen.Pure.qA_add_le_two_mul_qN n
    change pcQuorum n + n ≤ 2 * nQuorum n at hq
    omega
  refine ⟨by omega, ?_⟩
  intro C hconf
  have hinter : scoreSeats B ∩ scoreSeats C ⊆ F := by
    intro i hi
    obtain ⟨hiB, hiC⟩ := Finset.mem_inter.mp hi
    cases he : GridCO.equivocates raw i with
    | true => exact hcaps i he
    | false =>
      have hb := (Finset.mem_filter.mp hiB).2
      have hc := (Finset.mem_filter.mp hiC).2
      change (GridCO.equivocates raw i || Gen.AC.Root.poolSupports tree sup i B) = true at hb
      change (GridCO.equivocates raw i || Gen.AC.Root.poolSupports tree sup i C) = true at hc
      rw [he, Bool.false_or] at hb hc
      have hn := Gen.AC.Root.vote_pool_support_conflict tree raw sup i hsub he hb hconf
      rw [hn] at hc
      cases hc
  have hu : (scoreSeats B ∪ scoreSeats C).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_univ (scoreSeats B ∪ scoreSeats C)
  have hi := Finset.card_le_card hinter
  have he := Finset.card_union_add_card_inter (scoreSeats B) (scoreSeats C)
  have hsum : GridCO.goldfishScore tree raw sup B + GridCO.goldfishScore tree raw sup C ≤
      n + F.card := by
    rw [hscore, hscore]
    omega
  exact pcsa_n_score_gap hF hN (by omega)
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Proposer raw input cannot cap an honest HEAD seat. -/
theorem pcsa_proposer_honest_not_capped (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (x : V) (u : Time) (s : Slot) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest) :
    GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k x).st u) (s + 1)) i
      = false := by
  change GridCO.equivocates (GridCO.votesAt (clock p _ u).base (s + 1 - 1)) i = false
  rw [Nat.add_sub_cancel]
  delta GridCO.votesAt
  rw [pcsa_clock_heads]
  exact pcsa_honest_head_pool_not_capped E rho hv k x s i hi
/-- An honest voter seat is not capped with a floor at the freeze time of label `s`. -/
theorem pcsa_voter_honest_not_capped_from_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (k a : Nat) (y x : V) (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut) :
    GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1)) i = false := by
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  let L := GridCO.lateVotes p.toParams.engine
    (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s
  have hclean : GridCO.equivocates L i = false :=
    pcsa_honest_late_not_capped E rho h.valid a x _ s i hi
  have read (o : GridCO.Wire p.n .root) (ho : o ∈ headVotes p dst (s + 1))
      (hoi : GridCO.headSeat? o = some i) : o ∈ L := by
    have hl : GridCO.headLabel? o = some s := by
      rcases pcsa_headVotes_mem p dst (s + 1) o ho with hf | hc
      · simpa only [Nat.add_sub_cancel] using beq_iff_eq.mp (List.mem_filter.mp hf.1).2
      · obtain ⟨_, _, _, _, _, _, _, _, _, hl⟩ := hc
        simpa only [Nat.add_sub_cancel] using hl
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
    rcases pcsa_voter_tick_input_relay_late_win E rho h hD (hT := hT) k a y x hy
        hx s i r hc hk ha ho with hm | he
    · exact hm
    · rw [hclean] at he
      cases he
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨o, ho, o', ho', hne, hoi, ho'i⟩ := (Gen.AC.Root.cap_pair _ i).mp he
  have hcap : GridCO.equivocates L i = true := (Gen.AC.Root.cap_pair _ i).mpr
    ⟨o, read o ho hoi, o', read o' ho' ho'i, hne, hoi, ho'i⟩
  rw [hclean] at hcap
  cases hcap
/-- In the delivery window: Backward receipt prevents an honest cap in the actual voter raw input.
-/
theorem pcsa_voter_honest_not_capped_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (k a : Nat) (y x : V) (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut) :
    GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1)) i = false :=
  pcsa_voter_honest_not_capped_from_freeze E rho h hD k a y x hy hx s i hi hk ha
    (pcsa_floor_freeze hT) hc
/-- Backward receipt prevents an honest cap in the actual voter raw input. -/
theorem pcsa_voter_honest_not_capped (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (k a : Nat) (y x : V) (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (ha : rho.events[a]? = some (.tick x (SA.gateTime p.toParams s)))
    (hc : SA.gateTime p.toParams s ≤ cut) :
    GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1)) i = false := by
  let dst := clock p (V2.D.Run.stateBefore E rho k y).st (SA.voteTime p.toParams (s + 1))
  let L := GridCO.lateVotes p.toParams.engine
    (actView (clock p (V2.D.Run.stateBefore E rho a x).st (SA.gateTime p.toParams s))) s
  have hclean : GridCO.equivocates L i = false :=
    pcsa_honest_late_not_capped E rho h.valid a x _ s i hi
  have read (o : GridCO.Wire p.n .root) (ho : o ∈ headVotes p dst (s + 1))
      (hoi : GridCO.headSeat? o = some i) : o ∈ L := by
    have hl : GridCO.headLabel? o = some s := by
      rcases pcsa_headVotes_mem p dst (s + 1) o ho with hf | hc
      · simpa only [Nat.add_sub_cancel] using beq_iff_eq.mp (List.mem_filter.mp hf.1).2
      · obtain ⟨_, _, _, _, _, _, _, _, _, hl⟩ := hc
        simpa only [Nat.add_sub_cancel] using hl
    obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
    rcases pcsa_voter_tick_input_relay_late E rho h hD k a y x hy hx s i r hc hk ha ho with hm | he
    · exact hm
    · rw [hclean] at he
      cases he
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨o, ho, o', ho', hne, hoi, ho'i⟩ := (Gen.AC.Root.cap_pair _ i).mp he
  have hcap : GridCO.equivocates L i = true := (Gen.AC.Root.cap_pair _ i).mpr
    ⟨o, read o ho hoi, o', read o' ho' ho'i, hne, hoi, ho'i⟩
  rw [hclean] at hcap
  cases hcap
end AvailableChain.PCSA.Run

end

module
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBatch
public import AvailableChainPCSAProofs.Proofs.Clean.NCounts

public section

/-! C6 NHeads: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A resolved pooled HEAD of an honest seat names its actual HEAD decision. -/
theorem pcsa_honest_pool_head_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (a : Nat) (x : V) (hx : x ∈ rho.honest)
    (v : Time) (s : Slot) (B : Block) (o : GridCO.Wire p.n .root) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hm : o ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes)
    (hl : GridCO.headLabel? o = some s)
    (hoi : GridCO.headSeat? o = some i)
    (hr : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) o = some
      B) :
    HonestHeadAt p c E rho (rho.seatOf (.base (.head s)) i) s B := by
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hoi
  have hroot := FGSA.Run.resolvedHead_root _ _ hr
  change some r = some B.root at hroot
  have heq := Option.some.inj hroot
  subst r
  have hpool := hm
  change _ ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes at hpool
  rw [pcsa_clock_heads] at hpool
  obtain ⟨t, he⟩ := pcsa_pool_head_emission E rho h.valid.toUnforgeableSignatures a x s i B.root
    hi hpool
  have ht := pcsa_head_emission_time_awake E rho _ s i B.root t he
  have htime : SA.voteTime p.toParams s ≤ rho.horizon := by
    obtain ⟨j, hj, _⟩ := he
    have hh := (h.valid.in_horizon _ (List.mem_of_getElem? hj)).2
    change t ≤ rho.horizon at hh
    rwa [ht.1] at hh
  obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h _ hi s ht.2 htime
  have hEmitH := pcsa_honest_head_emits E rho _ s i H rfl hH
  have hBHroot := pcsa_honest_pool_head_eq_emitted E rho h.valid a x s i B.root H.root _ hi hpool
    hEmitH
  have hBm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
  have hBs := pcsa_clock_body_scope p (RootBlockInRun p c E rho) _ v
    (pcsa_body_scope E rho a x hx) B hBm
  obtain ⟨j, _, hHm, _⟩ := pcsa_honest_head_body_before_vote E rho h hF _ s H hH
  have hHs := pcsa_body_scope E rho j _ hi H hHm
  have hBH := pcsa_scoped_root_eq E rho h.idealization B H hBs hHs hBHroot
  rw [hBH]
  exact hH
/-- An early resolved HEAD of an honest seat names that holder's actual HEAD decision. -/
theorem pcsa_early_honest_head_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (a : Nat) (x : V) (hx : x ∈ rho.honest)
    (v : Time) (s : Slot) (B : Block) (o : GridCO.Wire p.n .root) (i : Fin p.n)
    (hi : rho.seatOf (.base (.head s)) i ∈ rho.honest)
    (hm : o ∈ GridCO.earlyVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s)
    (hoi : GridCO.headSeat? o = some i)
    (hr : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) o = some
      B) :
    HonestHeadAt p c E rho (rho.seatOf (.base (.head s)) i) s B := by
  have hl : GridCO.headLabel? o = some s :=
    beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hm).1).2
  exact pcsa_honest_pool_head_source E rho h hF a x hx v s B o i hi
    (List.mem_filter.mp (List.mem_filter.mp hm).1).1 hl hoi hr
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
private def NSeats (p : Params) (v : GridCO.State p.n .root) (s : Slot) (B : Block) :
    Finset (Fin p.n) :=
  (GridCO.seats p.n ((timelyHeads p v s).filter
    (fun o => GridCO.resolvedHead? v o == some B))).toFinset
private theorem NSeats_card (p : Params) (v : GridCO.State p.n .root) (s : Slot) (B : Block) :
    nCount p v s B = (NSeats p v s B).card := pcsa_nCount_card p v s B
private theorem NSeats_witness (p : Params) (v : GridCO.State p.n .root)
    (s : Slot) (B : Block) (i : Fin p.n) (hi : i ∈ NSeats p v s B) :
    ∃ o ∈ GridCO.earlyVotes p.toParams.engine v s, GridCO.headSeat? o = some i ∧
      GridCO.resolvedHead? v o = some B := by
  obtain ⟨o, ho, hoi⟩ := (Gen.AC.Root.vote_pool_mem_seats _ i).mp hi
  exact ⟨o, (List.mem_filter.mp (List.mem_filter.mp ho).1).1, hoi,
    beq_iff_eq.mp (List.mem_filter.mp ho).2⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}
private theorem N_fault_seats_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (s : Slot)
    (F : Finset (Fin p.n))
    (hF : ∀ i ∈ F, rho.seatOf (.base (.head s)) i ∉ rho.honest) :
    F.card ≤ (Gen.V2.Duty.faulty rho).card := by
  apply Finset.card_le_card_of_injOn (fun i : Fin p.n => rho.seatOf (.base (.head s)) i)
  · intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hF i hi⟩
  · intro i _ j _ he
    exact (h.cstar (.base (.head s)) trivial).1 he
/-- Every actual N target is the exact HEAD of at least one honest voter. -/
theorem pcsa_N_has_honest_head (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (a : Nat) (x : V) (hx : x ∈ rho.honest) (v : Time) (s : Slot) (B : Block)
    (hN : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true) :
    ∃ y, HonestHeadAt p c E rho y s B := by
  classical
  let st := actView (clock p (V2.D.Run.stateBefore E rho a x).st v)
  let F := Finset.univ.filter (fun i : Fin p.n => rho.seatOf (.base (.head s)) i ∉ rho.honest)
  have hFc : F.card < Gen.Pure.qA p.n := (N_fault_seats_bound E rho h s F (fun i hi =>
    (Finset.mem_filter.mp hi).2)).trans_lt hFault
  have hn : nQuorum p.n ≤ (NSeats p st s B).card := by
    have hh : nQuorum p.n ≤ nCount p st s B := of_decide_eq_true hN
    rwa [NSeats_card] at hh
  have hA : Gen.Pure.qA p.n ≤ (NSeats p st s B).card := by
    simpa only [Finset.inter_self, pcsa_pcQuorum_eq_qA] using pcsa_n_inter_card hn hn
  obtain ⟨i, hiN, hiF⟩ := Gen.Pure.qA_honest hFc hA
  have hi : rho.seatOf (.base (.head s)) i ∈ rho.honest := by
    simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hiF
  obtain ⟨o, ho, hoi, hr⟩ := NSeats_witness p st s B i hiN
  exact ⟨_, pcsa_early_honest_head_source E rho h hF a x hx v s B o i hi ho hoi hr⟩
/-- Two actual N counts of one label have the same full target. -/
theorem pcsa_N_targets_unique (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (hFault : FaultsBelowQA p c rho)
    (a b : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (v u : Time) (s : Slot) (B C : Block)
    (hB : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s B = true)
    (hC : holdsN p (actView (clock p (V2.D.Run.stateBefore E rho b y).st u)) s C = true) : B = C
      := by
  classical
  let src := actView (clock p (V2.D.Run.stateBefore E rho a x).st v)
  let dst := actView (clock p (V2.D.Run.stateBefore E rho b y).st u)
  let F := Finset.univ.filter (fun i : Fin p.n => rho.seatOf (.base (.head s)) i ∉ rho.honest)
  have hFc : F.card < Gen.Pure.qA p.n := (N_fault_seats_bound E rho h s F (fun i hi =>
    (Finset.mem_filter.mp hi).2)).trans_lt hFault
  have hnB : Gen.Pure.qN p.n ≤ (NSeats p src s B).card := by
    have hh : nQuorum p.n ≤ nCount p src s B := of_decide_eq_true hB
    rwa [NSeats_card] at hh
  have hnC : Gen.Pure.qN p.n ≤ (NSeats p dst s C).card := by
    have hh : nQuorum p.n ≤ nCount p dst s C := of_decide_eq_true hC
    rwa [NSeats_card] at hh
  obtain ⟨i, hi, hiF⟩ := Gen.Pure.qN_inter_honest hFc hnB hnC
  obtain ⟨hiB, hiC⟩ := Finset.mem_inter.mp hi
  have hih : rho.seatOf (.base (.head s)) i ∈ rho.honest := by
    simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hiF
  obtain ⟨oB, hoB, hiB, hrB⟩ := NSeats_witness p src s B i hiB
  obtain ⟨oC, hoC, hiC, hrC⟩ := NSeats_witness p dst s C i hiC
  have hheadB := pcsa_early_honest_head_source E rho h hF a x hx v s B oB i hih hoB hiB hrB
  have hheadC := pcsa_early_honest_head_source E rho h hF b y hy u s C oC i hih hoC hiC hrC
  exact Option.some.inj (hheadB.2.2.symm.trans hheadC.2.2)
end AvailableChain.PCSA.Run

end

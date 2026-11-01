module
public import AvailableChainPCSAProofs.Proofs.Clean.CommonRaw
public import AvailableChainPCSAProofs.Proofs.Clean.CommonBodies
public import AvailableChainPCSAProofs.Proofs.Clean.CountTransport

public section

/-! C6 CommonSupport: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
/-- In stage 1, active and cumulative HEAD resolution agree. -/
theorem pcsa_active_base_resolution (st : State n) (hf : st.fg.F = .genesis)
    (o : GridCO.Wire n .root) :
    GridCO.resolvedHead? (actView st) o = GridCO.resolvedHead? st.base o := by
  have hd : GridCO.resolutionTree (actView st) = GridCO.resolutionTree st.base := rfl
  delta GridCO.resolvedHead?
  rw [hd, pcsa_actView_blocks_of_genesis st hf]
/-- An admitted proposal contributes each declared, resolved, slot-correct support input. -/
theorem pcsa_headSupport_of_carried (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (hslot : N.slot = s)
    (hm : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ st.proposals)
    (o : GridCO.Wire p.n .root) (ho : o ∈ N.support.map baseVote)
    (hl : GridCO.headLabel? o = some (s - 1)) (B : Block)
    (hr : GridCO.resolvedHead? st.base o = some B) (hb : B.slot ≤ s - 1) :
    o ∈ headSupport p st s := by
  have hrow : (N.raw, N.support) ∈ proposalsAt st s := by
    apply List.mem_filterMap.mpr
    refine ⟨⟨.proposer s, .proposal N⟩, hm, ?_⟩
    change (if N.slot = s then some (N.raw, N.support) else none) = _
    rw [ite_eq_left hslot]
  delta headSupport
  apply List.mem_eraseDups.mpr
  apply List.mem_append_right
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨(N.raw, N.support), hrow, ho⟩, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  exact ⟨beq_iff_eq.mpr hl, by rw [hr]; exact decide_eq_true hb⟩
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: Exact proposer support is present and resolves identically at the voter
read. -/
theorem pcsa_proposer_support_in_voter_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (v : Time) (N : NamedProposal p.n) (hslot : N.slot = s)
    (ha : rho.events[a]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hk : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k)
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.voteTime p.toParams s ≤ cut)
    (hmem : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.proposals)
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho a x).st (SA.proposalTime p.toParams s)) s)
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ proposerSupport
      (clock p (V2.D.Run.stateBefore E rho a x).st (SA.proposalTime p.toParams s)) s) :
    o ∈ headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st v) s ∧
      GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st v)) o =
        GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st
          (SA.proposalTime p.toParams s))) o := by
  obtain ⟨hraw, hresolve⟩ := List.mem_filter.mp ho
  have hl : GridCO.headLabel? o = some (s - 1) := beq_iff_eq.mp (List.mem_filter.mp hraw).2
  have hseat : ∃ i r, o = ⟨.seat (s - 1) i, .head r⟩ := by
    rcases o with ⟨auth, payload⟩
    cases auth <;> cases payload <;> (delta GridCO.headLabel? at hl; cases hl)
    exact ⟨_, _, rfl⟩
  obtain ⟨i, r, rfl⟩ := hseat
  cases hB : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st
      (SA.proposalTime p.toParams s))) (⟨.seat (s - 1) i, .head r⟩ : GridCO.Wire p.n .root) with
  | none => rw [hB] at hresolve; cases hresolve
  | some B =>
    rw [hB] at hresolve
    have hb : B.slot ≤ s - 1 := of_decide_eq_true hresolve
    have hr := FGSA.Run.resolvedHead_root _ _ hB
    change some r = some B.root at hr
    have heq := Option.some.inj hr
    subst r
    have hm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hB)).1
    have hheld := pcsa_proposer_body_before_vote_win E rho h hF hD (hT := hT) a k x y hx hy s B ha
        hk hc hm
    have hdst := pcsa_resolved_head_of_held_body E rho h hF k y hy (s - 1) i B v hheld
    refine ⟨?_, hdst⟩
    apply pcsa_headSupport_of_carried p _ s N hslot
      (by rwa [pcsa_clock_proposals]) _ (hsup ▸ ho) hl B _ hb
    have hf : (clock p (V2.D.Run.stateBefore E rho k y).st v).fg.F = .genesis := by
      rw [pcsa_body_clock_fg]
      exact (hF y hy k).1
    rwa [pcsa_active_base_resolution _ hf] at hdst
/-- Exact proposer support is present and resolves identically at the voter read. -/
theorem pcsa_proposer_support_in_voter (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (v : Time) (N : NamedProposal p.n) (hslot : N.slot = s)
    (ha : rho.events[a]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hk : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s) ≤ k)
    (hc : SA.voteTime p.toParams s ≤ cut)
    (hmem : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho k y).st.proposals)
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho a x).st (SA.proposalTime p.toParams s)) s)
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ proposerSupport
      (clock p (V2.D.Run.stateBefore E rho a x).st (SA.proposalTime p.toParams s)) s) :
    o ∈ headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st v) s ∧
      GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st v)) o =
        GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st
          (SA.proposalTime p.toParams s))) o :=
  pcsa_proposer_support_in_voter_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s v N hslot ha hk (pcsa_zero_le_proposal s) hc hmem hsup o ho
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Honest proposal metadata fixes the carried arm of every voter support input. -/
theorem pcsa_honest_headSupport_source (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hv : V2.D.ExecutionValid E rho)
    (k : Nat) (y : V) (v : Time) (s : Slot) (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop s) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop s) (0 : Fin 1))
      (⟨.seat (.prop s) (0 : Fin 1), .proposal N⟩ : Obj p) (SA.proposalTime p.toParams s))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st v) s) :
    (o ∈ GridCO.votesAt (clock p (V2.D.Run.stateBefore E rho k y).st v).base (s - 1) ∧
      GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho k y).st v)) o
        (SA.freezeTime p.toParams (s - 1)) = true) ∨ o ∈ N.support.map baseVote := by
  rcases pcsa_headSupport_mem p _ s o ho with hf |
      ⟨w, hw, t, M, a, B, hd, hs, ha, hbase, _⟩
  · exact Or.inl hf
  · rw [pcsa_clock_proposals] at hw
    have ht := (pcsa_proposal_pool_slot E rho hv.toDeliveryWellFormed k y w t M hw hd).trans hs
    subst t
    have hMN := pcsa_proposal_decoded_eq_emitted E rho hv k y s N hx he w hw M hd
    subst M
    exact Or.inr (List.mem_map.mpr ⟨a, ha, hbase⟩)
/-- In the delivery window: Every frozen voter support input is proposer support unless the
proposer caps its seat. -/
theorem pcsa_frozen_support_in_proposer_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (v : Time) (o : GridCO.Wire p.n .root) (i : Fin p.n)
    (hk : rho.events[k]? = some (.tick y (SA.proposalTime p.toParams (s + 1))))
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hm : o ∈ GridCO.votesAt (clock p (V2.D.Run.stateBefore E rho a x).st v).base s)
    (hr : GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) o
      (SA.freezeTime p.toParams s) = true) (hi : GridCO.headSeat? o = some i) :
    o ∈ proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))) (s + 1)) i = true := by
  have hl : GridCO.headLabel? o = some s := beq_iff_eq.mp (List.mem_filter.mp hm).2
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s i hl hi
  obtain ⟨B, hres, hslot, hstamp, hbodyStamp⟩ :=
    pcsa_frozen_support_data p (clock p (V2.D.Run.stateBefore E rho a x).st v) (s + 1)
      ⟨.seat s i, .head r⟩ (by simpa only [Nat.add_sub_cancel] using hm)
      (by simpa only [Nat.add_sub_cancel] using hr)
  rw [Nat.add_sub_cancel] at hslot hstamp hbodyStamp
  have hroot := FGSA.Run.resolvedHead_root _ _ hres
  change some r = some B.root at hroot
  have heq := Option.some.inj hroot
  subst r
  rcases pcsa_frozen_input_in_proposer_win E rho h hD (hT := hT) a k x y hx hy s i B.root v hc hk
      (List.mem_filter.mp hm).1 hstamp with hraw | hcap
  · left
    have hpropCut : SA.proposalTime p.toParams (s + 1) ≤ cut := by
      apply le_trans _ hc
      change 4 * p.Δ * ((s + 1 : Nat) : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      have hp := p.deltaPos
      nlinarith
    have hbody := pcsa_frozen_body_in_proposer_win E rho h hF hD (hT := hT) a k x y hx hy s B v hk
        hpropCut
      (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hres)).1 hbodyStamp
    rw [pcsa_clock_blocks] at hbody
    have hlookup := pcsa_resolved_head_of_held_body E rho h hF k y hy s i B
      (SA.proposalTime p.toParams (s + 1)) hbody
    apply List.mem_filter.mpr
    refine ⟨hraw, ?_⟩
    rw [hlookup]
    exact decide_eq_true (by simpa only [Nat.add_sub_cancel] using hslot)
  · exact Or.inr hcap
/-- Every frozen voter support input is proposer support unless the proposer caps its seat. -/
theorem pcsa_frozen_support_in_proposer (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (v : Time) (o : GridCO.Wire p.n .root) (i : Fin p.n)
    (hk : rho.events[k]? = some (.tick y (SA.proposalTime p.toParams (s + 1))))
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hm : o ∈ GridCO.votesAt (clock p (V2.D.Run.stateBefore E rho a x).st v).base s)
    (hr : GridCO.resolvedBefore (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) o
      (SA.freezeTime p.toParams s) = true) (hi : GridCO.headSeat? o = some i) :
    o ∈ proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st
      (SA.proposalTime p.toParams (s + 1))) (s + 1)) i = true :=
  pcsa_frozen_support_in_proposer_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y
    hx hy s v o i hk (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hm hr hi
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Backward honest support needs a floor at the freeze time of label `s`. -/
theorem pcsa_honest_support_backward_from_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ headSupport p (clock p (V2.D.Run.stateBefore E rho a y).st v) (s + 1))
    (i : Fin p.n) (hi : GridCO.headSeat? o = some i) :
    o ∈ proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) i = true := by
  rcases pcsa_honest_headSupport_source E rho h.valid a y v (s + 1) N hx he o ho with
    ⟨hm, hr⟩ | hm
  · rw [Nat.add_sub_cancel] at hm hr
    exact pcsa_frozen_support_in_proposer_win E rho h hF hD (hT := hT) a k y _ hy
        hx s v o i hk hc hm hr hi
  · exact Or.inl (hsup ▸ hm)
/-- In the delivery window: Every support input at an honest proposer slot is proposer support or a
capped extra. -/
theorem pcsa_honest_support_backward_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ headSupport p (clock p (V2.D.Run.stateBefore E rho a y).st v) (s + 1))
    (i : Fin p.n) (hi : GridCO.headSeat? o = some i) :
    o ∈ proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) i = true :=
  pcsa_honest_support_backward_from_freeze E rho h hF hD a k y hy s v N hx he hk
    (pcsa_floor_freeze hT) hc hsup o ho i hi
/-- Every support input at an honest proposer slot is proposer support or a capped extra. -/
theorem pcsa_honest_support_backward (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (y : V) (hy : y ∈ rho.honest) (s : Slot) (v : Time)
    (N : NamedProposal p.n)
    (hx : rho.seatOf (.prop (s + 1)) (0 : Fin 1) ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (⟨.seat (.prop (s + 1)) (0 : Fin 1), .proposal N⟩ : Obj p)
        (SA.proposalTime p.toParams (s + 1)))
    (hk : rho.events[k]? = some (.tick (rho.seatOf (.prop (s + 1)) (0 : Fin 1))
      (SA.proposalTime p.toParams (s + 1))))
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ headSupport p (clock p (V2.D.Run.stateBefore E rho a y).st v) (s + 1))
    (i : Fin p.n) (hi : GridCO.headSeat? o = some i) :
    o ∈ proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1) ∨
    GridCO.equivocates (proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) i = true := by
  rcases pcsa_honest_headSupport_source E rho h.valid a y v (s + 1) N hx he o ho with
    ⟨hm, hr⟩ | hm
  · rw [Nat.add_sub_cancel] at hm hr
    exact pcsa_frozen_support_in_proposer E rho h hF hD a k y _ hy hx s v o i hk hc hm hr hi
  · exact Or.inl (hsup ▸ hm)
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
variable {n : Nat}
/-- Every stage-one voter support input resolves with a valid label bound. -/
theorem pcsa_headSupport_resolution (p : Params) (st : State p.n) (hf : st.fg.F = .genesis)
    (s : Slot) (o : GridCO.Wire p.n .root) (ho : o ∈ headSupport p st s) :
    GridCO.headLabel? o = some (s - 1) ∧ ∃ B,
      GridCO.resolvedHead? (actView st) o = some B ∧ B.slot ≤ s - 1 := by
  rcases pcsa_headSupport_mem p st s o ho with ⟨hm, hr⟩ |
      ⟨_, _, _, _, _, B, _, _, _, _, hl, hr, hs⟩
  · obtain ⟨B, hr, hs, _⟩ := pcsa_frozen_support_data p st s o hm hr
    exact ⟨beq_iff_eq.mp (List.mem_filter.mp hm).2, B, hr, hs⟩
  · exact ⟨hl, B, by rwa [pcsa_active_base_resolution st hf], hs⟩
end AvailableChain.PCSA

end

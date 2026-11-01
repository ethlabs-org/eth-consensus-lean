module
public import AvailableChainPCSAProofs.Proofs.Clean.CommonSupport

public section

/-! C6 CommonScores: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A resolved read body gives the exact slot and prefix tests used by vote support. -/
theorem pcsa_read_vote_support_iff (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (x : V) (t : Time)
    (o : GridCO.Wire p.n .root) (B X : Block)
    (hr : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k x).st t)) o =
      some B) :
    Gen.AC.Root.voteSupports (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks X o =
      true ↔ B.slot ≤ (GridCO.headLabel? o).getD 0 ∧ Block.Preceq X B := by
  have hd : GridCO.resolutionTree (actView (clock p (V2.D.Run.stateBefore E rho k x).st t)) =
      (clock p (V2.D.Run.stateBefore E rho k x).st t).base.blocks := by
    change (clock p _ _).base.headDomain.getD _ = _
    rw [pcsa_clock_headDomain, pcsa_headDomain_stateBefore_none]
    rfl
  have hl := FGSA.Run.resolvedHead_target _ _ hr
  rw [hd] at hl
  have hm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
  rw [Gen.AC.Root.vote_support_body]
  constructor
  · rintro ⟨C, hC, _, hs, hp⟩
    have he : C = B := Option.some.inj (hC.symm.trans hl)
    subst C
    exact ⟨hs, hp⟩
  · rintro ⟨hs, hp⟩
    exact ⟨B, hl, hm, hs, hp⟩
/-- Common walk counts need a floor at the freeze time of label `s`. -/
theorem pcsa_common_walk_counts_from_freeze (E : Generic.Env V)
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
    (ha : V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)) ≤ a)
    (hslot : N.slot = s + 1)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho a y).st.proposals)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hr : N.raw.map baseVote = proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1))
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) :
    let src := clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
    GridCO.voterCount (proposerVotes src (s + 1)) = GridCO.voterCount (headVotes p dst (s + 1)) ∧
      (∀ i, GridCO.equivocates (proposerVotes src (s + 1)) i =
        GridCO.equivocates (headVotes p dst (s + 1)) i) ∧
      ∀ B, GridCO.goldfishScore src.base.blocks (proposerVotes src (s + 1))
        (proposerSupport src (s + 1)) B =
          GridCO.goldfishScore dst.base.blocks (headVotes p dst (s + 1))
            (headSupport p dst (s + 1)) B := by
  let x := rho.seatOf (.prop (s + 1)) (0 : Fin 1)
  let src := clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
  have hraw := pcsa_common_raw_transfer_win E rho h hD (hT := hT) a k y hy s v N
      hx he hk hslot hmem hc hr
  have hvcut : SA.voteTime p.toParams (s + 1) ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  have forward (o : GridCO.Wire p.n .root) (ho : o ∈ proposerSupport src (s + 1)) :=
    pcsa_proposer_support_in_voter_win E rho h hF hD
      (hT := pcsa_floor_freeze_next hT) k a x y hx hy (s + 1) v N hslot hk ha
      hvcut hmem hsup o ho
  have backward (o : GridCO.Wire p.n .root) (ho : o ∈ headSupport p dst (s + 1))
      (i : Fin p.n) (hi : GridCO.headSeat? o = some i) :=
    pcsa_honest_support_backward_from_freeze E rho h hF hD (hT := hT) a k y hy s v N hx he hk
      hc hsup o ho i hi
  have incidence (X : Block) (i : Fin p.n)
      (hi : GridCO.equivocates (proposerVotes src (s + 1)) i = false) :
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X =
        Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X := by
    have toDst (hh : Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X =
        true) : Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X = true :=
          by
      obtain ⟨o, ho, hoi, hs⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ i X).mp hh
      obtain ⟨B, hB, _⟩ := pcsa_read_vote_support_body E rho hF k x hx _ o X hs
      obtain ⟨hm, heq⟩ := forward o ho
      have hdst := heq.trans hB
      have tests := (pcsa_read_vote_support_iff E rho k x _ o B X hB).mp hs
      exact (Gen.AC.Root.vote_pool_support_witness _ _ i X).mpr ⟨o, hm, hoi,
        (pcsa_read_vote_support_iff E rho a y v o B X hdst).mpr tests⟩
    have toSrc (hh : Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X =
        true) : Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X = true
          := by
      obtain ⟨o, ho, hoi, hs⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ i X).mp hh
      have hm : o ∈ proposerSupport src (s + 1) := (backward o ho i hoi).resolve_right
        (by rw [hi]; exact Bool.false_ne_true)
      obtain ⟨B, hB, _⟩ := pcsa_read_vote_support_body E rho hF a y hy v o X hs
      have hsrc := (forward o hm).2.symm.trans hB
      have tests := (pcsa_read_vote_support_iff E rho a y v o B X hB).mp hs
      exact (Gen.AC.Root.vote_pool_support_witness _ _ i X).mpr ⟨o, hm, hoi,
        (pcsa_read_vote_support_iff E rho k x _ o B X hsrc).mpr tests⟩
    cases hs : Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X <;>
      cases ht : Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X
    · rfl
    · have hh := toSrc ht; rw [hs] at hh; cases hh
    · have hh := toDst hs; rw [ht] at hh; cases hh
    · rfl
  have counts := Gen.AC.Root.score_eq_on src.base.blocks dst.base.blocks
    (proposerVotes src (s + 1)) (headVotes p dst (s + 1))
    (proposerSupport src (s + 1)) (headSupport p dst (s + 1)) Set.univ hraw.1
    (fun o ho i hi hnot => (hraw.2 o ho i hi).resolve_left hnot)
    (fun B _ i hi => incidence B i hi)
  exact ⟨counts.2.2.1, counts.2.1, fun B => counts.2.2.2 B (Set.mem_univ B)⟩
/-- In the delivery window: An honest proposal gives identical actual participant counts, caps, and
walk scores. -/
theorem pcsa_common_walk_counts_win (E : Generic.Env V)
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
    (ha : V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)) ≤ a)
    (hslot : N.slot = s + 1)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho a y).st.proposals)
    (hT : T₀ ≤ SA.proposalTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hr : N.raw.map baseVote = proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1))
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) :
    let src := clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
    GridCO.voterCount (proposerVotes src (s + 1)) = GridCO.voterCount (headVotes p dst (s + 1)) ∧
      (∀ i, GridCO.equivocates (proposerVotes src (s + 1)) i =
        GridCO.equivocates (headVotes p dst (s + 1)) i) ∧
      ∀ B, GridCO.goldfishScore src.base.blocks (proposerVotes src (s + 1))
        (proposerSupport src (s + 1)) B =
          GridCO.goldfishScore dst.base.blocks (headVotes p dst (s + 1))
            (headSupport p dst (s + 1)) B :=
  pcsa_common_walk_counts_from_freeze E rho h hF hD a k y hy s v N hx he hk ha hslot hmem
    (pcsa_floor_freeze hT) hc hr hsup
/-- An honest proposal gives identical actual participant counts, caps, and walk scores. -/
theorem pcsa_common_walk_counts (E : Generic.Env V)
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
    (ha : V2.D.Run.idxBefore rho (SA.voteTime p.toParams (s + 1)) ≤ a)
    (hslot : N.slot = s + 1)
    (hmem : (⟨.proposer (s + 1), .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho a y).st.proposals)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hr : N.raw.map baseVote = proposerVotes
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1))
    (hsup : N.support.map baseVote = proposerSupport
      (clock p (V2.D.Run.stateBefore E rho k (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st
        (SA.proposalTime p.toParams (s + 1))) (s + 1)) :
    let src := clock p (V2.D.Run.stateBefore E rho k
      (rho.seatOf (.prop (s + 1)) (0 : Fin 1))).st (SA.proposalTime p.toParams (s + 1))
    let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
    GridCO.voterCount (proposerVotes src (s + 1)) = GridCO.voterCount (headVotes p dst (s + 1)) ∧
      (∀ i, GridCO.equivocates (proposerVotes src (s + 1)) i =
        GridCO.equivocates (headVotes p dst (s + 1)) i) ∧
      ∀ B, GridCO.goldfishScore src.base.blocks (proposerVotes src (s + 1))
        (proposerSupport src (s + 1)) B =
          GridCO.goldfishScore dst.base.blocks (headVotes p dst (s + 1))
            (headSupport p dst (s + 1)) B := by
  let x := rho.seatOf (.prop (s + 1)) (0 : Fin 1)
  let src := clock p (V2.D.Run.stateBefore E rho k x).st (SA.proposalTime p.toParams (s + 1))
  let dst := clock p (V2.D.Run.stateBefore E rho a y).st v
  have hraw := pcsa_common_raw_transfer E rho h hD a k y hy s v N hx he hk hslot hmem hc hr
  have hvcut : SA.voteTime p.toParams (s + 1) ≤ cut := by
    apply le_trans _ hc
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  have forward (o : GridCO.Wire p.n .root) (ho : o ∈ proposerSupport src (s + 1)) :=
    pcsa_proposer_support_in_voter E rho h hF hD k a x y hx hy (s + 1) v N hslot hk ha
      hvcut hmem hsup o ho
  have backward (o : GridCO.Wire p.n .root) (ho : o ∈ headSupport p dst (s + 1))
      (i : Fin p.n) (hi : GridCO.headSeat? o = some i) :=
    pcsa_honest_support_backward E rho h hF hD a k y hy s v N hx he hk hc hsup o ho i hi
  have incidence (X : Block) (i : Fin p.n)
      (hi : GridCO.equivocates (proposerVotes src (s + 1)) i = false) :
      Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X =
        Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X := by
    have toDst (hh : Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X =
        true) : Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X = true :=
          by
      obtain ⟨o, ho, hoi, hs⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ i X).mp hh
      obtain ⟨B, hB, _⟩ := pcsa_read_vote_support_body E rho hF k x hx _ o X hs
      obtain ⟨hm, heq⟩ := forward o ho
      have hdst := heq.trans hB
      have tests := (pcsa_read_vote_support_iff E rho k x _ o B X hB).mp hs
      exact (Gen.AC.Root.vote_pool_support_witness _ _ i X).mpr ⟨o, hm, hoi,
        (pcsa_read_vote_support_iff E rho a y v o B X hdst).mpr tests⟩
    have toSrc (hh : Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X =
        true) : Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X = true
          := by
      obtain ⟨o, ho, hoi, hs⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ i X).mp hh
      have hm : o ∈ proposerSupport src (s + 1) := (backward o ho i hoi).resolve_right
        (by rw [hi]; exact Bool.false_ne_true)
      obtain ⟨B, hB, _⟩ := pcsa_read_vote_support_body E rho hF a y hy v o X hs
      have hsrc := (forward o hm).2.symm.trans hB
      have tests := (pcsa_read_vote_support_iff E rho a y v o B X hB).mp hs
      exact (Gen.AC.Root.vote_pool_support_witness _ _ i X).mpr ⟨o, hm, hoi,
        (pcsa_read_vote_support_iff E rho k x _ o B X hsrc).mpr tests⟩
    cases hs : Gen.AC.Root.poolSupports src.base.blocks (proposerSupport src (s + 1)) i X <;>
      cases ht : Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (s + 1)) i X
    · rfl
    · have hh := toSrc ht; rw [hs] at hh; cases hh
    · have hh := toDst hs; rw [ht] at hh; cases hh
    · rfl
  have counts := Gen.AC.Root.score_eq_on src.base.blocks dst.base.blocks
    (proposerVotes src (s + 1)) (headVotes p dst (s + 1))
    (proposerSupport src (s + 1)) (headSupport p dst (s + 1)) Set.univ hraw.1
    (fun o ho i hi hnot => (hraw.2 o ho i hi).resolve_left hnot)
    (fun B _ i hi => incidence B i hi)
  exact ⟨counts.2.2.1, counts.2.1, fun B => counts.2.2.2 B (Set.mem_univ B)⟩
end AvailableChain.PCSA.Run

end

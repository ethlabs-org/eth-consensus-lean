module
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs

public section

/-! C6 BackwardInputs: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem backward_baseVote_exact (a : HeadWire p.n) (s : Slot) (i : Fin p.n)
    (r : BlockId) (he : baseVote a = (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root)) :
    a = ⟨.seat (.head s) i, r⟩ := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => cases he
  | proposer t => cases he
  | seat l j =>
    cases l <;> delta baseVote baseHead HeadWire.decode? GridCO.fromHead at he <;> cases he
    rfl
private theorem backward_proposal_wire (w : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (hd : w.decode = some (.block s N)) : w = ⟨.proposer s, .proposal N⟩ := by
  rcases w with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at hd <;> cases hd
  | proposer t =>
    cases payload <;> delta Wire.decode at hd <;> cases hd
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at hd <;> cases hd
private theorem backward_slot_lower (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (j : Nat) (x : V) (o : Obj p) (t : Time) (s : Slot)
    (he : rho.events[j]? = some (.deliver x o t))
    (hslot : s ≤ (V2.D.Run.stateBefore E rho j x).st.slot p) :
    GridCO.proposalTime p.toParams.engine s ≤ t := by
  by_cases hz : s = 0
  · subst s
    change 4 * p.Δ * (0 : Int) ≤ t
    simp only [mul_zero]
    exact (h.valid.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? he)).1
  · change s ≤ ((V2.D.Run.stateBefore E rho j x).st.base.now / (4 * p.Δ)).toNat at hslot
    have hpos : 0 < ((V2.D.Run.stateBefore E rho j x).st.base.now / (4 * p.Δ)).toNat :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero hz) hslot
    have hn : 0 ≤ (V2.D.Run.stateBefore E rho j x).st.base.now / (4 * p.Δ) :=
      le_of_lt (Int.pos_iff_toNat_pos.mpr hpos)
    have hq : (s : Int) ≤ (V2.D.Run.stateBefore E rho j x).st.base.now / (4 * p.Δ) := by
      have hh : (s : Int) ≤
          (((V2.D.Run.stateBefore E rho j x).st.base.now / (4 * p.Δ)).toNat : Int) := by
        exact_mod_cast hslot
      rwa [Int.toNat_of_nonneg hn] at hh
    have hp := p.deltaPos
    have hlow := (Int.le_ediv_iff_mul_le (show 0 < 4 * p.Δ by positivity)).mp hq
    have ht := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho
      h.valid.toScheduleWellFormed h.noRestart he x
    rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j x)] at ht
    change (V2.D.Run.stateBefore E rho j x).st.base.now ≤ t at ht
    change 4 * p.Δ * (s : Int) ≤ t
    nlinarith
/-- In the delivery window: Every raw input at the actual voter tick reaches every honest source
late pool. -/
theorem pcsa_voter_tick_input_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      headVotes p (clock p (V2.D.Run.stateBefore E rho a x).st
        (SA.voteTime p.toParams (s + 1))) (s + 1)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) i =
        true := by
  have hs := h.valid.toScheduleWellFormed
  have he := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart ha
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at he
  rw [he] at hm
  have idx (bound : Time) (hb : bound ≤ SA.gateTime p.toParams s) :
      V2.D.Run.idxBefore rho bound ≤ k := by
    apply Nat.le_of_not_gt
    intro hi
    exact not_lt_of_ge hb ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mp hi)
  rcases pcsa_headVotes_mem p _ (s + 1) _ hm with hf | hcarried
  · have htime : SA.freezeTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
      rw [h.delta]
      change 4 * p.Δ * (s : Int) + 3 * p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      have hp := p.deltaPos
      linarith
    exact pcsa_frozen_input_relay_late_win E rho h hD (hT := hT) _ k x y hx hy s i r _ _ hc
      (idx _ htime) (List.mem_filter.mp hf.1).1 (by simpa only [Nat.add_sub_cancel] using hf.2)
  · obtain ⟨w, hw, t', N, v, hd, hNs, hv, hvote, _⟩ := hcarried
    rw [pcsa_clock_proposals] at hw
    rw [backward_proposal_wire w t' N hd] at hw
    obtain rfl := backward_baseVote_exact v s i r hvote
    obtain ⟨j, hj, t, o, t'', M, P, hjt, hdecode, hwire, hn, hparent, hacc⟩ :=
      pcsa_proposal_receipt_origin E rho _ x _ hw
    have hM : N = M := Msg.proposal.inj (congrArg (fun w : Wire p.n => w.payload) hwire)
    subst M
    have ht : t < SA.voteTime p.toParams (s + 1) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hs hjt _).mp hj
    have hslot := pcsa_blockAccepted_slot p _ t'' N P hacc
    have hNslot : N.erase.slot = s + 1 := by
      have heq : N.erase.slot = N.slot := by cases N <;> rfl
      exact heq.trans hNs
    rw [hNslot] at hslot
    have hlo := backward_slot_lower E rho h j x o t s hjt ((Nat.le_succ s).trans hslot)
    have hhandle : V2.D.Run.handlesAt E rho j x
        (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t := by
      refine ⟨o, hjt, Or.inr (Or.inl ?_)⟩
      rw [hdecode]
      exact ⟨⟨hn, P, hparent, hacc⟩, Or.inl (List.mem_map.mpr ⟨_, hv, rfl⟩)⟩
    have hpub : V2.PublicTime E (SA.voteTime p.toParams (s + 1)) := by
      refine ⟨4 * (s + 1) + 1, ?_⟩
      rw [h.delta]
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ =
        ((4 * (s + 1) + 1 : Nat) : Int) * p.Δ
      push_cast
      ring
    have hz : 0 ≤ SA.voteTime p.toParams (s + 1) := by
      have hp := p.deltaPos
      change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      positivity
    have htime : SA.voteTime p.toParams (s + 1) + E.Δ ≤ SA.gateTime p.toParams s := by
      rw [h.delta]
      change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ + p.Δ ≤
        4 * p.Δ * (s : Int) + 6 * p.Δ
      push_cast
      linarith
    exact pcsa_handled_input_relay_late_win E rho h hD
      (hT := pcsa_floor_vote (pcsa_floor_freeze_next hT)) j k x y hx hy s i r t _ _
      hpub hz (htime.trans hc) htime (idx _ htime) hlo ht hhandle
/-- Every raw input at the actual voter tick reaches every honest source late pool. -/
theorem pcsa_voter_tick_input_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      headVotes p (clock p (V2.D.Run.stateBefore E rho a x).st
        (SA.voteTime p.toParams (s + 1))) (s + 1)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) i =
        true :=
  pcsa_voter_tick_input_relay_late_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s i r (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc ha hk hm
end AvailableChain.PCSA.Run

end

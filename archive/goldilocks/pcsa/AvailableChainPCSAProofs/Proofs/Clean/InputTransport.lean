module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadRelay

public section

/-! C6 backward count inputs at the frozen and proposer read cutoffs. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A counted HEAD has the exact wire given by its label, seat, and root. -/
theorem pcsa_count_head_shape (o : GridCO.Wire p.n .root) (s : Slot) (i : Fin p.n)
    (hl : GridCO.headLabel? o = some s) (hi : GridCO.headSeat? o = some i) :
    ∃ r, o = ⟨.seat s i, .head r⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;>
    (delta GridCO.headLabel? GridCO.headSeat? at hl hi; cases hl <;> cases hi)
  exact ⟨_, rfl⟩
/-- In the delivery window: A source cap before a public cutoff becomes a cap in the receiving late
pool. -/
theorem pcsa_cap_before_public_cut_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hT : T₀ ≤ bound) (hc : bound + E.Δ ≤ cut) (hg : bound + E.Δ ≤
        SA.gateTime p.toParams s)
    (ha : a ≤ V2.D.Run.idxBefore rho bound)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (he : GridCO.equivocates (GridCO.votesAt (V2.D.Run.stateBefore E rho a x).st.base s) i = true) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  obtain ⟨v, hv, w, hw, hne, hvi, hwi⟩ := (Gen.AC.Root.cap_pair _ i).mp he
  have hvl : GridCO.headLabel? v = some s := beq_iff_eq.mp (List.mem_filter.mp hv).2
  have hwl : GridCO.headLabel? w = some s := beq_iff_eq.mp (List.mem_filter.mp hw).2
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape v s i hvl hvi
  obtain ⟨r', rfl⟩ := pcsa_count_head_shape w s i hwl hwi
  have relay (r : BlockId) (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes) :=
    pcsa_head_before_public_cut_relay_late_floor E rho h hD (hT := hT) a k x y hx hy s i r bound u
      hpub hzero hc hg hk hm
      (pcsa_head_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
        a x s i r bound ha hm)
  rcases relay r (List.mem_filter.mp hv).1 with hv' | he
  · rcases relay r' (List.mem_filter.mp hw).1 with hw' | he
    · exact (Gen.AC.Root.cap_pair _ i).mpr ⟨_, hv', _, hw', hne, hvi, hwi⟩
    · exact he
  · exact he
/-- A source cap before a public cutoff becomes a cap in the receiving late pool. -/
theorem pcsa_cap_before_public_cut_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hc : bound + E.Δ ≤ cut) (hg : bound + E.Δ ≤ SA.gateTime p.toParams s)
    (ha : a ≤ V2.D.Run.idxBefore rho bound)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (he : GridCO.equivocates (GridCO.votesAt (V2.D.Run.stateBefore E rho a x).st.base s) i = true) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true :=
  pcsa_cap_before_public_cut_relay_late_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x
    y hx hy s i bound u hpub hzero hzero hc hg ha hk he
/-- In the delivery window: A proposer pool input before its public read reaches a later late
denominator. -/
theorem pcsa_proposer_input_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (v u : Time)
    (hT : T₀ ≤ SA.proposalTime p.toParams (s + 1)) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : a ≤ V2.D.Run.idxBefore rho (GridCO.proposalTime p.toParams.engine (s + 1)))
    (hk : V2.D.Run.idxBefore rho
      (GridCO.proposalTime p.toParams.engine (s + 1) + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho a x).st v) (s + 1)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  have hmem := (List.mem_filter.mp hm).1
  rw [pcsa_clock_heads] at hmem
  have hpub : V2.PublicTime E (GridCO.proposalTime p.toParams.engine (s + 1)) := by
    refine ⟨4 * (s + 1), ?_⟩
    rw [h.delta]
    change 4 * p.Δ * ((s + 1 : Nat) : Int) = ((4 * (s + 1) : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ GridCO.proposalTime p.toParams.engine (s + 1) := by
    have hp := p.deltaPos
    change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Int)
    positivity
  have hg : GridCO.proposalTime p.toParams.engine (s + 1) + E.Δ ≤
      SA.gateTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  exact pcsa_head_before_public_cut_relay_late_floor E rho h hD (hT := hT) a k x y hx hy s i r _ u
    hpub hz (hg.trans hc) hg hk hmem
    (pcsa_head_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
      a x s i r _ ha hmem)
/-- A proposer pool input before its public read reaches a later late denominator. -/
theorem pcsa_proposer_input_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (v u : Time)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : a ≤ V2.D.Run.idxBefore rho (GridCO.proposalTime p.toParams.engine (s + 1)))
    (hk : V2.D.Run.idxBefore rho
      (GridCO.proposalTime p.toParams.engine (s + 1) + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho a x).st v) (s + 1)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true :=
  pcsa_proposer_input_relay_late_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy
    s i r v u (pcsa_zero_le_proposal (s + 1)) hc ha hk hm
/-- In the delivery window: A frozen pool input relays by the next proposal time into the source
late denominator. -/
theorem pcsa_frozen_input_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (v u : Time)
    (hT : T₀ ≤ SA.freezeTime p.toParams s) (hc : SA.gateTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes)
    (hs : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  rw [pcsa_clock_heads] at hm
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho a x ⟨.seat s i, .head r⟩ hm
  have hstamp : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head r⟩ = GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head r⟩ := by
    delta GridCO.stampVote
    rw [pcsa_clock_headStamps, hr]
    rfl
  rw [hstamp] at hs
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.freezeTime p.toParams s := by
    have hp := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  have hg : SA.freezeTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  exact pcsa_head_before_public_cut_relay_late_floor E rho h hD (hT := hT) a k x y hx hy s i r _ u
    hpub hz (hg.trans hc) hg hk hm hs

/-- A frozen pool input relays by the next proposal time into the source late denominator. -/
theorem pcsa_frozen_input_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (v u : Time)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes)
    (hs : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true :=
  pcsa_frozen_input_relay_late_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy s
    i r v u (pcsa_floor_freeze (pcsa_zero_le_proposal s)) hc hk hm hs
/-- In the delivery window: A handled raw input relays even when its source handler retained only a
cap. -/
theorem pcsa_handled_input_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (j k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (t bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hT : T₀ ≤ bound) (hc : bound + E.Δ ≤ cut) (hg : bound + E.Δ ≤
        SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (ht : GridCO.proposalTime p.toParams.engine s ≤ t) (hb : t < bound)
    (hh : V2.D.Run.handlesAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  obtain ⟨parent, he, hhandle⟩ := hh
  have hj : j + 1 ≤ V2.D.Run.idxBefore rho bound := Nat.succ_le_of_lt
    ((Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he bound).mpr hb)
  have hgate : t < SA.gateTime p.toParams s := by
    have hp := E.Δ_pos
    linarith
  rcases pcsa_handled_head_stateBefore_mem_or_cap E rho h j x t s i r ht hgate ⟨parent, he,
    hhandle⟩ with hm | he
  · exact pcsa_head_before_public_cut_relay_late_floor E rho h hD (hT := hT) (j + 1) k x y hx hy s
      i r bound u hpub hzero hc hg hk hm
      (pcsa_head_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
        (j + 1) x s i r bound hj hm)
  · exact Or.inr (pcsa_cap_before_public_cut_relay_late_win E rho h hD (hT := hT) (j + 1) k x y hx
      hy
      s i bound u hpub hzero hc hg hj hk he)

/-- A handled raw input relays even when its source handler retained only a cap. -/
theorem pcsa_handled_input_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (j k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (t bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hc : bound + E.Δ ≤ cut) (hg : bound + E.Δ ≤ SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (ht : GridCO.proposalTime p.toParams.engine s ≤ t) (hb : t < bound)
    (hh : V2.D.Run.handlesAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true :=
  pcsa_handled_input_relay_late_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) j k x y hx hy
    s i r t bound u hpub hzero hzero hc hg hk ht hb hh
/-- In the delivery window: The actual proposer tick supplies backward receipt at any honest source
gate. -/
theorem pcsa_proposer_tick_input_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hT : T₀ ≤ SA.proposalTime p.toParams (s + 1)) (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (GridCO.proposalTime p.toParams.engine (s + 1))))
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho a x).st
        (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) i =
        true := by
  have hs := h.valid.toScheduleWellFormed
  have he := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs h.noRestart ha
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at he
  rw [he] at hm
  have htime : GridCO.proposalTime p.toParams.engine (s + 1) + E.Δ ≤
      SA.gateTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    have hp := p.deltaPos
    nlinarith
  have hi : V2.D.Run.idxBefore rho
      (GridCO.proposalTime p.toParams.engine (s + 1) + E.Δ) ≤ k := by
    apply Nat.le_of_not_gt
    intro hi
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mp hi
    exact not_lt_of_ge htime ht
  exact pcsa_proposer_input_relay_late_win E rho h hD (hT := hT) _ k x y hx hy s i r _ _ hc
    (le_refl _) hi hm
/-- The actual proposer tick supplies backward receipt at any honest source gate. -/
theorem pcsa_proposer_tick_input_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId)
    (hc : SA.gateTime p.toParams s ≤ cut)
    (ha : rho.events[a]? = some (.tick x (GridCO.proposalTime p.toParams.engine (s + 1))))
    (hk : rho.events[k]? = some (.tick y (SA.gateTime p.toParams s)))
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      proposerVotes (clock p (V2.D.Run.stateBefore E rho a x).st
        (GridCO.proposalTime p.toParams.engine (s + 1))) (s + 1)) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s ∨
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine
      (actView (clock p (V2.D.Run.stateBefore E rho k y).st (SA.gateTime p.toParams s))) s) i =
        true :=
  pcsa_proposer_tick_input_relay_late_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y
    hx hy s i r (pcsa_zero_le_proposal (s + 1)) hc ha hk hm
end AvailableChain.PCSA.Run

end

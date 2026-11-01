module
public import AvailableChainPCSAProofs.Proofs.Clean.HeadTransport

public section

/-! C6 actual HEAD acceptance bounds and strict relay into late denominators. -/
namespace AvailableChain.PCSA
/-- A body that passes its handler has a slot no later than the store slot. -/
theorem pcsa_blockAccepted_slot (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (h : blockAccepted p st s N P = true) : N.erase.slot ≤ st.slot p := by
  change ((N.erase != .genesis && decide (N.erase.slot ≤ st.slot p)) &&
    _ && _ && _ && _ && _ && _ && _) = true at h
  have h8 := (Bool.and_eq_true_iff.mp h).1
  have h7 := (Bool.and_eq_true_iff.mp h8).1
  have h6 := (Bool.and_eq_true_iff.mp h7).1
  have h5 := (Bool.and_eq_true_iff.mp h6).1
  have h4 := (Bool.and_eq_true_iff.mp h5).1
  have h3 := (Bool.and_eq_true_iff.mp h4).1
  have h2 := (Bool.and_eq_true_iff.mp h3).1
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h2).2
end AvailableChain.PCSA
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem source_head_exact (a : HeadWire p.n) (s : Slot) (i : Fin p.n) (r : BlockId)
    (h : ofHead p a = (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p)) :
    a = ⟨.seat (.head s) i, r⟩ := by
  have he : (⟨a.auth, .head a.payload⟩ : Wire p.n) = ⟨.seat (.head s) i, .head r⟩ :=
    (toWireEquiv p).symm.injective h
  have ha := congrArg (fun w : Wire p.n => w.auth) he
  have hr := Msg.head.inj (congrArg (fun w : Wire p.n => w.payload) he)
  cases a
  cases ha
  cases hr
  rfl
/-- An actual accepting HEAD handler reads a store slot at least its label. -/
theorem pcsa_head_accepting_slot (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n) (r : BlockId) (t : Time)
    (ha : V2.D.Run.acceptsAt E rho k x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    s ≤ (V2.D.Run.stateBefore E rho k x).st.slot p := by
  obtain ⟨parent, he, hh⟩ := ha.1
  rcases hh with hdir | hh | hh
  · subst parent
    have hnot : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∉
        (V2.D.Run.stateBefore E rho k x).st.base.votes := by
      have hf := ha.2.1
      change decide ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBefore E rho k x).st.base.votes) = false at hf
      exact of_decide_eq_false hf
    have hmem : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBefore E rho (k + 1) x).st.base.votes := by
      have hp := ha.2.2
      change decide ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBefore E rho (k + 1) x).st.base.votes) = true at hp
      exact of_decide_eq_true hp
    rw [V2.D.Run.stateBefore_succ E rho he] at hmem
    change _ ∈ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.votes at hmem
    rw [Function.update_self] at hmem
    change _ ∈ (GridCO.admitVote p.toParams.engine
      (V2.D.Run.stateBefore E rho k x).st.base ⟨.seat s i, .head r⟩).votes at hmem
    by_contra hslot
    have hcur : ((V2.D.Run.stateBefore E rho k x).st.base.now / (4 * p.Δ)).toNat < s :=
      Nat.lt_of_not_ge hslot
    have hkeep : (GridCO.admitVote p.toParams.engine
        (V2.D.Run.stateBefore E rho k x).st.base ⟨.seat s i, .head r⟩).votes =
        (V2.D.Run.stateBefore E rho k x).st.base.votes := by
      change ((V2.D.Run.stateBefore E rho k x).st.base.now /
        (4 * p.toParams.engine.Δ)).toNat < s at hcur
      delta GridCO.admitVote
      simp only [hcur, decide_true, Bool.or_true, Bool.true_or, ite_true]
    exact hnot (hkeep ▸ hmem)
  · cases hd : (toWire p parent).decode with
    | none => rw [hd] at hh; exact hh.elim
    | some msg => cases msg with
      | vote j a root => rw [hd] at hh; exact hh.elim
      | row a body => rw [hd] at hh; exact hh.elim
      | ack j a root => rw [hd] at hh; exact hh.elim
      | pc C =>
        rw [hd] at hh
        obtain ⟨a, _, heq⟩ := List.mem_map.mp hh
        have hp := congrArg (fun o : Obj p => o.payload) heq
        cases hp
      | block j N =>
        rw [hd] at hh
        obtain ⟨⟨_, P, hp, hacc⟩, hh⟩ := hh
        rcases hh with hh | hh | hh
        · obtain ⟨a, ham, heq⟩ := List.mem_map.mp hh
          have hbody := pcsa_blockAccepted_slot p _ j N P hacc
          change N.erase.slot ≤ (V2.D.Run.stateBefore E rho k x).st.slot p at hbody
          have hw := h.valid.wire k x parent t he
          change wellFormed p (toWire p parent) = true at hw
          delta wellFormed at hw
          rw [hd] at hw
          change (N.erase != .genesis && j == N.erase.slot &&
            decide (N.erase.parent.slot < N.erase.slot) &&
            N.raw.all (fun v => match v.decode? with
              | some (q, _, _) => q + 1 == N.erase.slot
              | none => false) && _ && _ && _ && _) = true at hw
          have h8 := (Bool.and_eq_true_iff.mp hw).1
          have h7 := (Bool.and_eq_true_iff.mp h8).1
          have h6 := (Bool.and_eq_true_iff.mp h7).1
          have h5 := (Bool.and_eq_true_iff.mp h6).1
          have hraw := (Bool.and_eq_true_iff.mp h5).2
          have hv := List.all_eq_true.mp hraw a ham
          obtain rfl := source_head_exact a s i r heq
          change (s + 1 == N.erase.slot) = true at hv
          have hs : s + 1 = N.erase.slot := beq_iff_eq.mp hv
          rw [← hs] at hbody
          exact (Nat.le_succ s).trans hbody
        · obtain ⟨a, _, heq⟩ := List.mem_map.mp hh
          have hp := congrArg (fun o : Obj p => o.payload) heq
          cases hp
        · obtain ⟨a, _, heq⟩ := List.mem_map.mp hh
          have hp := congrArg (fun o : Obj p => o.payload) heq
          cases hp
  · obtain ⟨_, C, heq, _, _⟩ := hh
    have hp := congrArg (fun o : Obj p => o.payload) heq
    cases hp
/-- No accepted HEAD, including a faulty one, can arrive before its slot start. -/
theorem pcsa_head_acceptance_after_slot_start (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (k : Nat) (x : V) (s : Slot) (i : Fin p.n) (r : BlockId) (t : Time)
    (ha : V2.D.Run.acceptsAt E rho k x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t) :
    GridCO.proposalTime p.toParams.engine s ≤ t := by
  obtain ⟨parent, he, _⟩ := ha.1
  by_cases hs : s = 0
  · subst s
    change 4 * p.Δ * (0 : Int) ≤ t
    simp only [mul_zero]
    exact (h.valid.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? he)).1
  · have hslot := pcsa_head_accepting_slot E rho h k x s i r t ha
    change s ≤ ((V2.D.Run.stateBefore E rho k x).st.base.now / (4 * p.Δ)).toNat at hslot
    have hq : (s : Int) ≤ (V2.D.Run.stateBefore E rho k x).st.base.now / (4 * p.Δ) := by
      have hspos : 0 < s := Nat.pos_of_ne_zero hs
      have hpos : 0 < ((V2.D.Run.stateBefore E rho k x).st.base.now / (4 * p.Δ)).toNat :=
        lt_of_lt_of_le hspos hslot
      have hn : 0 ≤ (V2.D.Run.stateBefore E rho k x).st.base.now / (4 * p.Δ) :=
        le_of_lt (Int.pos_iff_toNat_pos.mpr hpos)
      have hh : (s : Int) ≤
          (((V2.D.Run.stateBefore E rho k x).st.base.now / (4 * p.Δ)).toNat : Int) := by
        exact_mod_cast hslot
      rwa [Int.toNat_of_nonneg hn] at hh
    have hd := p.deltaPos
    have hlow := (Int.le_ediv_iff_mul_le (show 0 < 4 * p.Δ by positivity)).mp hq
    have ht := V2.D.Engine.stateBefore_now_le_event_noRestart (pcsaClock p c) E rho
      h.valid.toScheduleWellFormed h.noRestart he x
    rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho k x)] at ht
    change (V2.D.Run.stateBefore E rho k x).st.base.now ≤ t at ht
    change 4 * p.Δ * (s : Int) ≤ t
    nlinarith
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem relay_clock_lt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (x : V)
    (cut : Time) (hc : 0 < cut) :
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho cut) x).st.base.now < cut := by
  have hr := pcsa_clock_read p c (m := m)
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho cut) x)
  rcases V2.D.Engine.stateBefore_now_source_noRestart (pcsaClock p c) E rho h.noRestart
      (V2.D.Run.idxBefore rho cut) x with hz | ⟨j, hj, he⟩
  · rw [hr] at hz
    rw [hz]
    exact hc
  · rw [hr] at he
    exact (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed he cut).mp hj
private theorem relay_slot_upper (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (x : V)
    (cut : Time) (s : Slot) (hc : 0 < cut) (hg : cut ≤ SA.gateTime p.toParams s) :
    (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho cut) x).st.slot p ≤ s + 1 := by
  have ht := relay_clock_lt E rho h x cut hc
  have hd := p.deltaPos
  change cut ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ at hg
  change ((V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho cut) x).st.base.now /
    (4 * p.Δ)).toNat ≤ s + 1
  apply Int.toNat_le.mpr
  apply (Int.ediv_le_iff_le_mul (show 0 < 4 * p.Δ by positivity)).mpr
  push_cast
  nlinarith
omit [DecidableEq V] in
private theorem pcsa_relay_idx_mono (rho : V2.D.Run V (pcsaWith m p c)) {a b : Time}
    (hab : a ≤ b) : V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) hab))
/-- An accepted HEAD reaches each honest node's late pool by the window deadline
`max t T₀ + Δ`, or its capped seat does. The acceptance may precede the floor. -/
theorem pcsa_head_relay_late_or_cap_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (j k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (t u : Time)
    (ha : V2.D.Run.acceptsAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t)
    (hc : max t T₀ + E.Δ ≤ cut)
    (hg : max t T₀ + E.Δ ≤ SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (max t T₀ + E.Δ) ≤ k) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
      GridCO.equivocates (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  let obj : Obj p := ⟨.seat (.base (.head s)) i, .head r⟩
  have hS := h.valid.toScheduleWellFormed
  have ht0 := pcsa_head_acceptance_after_slot_start E rho h j x s i r t ha
  have hnonneg : 0 ≤ t := by
    have hd := p.deltaPos
    change 4 * p.Δ * (s : Int) ≤ t at ht0
    nlinarith [Int.natCast_nonneg s]
  have hnr : ∀ body, obj.payload ≠ .row body := by intro body he; cases he
  obtain ⟨d, htd, hdD, _, hrel⟩ := pcsa_strict_relay_from E rho hD obj hnr x j t hx ha
  have hpos : 0 < d := lt_of_le_of_lt hnonneg htd
  have hdc : d ≤ cut := hdD.trans hc
  have hdg : d ≤ SA.gateTime p.toParams s := hdD.trans hg
  have hdk : V2.D.Run.idxBefore rho d ≤ k := (pcsa_relay_idx_mono rho hdD).trans hk
  obtain ⟨parent, hparent, _⟩ := ha.1
  have hj : j + 1 ≤ V2.D.Run.idxBefore rho d := Nat.succ_le_of_lt
    ((Gen.V2.Duty.index_lt_idxBefore_iff hS hparent _).mpr htd)
  by_cases hOld : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (j + 1) y) obj = true
  · have hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.base.votes := of_decide_eq_true hOld
    exact Or.inl (pcsa_head_before_cut_mem_late E rho hS h.noRestart (j + 1) k y s i r
      d u (hj.trans hdk) hj hdg hm)
  · by_cases hEx : (pcsaWith m p c).excludes (V2.D.Run.stateBeforeTime E rho d y) obj = true
    · have he : GridCO.excludes p.toParams.engine
          (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) y).st.base
          ⟨.seat s i, .head r⟩ = true := by
        rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
        exact hEx
      obtain ⟨_, hold | hcap⟩ := (FGSA.Run.Internal.grid_excludes_head_iff _ s i r).mp he
      · have hu := relay_slot_upper E rho h y d s hpos hdg
        change s + 1 <
          (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) y).st.slot p at hold
        exact (Nat.not_lt.mpr hu hold).elim
      · exact Or.inr (pcsa_cap_before_cut_mem_late E rho hS h.noRestart _ k y s i
          d u hdk (le_refl _) hdg hcap)
    · obtain ⟨t', htt, htd', hhandle⟩ := hrel y hy (Bool.eq_false_iff.mpr hOld) hdc
        (Bool.eq_false_iff.mpr hEx)
      obtain ⟨q, hq⟩ := hhandle
      have hq' : q + 1 ≤ V2.D.Run.idxBefore rho d := by
        obtain ⟨parent, he, _⟩ := hq
        exact Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hS he _).mpr htd')
      exact pcsa_handled_head_late_or_cap E rho h q k y t' d u s i r
        (hq'.trans hdk) (ht0.trans htt) htd' hdg hq
/-- An accepted HEAD reaches each honest node's later late pool, or its capped seat does. -/
theorem pcsa_head_relay_late_or_cap (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (j k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (t u : Time)
    (ha : V2.D.Run.acceptsAt E rho j x
      (⟨.seat (.base (.head s)) i, .head r⟩ : Obj p) t)
    (hc : t + E.Δ ≤ cut) (hg : t + E.Δ ≤ SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (t + E.Δ) ≤ k) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
      GridCO.equivocates (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  have ht0 := pcsa_head_acceptance_after_slot_start E rho h j x s i r t ha
  have hmax : max t 0 = t := by
    apply max_eq_left
    have hd := p.deltaPos
    change 4 * p.Δ * (s : Int) ≤ t at ht0
    nlinarith [Int.natCast_nonneg s]
  have hw := pcsa_head_relay_late_or_cap_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0)
    j k x y hx hy s i r t u ha
  rw [hmax] at hw
  exact hw hc hg hk
end AvailableChain.PCSA.Run
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Any pooled HEAD stamped before a public cutoff `bound` relays into the later late
denominator by the window deadline `max bound T₀ + Δ`. -/
theorem pcsa_head_before_public_cut_relay_late_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hc : max bound T₀ + E.Δ ≤ cut) (hg : max bound T₀ + E.Δ ≤ SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (max bound T₀ + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes)
    (hs : GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head r⟩ < bound) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
      GridCO.equivocates (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  obtain ⟨j, _, t, ha, ht⟩ := pcsa_head_accepted_before E rho h.valid.toScheduleWellFormed
    h.noRestart a x s i r bound hpub hzero hm hs
  have hd : max t T₀ + E.Δ ≤ max bound T₀ + E.Δ :=
    Int.add_le_add_right (max_le_max ht.le (le_refl T₀)) E.Δ
  exact pcsa_head_relay_late_or_cap_win E rho h hD j k x y hx hy s i r t u ha
    (hd.trans hc) (hd.trans hg) ((pcsa_relay_idx_mono rho hd).trans hk)
/-- The public-cut HEAD relay with a floor `T₀ ≤ bound`: the deadline is `bound + Δ`. -/
theorem pcsa_head_before_public_cut_relay_late_floor (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound) (hT : T₀ ≤ bound)
    (hc : bound + E.Δ ≤ cut) (hg : bound + E.Δ ≤ SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes)
    (hs : GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head r⟩ < bound) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
      GridCO.equivocates (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  have hw := pcsa_head_before_public_cut_relay_late_win E rho h hD a k x y hx hy s i r bound u
    hpub hzero
  rw [max_eq_left hT] at hw
  exact hw hc hg hk hm hs
/-- Any pooled HEAD stamped before a public cutoff relays into the later late denominator. -/
theorem pcsa_head_before_public_cut_relay_late (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (bound u : Time)
    (hpub : V2.PublicTime E bound) (hzero : 0 ≤ bound)
    (hc : bound + E.Δ ≤ cut) (hg : bound + E.Δ ≤ SA.gateTime p.toParams s)
    (hk : V2.D.Run.idxBefore rho (bound + E.Δ) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes)
    (hs : GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head r⟩ < bound) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈ GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s ∨
      GridCO.equivocates (GridCO.lateVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho k y).st u)) s) i = true := by
  have hw := pcsa_head_before_public_cut_relay_late_win E rho h
    (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy s i r bound u hpub hzero
  rw [max_eq_left hzero] at hw
  exact hw hc hg hk hm hs
end AvailableChain.PCSA.Run

end

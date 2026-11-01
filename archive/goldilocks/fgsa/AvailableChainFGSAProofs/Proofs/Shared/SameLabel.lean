module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSARun.Proofs.RootResolution

public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

private theorem sl_vote_shape {n : Nat} (o : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

private theorem sl_clean_mem (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (o : GridCO.Wire p.n .root) (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s) :
    o ∈ v.votes ∧ GridCO.headLabel? o = some s ∧
      GridCO.stampVote v o < SA.earlyTime p.toParams s ∧
      ∀ u ∈ GridCO.lateVotes p.toParams.engine v s,
        GridCO.sameSeat u o = true → u = o := by
  change o ∈ (GridCO.earlyVotes p.toParams.engine v s).filter _ at ho
  obtain ⟨he, hc⟩ := List.mem_filter.mp ho
  obtain ⟨hv, hr⟩ := List.mem_filter.mp he
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hv
  have hstamp : GridCO.stampVote v o < SA.earlyTime p.toParams s := by
    unfold GridCO.resolvedBefore at hr
    cases ht : GridCO.resolvedHead? v o with
    | none => simp only [ht, Bool.false_eq_true] at hr
    | some B =>
      rw [ht] at hr
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).2
  refine ⟨hm, by simpa only [beq_iff_eq] using hl, hstamp, ?_⟩
  intro u hu hs
  have hc' : (GridCO.lateVotes p.toParams.engine v s).any
      (fun u => GridCO.sameSeat u o && u != o) = false := by
    simpa only [Bool.not_eq_true'] using hc
  have hn := List.any_eq_false.mp hc' u hu
  simpa only [hs, Bool.true_and, bne_iff_ne, not_not] using hn

private theorem sl_clean_late (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    GridCO.cleanSupport p.toParams.engine v s ⊆ GridCO.lateVotes p.toParams.engine v s := by
  intro o ho
  have h := sl_clean_mem p v s o ho
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨h.1, by simpa only [beq_iff_eq] using h.2.1⟩, ?_⟩
  apply decide_eq_true
  have hd := p.deltaPos
  change GridCO.stampVote v o < 4 * p.Δ * (s : Int) + 6 * p.Δ
  have ht := h.2.2.1
  change GridCO.stampVote v o < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
  linarith

private theorem sl_same_seat {n : Nat} (u v : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hu : GridCO.headLabel? u = some s) (hv : GridCO.headLabel? v = some s)
    (hku : GridCO.headSeat? u = some k) (hkv : GridCO.headSeat? v = some k) :
    GridCO.sameSeat u v = true := by
  obtain ⟨B, rfl⟩ := sl_vote_shape u s k hu hku
  obtain ⟨C, rfl⟩ := sl_vote_shape v s k hv hkv
  change (s == s && k == k) = true
  simp only [BEq.rfl, Bool.and_self]

private theorem sl_clean_no_equiv (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (o : GridCO.Wire p.n .root) (ho : o ∈ GridCO.cleanSupport p.toParams.engine v s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) k = false := by
  cases he : GridCO.equivocates (GridCO.lateVotes p.toParams.engine v s) k with
  | false => rfl
  | true =>
    obtain ⟨u, hu, w, hw, hn, hku, hkw⟩ := (cap_pair _ k).mp he
    have h := sl_clean_mem p v s o ho
    have hl (a : GridCO.Wire p.n .root) (ha : a ∈ GridCO.lateVotes p.toParams.engine v s) :
        GridCO.headLabel? a = some s := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp (List.mem_filter.mp ha).1).2
    have eu := h.2.2.2 u hu (sl_same_seat u o s k (hl u hu) h.2.1 hku hk)
    have ew := h.2.2.2 w hw (sl_same_seat w o s k (hl w hw) h.2.1 hkw hk)
    exact (hn (eu.trans ew.symm)).elim

private theorem sl_clean_pool (p : Params) (v : GridCO.State p.n .root) (s : Slot) :
    ∀ k, GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) k = false := by
  intro k
  cases he : GridCO.equivocates (GridCO.cleanSupport p.toParams.engine v s) k with
  | false => rfl
  | true =>
    obtain ⟨u, hu, _, _, _, hk, _⟩ := (cap_pair _ k).mp he
    have hf := sl_clean_no_equiv p v s u hu k hk
    have ht := vote_pool_equivocates_mono _ _ k (sl_clean_late p v s) he
    rw [hf] at ht
    contradiction

private def sl_support (p : Params) (v : GridCO.State p.n .root) (s : Slot) (B : Block) :
    Finset (Fin p.n) :=
  (GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset.filter
    (fun k => poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) k B = true)

private theorem sl_support_mem (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (B : Block) (k : Fin p.n) : k ∈ sl_support p v s B ↔
      ∃ o ∈ GridCO.cleanSupport p.toParams.engine v s,
        GridCO.headSeat? o = some k ∧ voteSupports v.blocks B o = true := by
  change k ∈ ((GridCO.seats p.n (GridCO.cleanSupport p.toParams.engine v s)).toFinset.filter
    (fun j => poolSupports v.blocks (GridCO.cleanSupport p.toParams.engine v s) j B = true)) ↔ _
  rw [Finset.mem_filter, vote_pool_support_witness]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(vote_pool_mem_seats _ k).mpr (by obtain ⟨o, ho, hk, _⟩ := h; exact ⟨o, ho, hk⟩), h⟩

private theorem sl_score (p : Params) (v : GridCO.State p.n .root) (s : Slot) (B : Block)
    (hscore : SA.Root.prefixSupport p.toParams v s B =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) B) :
    SA.Root.prefixSupport p.toParams v s B = (sl_support p v s B).card := by
  rw [hscore]
  rw [vote_pool_score_card]
  simp only [sl_clean_pool p v s, Bool.false_or]
  rfl

private theorem sl_result_majority (p : Params) (v : GridCO.State p.n .root) (s : Slot)
    (a B : Block) (h : SA.Root.confirmationFrom p.toParams a v s = some B)
    (hscore : ∀ C, SA.Root.prefixSupport p.toParams v s C =
      GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) C) :
    (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset.card <
      2 * (sl_support p v s B).card := by
  have hex : ∃ C, GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s C ∧ some C = some B := by
    change (if _ then some _ else none) = some B at h
    split at h
    · exact ⟨_, ‹_›, h⟩
    · contradiction
  obtain ⟨C, hc, he⟩ := hex
  have := Option.some.inj he
  subst C
  rwa [sl_score p v s B (hscore B), vote_pool_voterCount_card] at hc

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem sl_idx_mono (rho : V2.D.Run V (fgsa p c)) : Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

private theorem sl_votes_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho j x).st.base.votes :=
  fgsa_votes_cumulative_on p c E rho hij x (hN.restartFree x i j)

private theorem sl_gate_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes) :
    GridCO.stampVote (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
      (SA.gateTime p.toParams s))) o =
      GridCO.stampVote (V2.D.Run.stateBefore E rho i x).st.base o := by
  have hk := fgsa_vote_stamp_keys E rho i x
  rw [← hk] at hm
  obtain ⟨⟨v, t⟩, hv, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst v
  change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
  rw [(clockPre_stamps p _ _).2]
  unfold GridCO.stampVote
  cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
      (fun row => row.1 == o) with
  | none =>
    have hn := List.find?_eq_none.mp hf (o, t) hv
    simp only [beq_self_eq_true] at hn
    contradiction
  | some row => rfl

private theorem sl_gate_late (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (hEpoch : ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w < SA.gateTime p.toParams s)
    (o : GridCO.Wire p.n .root) (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hl : GridCO.headLabel? o = some s) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s))) s := by
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [beq_iff_eq] using hl⟩
    change o ∈ (clockPre p _ _).base.votes
    rwa [(Internal.clockPre_vn _ _).1]
  · rw [sl_gate_stamp E rho i x s o hm]
    have hpos : 0 < SA.gateTime p.toParams s := by
      change 0 < 4 * p.Δ * (s : Int) + 6 * p.Δ
      have hd := p.deltaPos
      positivity
    have hn := fgsa_preTick_now_lt E rho hS hi hpos hEpoch
    have hb := (fgsa_stateBefore_bounds E rho hS i x).2
    unfold GridCO.stampVote
    cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
        (fun row => row.1 == o) with
    | none => exact hn
    | some row => exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

private theorem sl_read_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (d : Time) (hd : d ≤ SA.gateTime p.toParams s) :
    (V2.D.Run.stateBeforeTime E rho d x).st.slot p ≤ s + 1 := by
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (sl_idx_mono rho hd) x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho d) x),
    fgsa_clock_now p c (V2.D.Run.stateBefore E rho
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)) x)] at hm
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho d hS,
    Gen.V2.Duty.stateBefore_idxBefore E rho _ hS,
    ← fgsa_preTick_eq_timeRead E rho hS hN hi] at hm
  have hb := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c)
    E rho hS hi x
  rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x)] at hb
  have hs := Internal.slotOf_mono (p := p) (hm.trans hb)
  have he : p.slotOf (SA.gateTime p.toParams s) = s + 1 := by
    exact (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  exact hs.trans_eq he

private theorem sl_relay (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.gateTime p.toParams s)))
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late k = true := by
  dsimp only
  have hc := sl_clean_mem p _ s o ho
  obtain ⟨B, rfl⟩ := sl_vote_shape o s k hc.2.1 hk
  have hmem : (⟨.seat s k, .head B⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho ix x).st.base.votes := by
    have hm := hc.1
    change _ ∈ (clockPre p _ _).base.votes at hm
    rwa [(Internal.clockPre_vn _ _).1] at hm
  have ht := hc.2.2.1
  rw [sl_gate_stamp E rho ix x s _ hmem] at ht
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity
  obtain ⟨j, _, t, ha, ht⟩ := fgsa_vote_accepted_before E rho hE hN
    ix x s k B _ hpub hz hmem ht
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hd : dl t ≤ SA.gateTime p.toParams s := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) ≤
        4 * p.Δ * (s : Int) + 2 * p.Δ := max_le (le_of_lt ht) (by linarith)
    linarith
  have hT : Gen.V2.Duty.Trigger E rho
      (ofHead p ⟨.seat (.head s) k, B⟩) t :=
    Or.inr ⟨x, hx, j, ha⟩
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s k B t y hD
    hT hy (hd.trans hcut) (hlt t)
    (sl_read_window E rho hE.toScheduleWellFormed hN hiy (dl t) hd)
    (hd.trans (hE.in_horizon _ (List.mem_of_getElem? hiy)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hiy hy
      (fgsa_trigger_nonneg E rho hE.toScheduleWellFormed hT) hd)
  have hkeep : (V2.D.Run.stateBeforeTime E rho (dl t) y).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho iy y).st.base.votes := by
    rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hiy,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact sl_votes_mono E rho hN y (sl_idx_mono rho hd)
  rcases hr with hr | ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩
  · exact Or.inl (sl_gate_late E rho hE.toScheduleWellFormed hiy
        (fun j w _ he => False.elim (hN j _ w he)) _ (hkeep hr.1) rfl)
  · exact Or.inr ((cap_pair _ k).mpr ⟨u,
      sl_gate_late E rho hE.toScheduleWellFormed hiy
        (fun j w _ he => False.elim (hN j _ w he)) u (hkeep hu) hlu, v,
      sl_gate_late E rho hE.toScheduleWellFormed hiy
        (fun j w _ he => False.elim (hN j _ w he)) v (hkeep hv) hlv, hne, hku, hkv⟩)

private theorem sl_gate_input (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (s : Slot) (B : Block) (h : gateResult p c E rho x s = some (some B)) :
    ∃ i, rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p (V2.D.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s)).fg.F)
        (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
          (SA.gateTime p.toParams s))) s = some B := by
  have hex : ∃ i, IsGateTick p c rho i x s := by
    rw [gateResult_def] at h
    obtain ⟨st, hgate, _⟩ := Option.map_eq_some_iff.mp h
    rw [gateIn_def, preTick_def] at hgate
    obtain ⟨nd, hpre, _⟩ := Option.map_eq_some_iff.mp hgate
    obtain ⟨i, hi, _⟩ := Option.map_eq_some_iff.mp hpre
    exact ⟨i, V2.D.Run.tickIdx?_spec hi⟩
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, (fgsa_gate_raw_of_nonempty p c E rho hS hi h).2⟩


/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
P3 F1b.2, blueprint 02 §2.2 and 21 IF.6: two honest raw gate results
at one synchronized label are compatible. Class (ii), T7.8 receipt instance
and Gen A2/A3 count assembly. DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405
`eligible_compatible`. INTENTIONAL: use the optional F-anchored active-view
result (spec/fgsa-protocol.tex:2496–2513), with label-local synchronization.
No participation or honest-majority premise is needed for compatibility.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_sameLabel (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ x y B C, x ∈ rho.honest → y ∈ rho.honest →
      gateResult p c E rho x s = some (some B) →
      gateResult p c E rho y s = some (some C) → Block.Compatible B C := by
  intro x y B C hx hy hB hC
  obtain ⟨ix, hix, hB⟩ := sl_gate_input E rho hE.toScheduleWellFormed x s B hB
  obtain ⟨iy, hiy, hC⟩ := sl_gate_input E rho hE.toScheduleWellFormed y s C hC
  let vx := actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))
  let vy := actView (clockPre p (V2.D.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))
  let Lx := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine vx s)).toFinset
  let Ly := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine vy s)).toFinset
  have own (v : GridCO.State p.n .root) (D : Block) : sl_support p v s D ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset := by
    intro k hk
    obtain ⟨o, ho, hko, _⟩ := (sl_support_mem p v s D k).mp hk
    exact (vote_pool_mem_seats _ k).mpr ⟨o, sl_clean_late p v s ho, hko⟩
  have cross {ia ib : Nat} {a b : V} (ha : a ∈ rho.honest) (hb : b ∈ rho.honest)
      (hib : rho.events[ib]? = some (.tick b (SA.gateTime p.toParams s))) (D : Block) :
      sl_support p (actView (clockPre p (V2.D.Run.stateBefore E rho ia a).st
        (SA.gateTime p.toParams s))) s D ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
        (actView (clockPre p (V2.D.Run.stateBefore E rho ib b).st
          (SA.gateTime p.toParams s))) s)).toFinset := by
    intro k hk
    obtain ⟨o, ho, hko, _⟩ := (sl_support_mem p _ s D k).mp hk
    rcases sl_relay E rho hE hN hDelta s hSync ha hb hib o ho k hko with hm | he
    · exact (vote_pool_mem_seats _ k).mpr ⟨o, hm, hko⟩
    · exact vote_pool_equivocates_participant _ k he
  have hLx : sl_support p vx s B ∪ sl_support p vy s C ⊆ Lx :=
    Finset.union_subset (own vx B) (cross hy hx hix C)
  have hLy : sl_support p vx s B ∪ sl_support p vy s C ⊆ Ly :=
    Finset.union_subset (cross hx hy hiy B) (own vy C)
  have score (i : Nat) (z : V) (D : Block) :
      let pre := clockPre p (rho.stateBefore E i z).st (SA.gateTime p.toParams s)
      let v := actView pre
      SA.Root.prefixSupport p.toParams v s D =
        GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
          (GridCO.cleanSupport p.toParams.engine v s) D := by
    intro pre v
    exact actView_score p pre (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i z) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i z))
      _ _ D
  obtain ⟨k, hk⟩ := Gen.Pure.two_majorities_intersect hLx hLy
    (sl_result_majority p _ s _ B hB (score ix x))
    (sl_result_majority p _ s _ C hC (score iy y))
  obtain ⟨hkB, hkC⟩ := Finset.mem_inter.mp hk
  obtain ⟨u, hu, hku, hBu⟩ := (sl_support_mem p vx s B k).mp hkB
  obtain ⟨v, hv, hkv, hCv⟩ := (sl_support_mem p vy s C k).mp hkC
  have hn := sl_clean_no_equiv p vx s u hu k hku
  have hrelay := sl_relay E rho hE hN hDelta s hSync hy hx hix v hv k hkv
  have hvx : v ∈ GridCO.lateVotes p.toParams.engine vx s := by
    rcases hrelay with h | h
    · exact h
    · rw [hn] at h
      contradiction
  have hu' := sl_clean_mem p vx s u hu
  have hv' := sl_clean_mem p vy s v hv
  have he : v = u := hu'.2.2.2 v hvx
    (sl_same_seat v u s k hv'.2.1 hu'.2.1 hkv hku)
  subst v
  obtain ⟨K, hK, hmK, _, hBK⟩ := (vote_support_body _ _ _).mp hBu
  obtain ⟨L, hL, hmL, _, hCL⟩ := (vote_support_body _ _ _).mp hCv
  have hxK : K ∈ (rho.stateBefore E ix x).st.base.blocks := by
    have hm := (List.mem_filter.mp hmK).1
    change K ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hyL : L ∈ (rho.stateBefore E iy y).st.base.blocks := by
    have hm := (List.mem_filter.mp hmL).1
    change L ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hKL := stored_block_eq_of_root_eq E rho hroots ix iy x y hxK hyL
    (Option.some.inj ((resolvedTarget_root _ u hK).symm.trans (resolvedTarget_root _ u hL)))
  exact Gen.Pure.block_compatible_of_common hBK (hKL.symm ▸ hCL)

/-- Service windows for each cross-reader HEAD, and epochs at the enabled gate reads.
A retained relay must supply its own safe history; a past receipt is insufficient. -/
structure SameLabelServiceScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) : Prop where
  epochs : ∀ i x, enabledGateAt p c E rho i x s →
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)) i
  restartBound : ∀ i x, enabledGateAt p c E rho i x s →
    ∀ j w, j < i → rho.events[j]? = some (.restart x w) → w < SA.gateTime p.toParams s
  services : ∀ ia ib x y, x ∈ rho.honest → y ∈ rho.honest →
    enabledGateAt p c E rho ia x s → enabledGateAt p c E rho ib y s →
    ∀ q b, baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) ∈
      GridCO.cleanSupport p.toParams.engine
        (actView (clockPre p (storeAt p c E rho ia x) (SA.gateTime p.toParams s))) s →
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) y)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false →
    ∃ send, Nonempty (ReceiverService E rho (ofHead p ⟨.seat (.head s) q, b⟩) send
      (SA.gateTime p.toParams s) y)

private theorem sl_relay_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (s : Slot) (hScope : SameLabelServiceScope E rho s)
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : enabledGateAt p c E rho ix x s) (hiy : enabledGateAt p c E rho iy y s)
    (o : GridCO.Wire p.n .root)
    (ho : o ∈ GridCO.cleanSupport p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s)
    (k : Fin p.n) (hk : GridCO.headSeat? o = some k) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late k = true := by
  dsimp only
  have hc := sl_clean_mem p _ s o ho
  obtain ⟨B, rfl⟩ := sl_vote_shape o s k hc.2.1 hk
  have hS := hE.toScheduleWellFormed
  have hid : V2.D.Run.idxBefore rho (SA.gateTime p.toParams s) ≤ iy := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS hiy.1 _).mp (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim
  have hkeep : (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) y).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho iy y).st.base.votes := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact fgsa_votes_cumulative_on p c E rho hid y (hScope.epochs iy y hiy)
  have hwindow : (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) y).st.slot p ≤
      s + 1 := by
    have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hid y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho _ y),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho iy y),
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm
    have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho iy y) _).2.symm.trans
        (fgsa_gate_slot (c := c) _ s)
    exact (Internal.slotOf_mono (p := p)
      (hm.trans (fgsa_preTick_now_le E rho hS hiy.1))).trans_eq hs
  by_cases hNX : (fgsa p c).excludes
      (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) y)
        (ofHead p ⟨.seat (.head s) k, B⟩) = false
  · obtain ⟨send, ⟨hService⟩⟩ := hScope.services ix iy x y hx hy hix hiy k B ho hNX
    have hp := hService.processed hS hy (by change ¬ False; exact not_false)
    have hmem : (⟨.seat s k, .head B⟩ : GridCO.Wire p.n .root) ∈
        (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) y).st.base.votes :=
      of_decide_eq_true hp
    exact Or.inl (sl_gate_late E rho hS hiy.1 (hScope.restartBound iy y hiy) _ (hkeep hmem) rfl)
  · have hn : excludesS p _ (ofHead p ⟨.seat (.head s) k, B⟩) = true :=
      Bool.eq_true_of_ne_false hNX
    obtain ⟨u, hu, v, hv, hn, hlu, hlv, hku, hkv, _, _⟩ :=
      fgsa_head_excluded_before E rho hS y (SA.gateTime p.toParams s) s k B hwindow hn
    exact Or.inr ((cap_pair _ k).mpr ⟨u,
      sl_gate_late E rho hS hiy.1 (hScope.restartBound iy y hiy) u (hkeep hu) hlu, v,
      sl_gate_late E rho hS hiy.1 (hScope.restartBound iy y hiy) v (hkeep hv) hlv, hn, hku, hkv⟩)

/-- Local ready relay services preserve compatibility at one enabled gate label. -/
theorem fgsa_sameLabel_on (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho)
    (s : Slot) (hScope : SameLabelServiceScope E rho s)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ x y B C, x ∈ rho.honest → y ∈ rho.honest →
      gateResult p c E rho x s = some (some B) →
      gateResult p c E rho y s = some (some C) → Block.Compatible B C := by
  intro x y B C hx hy hB hC
  have hBx := hB
  have hCy := hC
  obtain ⟨ix, hix, hB⟩ := sl_gate_input E rho hE.toScheduleWellFormed x s B hB
  obtain ⟨iy, hiy, hC⟩ := sl_gate_input E rho hE.toScheduleWellFormed y s C hC
  have enabled (i : Nat) (z : V) (D : Block) (hi : IsGateTick p c rho i z s)
      (hr : gateResult p c E rho z s = some (some D)) : enabledGateAt p c E rho i z s := by
    refine ⟨hi, ?_⟩
    have hg := (fgsa_gate_raw_of_nonempty p c E rho hE.toScheduleWellFormed hi hr).1
    have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i z) _).2.symm.trans
        (fgsa_gate_slot (c := c) _ s)
    change (match (storeAt p c E rho i z).restartTime with
      | none => True | some w => w ≤ 4 * p.Δ * (s : Int))
    cases hw : (storeAt p c E rho i z).restartTime with
    | none => trivial
    | some w =>
      change joinedAtTime p (storeAt p c E rho i z).restartTime _ = true at hg
      rw [hw] at hg
      change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) = true
        at hg
      rw [hs] at hg
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, decide_eq_true_eq] using hg
  have hixEnabled := enabled ix x B hix hBx
  have hiyEnabled := enabled iy y C hiy hCy
  let vx := actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))
  let vy := actView (clockPre p (V2.D.Run.stateBefore E rho iy y).st (SA.gateTime p.toParams s))
  let Lx := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine vx s)).toFinset
  let Ly := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine vy s)).toFinset
  have own (v : GridCO.State p.n .root) (D : Block) : sl_support p v s D ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine v s)).toFinset := by
    intro k hk
    obtain ⟨o, ho, hko, _⟩ := (sl_support_mem p v s D k).mp hk
    exact (vote_pool_mem_seats _ k).mpr ⟨o, sl_clean_late p v s ho, hko⟩
  have cross {ia ib : Nat} {a b : V} (ha : a ∈ rho.honest) (hb : b ∈ rho.honest)
      (hia : enabledGateAt p c E rho ia a s)
      (hib : enabledGateAt p c E rho ib b s) (D : Block) :
      sl_support p (actView (clockPre p (V2.D.Run.stateBefore E rho ia a).st
        (SA.gateTime p.toParams s))) s D ⊆
      (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
        (actView (clockPre p (V2.D.Run.stateBefore E rho ib b).st
          (SA.gateTime p.toParams s))) s)).toFinset := by
    intro k hk
    obtain ⟨o, ho, hko, _⟩ := (sl_support_mem p _ s D k).mp hk
    rcases sl_relay_on E rho hE s hScope ha hb hia hib o ho k hko with hm | he
    · exact (vote_pool_mem_seats _ k).mpr ⟨o, hm, hko⟩
    · exact vote_pool_equivocates_participant _ k he
  have hLx : sl_support p vx s B ∪ sl_support p vy s C ⊆ Lx :=
    Finset.union_subset (own vx B) (cross hy hx hiyEnabled hixEnabled C)
  have hLy : sl_support p vx s B ∪ sl_support p vy s C ⊆ Ly :=
    Finset.union_subset (cross hx hy hixEnabled hiyEnabled B) (own vy C)
  have score (i : Nat) (z : V) (D : Block) :
      let pre := clockPre p (rho.stateBefore E i z).st (SA.gateTime p.toParams s)
      let v := actView pre
      SA.Root.prefixSupport p.toParams v s D =
        GridCO.goldfishScore v.blocks (GridCO.cleanSupport p.toParams.engine v s)
          (GridCO.cleanSupport p.toParams.engine v s) D := by
    intro pre v
    exact actView_score p pre (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i z) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i z))
      _ _ D
  obtain ⟨k, hk⟩ := Gen.Pure.two_majorities_intersect hLx hLy
    (sl_result_majority p _ s _ B hB (score ix x))
    (sl_result_majority p _ s _ C hC (score iy y))
  obtain ⟨hkB, hkC⟩ := Finset.mem_inter.mp hk
  obtain ⟨u, hu, hku, hBu⟩ := (sl_support_mem p vx s B k).mp hkB
  obtain ⟨v, hv, hkv, hCv⟩ := (sl_support_mem p vy s C k).mp hkC
  have hn := sl_clean_no_equiv p vx s u hu k hku
  have hrelay := sl_relay_on E rho hE s hScope hy hx hiyEnabled hixEnabled v hv k hkv
  have hvx : v ∈ GridCO.lateVotes p.toParams.engine vx s := by
    rcases hrelay with h | h
    · exact h
    · rw [hn] at h
      contradiction
  have hu' := sl_clean_mem p vx s u hu
  have hv' := sl_clean_mem p vy s v hv
  have he : v = u := hu'.2.2.2 v hvx
    (sl_same_seat v u s k hv'.2.1 hu'.2.1 hkv hku)
  subst v
  obtain ⟨K, hK, hmK, _, hBK⟩ := (vote_support_body _ _ _).mp hBu
  obtain ⟨L, hL, hmL, _, hCL⟩ := (vote_support_body _ _ _).mp hCv
  have hxK : K ∈ (rho.stateBefore E ix x).st.base.blocks := by
    have hm := (List.mem_filter.mp hmK).1
    change K ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hyL : L ∈ (rho.stateBefore E iy y).st.base.blocks := by
    have hm := (List.mem_filter.mp hmL).1
    change L ∈ (clockPre p _ _).base.blocks at hm
    rwa [(clockPre_fields p _ _).2.1] at hm
  have hKL := stored_block_eq_of_root_eq E rho hroots ix iy x y hxK hyL
    (Option.some.inj ((resolvedTarget_root _ u hK).symm.trans (resolvedTarget_root _ u hL)))
  exact Gen.Pure.block_compatible_of_common hBK (hKL.symm ▸ hCL)

private theorem sl_grid_future_absent (st : GridCO.State p.n .root) (r : Slot) (i : Fin p.n)
    (b : BlockId) (o : GridCO.Wire p.n .root) (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉
      (GridCO.admitVote p.toParams.engine st o).votes := by
  by_cases ho : o = ⟨.seat r i, .head b⟩
  · subst o
    unfold GridCO.admitVote
    change _ ∉ (if r < (st.now / (4 * p.Δ)).toNat - 1 ||
        (st.now / (4 * p.Δ)).toNat < r || decide (_ ∈ st.votes) ||
        GridCO.equivocates (GridCO.votesAt st r) i then st else _).votes
    simp [hf, hm]
  · obtain ⟨auth, payload⟩ := o
    cases auth <;> cases payload <;> dsimp only [GridCO.admitVote]
    all_goals first
      | exact hm
      | split_ifs
        · exact hm
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hm, fun he => ho he.symm⟩

private theorem sl_grid_future_fold (raw : List (GridCO.HeadWire p.n .root))
    (st : GridCO.State p.n .root) (r : Slot) (i : Fin p.n) (b : BlockId)
    (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉
      (raw.foldl (fun v h => GridCO.admitVote p.toParams.engine v
        (GridCO.fromHead h)) st).votes := by
  induction raw generalizing st with
  | nil => exact hm
  | cons h raw ih =>
    apply ih _ _ (sl_grid_future_absent st r i b _ hf hm)
    rwa [Internal.grid_admitVote_now]

private theorem sl_grid_future_proposal (st : GridCO.State p.n .root) (r : Slot) (i : Fin p.n)
    (b : BlockId) (o : GridCO.Wire p.n .root) (B : Block) (raw : List (GridCO.HeadWire p.n .root))
    (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉
      (GridCO.admitProposal p.toParams.engine st o B raw).votes := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · exact hm
  · exact sl_grid_future_fold raw _ r i b hf hm

private theorem sl_future_head_process (st : State p.n) (r : Slot) (i : Fin p.n)
    (b : BlockId) (o : Wire p.n) (hf : st.slot p < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ st.base.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n .root) ∉ (FGSA.process p st o).base.votes := by
  dsimp only [FGSA.process]
  cases hd : o.decode with
  | none => exact hm
  | some m =>
    cases m with
    | vote s j B => exact sl_grid_future_absent st.base r i b _ hf hm
    | row j B => rwa [Internal.admitRow_base]
    | block s N =>
      dsimp only [admitBlock]
      split
      · exact hm
      · cases hP : parentFG st N.erase with
        | none => exact hm
        | some P =>
          let st1 : State p.n := { st with
            base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s N.erase N.raw
                N.support) N.erase
              (N.raw.map baseHead)
            fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
            proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
          dsimp only
          split
          · rw [Internal.foldl_admitRow_base, (Internal.ite_reconcile st1 st).1]
            exact sl_grid_future_proposal st.base r i b _ _ _ hf hm
          · exact hm

private theorem sl_replay_head_step_origin (st : State p.n) (h : HeadWire p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (FGSA.process p st ⟨h.auth, .head h.payload⟩).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      h = ⟨.seat (.head s) i, b⟩ := by
  rcases h with ⟨auth, payload⟩
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> try exact Or.inl hm
  rename_i j r
  change (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
    (GridCO.admitVote p.toParams.engine st.base ⟨.seat r j, .head payload⟩).votes at hm
  unfold GridCO.admitVote at hm
  dsimp only at hm
  split at hm
  · exact Or.inl hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact Or.inl hm
    · have he : s = r ∧ i = j ∧ b = payload := by
        simpa only [List.mem_singleton, Signed.mk.injEq, Auth.seat.injEq,
          GridCO.Msg.head.injEq, and_assoc] using hm
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr rfl

private theorem sl_replay_heads_origin (raw : List (HeadWire p.n)) (st : State p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (raw.foldl (fun acc h => FGSA.process p acc ⟨h.auth, .head h.payload⟩) st).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ raw := by
  induction raw generalizing st with
  | nil => exact Or.inl hm
  | cons h raw ih =>
    rcases ih _ hm with hh | hh
    · rcases sl_replay_head_step_origin st h s i b hh with hh | rfl
      · exact Or.inl hh
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ hh)

private theorem sl_replay_sources_origin (sources : List (NamedProposal p.n)) (st : State p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (sources.foldl (fun acc N => N.raw.foldl
        (fun acc h => FGSA.process p acc ⟨h.auth, .head h.payload⟩) acc) st).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      ∃ N ∈ sources, (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ N.raw := by
  induction sources generalizing st with
  | nil => exact Or.inl hm
  | cons N sources ih =>
    rcases ih _ hm with hh | ⟨M, hM, hh⟩
    · rcases sl_replay_heads_origin N.raw st s i b hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr ⟨N, List.mem_cons_self .., hh⟩
    · exact Or.inr ⟨M, List.mem_cons_of_mem _ hM, hh⟩


private theorem sl_restart_bound (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : enabledGateAt p c E rho i x s) :
    ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s := by
  intro j w hji hj
  obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hS hj hji
  have he := hi.2
  change (match (rho.stateBefore E i x).st.restartTime with
    | none => True | some t => t ≤ 4 * p.Δ * (s : Int)) at he
  rw [hu] at he
  exact hwu.trans he

private theorem sl_awake_suffix (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hi : enabledGateAt p c E rho i x s)
    {u : Time} (hu : 0 ≤ u) (hpu : SA.proposalTime p.toParams s ≤ u)
    (hug : u ≤ SA.gateTime p.toParams s) : E.awake x u = true := by
  by_contra hn
  have hg := hV.tick_awake x _ (List.mem_of_getElem? hi.1)
  obtain ⟨w, huw, hwg, hw⟩ := V2.D.Engine.wake_between hug (Bool.eq_false_iff.mpr hn) hg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hV.wake_restart x hx w (hu.trans_lt huw)
      (hwg.trans (hV.in_horizon _ (List.mem_of_getElem? hi.1)).2) hw)
  have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hj hi.1 hwg
    (show 0 < 1 from by decide)
  exact (not_lt.mpr (sl_restart_bound E rho hV.toScheduleWellFormed hi j w hji hj))
    (hpu.trans_lt huw)

private theorem sl_epoch_after_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i it : Nat} {x : V} {s : Slot}
    (hi : enabledGateAt p c E rho i x s)
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s))) :
    V2.D.restartFree rho x it i := by
  intro j w htj hji hj
  have hwp := sl_restart_bound E rho hS hi j w hji hj
  have hjt := V2.D.Engine.restart_index_lt_event hS hj hit hwp (show 0 < 1 from by decide)
  omega

private theorem sl_replay_before_proposal_absent
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hs : 0 < s) (k : Nat) (hki : k ≤ i) (w : Time) (q : Fin p.n) (b : BlockId) :
    (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∉
      (acRestart p (rho.stateBefore E k x).st w).base.votes := by
  intro hm
  rw [acRestart_replay_order] at hm
  rcases sl_replay_sources_origin _ _ s q b hm with hm | ⟨N, hN, hh⟩
  · exact (List.not_mem_nil hm).elim
  · unfold restartSources at hN
    obtain ⟨wire, hwire, he⟩ := List.mem_filterMap.mp hN
    cases hd : wire.decode with
    | none => simp only [hd, reduceCtorEq] at he
    | some input =>
      cases input with
      | vote r j B => simp only [hd, reduceCtorEq] at he
      | row j body => simp only [hd, reduceCtorEq] at he
      | block r M =>
        simp only [hd] at he
        split at he
        · cases Option.some.inj he
          have hB : N.erase ∈ (rho.stateBefore E k x).st.base.blocks := by
            obtain ⟨r', M', hw, _, _, _, B, hB, heB, _⟩ :=
              (metaInv_stateBefore E rho k x).wireTree wire hwire
            have eqwire := decode_eq_block.mp hd
            have heq : r' = r ∧ M' = N := by simpa only [Signed.mk.injEq,
              Auth.proposer.injEq, Msg.proposal.injEq] using hw.symm.trans eqwire
            obtain ⟨rfl, rfl⟩ := heq
            exact ((cstoreInv_stateBefore E rho k x).baseTree _).mpr ⟨B, hB, heB⟩
          have hold := (fgsa_stored_block_slots E rho hV.toScheduleWellFormed hi hs).1
            N.erase ((fgsa_store_durable p c E rho hki x).2.1.subset hB)
          obtain ⟨j, o, t, _, hj, ho, _, _⟩ := stored_proposal_delivered E rho k x wire hwire
          have hf := hV.wire j x o t hj
          change FGSA.wellFormed p (toWire p o) = true at hf
          rw [ho] at hf
          unfold FGSA.wellFormed at hf
          rw [hd] at hf
          have hr := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).2
          have hl := List.all_eq_true.mp hr _ hh
          change (s + 1 == N.erase.slot) = true at hl
          have heq := beq_iff_eq.mp hl
          exact (Nat.not_le_of_lt hold) (heq ▸ Nat.le_succ s)
        · cases he

private theorem sl_before_proposal_absent
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)))
    (q : Fin p.n) (b : BlockId) :
    ∀ k, k ≤ i → (fgsa p c).processed (rho.stateBefore E k x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  have all : ∀ k, k ≤ i →
      (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∉
        (rho.stateBefore E k x).st.base.votes := by
    intro k hki
    refine V2.D.Engine.stateBefore_step_induction E rho
      (fun nd => (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∉ nd.st.base.votes)
      (Nat.zero_le k) x ?_ (List.not_mem_nil ·)
    intro j e _ hjk he hnode hprev
    cases e with
    | tick v t =>
      change v = x at hnode; subst v
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st (c := c) E rho (rho.stateBefore E j x) x t, (clock_vn _ _).1]
      exact hprev
    | restart v w =>
      change v = x at hnode; subst v
      simp only [V2.D.World.step, Function.update_self]
      change _ ∉ (acRestart p (rho.stateBefore E j x).st w).base.votes
      by_cases hs : 0 < s
      · exact sl_replay_before_proposal_absent E rho hV hi hs j (by omega) w q b
      · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
        have hw0 := (hR x w (List.mem_of_getElem? he)).1
        have hm := List.pairwise_iff_getElem.mp hV.sorted
          j i (List.getElem?_eq_some_iff.mp he).1
          (List.getElem?_eq_some_iff.mp hi).1 (by omega)
        rw [(List.getElem?_eq_some_iff.mp he).2,
          (List.getElem?_eq_some_iff.mp hi).2] at hm
        have ht := V2.D.Engine.time_le_of_key_le _ _ hm
        change w ≤ SA.proposalTime p.toParams s at ht
        change w ≤ 4 * p.Δ * (s : Int) at ht
        rw [hs0] at ht
        norm_num at ht
        exact ((not_lt.mpr ht) hw0).elim
    | deliver v o t =>
      change v = x at hnode; subst v
      have ht : t < SA.proposalTime p.toParams s := by
        by_contra hn
        have ht := V2.D.Engine.tick_index_lt_delivery E rho hV.toScheduleWellFormed
          hi he (le_of_not_gt hn)
        omega
      have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hV.toScheduleWellFormed he x
      have hnow : (rho.stateBefore E j x).st.base.now ≤ t :=
        (fgsa_clock_now p c (rho.stateBefore E j x)) ▸ hn
      have hslot : (rho.stateBefore E j x).st.slot p < s := by
        have hs : 0 < s := by
          have hz := (hV.in_horizon _ (List.mem_of_getElem? he)).1
          by_contra hs
          have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
          change t < 4 * p.Δ * (s : Int) at ht
          rw [hs0] at ht
          norm_num at ht
          exact (not_lt.mpr hz) ht
        apply (Int.toNat_lt' hs).mpr
        apply (Int.ediv_lt_iff_lt_mul (by linarith [p.deltaPos])).mpr
        have ht' : (rho.stateBefore E j x).st.base.now < 4 * p.Δ * (s : Int) :=
          hnow.trans_lt ht
        nlinarith
      simp only [V2.D.World.step, Function.update_self]
      exact sl_future_head_process _ s q b (toWire p o) hslot hprev
  intro k hki
  exact decide_eq_false_iff_not.mpr (all k hki)

private theorem sl_gate_idx_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : enabledGateAt p c E rho i x s) :
    V2.D.Run.idxBefore rho (SA.gateTime p.toParams s) ≤ i := by
  by_contra hn
  have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS hi.1 _).mp (Nat.lt_of_not_ge hn)
  exact (lt_irrefl _ ht).elim

private theorem sl_cut_le_gate (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : enabledGateAt p c E rho i x s) :
    V2.D.Run.actionCut rho (SA.earlyTime p.toParams s) ≤ i := by
  by_contra hn
  have ht := (V2.D.Engine.index_lt_actionCut_iff hS hi.1 _).mp (Nat.lt_of_not_ge hn)
  have hd := p.deltaPos
  rcases ht with ht | ⟨_, hphase⟩
  · change 4 * p.Δ * (s : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    linarith
  · change (1 : Nat) = 0 at hphase
    cases hphase

private theorem sl_early_epoch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : enabledGateAt p c E rho i x s) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.earlyTime p.toParams s)) i := by
  intro j w hjc hji hj
  have hw := sl_restart_bound E rho hS hi j w hji hj
  have hd := p.deltaPos
  have hwe : w < SA.earlyTime p.toParams s := by
    change w ≤ 4 * p.Δ * (s : Int) at hw
    change w < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith
  have hjcut := (V2.D.Engine.index_lt_actionCut_iff hS hj _).mpr (Or.inl hwe)
  omega

private theorem sl_proposal_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : enabledGateAt p c E rho i x s) :
    ∃ (it : Nat), rho.events[it]? = some (V2.Event.tick x (SA.proposalTime p.toParams s)) := by
  have ht : (((4 * s : Nat) : Time) * p.Δ) = SA.proposalTime p.toParams s := by
    change ((4 * s : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int)
    push_cast
    ring
  have hpg : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have hd := p.deltaPos
    positivity
  obtain ⟨it, hit, _⟩ := fgsa_tick_total E rho hV.toScheduleWellFormed hDelta x hx (4 * s)
    (ht ▸ (hpg.trans (hV.in_horizon _ (List.mem_of_getElem? hi.1)).2))
    (ht ▸ sl_awake_suffix E rho hV hx hi hp0 le_rfl hpg)
  exact ⟨it, ht ▸ hit⟩

private theorem sl_head_history_at_early
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    (hDelta : E.Δ = p.Δ) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hi : enabledGateAt p c E rho i x s)
    (q : Fin p.n) (b : BlockId) :
    Gen.V2.Duty.HistorySafeAt E rho x (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.earlyTime p.toParams s) := by
  obtain ⟨it, hit⟩ := sl_proposal_tick E rho hV hDelta hx hi
  have hep : SA.proposalTime p.toParams s < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have htc := (V2.D.Engine.index_lt_actionCut_iff hV.toScheduleWellFormed hit _).mpr
    (Or.inl hep)
  rintro ⟨k, hk, hp⟩
  change (fgsa p c).processed
    (rho.stateBefore E (V2.D.Run.actionCut rho (SA.earlyTime p.toParams s)) x)
    (ofHead p ⟨.seat (.head s) q, b⟩) = true
  by_cases hkt : k ≤ it
  · have hf := sl_before_proposal_absent E rho hV hR hit q b k hkt
    rw [hf] at hp
    cases hp
  · exact (fgsaHooks p c).processed_stable E rho hV.toScheduleWellFormed x
      (ofHead p ⟨.seat (.head s) q, b⟩) k _ hk
      ((sl_epoch_after_tick E rho hV.toScheduleWellFormed hi hit).mono
        (Nat.le_of_lt (Nat.lt_of_not_ge hkt)) (sl_cut_le_gate E rho hV.toScheduleWellFormed hi)) hp

private theorem sl_vote_stamp_mem (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (rho.stateBefore E i x).st.base.votes) :
    (o, GridCO.stampVote (rho.stateBefore E i x).st.base o) ∈
      (rho.stateBefore E i x).st.base.voteStamp := by
  rw [← fgsa_vote_stamp_keys E rho i x] at hm
  obtain ⟨⟨a, t⟩, ha, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst a
  unfold GridCO.stampVote
  cases hf : (rho.stateBefore E i x).st.base.voteStamp.find? (fun row => row.1 == o) with
  | none => have h := List.find?_eq_none.mp hf (o, t) ha; simp at h
  | some row =>
    have he : row.1 = o := by simpa using List.find?_some hf
    simpa only [Option.map_some, Option.getD_some, ← he] using List.mem_of_find?_eq_some hf

/-- Base execution and label synchronization supply the local SameLabel service.
The label's HEADs cannot be old before its proposal tick. Enabled gates bound
all later restarts, so their histories persist to the ready anchor. -/
theorem fgsa_sameLabel_serviceScope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    (hDelta : E.Δ = p.Δ) (s : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams s) (SA.gateTime p.toParams s)) :
    SameLabelServiceScope E rho s := by
  have hS := hV.toScheduleWellFormed
  have hpe : SA.proposalTime p.toParams s < SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have hp0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have hd := p.deltaPos
    positivity
  constructor
  · intro i x hi j w hbj hji hj
    have hw : w < SA.gateTime p.toParams s :=
      (sl_restart_bound E rho hS hi j w hji hj).trans_lt (by
      change 4 * p.Δ * (s : Int) < 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos])
    have hjb := (Gen.V2.Duty.index_lt_idxBefore_iff hS hj _).mpr hw
    omega
  · intro i x hi j w hji hj
    have hw := sl_restart_bound E rho hS hi j w hji hj
    change w ≤ 4 * p.Δ * (s : Int) at hw
    change w < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  · intro ia ib x y hx hy hia hib q b ho hNX
    have hc := sl_clean_mem p _ s _ ho
    have hm : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        (rho.stateBefore E ia x).st.base.votes := by
      have hm := hc.1
      change _ ∈ (clockPre p _ _).base.votes at hm
      rwa [(Internal.clockPre_vn _ _).1] at hm
    have ht := hc.2.2.1
    change GridCO.stampVote (actView (clockPre p (rho.stateBefore E ia x).st
      (SA.gateTime p.toParams s))) ⟨.seat s q, .head b⟩ < SA.earlyTime p.toParams s at ht
    rw [sl_gate_stamp E rho ia x s _ hm] at ht
    obtain ⟨it, hit⟩ := sl_proposal_tick E rho hV hDelta hx hia
    have horigin := fgsa_vote_stamp_source_or_restart E rho ia x s q b _
      (sl_vote_stamp_mem E rho ia x _ hm)
    have accepted : ∃ j < ia, ∃ t, rho.acceptsAt E j x
        (ofHead p ⟨.seat (.head s) q, b⟩) t ∧ t < SA.earlyTime p.toParams s := by
      rcases horigin with ⟨j, hj, t, ha, he⟩ | ⟨j, hj, w, hjw, _, hrep⟩
      · refine ⟨j, hj, t, ha, ?_⟩
        by_contra hn
        obtain ⟨parent, hd, _⟩ := ha.1
        have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
          refine ⟨4 * s + 2, ?_⟩
          rw [hDelta]
          change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
          push_cast
          ring
        have hb := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
          (fgsaRestoreTimeLaw p c) E rho hV hd hpub (hp0.trans (le_of_lt hpe))
          (le_of_not_gt hn)
        have hnow : SA.earlyTime p.toParams s ≤ (rho.stateBefore E j x).st.base.now :=
          (fgsa_clock_now p c (rho.stateBefore E j x)) ▸ hb
        exact (not_lt.mpr hnow) (he ▸ ht)
      · have hwp := sl_restart_bound E rho hS hia j w hj hjw
        have hjt := V2.D.Engine.restart_index_lt_event hS hjw hit hwp (show 0 < 1 from by decide)
        by_cases hs : 0 < s
        · exact (sl_replay_before_proposal_absent E rho hV hit hs j hjt.le w q b hrep).elim
        · have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
          have hw0 := (hR x w (List.mem_of_getElem? hjw)).1
          change w ≤ 4 * p.Δ * (s : Int) at hwp
          rw [hs0] at hwp
          norm_num at hwp
          exact ((not_lt.mpr hwp) hw0).elim
    obtain ⟨j, _, t, ha, hte⟩ := accepted
    obtain ⟨dl, cut, hD, _, hlt, hbound, _, hcut, hhor⟩ := hSync
    have hed : dl (SA.earlyTime p.toParams s) ≤ SA.gateTime p.toParams s := by
      have hb := hbound (SA.earlyTime p.toParams s)
      rw [hDelta] at hb
      change dl _ ≤ max (4 * p.Δ * (s : Int) + 2 * p.Δ)
        (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
      rw [max_eq_left (by linarith [p.deltaPos])] at hb
      change dl _ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    have hRF := (sl_early_epoch E rho hS hib).mono le_rfl (sl_gate_idx_le E rho hS hib)
    have hnot : (fgsa p c).excludes
        (rho.stateBeforeTime E (dl (SA.earlyTime p.toParams s)) y)
        (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
      by_contra hn
      have hex := Bool.eq_true_of_ne_false hn
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hex hNX
      have he := (fgsaHooks p c).excludes_stable E rho hS y
        (ofHead p ⟨.seat (.head s) q, b⟩) _ _ (fgsa_idxBefore_mono rho hed)
        (hRF.mono (Gen.V2.Duty.actionCut_le_idxBefore hS (hlt _)) le_rfl) hex
      rw [hNX] at he
      cases he
    refine ⟨t, ⟨{
      dl := dl, cut := cut, anchor := SA.earlyTime p.toParams s
      within := hD
      ready := ⟨x, hx, Or.inr ⟨j, ha⟩, ?_⟩
      send_le := hte.le
      nonneg := hp0.trans hpe.le
      later := hlt _
      cut_le := hed.trans hcut
      horizon := hed.trans hhor
      freeze_le := hed
      history := sl_head_history_at_early E rho hV hR hDelta hy hib q b
      epoch := hRF
      handlers := ?_
      not_excluded := hnot }⟩⟩
    · intro u heu hud
      exact sl_awake_suffix E rho hV hy hib (hp0.trans (hpe.le.trans heu))
        (hpe.le.trans heu) (hud.le.trans hed)
    · intro k u heu hud hh
      have hcall := hh
      obtain ⟨parent, hk, _⟩ := hh
      have deps := fgsa_hReady_of_not_block (by intro r N h; cases h)
        (fgsa_hWF_of_delivery hV.wire) k u
        ((Gen.V2.Duty.index_lt_idxBefore_iff hS hk _).mpr hud) hcall
      refine ⟨deps.1, deps.2, ?_⟩
      have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
        refine ⟨4 * s, ?_⟩
        rw [hDelta]
        change 4 * p.Δ * (s : Int) = _
        push_cast
        ring
      have hb := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hV hk hpub hp0 (hpe.le.trans heu)
      have hn : SA.proposalTime p.toParams s ≤ (rho.stateBefore E k y).st.base.now :=
        (fgsa_clock_now p c (rho.stateBefore E k y)) ▸ hb
      exact hn

/-- A local restart bound before the HEAD label rules out a replay-only origin.
This supplies a network acceptance without requiring global NoRestart. -/
theorem fgsa_vote_accepted_before_local
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    {k it : Nat} {x : V} (s : Slot)
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hBound : ∀ j w, j < k → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s)
    (q : Fin p.n) (b : BlockId) (X : Time)
    (hpub : V2.PublicTime E X) (hzero : 0 ≤ X)
    (hm : (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
      (rho.stateBefore E k x).st.base.votes)
    (ht : GridCO.stampVote (rho.stateBefore E k x).st.base ⟨.seat s q, .head b⟩ < X) :
    ∃ j < k, ∃ t, rho.acceptsAt E j x (ofHead p ⟨.seat (.head s) q, b⟩) t ∧ t < X := by
  rcases fgsa_vote_stamp_source_or_restart E rho k x s q b _
      (sl_vote_stamp_mem E rho k x _ hm) with ⟨j, hj, t, ha, he⟩ | ⟨j, hj, w, hw, _, hrep⟩
  · refine ⟨j, hj, t, ha, ?_⟩
    by_contra hn
    obtain ⟨parent, hd, _⟩ := ha.1
    have hb := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hV hd hpub hzero (le_of_not_gt hn)
    have hnow : X ≤ (rho.stateBefore E j x).st.base.now :=
      (fgsa_clock_now p c (rho.stateBefore E j x)) ▸ hb
    exact (not_lt.mpr hnow) (he ▸ ht)
  · have hwp := hBound j w hj hw
    have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hw hit hwp
      (show 0 < 1 from by decide)
    by_cases hs : 0 < s
    · exact (sl_replay_before_proposal_absent E rho hV hit hs j hji.le w q b hrep).elim
    · have hs0 := Nat.eq_zero_of_not_pos hs
      have hw0 := (hR x w (List.mem_of_getElem? hw)).1
      change w ≤ 4 * p.Δ * (s : Int) at hwp
      rw [hs0] at hwp
      norm_num at hwp
      exact ((not_lt.mpr hwp) hw0).elim

/-- A local restart bound keeps label HEAD history at a later service anchor.
The source proposal tick is real; no gate or global NoRestart is assumed. -/
theorem fgsa_head_historySafeAt_of_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    {it : Nat} {x : V} {s : Slot} {a : Time}
    (hit : rho.events[it]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hBound : ∀ j w, j < V2.D.Run.actionCut rho a →
      rho.events[j]? = some (.restart x w) → w ≤ SA.proposalTime p.toParams s)
    (q : Fin p.n) (b : BlockId) :
    Gen.V2.Duty.HistorySafeAt E rho x (ofHead p ⟨.seat (.head s) q, b⟩) a := by
  have hS := hV.toScheduleWellFormed
  rintro ⟨k, hk, hp⟩
  by_cases hkt : k ≤ it
  · have hf := sl_before_proposal_absent E rho hV hR hit q b k hkt
    rw [hf] at hp
    cases hp
  · exact (fgsaHooks p c).processed_stable E rho hS x _ k _ hk (by
      intro j w hkj hja hj
      have hji := V2.D.Engine.restart_index_lt_event hS hj hit (hBound j w hja hj)
        (show 0 < 1 from by decide)
      omega) hp

end AvailableChain.FGSA.Run
end

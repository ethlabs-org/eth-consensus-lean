module
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService

public section

/-! H-SUPPORT relay adapters (plan §4 steps 3–5; G4, G5 inputs). The private
helpers restate the private Shared/Relay.lean helpers that this lane may not edit. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem support_vote_shape {n : Nat} (o : GridCO.Wire n .root) (s : Slot) (k : Fin n)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k) :
    ∃ B, o = ⟨.seat s k, .head B⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> try contradiction
  rename_i r j B
  have hr : r = s := Option.some.inj hl
  have hj : j = k := Option.some.inj hk
  subst r; subst j
  exact ⟨B, rfl⟩

omit [DecidableEq V] in
private theorem support_idx_mono (rho : V2.D.Run V (fgsa p c)) :
    Monotone (V2.D.Run.idxBefore rho) := by
  intro a b hab
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he => decide_eq_true
    (lt_of_lt_of_le (of_decide_eq_true he) hab))

private theorem support_votes_mono (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hN : V2.D.NoRestart rho) (x : V) {i j : Nat} (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho j x).st.base.votes := by
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => (V2.D.Run.stateBefore E rho i x).st.base.votes ⊆ nd.st.base.votes)
    ?_ ?_ (fun _ _ h => h) E rho hij x (hN.restartFree x i j) (List.Subset.refl _)
  · intro nd t h
    change _ ⊆ (clock p nd.st t).base.votes
    rwa [(clock_vn nd.st t).1]
  · intro nd o h
    exact List.Subset.trans h (process_votes_subset nd.st (toWire p o))

private theorem support_read_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (readTime : Time) (o : GridCO.Wire p.n .root)
    (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes) :
    GridCO.stampVote (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
      readTime)) o =
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–699 (H.1, reverse relay); plan H-SUPPORT §4 step 4.
DC: SAME a stored label-s vote at the source gate input is in its late pool. -/
theorem healing_support_gate_late (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (o : GridCO.Wire p.n .root) (hm : o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes)
    (hl : GridCO.headLabel? o = some s)
    (hj : joinedAtTime p (storeAt p c E rho i x).restartTime
      (SA.gateTime p.toParams s) = true) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st (SA.gateTime p.toParams s))) s := by
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [beq_iff_eq] using hl⟩
    change o ∈ (clockPre p _ _).base.votes
    rwa [(Internal.clockPre_vn _ _).1]
  · rw [support_read_stamp E rho i x (SA.gateTime p.toParams s) o hm]
    have hpos : 0 < SA.gateTime p.toParams s := by
      change 0 < 4 * p.Δ * (s : Int) + 6 * p.Δ
      have hd := p.deltaPos
      positivity
    have hn := fgsa_preTick_now_lt_joined E rho hS hi hpos hj
    have hb := (fgsa_stateBefore_bounds E rho hS i x).2
    unfold GridCO.stampVote
    cases hf : (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.find?
        (fun row => row.1 == o) with
    | none => exact hn
    | some row => exact lt_of_le_of_lt (hb row (List.mem_of_find?_eq_some hf)) hn

private theorem support_read_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.gateTime p.toParams s)))
    (d : Time) (hd : d ≤ SA.gateTime p.toParams s) :
    (V2.D.Run.stateBeforeTime E rho d x).st.slot p ≤ s + 1 := by
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hN
    (support_idx_mono rho hd) x
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–699 (H.1 reverse relay), 689–692 (release); plan H-SUPPORT
§4 steps 4–5 (G5 input). DC: Handlers/GoldfishVotePool.lean:755,791.
INTENTIONAL: every label-s vote stored at the receiver before its q_s tick, not only
its frozen arm, reaches the source late pool, as itself or as cap-two evidence. -/
theorem healing_support_vote_backward (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : rho.events[ix]? = some (.tick x (SA.gateTime p.toParams s)))
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (o : GridCO.Wire p.n .root) (ho : o ∈ GridCO.votesAt (V2.D.Run.stateBefore E rho iy
        y).st.base s)
    (seat : Fin p.n) (hk : GridCO.headSeat? o = some seat) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (V2.D.Run.stateBefore E rho ix x).st (SA.gateTime p.toParams s))) s
    o ∈ late ∨ GridCO.equivocates late seat = true := by
  dsimp only
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  have hl' : GridCO.headLabel? o = some s := by simpa only [beq_iff_eq] using hl
  obtain ⟨B, rfl⟩ := support_vote_shape o s seat hl' hk
  obtain ⟨j, _, t, ha, ht⟩ :=
    fgsa_vote_accepted_before_head_read E rho hE hN hDelta iy y s hiy seat B hm
  obtain ⟨dl, cut, hD, _, hlt, hb, _, hcut, _⟩ := hSync
  have hd : dl t < SA.gateTime p.toParams s := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
    push_cast at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t < 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) <
        4 * p.Δ * (s : Int) + 5 * p.Δ := max_lt (by linarith) (by linarith)
    linarith
  have hr := fgsa_head_receipt E rho hDelta hE hN dl cut s seat B t x hD
    (Or.inr ⟨y, hy, j, ha⟩) hx ((le_of_lt hd).trans hcut) (hlt t)
    (support_read_window E rho hE.toScheduleWellFormed hN hix (dl t) (le_of_lt hd))
    (hd.le.trans (hE.in_horizon _ (List.mem_of_getElem? hix)).2)
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hix hx
      (fgsa_trigger_nonneg E rho hE.toScheduleWellFormed (Or.inr ⟨y, hy, j, ha⟩)) hd.le)
  have hkeep : (V2.D.Run.stateBeforeTime E rho (dl t) x).st.base.votes ⊆
      (V2.D.Run.stateBefore E rho ix x).st.base.votes := by
    rw [fgsa_preTick_eq_timeRead E rho hE.toScheduleWellFormed hN hix,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hE.toScheduleWellFormed,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hE.toScheduleWellFormed]
    exact support_votes_mono E rho hN x (support_idx_mono rho (le_of_lt hd))
  have hjoin := fgsa_gate_joined_of_enabled E rho
    (fgsa_enabledGate_noRestart E rho hN hix)
  rcases hr with hr | ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, _, _⟩
  · exact Or.inl (healing_support_gate_late E rho hE.toScheduleWellFormed hix
      _ (hkeep hr.1) rfl hjoin)
  · exact Or.inr ((cap_pair _ seat).mpr ⟨u,
      healing_support_gate_late E rho hE.toScheduleWellFormed hix u (hkeep hu) hlu hjoin, v,
      healing_support_gate_late E rho hE.toScheduleWellFormed hix v (hkeep hv) hlv hjoin,
      hne, hku, hkv⟩)

private theorem support_stamp_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp hf row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

private theorem support_read_block_stamp (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hsch : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    (y : V) (D : Time) (hD : 0 < D) (b : Block)
    (hb : b ∈ (V2.D.Run.stateBeforeTime E rho D y).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBeforeTime E rho D y).st.base b < D := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hb ⊢
  have hkeys : b ∈
      ((V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.base.blockStamp.map
        Prod.fst) := by
    rw [(storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho D) y).«meta».stampKeys]
    exact hb
  change (((V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.base.blockStamp.find? _).map
    Prod.snd).getD _ < D
  cases he : (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.base.blockStamp.find?
      (fun row => row.1 == b) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
    have hn := List.find?_eq_none.mp he row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row =>
    change row.2 < D
    rcases fgsa_block_stamp_source E rho hN _ y row.1 row.2 (List.mem_of_find?_eq_some he) with
      hg | ⟨l, hl, t, o, _, ha, hs⟩
    · rw [hg.2]; exact hD
    · obtain ⟨parent, hd, _⟩ := ha.1
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hd D).mp hl
      have hc := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hsch hd y
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l y)] at hc
      rw [hs]
      exact hc.trans_lt ht

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–689 (H.1 forward relay), 748–783 (H.3 frozen path); plan
H-SUPPORT §4 steps 3–4. DC: GSTZeroPreparedWalk.lean:546.
INTENTIONAL: a block held before the freeze z_s keeps its whole ancestor path and its
original strict stamps at the receiver's post-clock q_s read. -/
theorem healing_support_prefreeze_path (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hsch : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    {K : FGBlock (Fin p.n)}
    (hK : K ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.fg.TF) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A K →
      A ∈ st.fg.TF ∧ GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st A hA
  let D := SA.freezeTime p.toParams s
  let j := V2.D.Run.idxBefore rho D
  have hjk : j ≤ iy := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hiy D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  have hc := fgsa_store_cumulative p c E rho hN hjk y
  have hread : storeAt p c E rho j y = (V2.D.Run.stateBeforeTime E rho D y).st := by
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch]
  have hAm := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho D y).cstore.fg.closed K hK A hA
  have hAb := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree (eraseFG A)).mpr
    ⟨A, hAm, rfl⟩
  have hAstamp := support_read_block_stamp E rho hsch hN y D (by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity) (eraseFG A) hAb
  rw [← hread] at hAm hAb hAstamp
  have hkeys : eraseFG A ∈ (storeAt p c E rho j y).base.blockStamp.map Prod.fst := by
    change eraseFG A ∈ (V2.D.Run.stateBefore E rho j y).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j y).«meta».stampKeys]
    exact hAb
  constructor
  · change A ∈ (FGSA.clock p (storeAt p c E rho iy y) _).fg.TF
    rw [(clock_cumulative p _ _).1]
    exact hc.1 hAm
  · have heq := support_stamp_kept hc.2.2.1 (eraseFG A) hkeys
    change (((FGSA.clock p (storeAt p c E rho iy y) _).base.blockStamp.find? _).map
      Prod.snd).getD _ < D
    rw [(clock_cumulative p _ _).2.2.1, heq]
    unfold GridCO.stampBlock at hAstamp
    cases hfind : (storeAt p c E rho j y).base.blockStamp.find? (fun row => row.1 == eraseFG A) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp hfind row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => simpa only [hfind, Option.map_some, Option.getD_some] using hAstamp

/-- Frozen paths keep stamps on the exact receiver epoch through the actual read. -/
theorem healing_support_prefreeze_path_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hsch : V2.D.ScheduleWellFormed E rho)
    {iy : Nat} {y : V} {s : Slot}
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hEpoch : V2.D.restartFree rho y
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) iy)
    {K : FGBlock (Fin p.n)}
    (hK : K ∈ (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st.fg.TF) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A K →
      A ∈ st.fg.TF ∧ GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st A hA
  let D := SA.freezeTime p.toParams s
  let j := V2.D.Run.idxBefore rho D
  have hjk : j ≤ iy := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hiy D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  have hc := fgsa_store_cumulative_on p c E rho hjk y hEpoch
  have hread : storeAt p c E rho j y = (V2.D.Run.stateBeforeTime E rho D y).st := by
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch]
  have hAm := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho D y).cstore.fg.closed K hK A hA
  have hAb := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree (eraseFG A)).mpr
    ⟨A, hAm, rfl⟩
  have hAstamp := fgsa_block_stamp_before_read E rho hsch y D (by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity) (eraseFG A) hAb
  rw [← hread] at hAm hAb hAstamp
  have hkeys : eraseFG A ∈ (storeAt p c E rho j y).base.blockStamp.map Prod.fst := by
    change eraseFG A ∈ (V2.D.Run.stateBefore E rho j y).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j y).«meta».stampKeys]
    exact hAb
  constructor
  · change A ∈ (FGSA.clock p (storeAt p c E rho iy y) _).fg.TF
    rw [(clock_cumulative p _ _).1]
    exact hc.1 hAm
  · have heq := support_stamp_kept hc.2.2.1 (eraseFG A) hkeys
    change (((FGSA.clock p (storeAt p c E rho iy y) _).base.blockStamp.find? _).map
      Prod.snd).getD _ < D
    rw [(clock_cumulative p _ _).2.2.1, heq]
    unfold GridCO.stampBlock at hAstamp
    cases hfind : (storeAt p c E rho j y).base.blockStamp.find? (fun row => row.1 == eraseFG A) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp hfind row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => simpa only [hfind, Option.map_some, Option.getD_some] using hAstamp

private theorem support_decode {o : Obj p} {b : Block} (h : blockOf? p o = some b) :
    ∃ u N, o = ofWire p ⟨.proposer u, .proposal N⟩ ∧ N.erase = b := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i u N
    refine ⟨u, N, ?_, h⟩
    apply toWire_injective (p := p)
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:673–689 (H.1, IF.5 relay of each supporter head); plan H-SUPPORT
§4
step 4 and gap G4. DC: Schedule/AdoptionTransport.lean:346.
INTENTIONAL: per-vote relay, also for faulty seats, not TDel. A block resolved before
e_s at the honest source gate reaches each honest receiver before z_s when the receiver's
q_s finality is below it; its whole FG path then has strict stamps before z_s. -/
theorem healing_support_target_path (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s)
      (SA.gateTime p.toParams s))
    {ix iy : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (K : Block)
    (hK : K ∈ (storeAt p c E rho ix x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho ix x).base K < SA.earlyTime p.toParams s)
    (hF : Block.Preceq (eraseFG (((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st).fg.F) K)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho iy y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Kfg : FGBlock (Fin p.n), eraseFG Kfg = K ∧
      ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A Kfg →
        A ∈ st.fg.TF ∧ GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st
  have hsch := hE.toScheduleWellFormed
  let D := SA.freezeTime p.toParams s
  have hFpost : st.fg.F = (storeAt p c E rho iy y).fg.F := by
    change (clock p _ _).fg.F = _
    rw [clock_fg]
    rfl
  have hDiy : V2.D.Run.idxBefore rho D ≤ iy := by
    by_contra hn
    have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hiy D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at htime
    push_cast at htime
    have hd := p.deltaPos
    nlinarith
  by_cases hg : K = .genesis
  · subst K
    refine ⟨.genesis, rfl, ?_⟩
    exact healing_support_prefreeze_path E rho hsch hN hiy
      (storeBundle_stateBeforeTime E rho D y).cstore.fg.gen
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
  obtain ⟨j, _, t, o, ho, ha, ht⟩ :=
    fgsa_block_accepted_before E rho hE ix x K _ hg hpub hz hK hstamp
  obtain ⟨u, N, rfl, heN⟩ := support_decode ho
  obtain ⟨dl, cut, hD, hmono, hlt, hb, _, hcut, _⟩ := hSync
  have hdz : dl t < D := by
    have hb := hb t
    rw [hDelta] at hb
    change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
    change dl t ≤ max t (4 * p.Δ * (s : Int) + p.Δ) + p.Δ at hb
    change dl t < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hp := p.deltaPos
    have hh : max t (4 * p.Δ * (s : Int) + p.Δ) <
        4 * p.Δ * (s : Int) + 2 * p.Δ := max_lt ht (by linarith)
    linarith
  have hdcut : dl t ≤ cut := by
    refine (le_of_lt hdz).trans (le_trans ?_ hcut)
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (dl t) ≤ iy :=
    (support_idx_mono rho (le_of_lt hdz)).trans hDiy
  have hFd : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho (dl t) y).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hsch]
    refine Gen.Pure.block_preceq_trans (eraseFG_preceq ?_) (hFpost ▸ hF)
    have h := fgsa_monoAlong_preceq_F p c (storeAt p c E rho (V2.D.Run.idxBefore rho (dl t)) y).fg.F
    rw [Gen.V2.Duty.MonoAlong_def] at h
    exact V2.D.Engine.stateBefore_stable _ h.1 h.2.1 h.2.2 E rho hidx y
      (hN.restartFree y _ iy) (KitFG.preceq_refl _)
  have hfreezeVote : D ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨Y, hY, hYK⟩ := fgsa_proposal_receipt (hRoots := hroots) E rho hDelta hE hN dl cut u N t y
    hD (Or.inr ⟨x, hx, j, ha⟩) hy hdcut (hlt t)
    (by simpa only [heN] using
      Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl K) hFd)
    (hdz.le.trans (hfreezeVote.trans (hE.in_horizon _ (List.mem_of_getElem? hiy)).2))
    (fgsa_awakeOn_before_tick_noRestart E rho hE hN hiy hy
      (fgsa_trigger_nonneg E rho hsch (Or.inr ⟨x, hx, j, ha⟩)) (by
        change dl t ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
        change dl t < 4 * p.Δ * (s : Int) + 3 * p.Δ at hdz
        push_cast
        linarith [p.deltaPos]))
  refine ⟨Y, hYK.trans heN, ?_⟩
  have hYD : Y ∈ (V2.D.Run.stateBeforeTime E rho D y).st.fg.TF := by
    have hc := (fgsa_store_cumulative p c E rho hN (support_idx_mono rho (le_of_lt hdz)) y).1
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (dl t)) y).st.fg.TF ⊆
      (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.fg.TF at hc
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho (dl t) hsch,
      Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hc
    exact hc hY
  exact healing_support_prefreeze_path E rho hsch hN hiy hYD

private theorem support_gate_late_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (ix : Nat) (x : V) (s : Slot)
    (o : GridCO.Wire p.n .root) (hm : o ∈ (rho.stateBefore E ix x).st.base.votes)
    (hl : GridCO.headLabel? o = some s)
    (ht : GridCO.stampVote (rho.stateBefore E ix x).st.base o < SA.gateTime p.toParams s) :
    o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (rho.stateBefore E ix x).st (SA.gateTime p.toParams s))) s := by
  refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · change o ∈ (clockPre p _ _).base.votes
    rwa [(Internal.clockPre_vn _ _).1]
  · simpa only [hl] using beq_self_eq_true (some s)
  · rw [support_read_stamp E rho ix x _ o hm]
    exact decide_eq_true ht

/-- Exact raw HEAD service at the source gate gives late-pool membership or a cap.
The service keeps its own history premise, including after replay. -/
theorem healing_support_raw_backward_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    {ix : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (q : Fin p.n) (b : BlockId)
    (hScope : HeadRelayLocalServiceScope E rho s q b (SA.gateTime p.toParams s) ix x) :
    let late := GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (rho.stateBefore E ix x).st (SA.gateTime p.toParams s))) s
    (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈ late ∨
      GridCO.equivocates late q = true := by
  intro late
  rcases (hScope.toReceiptScope E rho hE s q b _ ix x hx).service with hm | hc
  · exact Or.inl (support_gate_late_receipt E rho ix x s _ hm.1 rfl hm.2)
  · obtain ⟨u, hu, v, hv, hne, hlu, hlv, hku, hkv, htu, htv⟩ := hc
    exact Or.inr ((cap_pair late q).mpr
      ⟨u, support_gate_late_receipt E rho ix x s u hu hlu htu,
        v, support_gate_late_receipt E rho ix x s v hv hlv htv, hne, hku, hkv⟩)

/-- Exact target service and the receiver epoch supply the frozen ancestor path. -/
theorem healing_support_target_path_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {iy : Nat} {y : V} {s : Slot} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hEpoch : V2.D.restartFree rho y
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) iy)
    (K : Block) (hService : TargetReceiptService E rho K (SA.freezeTime p.toParams s) y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (rho.stateBefore E iy y)
      (SA.voteTime p.toParams (s + 1))).st
    ∃ Kfg : FGBlock (Fin p.n), eraseFG Kfg = K ∧
      ∀ A, FGBlock.Preceq A Kfg →
        A ∈ st.fg.TF ∧ GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st
  have hBase := fgsa_target_receipt_on E rho hS hroots K
    (SA.freezeTime p.toParams s) y hy hService
  obtain ⟨Kfg, hK, he⟩ := ((storeBundle_stateBeforeTime E rho
    (SA.freezeTime p.toParams s) y).cstore.baseTree K).mp hBase
  exact ⟨Kfg, he, healing_support_prefreeze_path_on E rho hS hiy hEpoch hK⟩

/-- A joined transfer receiver uses earlyTime as the proposal service anchor.
The deadline and every N4 input refer to that same anchor. -/
theorem healing_transfer_proposal_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hDelta : E.Δ = p.Δ) {s r : Slot} {y v : V} {k : Nat} {N : NamedProposal p.n}
    {t : Time} (hy : y ∈ rho.honest) (hv : v ∈ rho.honest)
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hhor : SA.voteTime p.toParams (s + 1) ≤ rho.horizon)
    (hacc : V2.D.Run.acceptsAt E rho k v (ofWire p ⟨.proposer r, .proposal N⟩) t)
    (ht : t < SA.earlyTime p.toParams s)
    (dl : Time → Time) (cut : Time)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hl : SA.earlyTime p.toParams s < dl (SA.earlyTime p.toParams s))
    (hb : dl (SA.earlyTime p.toParams s) ≤ SA.freezeTime p.toParams s)
    (hc : SA.freezeTime p.toParams s ≤ cut)
    (hNX : (fgsa p c).excludes
      (rho.stateBeforeTime E (dl (SA.earlyTime p.toParams s)) y)
      (ofWire p ⟨.proposer r, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer r, .proposal N⟩) t
      (SA.freezeTime p.toParams s) y) := by
  have hd : (toWire p (ofWire p ⟨.proposer r, .proposal N⟩)).decode =
      some (.block r N) := by rw [toWire_ofWire]; rfl
  obtain ⟨hT, hH, hRF, hReady⟩ := fgsa_transfer_path_anchor_service hE hDelta hy hv hJ hhor
    hd hacc ht
  have hfv : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have h0 : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have := p.deltaPos
    positivity
  refine ⟨⟨dl, cut, SA.earlyTime p.toParams s, hD, ?_, ht.le, h0, hl,
    hb.trans hc, hb.trans (hfv.trans hhor), hb, hH,
    hRF.mono le_rfl (fgsa_idxBefore_mono rho hfv), ?_, hNX⟩⟩
  · obtain ⟨z, hz, htr, hAw⟩ := hT
    exact ⟨z, hz, htr, fun u hau hud => hAw u hau (hud.trans_le hb)⟩
  · exact fun j u hau hud hh => hReady j u hau (hud.trans_le hb) hh

end AvailableChain.FGSA.Run
end

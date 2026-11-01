module
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers
public import AvailableChainFGSAProofs.Proofs.Outage.RelayKernel

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Clean services use the actual vote-time GST bound, including prior labels. -/
theorem inclusion_clean_vote_gst [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) (s : Slot) : E.t_GST ≤ SA.voteTime p.toParams s := by
  rw [hset.gst]
  change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
  have := p.deltaPos
  positivity

/-- The Clean count supplies a joined receiver at the exact time, including the horizon. -/
theorem inclusion_joined_witness [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) (t : Time) (ht : 0 ≤ t) (hhor : t ≤ rho.horizon) :
    ∃ x ∈ rho.honest, joinedAt p E rho x (slotAt p t) t := by
  classical
  have hc : (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card := by
    rcases hhor.lt_or_eq with hlt | rfl
    · exact hset.sleepPre.sleepPre.joinedPartBefore t ht hlt
    · exact hset.sleepPre.joinedPartAt
  obtain ⟨x, hx⟩ := Finset.card_pos.mp ((Nat.zero_le _).trans_lt hc)
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- T35: choose a joined vote reader; the proposer can sleep after its proposal. -/
theorem inclusion_joined_vote_witness [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) (s : Slot)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon) :
    ∃ x ∈ rho.honest, joinedAt p E rho x s (SA.voteTime p.toParams s) ∧
      ∃ i : Nat, rho.events[i]? = some (V2.Event.tick x (SA.voteTime p.toParams s)) := by
  have hd := p.deltaPos
  have ht : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    positivity
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ hd.le (by dsimp [Time] at *; omega)
  obtain ⟨x, hx, hJ⟩ := inclusion_joined_witness E rho hset _ ht hhor
  rw [hslot] at hJ
  have he : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hset.pre.base.valid.toScheduleWellFormed
    hset.pre.base.delta x hx (4 * s + 1) (he ▸ hhor) (he ▸ hJ.1)
  exact ⟨x, hx, hJ, i, he ▸ hi⟩

/-- T31/T37: use a joined gate receiver. Its earlier vote has the same restart bound. -/
theorem inclusion_joined_gate_witness [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) (s : Slot)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ x ∈ rho.honest, joinedAt p E rho x (s + 1) (SA.gateTime p.toParams s) ∧
      joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) ∧
      ∃ i, enabledGateAt p c E rho i x s := by
  have hd := p.deltaPos
  have ht : 0 ≤ SA.gateTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    positivity
  have hslot : slotAt p (SA.gateTime p.toParams s) = s + 1 := by
    rw [show SA.gateTime p.toParams s =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 2 * p.Δ from by
        change 4 * p.Δ * (s : Int) + 6 * p.Δ = _
        push_cast
        ring]
    exact slotOf_offset p (s + 1) (2 * p.Δ) (by dsimp [Time] at *; omega)
      (by dsimp [Time] at *; omega)
  obtain ⟨x, hx, hJ⟩ := inclusion_joined_witness E rho hset _ ht hhor
  rw [hslot] at hJ
  have hvg : SA.voteTime p.toParams (s + 1) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith
  have hb : slotStartZ p (((s + 1 : Nat) : Int) - 1) ≤
      SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (((s + 1 : Nat) : Int) - 1) ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hv0 : 0 ≤ SA.voteTime p.toParams (s + 1) := by
    change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    positivity
  have hJV : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)) :=
    ⟨fgsa_awake_of_joinedAt E rho x (s + 1) _ _ hJ hv0 hb hvg,
      fun u hu huv => hJ.2.1 u hu (huv.trans hvg),
      fun u hu huv => hJ.2.2 u hu (huv.trans hvg)⟩
  have he : ((4 * s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams s := by
    change ((4 * s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    ring
  have hs := hset.pre.base.valid.toScheduleWellFormed
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hset.pre.base.delta x hx
    (4 * s + 6) (he ▸ hhor) (he ▸ hJ.1)
  rw [he] at hi
  refine ⟨x, hx, hJ, hJV, i, hi, ?_⟩
  have hm := fgsa_restartTime_bound E rho i x (slotStartZ p (s : Int)) (by
    intro j u hji hj
    have htu : u ≤ SA.gateTime p.toParams s := by
      by_contra hn
      have hij := V2.D.Engine.eventIndex_lt_of_time_lt hs hi hj (lt_of_not_ge hn)
      omega
    have hu := (hs.in_horizon _ (List.mem_of_getElem? hj)).1
    simpa using hJ.2.2 u hu htu (List.mem_of_getElem? hj))
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some u => exact hm u hr

/-- An enabled honest gate supplies the public confirmed-reader guard at that gate. -/
theorem inclusion_confirmedReader_of_enabledGate
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) {k : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho k x s) :
    confirmedReader p c E rho x (SA.gateTime p.toParams s) := by
  have hs := hV.toScheduleWellFormed
  have hd := p.deltaPos
  have hbound : ∀ (j : Nat) (u : Time), rho.events[j]? = some (V2.Event.restart x u) →
      u ≤ SA.gateTime p.toParams s → u ≤ slotStartZ p (s : Int) := by
    intro j u hj hu
    have hjk := V2.D.Engine.restart_index_lt_event hs hj hG.1 hu
      (by change (0 : Nat) < 1; decide)
    obtain ⟨w, hw, huw⟩ := fgsa_restartTime_ge E rho hs hj hjk
    have hb := hG.2
    change (storeAt p c E rho k x).restartTime = some w at hw
    rw [hw] at hb
    exact huw.trans hb
  have hread := fgsa_restartTime_bound E rho (timeIdx rho (SA.gateTime p.toParams s))
    x (slotStartZ p (s : Int)) (by
      intro j u hj hR
      exact hbound j u hR
        ((V2.D.Engine.index_lt_read_length_iff hs _ hR).mp hj))
  have hA := fgsa_enabledGate_awakeClosed hV hx hG
  refine ⟨hx, hV.tick_awake x _ (List.mem_of_getElem? hG.1), ?_⟩
  cases hr : (storeAt p c E rho (timeIdx rho (SA.gateTime p.toParams s)) x).restartTime with
  | none => trivial
  | some w =>
    refine ⟨s, k, hread w hr, le_rfl,
      (V2.D.Engine.index_lt_read_length_iff hs _ hG.1).mpr le_rfl, hG, hA, ?_⟩
    intro u hsu hug hR
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hR
    exact (not_lt_of_ge (hbound j u hj hug) hsu).elim

omit [DecidableEq V] in
/-- The local joined bound excludes restarts from a later event cut to the read tick. -/
theorem inclusion_epoch_of_joined_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {s : Slot} {t a : Time}
    (hi : rho.events[i]? = some (.tick x t)) (hJ : joinedAt p E rho x s t)
    (ha : slotStartZ p ((s : Int) - 1) < a) :
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho a) i := by
  intro k u hk hki he
  have hau : a ≤ u := by
    by_contra hn
    have hka := (Gen.V2.Duty.index_lt_idxBefore_iff hs he a).mpr (lt_of_not_ge hn)
    omega
  have hut : u ≤ t := by
    by_contra hn
    have hik := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he (lt_of_not_ge hn)
    omega
  have hb := hJ.2.2 u (hs.in_horizon _ (List.mem_of_getElem? he)).1 hut
    (List.mem_of_getElem? he)
  exact (not_lt_of_ge hb (ha.trans_le hau)).elim

/-- An actual proposal supplies the environment join guard at its emission tick. -/
theorem inclusion_joinedAt_of_proposal
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hV : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.proposalTime p.toParams s)))
    (N : NamedProposal p.n)
    (ho : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E i) :
    joinedAt p E rho x s (SA.proposalTime p.toParams s) := by
  have hem := ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have he := (fgsa_emits_proposal E rho _ x _ s (.proposal N)).mp hem
  have hslot : p.slotOf (SA.proposalTime p.toParams s) = s := by
    change p.slotOf (4 * p.Δ * (s : Int)) = s
    simpa only [add_zero] using slotOf_offset p s 0 (by decide)
      (by have hd := p.deltaPos; dsimp [Time] at *; omega)
  have hbound (w : Time) (_hw : 0 ≤ w) (hwt : w ≤ SA.proposalTime p.toParams s)
      (hr : V2.Event.restart x w ∈ rho.events) : w ≤ slotStartZ p ((s : Int) - 1) := by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hji := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hj hi hwt
      (by change (0 : Nat) < 1; decide)
    obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hV.toScheduleWellFormed hj hji
    have hg := he.2.2.2.1
    unfold joinedNow at hg
    rw [fgsa_clock_restartTime, hu, (clock_vn _ _).2] at hg
    unfold joinedAtTime at hg
    rw [hslot] at hg
    exact hwu.trans (of_decide_eq_true hg)
  refine ⟨he.1, ?_, hbound⟩
  intro w hw hwt hW
  exact hbound w hw.le hwt (hV.wake_restart x
    (hV.honest_only _ (List.mem_of_getElem? hi)) w hw
    (hwt.trans (hV.in_horizon _ (List.mem_of_getElem? hi)).2) hW)

/-- Stored honest HEADs map outside the selected joined seats only to faulty nodes. -/
theorem inclusion_joined_rest_bound [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hE : V2.D.ExecutionValid E rho)
    (r : Slot) (H : Finset (Fin p.n))
    (hH : ∀ k, rho.seatOf (.base (.head r)) k ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head r)) k) r (SA.voteTime p.toParams r) → k ∈ H)
    (L : List (GridCO.Wire p.n .root))
    (hL : ∀ o ∈ L, ∀ k, GridCO.headSeat? o = some k →
      ∃ i x, ∃ o' ∈ (storeAt p c E rho i x).base.votes,
        GridCO.headLabel? o' = some r ∧ GridCO.headSeat? o' = some k) :
    ((GridCO.seats p.n L).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
  classical
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head r)))
  · intro k hk
    obtain ⟨hl, hn⟩ := Finset.mem_sdiff.mp hk
    rw [Gen.V2.Duty.faulty_def]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hh
    apply hn (hH k hh ?_)
    obtain ⟨o, ho, hs⟩ := (Gen.AC.Root.vote_pool_mem_seats _ k).mp hl
    obtain ⟨i, x, o', ho', hl', hs'⟩ := hL o ho k hs
    exact fgsa_stored_honest_head_joined E rho hE i x r k o' ho' hl' hs' hh
  · intro k _ j _ he
    exact (hC (.base (.head r)) trivial).injective he

/-- Local services for the retained Clean consumer. The joint invariant must
derive these fields at each cut; they are not public claim premises. -/
structure InclusionReceiverInputs (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  early : ∀ r a x, a = SA.proposalTime p.toParams (r + 1) ∨
      a = SA.voteTime p.toParams (r + 1) → a ≤ rho.horizon →
    E.t_GST ≤ SA.voteTime p.toParams r →
    headReader p E rho x (r + 1) a →
    ∀ ie, rho.events[ie]? = some (.tick x (SA.earlyTime p.toParams r)) →
    ∀ q K, rho.seatOf (.base (.head r)) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) (SA.voteTime p.toParams r) K →
      Block.Preceq (F_at p c E rho ie x) K →
      Nonempty (FreshHeadService E rho r q K.root (SA.earlyTime p.toParams r) x) ∧
        TargetReceiptService E rho K (SA.earlyTime p.toParams r) x
  retained : ∀ s ip x N, x ∈ rho.honest →
    E.t_GST ≤ SA.voteTime p.toParams (s - 1) →
    rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip →
    ∀ ih y, headReader p E rho y s (SA.voteTime p.toParams s) →
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq (F_at p c E rho ih y) N.erase →
      RetainedServiceScope E rho ip ih x y s N

/-- The field projection required from the Clean history supplier. -/
structure InclusionHistoryBounds (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop where
  below : ∀ i x, i ≤ timeIdx rho rho.horizon → x ∈ rho.honest →
    let st := storeAt p c E rho i x
    let bound := BelowLabel p c E rho i (labelBoundAt p c rho i)
    bound (F_at p c E rho i x) ∧ bound (J_at p c E rho i x) ∧ bound (S_at p c E rho i x) ∧
      (∀ row ∈ st.base.obligations, bound row.1) ∧
      (∀ r C, GridCO.savedGenuine st.base r = some (some C) → bound C)

/-- The guarded event result reads the exact pre-gate confirmation. -/
theorem inclusion_gate_raw_at_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {s : Slot}
    (hG : enabledGateAt p c E rho j x s) :
    gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
  rw [gateResultAt_eq_gateResult p c E rho hs hG.1, gateResult_eq_saved p c E rho hs hG.1]
  have h := fgsa_gate_saved_result E rho hs hG.1 (fgsa_gate_joined_of_enabled E rho hG)
  change GridCO.savedGenuine (clock p (rho.stateBefore E j x).st
    (SA.gateTime p.toParams s)).base s = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (rho.stateBefore E j x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (rho.stateBefore E j x).st (SA.gateTime p.toParams s))) s)
  rw [clockPre_fg]
  exact h

/-- A nonempty gate result has an actual enabled gate origin. -/
theorem inclusion_gate_origin_of_result
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (s : Slot) (B : Block)
    (hB : gateResult p c E rho x s = some (some B)) :
    ∃ i, enabledGateAt p c E rho i x s ∧ gateResultAt p c E rho i = some (some B) := by
  cases hi : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none =>
    have hn : gateResult p c E rho x s = none := by
      rw [gateResult_def, gateIn_def, preTick_def, hi]
      rfl
    rw [hn] at hB
    cases hB
  | some i =>
    have ht := V2.D.Run.tickIdx?_spec hi
    have hSaved := (gateResult_eq_saved p c E rho hs ht).symm.trans hB
    change GridCO.savedGenuine (clock p (rho.stateBefore E i x).st
      (SA.gateTime p.toParams s)).base s = some (some B) at hSaved
    have hJ : joinedAtTime p (rho.stateBefore E i x).st.restartTime
        (SA.gateTime p.toParams s) = true := by
      cases hj : joinedAtTime p (rho.stateBefore E i x).st.restartTime
        (SA.gateTime p.toParams s) with
      | true => rfl
      | false =>
        rw [fgsa_gate_saved_unjoined E rho hs ht hj] at hSaved
        cases hSaved
    have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
      (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
        (fgsa_gate_slot (c := c) (rho.stateBefore E i x) s)
    have hG : enabledGateAt p c E rho i x s := by
      refine ⟨ht, ?_⟩
      cases hm : (storeAt p c E rho i x).restartTime with
      | none => trivial
      | some w =>
        change (rho.stateBefore E i x).st.restartTime = some w at hm
        rw [hm] at hJ
        change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) =
          true at hJ
        change w ≤ 4 * p.Δ * (s : Int)
        simpa only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
          decide_eq_true_eq] using hJ
    exact ⟨i, hG, (gateResultAt_eq_gateResult p c E rho hs ht).trans hB⟩

/-- Scoped Clean result ordering applies to every nonempty executed result:
each result supplies its own enabled gate and confirmed-reader guard. -/
theorem inclusion_ordered_of_scoped
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    (hOrdered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      confirmedReader p c E rho x (SA.gateTime p.toParams r) →
      confirmedReader p c E rho y (SA.gateTime p.toParams s) →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) :
    ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C) := by
  intro x y r s B C hx hy hr hs hB hC
  obtain ⟨i, hGX, _⟩ := inclusion_gate_origin_of_result E rho hV.toScheduleWellFormed x r B hB
  obtain ⟨j, hGY, _⟩ := inclusion_gate_origin_of_result E rho hV.toScheduleWellFormed y s C hC
  exact hOrdered x y r s B C hx hy hr hs
    (inclusion_confirmedReader_of_enabledGate E rho hV hx hGX)
    (inclusion_confirmedReader_of_enabledGate E rho hV hy hGY) hB hC

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.6:932–944, 03:293–312; spec 1240–1243; plan I-EXACT, G1
steps 4 and 6. Class (iii). DC: Goldfish/Confirmation:494,508,567; INTENTIONAL:
the batch count is read in the actual proposer pools. Every awake honest
label-(s−1) HEAD is a received, resolved vote above D0, so every prefix L of
D0 has a strict majority and beats each conflicting block. -/
theorem inclusion_proposer_prior_of_F_prefix_cover [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hHon : ∀ q ∈ H, rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest)
    (hCover : ∀ q, rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (s - 1))) q) (s - 1)
        (SA.voteTime p.toParams (s - 1)) → q ∈ H)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hFD : Block.Preceq (eraseFG st.fg.F) D0)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  intro L hL
  have hstored (o : GridCO.Wire p.n .root) (ho : o ∈ proposerVotes st s) :
      o ∈ (storeAt p c E rho i x).base.votes ∧ GridCO.headLabel? o = some (s - 1) := by
    have h := List.mem_filter.mp ho
    exact ⟨hvotes ▸ h.1, beq_iff_eq.mp h.2⟩
  have hclean : ∀ q ∈ H, GridCO.equivocates (proposerVotes st s) q = false := by
    intro q hq
    obtain ⟨K, t, he, _, _, _, _, _⟩ := hrec q hq
    refine inclusion_no_equivocation _ q
      (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) ?_
    intro o ho hs
    obtain ⟨hm, hl⟩ := hstored o ho
    exact fgsa_honest_head_eq_of_stored E rho hE i x (s - 1) q K.root t (hHon q hq) he
      o hm hl hs
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports st.base.blocks (proposerSupport st s) q D0 = true := by
    intro q hq
    obtain ⟨K, t, _, hv, hK, hlookup, hslot, hDK⟩ := hrec q hq
    have hKb := (List.mem_filter.mp (resolvedHead_mem _ _ hK)).1
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head (s - 1)) q, K.root⟩, ?_, rfl, ?_⟩
    · apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨hv, beq_self_eq_true _⟩, ?_⟩
      change (match GridCO.resolvedHead? (actView st) _ with
        | some H => Block.preceq (eraseFG st.fg.F) H && decide (H.slot ≤ s - 1)
        | none => false) = true
      rw [hK]
      exact Bool.and_eq_true_iff.mpr ⟨block_preceq_trans hFD hDK, decide_eq_true hslot⟩
    · exact (Gen.AC.Root.vote_support_body _ _ _).mpr ⟨K, hlookup, hKb, hslot, hDK⟩
  have hother := inclusion_joined_rest_bound E rho hC hE (s - 1) H
    hCover (proposerVotes st s)
    (fun o ho k hk => ⟨i, x, o, (hstored o ho).1, (hstored o ho).2, hk⟩)
  have hc := Gen.AC.Root.batch_counts st.base.blocks (proposerVotes st s) (proposerVotes st s)
    (proposerSupport st s) H H.card (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) (fun _ h => (List.mem_filter.mp h).1) rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, hrival, _⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  have hDB : Block.compatible D0 B = false := by
    cases h : Block.compatible D0 B with
    | false => rfl
    | true =>
      have hLB := block_compatible_of_preceq_compatible hL h
      change Block.compatible L B = true at hLB
      rw [hB] at hLB
      contradiction
  exact lt_of_le_of_lt (hrival B hDB) (lt_of_lt_of_le hbatch.lt (hprefix L hL).1)

/-- Joined proposer counts use authentic receipts and cover all joined honest seats. -/
theorem inclusion_receiver_proposer_prior_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head (s - 1))) q) (s - 1)
        (SA.voteTime p.toParams (s - 1)))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hFD : Block.Preceq (eraseFG st.fg.F) D0)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  exact inclusion_proposer_prior_of_F_prefix_cover E rho hE hC s i x st hvotes H
    (fun q hq => ((hH q).mp hq).1) (fun q hh hJ => (hH q).mpr ⟨hh, hJ⟩)
    hbatch D0 hFD hrec

/-- The legacy awake count also covers the joined seats. Its explicit receipt
premise still requires an actual emission and resolved target for every counted seat. -/
theorem inclusion_proposer_prior_of_F_prefix [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (s : Slot) (i : Nat) (x : V)
    (st : State p.n) (hvotes : st.base.votes = (storeAt p c E rho i x).base.votes)
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head (s - 1))) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head (s - 1))) q) (SA.voteTime p.toParams (s - 1)) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hFD : Block.Preceq (eraseFG st.fg.F) D0)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (s - 1))) q)
        (ofHead p ⟨.seat (.head (s - 1)) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head (s - 1)) q, K.root⟩ : HeadWire p.n) ∈ st.base.votes ∧
      GridCO.resolvedHead? (actView st) (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      Gen.AC.Root.resolvedTarget? st.base.blocks
        (baseVote ⟨.seat (.head (s - 1)) q, K.root⟩) = some K ∧
      K.slot ≤ s - 1 ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 →
      GridCO.voterCount (proposerVotes st s) < 2 * RetainedWalk.ss st s L ∧
      (∀ B, Block.compatible L B = false → RetainedWalk.ss st s B < RetainedWalk.ss st s L) := by
  exact inclusion_proposer_prior_of_F_prefix_cover E rho hE hC s i x st hvotes H
    (fun q hq => ((hH q).mp hq).1) (fun q hh hJ => (hH q).mpr ⟨hh, hJ.1⟩)
    hbatch D0 hFD hrec

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.17:2980–3001, 03:293–331; spec 1283–1294; plan I-EXACT,
G1 steps 4 and 6. Class (iii). DC: Goldfish/Confirmation:494,508,567;
INTENTIONAL: the batch count is read in the actual HEAD pools, carried votes
included. Provenance maps each pooled seat to a stored vote. Every prefix L
of D0 gets a strict majority, and no conflicting block gets one. -/
theorem inclusion_receiver_scores_on [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (hDelta : E.Δ = p.Δ) (r : Slot)
    {ih : Nat} {y : V}
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head r)) q) r (SA.voteTime p.toParams r))
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
        (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq D0 K)
    (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1))) :
    ∀ L, Block.Preceq L D0 → RetainedTargetScores p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1)))
      (r + 1) L := by
  intro L hL
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))
  have hsub : headSupport p dst (r + 1) ⊆ headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
  obtain ⟨it, hit⟩ := inclusion_relay_vote_proposal_tick hE
    hDelta hy hih hJ
  have hprov := inclusion_relay_headVotes_provenance E rho hE ih y r hih hJ hit
  have hseat (q : Fin p.n) (hq : q ∈ H) : ∃ K t,
      V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (r + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ r ∧ Block.Preceq D0 K ∧
      ∀ o ∈ headVotes p dst (r + 1), GridCO.headSeat? o = some q →
        o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
    obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrec q hq
    have hpre : ∀ o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r,
        GridCO.headSeat? o = some q →
          o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
      intro o ho hs
      have h := List.mem_filter.mp ho
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K.root t ((hH q).mp hq).1 he
        o h.1 (beq_iff_eq.mp h.2) hs
    refine ⟨K, t, he, hv, hK, hslot, hDK, ?_⟩
    intro o ho hs
    rcases hprov o ho q hs with hm | heq
    · exact hpre o hm hs
    · have hne : GridCO.equivocates
          (GridCO.votesAt (V2.D.Run.stateBefore E rho ih y).st.base r) q = false :=
        inclusion_no_equivocation _ q _ hpre
      rw [hne] at heq
      contradiction
  have hclean : ∀ q ∈ H, GridCO.equivocates (headVotes p dst (r + 1)) q = false := by
    intro q hq
    obtain ⟨K, _, _, _, _, _, _, hu⟩ := hseat q hq
    exact inclusion_no_equivocation _ q _ hu
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (r + 1)) q D0 = true := by
    intro q hq
    obtain ⟨K, _, _, hv, hK, hslot, hDK, _⟩ := hseat q hq
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head r) q, K.root⟩, hv, rfl, ?_⟩
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
        (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)) _ hK rfl,
        hK, hslot, hDK⟩
  have hother := inclusion_joined_rest_bound E rho hC hE r H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.Root.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.Root.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card
    (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) hsub rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, _, hnone⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  apply hnone B
  intro q hq
  obtain ⟨K, _, _, _, hK, _, hDK, hu⟩ := hseat q hq
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨o, ho, hk, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ q B).mp hs
  rw [hu o (hsub ho) hk] at hvote
  have hlookup := resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _))
    (baseVote ⟨.seat (.head r) q, K.root⟩) hK rfl
  rw [Gen.AC.Root.voteSupports_def, hlookup] at hvote
  change (_ && _ && Block.preceq B K) = true at hvote
  have hBK : Block.Preceq B K := (Bool.and_eq_true_iff.mp hvote).2
  have hLB := block_compatible_of_common (block_preceq_trans hL hDK) hBK
  change Block.compatible L B = true at hLB
  rw [hB] at hLB
  contradiction

/-- Legacy score count with explicit global restart freedom.
Sleep consumers use inclusion_receiver_scores_on and actual joined-tick provenance. -/
theorem inclusion_reader_scores [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) (r : Slot)
    {ih : Nat} {y : V}
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (r + 1))))
    (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head r)) q) (SA.voteTime p.toParams r) = true)
    (hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card) (D0 : Block)
    (hrec : ∀ q ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p
        (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))) (r + 1) ∧
      K ∈ (clock p (V2.D.Run.stateBefore E rho ih y).st
        (SA.voteTime p.toParams (r + 1))).base.blocks ∧
      K.slot ≤ r ∧ Block.Preceq D0 K) :
    ∀ L, Block.Preceq L D0 → RetainedTargetScores p
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1)))
      (r + 1) L := by
  intro L hL
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (r + 1))
  have hsub : headSupport p dst (r + 1) ⊆ headVotes p dst (r + 1) :=
    fgsa_headSupport_subset_headVotes E rho hE ih y r
  have hprov := fgsa_headVotes_provenance E rho hE hN ih y r hih
  have hseat (q : Fin p.n) (hq : q ∈ H) : ∃ K t,
      V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (r + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ r ∧ Block.Preceq D0 K ∧
      ∀ o ∈ headVotes p dst (r + 1), GridCO.headSeat? o = some q →
        o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
    obtain ⟨K, t, he, hv, hK, hslot, hDK⟩ := hrec q hq
    have hpre : ∀ o ∈ GridCO.votesAt (storeAt p c E rho ih y).base r,
        GridCO.headSeat? o = some q →
          o = baseVote (⟨.seat (.head r) q, K.root⟩ : HeadWire p.n) := by
      intro o ho hs
      have h := List.mem_filter.mp ho
      exact fgsa_honest_head_eq_of_stored E rho hE ih y r q K.root t ((hH q).mp hq).1 he
        o h.1 (beq_iff_eq.mp h.2) hs
    refine ⟨K, t, he, hv, hK, hslot, hDK, ?_⟩
    intro o ho hs
    rcases hprov o ho q hs with hm | heq
    · exact hpre o hm hs
    · have hne : GridCO.equivocates
          (GridCO.votesAt (V2.D.Run.stateBefore E rho ih y).st.base r) q = false :=
        inclusion_no_equivocation _ q _ hpre
      rw [hne] at heq
      contradiction
  have hclean : ∀ q ∈ H, GridCO.equivocates (headVotes p dst (r + 1)) q = false := by
    intro q hq
    obtain ⟨K, _, _, _, _, _, _, hu⟩ := hseat q hq
    exact inclusion_no_equivocation _ q _ hu
  have hsupp : ∀ q ∈ H,
      Gen.AC.Root.poolSupports dst.base.blocks (headSupport p dst (r + 1)) q D0 = true := by
    intro q hq
    obtain ⟨K, _, _, hv, hK, hslot, hDK, _⟩ := hseat q hq
    apply (Gen.AC.Root.vote_pool_support_witness _ _ q D0).mpr
    refine ⟨baseVote ⟨.seat (.head r) q, K.root⟩, hv, rfl, ?_⟩
    exact (Gen.AC.Root.vote_support_body _ _ _).mpr
      ⟨K, resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
        (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _)) _ hK rfl,
        hK, hslot, hDK⟩
  have hother := inclusion_rest_bound E rho hC hE r H
    (fun k hh ha => (hH k).mpr ⟨hh, ha⟩) (headVotes p dst (r + 1)) (by
      intro o ho k hk
      rcases hprov o ho k hk with hm | heq
      · have h := List.mem_filter.mp hm
        exact ⟨ih, y, o, h.1, beq_iff_eq.mp h.2, hk⟩
      · obtain ⟨u, hu, _, _, _, hku, _⟩ := (Gen.AC.Root.cap_pair _ k).mp heq
        have h := List.mem_filter.mp hu
        exact ⟨ih, y, u, h.1, beq_iff_eq.mp h.2, hku⟩)
  have hc := Gen.AC.Root.batch_counts dst.base.blocks (headVotes p dst (r + 1))
    (headVotes p dst (r + 1)) (headSupport p dst (r + 1)) H H.card
    (Gen.V2.Duty.faulty rho).card D0
    (fun _ h => h) hsub rfl hclean hsupp hother hbatch
  rw [Gen.AC.Root.BatchBounds_def] at hc
  obtain ⟨_, _, hprefix, _, hnone⟩ := hc
  refine ⟨(hprefix L hL).2, ?_⟩
  intro B hB
  apply hnone B
  intro q hq
  obtain ⟨K, _, _, _, hK, _, hDK, hu⟩ := hseat q hq
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨o, ho, hk, hvote⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ q B).mp hs
  rw [hu o (hsub ho) hk] at hvote
  have hlookup := resolvedTarget_of_mem _ (baseBlocks_rootInj p dst
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _))
    (baseVote ⟨.seat (.head r) q, K.root⟩) hK rfl
  rw [Gen.AC.Root.voteSupports_def, hlookup] at hvote
  change (_ && _ && Block.preceq B K) = true at hvote
  have hBK : Block.Preceq B K := (Bool.and_eq_true_iff.mp hvote).2
  have hLB := block_compatible_of_common (block_preceq_trans hL hDK) hBK
  change Block.compatible L B = true at hLB
  rw [hB] at hLB
  contradiction


end AvailableChain.FGSA.Run
end

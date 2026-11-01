module
public import AvailableChainFGSAProofs.Proofs.Clean.Chain

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] in
/-- A local non-restart event extends an event-index epoch by one event. -/
theorem clean_restartFree_succ {i j : Nat} {v : V}
    (hRF : V2.D.restartFree rho v i j)
    (hN : ∀ t, rho.events[j]? ≠ some (.restart v t)) :
    V2.D.restartFree rho v i (j + 1) := by
  intro k t hik hkj ht
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hkj) with hk | rfl
  · exact hRF k t hik hk ht
  · exact hN t ht

omit [DecidableEq V] in
/-- A gate tick has no local restart in its one-event interval. -/
theorem clean_gate_restartFree {j : Nat} {x v : V} {s : Slot}
    (ht : IsGateTick p c rho j x s) : V2.D.restartFree rho v j (j + 1) := by
  apply clean_restartFree_succ (by intro k t hj hk; omega)
  intro t hn
  rw [ht] at hn
  cases hn

/-- A gate tick keeps the FG fields, including both finalized and justified blocks. -/
theorem clean_gate_fg_eq {j : Nat} {x : V} {s : Slot}
    (ht : IsGateTick p c rho j x s) :
    (storeAt p c E rho (j + 1) x).fg = (storeAt p c E rho j x).fg := by
  change (V2.D.Run.stateBefore E rho (j + 1) x).st.fg = _
  rw [(V2.D.Run.step_tick_eq E rho ht).1,
    tick_st (p := p) (c := c) E rho (V2.D.Run.stateBefore E rho j x) x
      (SA.gateTime p.toParams s), clock_fg]
  rfl

/-- A restart keeps the durable Clean state and starts empty saved histories. -/
theorem clean_restart_fields {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.restart v t)) :
    let a := storeAt p c E rho j v
    let b := storeAt p c E rho (j + 1) v
    b.fg = a.fg ∧ b.base.blocks = a.base.blocks ∧
      b.base.obligations = a.base.obligations ∧
      b.base.stableRecord = a.base.stableRecord ∧
      b.base.genuine = [] ∧ b.fastWrite = [] ∧ b.restartTime = some t := by
  have hs : storeAt p c E rho (j + 1) v = acRestart p (storeAt p c E rho j v) t := by
    change (V2.D.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.D.Engine.state_after_restart he]
    rfl
  dsimp only
  rw [hs]
  exact ⟨acRestart_fg p _ t, acRestart_blocks p _ t, acRestart_obligations p _ t,
    acRestart_stableRecord p _ t, acRestart_genuine p _ t, acRestart_fastWrite p _ t,
    acRestart_restartTime p _ t⟩

/-- Completed event results stay in the global history when local caches are erased. -/
theorem cleanHist_step_restart
    {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.restart v t))
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) := by
  have hn (x : V) (s : Slot) : ¬ IsGateTick p c rho i x s := by
    intro ht
    change rho.events[i]? = some (.tick x _) at ht
    rw [he] at ht
    cases ht
  have hr : cleanResults p c E rho (i + 1) = cleanResults p c E rho i := by
    ext ⟨s, B⟩
    rw [cleanResults_mem_succ_iff]
    constructor
    · rintro (h | ⟨x, ht, _⟩)
      · exact h
      · exact (hn x s ht.1).elim
    · exact Or.inl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hr] using hh.ordered
  · simpa only [hr] using hh.same
  · intro j x s hj ht
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s ht.1).elim
    exact hh.nonempty j x s hji ht
  · intro j k x y s B hj hk ht hy hJ hB
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s ht).elim
    exact hh.continues j k x y s B hji hk ht hy hJ hB

/-- The enabled gate's receiver interval gives N4 its exact event-index epoch. -/
theorem clean_enabledGate_service_epoch (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {j : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho j x s)
    {a freeze : Time} (ha : slotStartZ p (s : Int) ≤ a) (haf : a < freeze)
    (hf : freeze ≤ SA.gateTime p.toParams s) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho freeze) := by
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hV.toScheduleWellFormed haf
  intro k t ht hat htf
  exact clean_enabledGate_restartFreeTime hV hR hx hG t (ha.trans_lt hat)
    (htf.le.trans hf) (List.mem_of_getElem? ht)

/-- Restarts before this same-time tick keep the FG fields of the strict time read. -/
theorem clean_gate_fg_before_time (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hi : IsGateTick p c rho i x s) :
    (storeAt p c E rho i x).fg =
      (V2.D.Run.stateBeforeTime E rho (SA.gateTime p.toParams s) x).st.fg := by
  let a := V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)
  have hai : a ≤ i := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hS hi
      (SA.gateTime p.toParams s)).mp (Nat.lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim
  have hp : (storeAt p c E rho i x).fg = (storeAt p c E rho a x).fg := by
    apply V2.D.Engine.stateBefore_step_induction E rho
      (fun nd => nd.st.fg = (storeAt p c E rho a x).fg) hai x ?_ rfl
    intro j e haj hji he hx hfg
    have htime : e.time = SA.gateTime p.toParams s := by
      have hlo : SA.gateTime p.toParams s ≤ e.time := by
        by_contra hn
        have hj := (Gen.V2.Duty.index_lt_idxBefore_iff hS he
          (SA.gateTime p.toParams s)).mpr (lt_of_not_ge hn)
        exact (Nat.not_lt_of_ge haj) hj
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      have hk := List.pairwise_iff_getElem.mp hS.sorted j i hjl hil hji
      rw [hje, hie] at hk
      exact le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk) hlo
    cases e with
    | restart v t =>
      change v = x at hx
      subst v
      simp only [V2.D.World.step, Function.update_self]
      change (acRestart p (storeAt p c E rho j x) t).fg = _
      rwa [acRestart_fg]
    | tick v t =>
      change v = x at hx
      subst v
      change t = SA.gateTime p.toParams s at htime
      subst t
      have hji' := fgsa_tick_unique E rho hS he hi
      exact (Nat.ne_of_lt hji hji').elim
    | deliver v o t =>
      change t = SA.gateTime p.toParams s at htime
      exact (Nat.not_lt_of_ge (V2.D.Engine.tick_index_lt_delivery E rho hS hi he
        htime.symm.le).le) hji |>.elim
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.gateTime p.toParams s) hS]
  exact hp

/-- A confirmed reader after this gate has the cutoff for this same enabled gate. -/
theorem clean_enabledGate_of_confirmedReader (hS : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {s : Slot} (ht : IsGateTick p c rho j x s)
    (hC : confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
      (SA.gateTime p.toParams s)) : enabledGateAt p c E rho j x s := by
  have hmarker :
      (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams s)) x).restartTime =
        (storeAt p c E rho j x).restartTime := by
    have hb := congrArg (fun nd : Node p => nd.st.restartTime) (afterTicks_node E rho hS ht)
    rw [afterTicks_eq_stateBefore E rho hS] at hb
    have hk := congrArg (fun st : State p.n => st.restartTime)
      (tick_st (p := p) (c := c) E rho (V2.D.Run.stateBefore E rho j x) x
        (SA.gateTime p.toParams s))
    exact hb.trans (hk.trans (fgsa_clock_restartTime _ _))
  refine ⟨ht, ?_⟩
  have hc := hC.2.2
  change (match (storeAt p c E rho j x).restartTime with
    | none => True | some w => w ≤ slotStartZ p (s : Int))
  rw [hmarker] at hc
  cases hm : (storeAt p c E rho j x).restartTime with
  | none => trivial
  | some w =>
    rw [hm] at hc
    obtain ⟨r, k, hwr, htime, _, _, _, _⟩ := hc
    have hrs : (r : Int) ≤ s := by
      change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ at htime
      have := p.deltaPos
      nlinarith
    have hrle : slotStartZ p (r : Int) ≤ slotStartZ p (s : Int) := by
      change 4 * p.Δ * (r : Int) ≤ 4 * p.Δ * (s : Int)
      exact mul_le_mul_of_nonneg_left hrs (by have := p.deltaPos; positivity)
    exact hwr.trans hrle

/-- T10: order older results through an earlier joined node, then transfer to this voter. -/
theorem clean_gate_head_prefixes_joined [Fintype V] {ΔF b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) (hf : FGFoundation p c E rho)
    {i k : Nat} {x y : V} {s : Slot} (hi : i < timeIdx rho b₀)
    (ht : IsGateTick p c rho i x (s + 1))
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i) :
    (∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s + 1 →
      Block.Preceq B (headAtIdx p c E rho k (s + 1))) ∧
    (∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x)
      (headAtIdx p c E rho k (s + 1))) := by
  have hS := h.base.valid.toScheduleWellFormed
  have hx := hS.honest_only _ (List.mem_of_getElem? ht)
  have htime := (V2.D.Engine.index_lt_read_length_iff hS b₀ ht).mp hi
  have hprev : SA.gateTime p.toParams s < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ <
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    nlinarith [p.deltaPos]
  obtain ⟨z, j, _, hG, _⟩ := clean_joined_gate_witness h s (hprev.trans_le htime)
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hS hG.1 ht hprev
  have hbefore : ∀ j z, IsGateTick p c rho j z s → k < j := by
    intro j z hj
    apply V2.D.Engine.eventIndex_lt_of_time_lt hS hk hj
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    nlinarith [p.deltaPos]
  obtain ⟨D, hD, _⟩ := hh.nonempty j z s hji hG
  have hDH := hh.continues j k z y s D hji (hbefore j z hG.1) hG.1 hk hJ hD
  have hresults : ∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s + 1 →
      Block.Preceq B (headAtIdx p c E rho k (s + 1)) := by
    intro r B hB hr
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hrs | heq
    · exact Gen.Pure.block_preceq_trans
        (hh.ordered r s B D hB ⟨j, hji, z, hG.1, hG.2, hD⟩ hrs) hDH
    · subst r
      obtain ⟨l, hl, z, hz, _, hB⟩ := hB
      exact hh.continues l k z y s B hl (hbefore l z hz) hz hk hJ hB
  refine ⟨hresults, ?_⟩
  have hF : Block.Preceq (F_at p c E rho i x) (headAtIdx p c E rho k (s + 1)) := by
    rcases (hs.gateInputs x (s + 1) ht).1 with hg | ⟨r, B, hB, hr, hFB⟩
    · rw [hg]
      exact Gen.Pure.block_genesis_preceq _
    · exact Gen.Pure.block_preceq_trans hFB (hresults r B hB hr)
  intro j hji
  exact Gen.Pure.block_preceq_trans (eraseFG_preceq (hf.mono j i x hx hji).1) hF

/-- P6: the selected joined HEAD voters give the strict Clean batch denominator. -/
theorem clean_gate_batch_joined [Fintype V] {ΔF b₀ : Time}
    (h : CleanCutSet p c E rho b₀ ΔF) {i : Nat} {x : V} {s : Slot}
    (hi : i < timeIdx rho b₀) (ht : IsGateTick p c rho i x s) :
    ∃ H : Finset (Fin p.n),
      (∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head s)) k) s (SA.voteTime p.toParams s)) ∧
      Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card := by
  classical
  let A := joinedHonest p E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (h.base.cstar (.base (.head s)) trivial)
  let H := A.image e.symm
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_vote_slot (c := c) (V2.D.Run.stateBefore E rho i x) s)
  refine ⟨H, ?_, ?_⟩
  · intro k
    have he : k ∈ H ↔ e k ∈ A := by
      change k ∈ A.image e.symm ↔ e k ∈ A
      simp only [Finset.mem_image, e.symm_apply_eq]
      exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hk => ⟨e k, hk, rfl⟩⟩
    rw [he]
    change rho.seatOf (.base (.head s)) k ∈ rho.honest.filter
      (fun v => joinedAt p E rho v (slotAt p (SA.voteTime p.toParams s))
        (SA.voteTime p.toParams s)) ↔ _
    rw [hslot]
    exact Finset.mem_filter
  have htime := (V2.D.Engine.index_lt_read_length_iff h.base.valid.toScheduleWellFormed
    b₀ ht).mp hi
  have hv : 0 ≤ SA.voteTime p.toParams s ∧ SA.voteTime p.toParams s < b₀ := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ b₀ at htime
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ ∧ 4 * p.Δ * (s : Int) + p.Δ < b₀
    have := p.deltaPos
    constructor <;> nlinarith [Int.natCast_nonneg s]
  have hcard : H.card = (joinedHonest p E rho (SA.voteTime p.toParams s)).card :=
    Finset.card_image_of_injective A e.symm.injective
  exact ⟨hcard ▸ h.joinedPartBefore _ hv.1 hv.2⟩

/-- The joined voter guard gives the stored duty guard at this exact HEAD tick. -/
theorem clean_joinedNow_of_joined_vote (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hJ : joinedAt p E rho x s (SA.voteTime p.toParams s)) :
    joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (SA.voteTime p.toParams s)).st = true := by
  have hslot : p.slotOf (SA.voteTime p.toParams s) = s :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_vote_slot (c := c) (V2.D.Run.stateBefore E rho i x) s)
  apply fgsa_joinedNow_of_joinedEnv E rho hS hi
  intro w hw0 hwt hw
  rw [hslot]
  exact hJ.2.2 w hw0 hwt hw

end AvailableChain.FGSA.Run
end

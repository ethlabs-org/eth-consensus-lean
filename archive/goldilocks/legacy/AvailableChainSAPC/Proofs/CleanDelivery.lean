module
public import AvailableChainSAPC.Proofs.CleanConsequences
public import AvailableChainSAPC.Proofs.Timely

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A later successful save names the exact successful first save,
without a quorum-uniqueness or cap premise. -/
theorem savedTimely_first_save {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (r : Slot) (b : Block)
    (hn : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b)) :
    ∃ j < index, rho.events[j]? = some (.tick v (earlyTime p r)) ∧
      savedTimely (Run.stateBefore (sapc p) rho (j + 1) v) r = some (some b) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨row, hf, hb⟩ := Option.map_eq_some_iff.mp hn
  have hr : row.1 = r := by simpa using List.find?_some hf
  have hrow : row = (r, some b) := Prod.ext hr hb
  have hm := List.mem_of_find?_eq_some hf
  rw [hrow] at hm
  obtain ⟨j, hj, ht, hfind⟩ := timely_origin_before p rho index v r (some b) hm
  refine ⟨j, hj, ht, ?_⟩
  have hnone := savedTimely_none_before_early p E rho hs j v r ht
  have hsaved := saveTimely_result p
    (timelyInput p (Run.stateBefore (sapc p) rho j v) (earlyTime p r)) r
    (by simpa only [savedTimely, timelyInput_timely] using! hnone)
  rw [stateBefore_succ_event ht]
  simp only [World.step, sapc, Function.update_self, savedTimely, clock_timely_at_early]
  exact hsaved.trans (congrArg some hfind.symm)

/-- An honest emitted ack supplies its actual early save. Keeping the
saved value avoids assuming uniqueness of uncapped timely candidates. -/
theorem emitted_ack_first_save {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (v : V) (r s : Slot) (seat : Fin p.n) (data : HeadData) (b : Block)
    (hem : Run.emits (sapc p) E rho v (fromHead ⟨.seat r seat, data⟩) (voteTime p r))
    (hack : data.ack = some (s, b)) :
    ∃ j, rho.events[j]? = some (.tick v (earlyTime p s)) ∧
      savedTimely (Run.stateBefore (sapc p) rho (j + 1) v) s = some (some b) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨index, _, he⟩ := hem
  have hact := (emittedAt_seat_action (sapc p) E rho index v (voteTime p r)
    r seat (.head data) he).2
  change some (Msg.head _) = some (Msg.head data) at hact
  have hd := Msg.head.inj (Option.some.inj hact)
  have ha : ackFor (clock p (Run.stateBefore (sapc p) rho index v) (voteTime p r)) r
      data.target = some (s, b) := by
    rw [← hd]
    exact (congrArg HeadData.ack hd).trans hack
  have hsave := (ackFor_saved _ r s data.target b ha).2.1
  simp only [savedTimely, clock_timely_at_vote] at hsave
  obtain ⟨j, _, ht, hn⟩ := savedTimely_first_save p E rho hs index v s b hsave
  exact ⟨j, ht, hn⟩

/-- The honest timely save behind a PC is strictly before the
current input, even when the PC is first assembled by this delivery.
The strict bound lets the delivery step use the earlier joint invariant. -/
theorem validPC_prior_timely {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (index : Nat) (reader : V) (c : PC p.n)
    (hc : pcValid p (Run.stateBefore (sapc p) rho index reader) c = true) :
    ∃ v ∈ rho.honest, ∃ j, j + 1 < index ∧
      rho.events[j]? = some (.tick v (earlyTime p c.slot)) ∧
      savedTimely (Run.stateBefore (sapc p) rho (j + 1) v) c.slot = some (some c.target) := by
  obtain ⟨seat, data, hv, hm, hack, _⟩ := pc_honest_witness p rho _ c hc ha
  have hem := archive_authenticated_before p E rho hx.toUnforgeableSignatures index reader
    (c.slot + 1) seat data hm hv
  obtain ⟨j, hj, hsave⟩ := emitted_ack_first_save p E rho hx.toScheduleWellFormed
    (rho.seatOf (c.slot + 1) seat) (c.slot + 1) c.slot seat data c.target hem hack
  obtain ⟨d, hd, t, hac⟩ := stored_head_accepted p rho index reader _ hm
  obtain ⟨parent, hdelivery, _⟩ := hac.1
  have hread : (⟨.seat (c.slot + 1) seat, data⟩ : HeadWire p.n) ∈
      (Run.readAt (sapc p) rho t reader).receivedHeads := by
    have h := accepted_head_before_cut p E rho hx.toScheduleWellFormed
      d reader ⟨.seat (c.slot + 1) seat, data⟩ t (t + 1) hac
        (Int.lt_add_one_iff.mpr (le_refl t))
    simpa only [Run.stateBeforeTime, Run.readAt, Int.lt_add_one_iff] using h
  have htime := archived_honest_head_time_le_read p E rho hx.toUnforgeableSignatures
    reader t (c.slot + 1) seat data hread hv
  have hearly : earlyTime p c.slot < voteTime p (c.slot + 1) := by
    change 4 * p.Δ * (c.slot : Time) + 2 * p.Δ <
      4 * p.Δ * ((c.slot + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hjd := eventIndex_lt_of_time_lt hx.toScheduleWellFormed hj hdelivery
    (hearly.trans_le htime)
  exact ⟨_, hv, j, by omega, hj, hsave⟩

theorem process_obligations (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).base.obligations = st.base.obligations := by
  apply process_base_invariant p (fun acc => acc.obligations = st.base.obligations)
  · intro acc obj ha
    unfold GridCO.admitVote
    split <;> (try dsimp only) <;> (try split_ifs) <;> exact ha
  · intro acc obj b ha
    unfold GridCO.admitProposal
    dsimp only
    split_ifs <;> exact ha
  · rfl

/-- All three delivery kinds preserve the whole joint invariant when
q exceeds the faulty count. Storage does not itself exercise authority.
Under the cap, the earlier timely save also puts the PC on the path.
This includes carried evidence, late assembly, and sleeping readers. -/
theorem cleanPathFacts_delivery {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (index : Nat) (reader : V) (obj : Wire p.n) (t : Time)
    (he : rho.events[index]? = some (.deliver reader obj t))
    {path : Block → Prop} (h : CleanPathFacts p E rho index path) :
    CleanPathFacts p E rho (index + 1) path := by
  have noTick (j : Nat) (v : V) (time : Time) (hj : j < index + 1)
      (ht : rho.events[j]? = some (.tick v time)) : j < index := by
    have hn : j ≠ index := by
      intro heq
      subst j
      rw [he] at ht
      cases ht
    omega
  have saved (v : V) : (Run.stateBefore (sapc p) rho (index + 1) v).timely =
      (Run.stateBefore (sapc p) rho index v).timely := by
    rw [stateBefore_succ_event he]
    by_cases hv : v = reader
    · subst v; simp only [World.step, sapc, Function.update_self, process_timely]
    · simp only [World.step, Function.update_of_ne hv]
  refine ⟨h.chain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi v hv
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · rw [stateBefore_succ_event he]
      by_cases heq : v = reader
      · subst v
        simpa only [World.step, sapc, Function.update_self] using
          process_clean p _ obj (h.states index (le_refl _) reader hv)
      · simpa only [World.step, Function.update_of_ne heq] using
          h.states index (le_refl _) v hv
    · exact h.states i (by omega) v hv
  · intro b hb
    rcases h.accessible b hb with hg | ⟨v, hv, i, hi, hk⟩
    · exact Or.inl hg
    · exact Or.inr ⟨v, hv, i, by omega, hk⟩
  · intro v hv b g d hm
    have hold : (b, g, d) ∈ (Run.stateBefore (sapc p) rho index v).base.obligations := by
      rw [stateBefore_succ_event he] at hm
      by_cases heq : v = reader
      · subst v
        simpa only [World.step, sapc, Function.update_self, process_obligations] using hm
      · simpa only [World.step, Function.update_of_ne heq] using hm
    obtain ⟨j, hj, rest⟩ := h.finiteSources v hv b g d hold
    exact ⟨j, by omega, rest⟩
  · intro j hj v hv r b ht hb
    exact h.genuine j (noTick j v _ hj ht) v hv r b ht hb
  · intro j hj v hv r b ht hb k hk w hw s hrs hhead
    exact h.transferred j (noTick j v _ hj ht) v hv r b ht hb
      k (noTick k w _ hk hhead) w hw s hrs hhead
  · intro i hi v _ c hc
    obtain ⟨w, hw, j, hj, ht, hn⟩ := validPC_prior_timely p E rho hx ha i v c hc
    refine ⟨⟨w, hw, j, by omega, ht, hn⟩, fun hcap => ?_⟩
    exact (h.timely (j + 1) (by omega) w hw c.slot c.target hn).2 hcap
  · intro i hi v hv r b hn
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · have hold : savedTimely (Run.stateBefore (sapc p) rho index v) r = some (some b) := by
        simpa only [savedTimely, saved v] using hn
      obtain ⟨⟨w, hw, j, hj, ht, hs⟩, hp⟩ := h.timely index (le_refl _) v hv r b hold
      exact ⟨⟨w, hw, j, by omega, ht, hs⟩, hp⟩
    · exact h.timely i (by omega) v hv r b hn
  · intro cap i _ v _
    exact capBroken_false_before p E rho hx cap v i
  · intro i _ v _
    exact archive_authenticated_before p E rho hx.toUnforgeableSignatures i v
  · intro i hi v hv r c ht hm hc
    exact h.gateAuthorities i (noTick i v _ hi ht) v hv r c ht hm hc
  · intro i hi v hv r c ht hm hc
    exact h.headAuthorities i (noTick i v _ hi ht) v hv r c ht hm hc
  · intro i hi v hv r c ht hm hc
    exact h.proposalAuthorities i (noTick i v _ hi ht) v hv r c ht hm hc

theorem sleepy_quorum_above_faults {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (t₀ : Time)
    (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀) :
    (faulty rho).card < pcQuorum p := by
  have hm := hs.participation 0 (by rw [hs.start_zero]) hs.execution.horizon_nonneg
  have htotal : rho.honest.card + (faulty rho).card = p.n := by
    have hc : Fintype.card V = p.n := by
      simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
    dsimp [faulty]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have := Finset.card_le_univ rho.honest
    omega
  have hsub : (awakeAt E rho.honest 0).card ≤ rho.honest.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact quorum_above_faults p _ _ hm (by omega)

/-- Complete preservation for HEAD, proposal, and PC deliveries under
the unchanged Sleepy premises. There is no fault cap in this step. -/
theorem cleanPathFacts_delivery_of_sleepy {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (t₀ : Time)
    (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (index : Nat) (reader : V) (obj : Wire p.n) (t : Time)
    (he : rho.events[index]? = some (.deliver reader obj t))
    {path : Block → Prop} (h : CleanPathFacts p E rho index path) :
    CleanPathFacts p E rho (index + 1) path :=
  cleanPathFacts_delivery p E rho hs.execution (sleepy_quorum_above_faults p E rho t₀ hs)
    index reader obj t he h

end AvailableChain.SAPC
end

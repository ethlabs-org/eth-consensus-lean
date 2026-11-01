module
public import AvailableChainSAPC.Proofs.ProposalViews

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A base proposal retains the payload of its original direct receipt.
PC completion cannot add or replace proposal metadata. -/
theorem process_base_proposal_origin (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (key : GridCO.Wire n) (hm : key ∈ (process p st o).base.proposals) :
    key ∈ st.base.proposals ∨ ∃ b raw support c,
      o.payload = .proposal b raw support c ∧ key = baseProposal o b raw support := by
  unfold process at hm
  split at hm
  · simpa only [admitHead, collectPCs_base, receiveHead_base_proposals] using Or.inl hm
  · rename_i s b raw support c ha hp
    unfold admitProposal at hm
    split at hm
    · rename_i he
      simp only [collectPCs_base, receiveHeads_base_proposals,
        (proposalEnters_data p st o b raw support he).1] at hm
      rcases List.mem_append.mp hm with hold | hnew
      · exact Or.inl hold
      · exact Or.inr ⟨b, raw, support, c, hp, List.mem_singleton.mp hnew⟩
    · exact Or.inl hm
  · split at hm
    · simpa only [collectPCs_base, installPC, receiveHeads_base_proposals] using Or.inl hm
    · exact Or.inl hm
  · exact Or.inl hm

theorem base_proposal_origin_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (reader : V) (key : GridCO.Wire p.n)
    (hm : key ∈ (Run.stateBefore (sapc p) rho index reader).base.proposals) :
    ∃ j < index, ∃ t o b raw support c,
      rho.events[j]? = some (.deliver reader o t) ∧
      o.payload = .proposal b raw support c ∧ key = baseProposal o b raw support := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, sapc, initial, GridCO.initial] at hm
  | succ index ih =>
    cases he : rho.events[index]? with
    | none =>
      have old : key ∈ (Run.stateBefore (sapc p) rho index reader).base.proposals := by
        simpa [Run.stateBefore, List.take_add_one, he] using hm
      obtain ⟨j, hj, rest⟩ := ih old
      exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
    | some e =>
      rw [stateBefore_succ_event he] at hm
      have old (h : key ∈ (Run.stateBefore (sapc p) rho index reader).base.proposals) :
          ∃ j < index + 1, ∃ t o b raw support c,
            rho.events[j]? = some (.deliver reader o t) ∧
            o.payload = .proposal b raw support c ∧ key = baseProposal o b raw support := by
        obtain ⟨j, hj, rest⟩ := ih h
        exact ⟨j, Nat.lt_succ_of_lt hj, rest⟩
      cases e with
      | tick v t =>
        by_cases hv : reader = v
        · subst v
          apply old
          simpa only [World.step, Function.update_self, sapc, clock_base_proposals] using hm
        · exact old (by simpa [World.step, hv] using hm)
      | deliver v o t =>
        by_cases hv : reader = v
        · subst v
          simp only [World.step, Function.update_self, sapc] at hm
          rcases process_base_proposal_origin p _ o key hm with hold | ⟨b, raw, support, c, hp, hk⟩
          · exact old hold
          · exact ⟨index, Nat.lt_succ_self index, t, o, b, raw, support, c, he, hp, hk⟩
        · exact old (by simpa [World.step, hv] using hm)

/-- Proposer authentication fixes the complete payload, including its
original HEAD signatures and carried PC. -/
theorem honest_proposal_payload_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (msg : Msg p.n) (t : Time)
    (hem : Run.emits (sapc p) E rho (rho.proposerOf s) ⟨.proposer s, msg⟩ t) :
    let source := proposalState p rho s
    msg = .proposal b (originalHeads source (GridCO.proposerView source.base s))
      (originalHeads source (GridCO.proposerSupportView source.base s)) source.bestPC := by
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨ht, _, hp⟩ := emittedAt_proposal_action (sapc p) E rho i _ t s msg ho
  subst t
  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hp
  obtain ⟨_, _, j, hj, hjmem⟩ := honest_proposal_views p E rho hs s b hb
  have hq := (emittedAt_proposal_action (sapc p) E rho j _ _ s _ hjmem).2.2
  rw [stateBefore_tick_eq_stateBeforeTime hs hj] at hq
  exact Option.some.inj (hp.symm.trans hq)

/-- All stored current-slot base envelopes have the honest proposer's
exact raw and declared support views. The fault cap is not needed. -/
theorem stored_honest_base_proposal_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (index : Nat) (reader : V) (key : GridCO.Wire p.n)
    (hm : key ∈ GridCO.proposalsAt (Run.stateBefore (sapc p) rho index reader).base s) :
    key = ⟨.proposer s, .proposal b
      ((GridCO.proposerView (proposalState p rho s).base s).filterMap GridCO.toHead?)
      ((GridCO.proposerSupportView (proposalState p rho s).base s).filterMap GridCO.toHead?)⟩ := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨hm, hs⟩ := List.mem_filter.mp hm
  obtain ⟨j, _, t, o, target, raw, support, c, he, hp, hk⟩ :=
    base_proposal_origin_before p rho index reader key hm
  have hw := hx.wire j reader o t he
  change wellFormed p o = true at hw
  have hslot : target.slot = s := by simpa only [hk, baseProposal, beq_iff_eq] using hs
  have ha : o.auth = .proposer s := by
    cases ho : o.auth <;> simp only [wellFormed, ho, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq] at hw
        rw [hw.1.1.1.1.1, hslot]
  obtain ⟨t', _, hem⟩ := hx.unforgeable reader o t ⟨j, he⟩ (rho.proposerOf s) hb.1
    (by simp [Run.holder, ha])
  have ho : o = ⟨.proposer s, o.payload⟩ := by cases o; simp_all
  rw [ho] at hem
  have hmsg := honest_proposal_payload_unique p E rho hx.toScheduleWellFormed s b hb _ t' hem
  rw [hp] at hmsg
  have eq := Msg.proposal.inj hmsg
  rw [hk, baseProposal, ha, eq.1, eq.2.1, eq.2.2.1]
  rw [originalHeads_base_heads _ (proposalState_baseArchived p rho s)
      (GridCO.proposerView (proposalState p rho s).base s)
      (fun _ h => (List.mem_filter.mp h).1),
    originalHeads_base_heads _ (proposalState_baseArchived p rho s)
      (GridCO.proposerSupportView (proposalState p rho s).base s)
      (fun _ h => (List.mem_filter.mp (List.mem_filter.mp h).1).1)]

theorem headState_honest_base_proposal_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (reader : V) (key : GridCO.Wire p.n)
    (hm : key ∈ GridCO.proposalsAt (headState p rho s reader).base s) :
    key = ⟨.proposer s, .proposal b
      ((GridCO.proposerView (proposalState p rho s).base s).filterMap GridCO.toHead?)
      ((GridCO.proposerSupportView (proposalState p rho s).base s).filterMap GridCO.toHead?)⟩ := by
  set_option backward.isDefEq.respectTransparency false in
  unfold GridCO.proposalsAt headState at hm
  rw [clock_base_proposals, time_input_eq_event_prefix p E rho hx.toScheduleWellFormed] at hm
  exact stored_honest_base_proposal_unique p E rho hx s b hb _ reader key hm

end AvailableChain.SAPC
end

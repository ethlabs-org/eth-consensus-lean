module
public import AvailableChainSAPC.Proofs.ProposalOrigins
public import AvailableChainSAPC.Proofs.FreezeOrigins
public import AvailableChainSAPC.Proofs.CertificateRelay

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem process_proposal_origin (p : Params) {n : Nat} (st : State n)
    (o key : Wire n) (hm : key ∈ (process p st o).proposals) :
    key ∈ st.proposals ∨ key = o := by
  unfold process at hm
  split at hm
  · exact Or.inl (by simpa only [admitHead, collectPCs_proposals,
      receiveHead_proposals] using hm)
  · unfold admitProposal at hm
    split at hm
    · simpa only [collectPCs_proposals, receiveHeads_proposals,
        List.mem_append, List.mem_singleton] using hm
    · exact Or.inl hm
  · split at hm
    · exact Or.inl (by simpa only [collectPCs_proposals, installPC,
        receiveHeads_proposals] using hm)
    · exact Or.inl hm
  · exact Or.inl hm

private theorem fold_proposal_origin {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (w : World V (sapc p))
    (v : V) (o : Wire p.n) (hm : o ∈ ((events.foldl World.step w) v).proposals) :
    o ∈ (w v).proposals ∨ ∃ t, .deliver v o t ∈ events := by
  set_option backward.isDefEq.respectTransparency false in
  induction events generalizing w with
  | nil => exact Or.inl hm
  | cons e events ih =>
    rcases ih _ hm with hold | ⟨t, ht⟩
    · cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          exact Or.inl (by simpa only [World.step, Function.update_self, sapc,
            clock_proposals] using hold)
        · exact Or.inl (by simpa [World.step, hv] using hold)
      | deliver u key t =>
        by_cases hv : v = u
        · subst u
          rcases process_proposal_origin p (w v) key o
            (by simpa only [World.step, Function.update_self, sapc] using hold) with old | rfl
          · exact Or.inl old
          · exact Or.inr ⟨t, by simp⟩
        · exact Or.inl (by simpa [World.step, hv] using hold)
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht⟩

/-- Authentication fixes the carried PC as well as the proposal views.
The original envelope is never reconstructed from its base projection. -/
theorem headState_honest_proposal_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (reader : V) (o : Wire p.n) (target : Block)
    (raw support : List (HeadWire p.n)) (c : Option (PC p.n))
    (hm : o ∈ (headState p rho s reader).proposals)
    (hp : o.payload = .proposal target raw support c) (ht : target.slot = s) :
    target = b ∧ c = (proposalState p rho s).bestPC := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [headState, clock_proposals] at hm
  rcases fold_proposal_origin p _ World.init reader o hm with old | ⟨t, he⟩
  · simp [World.init, sapc, initial] at old
  obtain ⟨he, _⟩ := List.mem_filter.mp he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
  have hw := hx.wire i reader o t hi
  change wellFormed p o = true at hw
  have ha : o.auth = .proposer s := by
    cases ho : o.auth <;> simp only [wellFormed, ho, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq] at hw
        rw [hw.1.1.1.1.1, ht]
  obtain ⟨t', _, hem⟩ := hx.unforgeable reader o t ⟨i, hi⟩ (rho.proposerOf s) hb.1
    (by simp [Run.holder, ha])
  have ho : o = ⟨.proposer s, o.payload⟩ := by cases o; simp_all
  rw [ho] at hem
  have eq := honest_proposal_payload_unique p E rho hx.toScheduleWellFormed s b hb _ t' hem
  rw [hp] at eq
  exact ⟨(Msg.proposal.inj eq).1, (Msg.proposal.inj eq).2.2.2⟩

/-- Strict input evidence also relays. This includes all PC paths and
original signatures; it does not require an evidence-gossip tick. -/
theorem strict_pc_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source deadline : Time)
    (ht : source ≤ deadline) (hrelay : RelayBy p rho source deadline)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (c : PC p.n)
    (hc : pcValid p (Run.stateBeforeTime (sapc p) rho source v) c = true) :
    pcValid p (Run.stateBeforeTime (sapc p) rho deadline w) c = true := by
  have he : Run.stateBeforeTime (sapc p) rho source =
      Run.readAt (sapc p) rho (source - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [he] at hc
  exact read_pc_relay p E rho hs (source - 1) deadline (by linarith)
    (fun v hv i o t ht ha w hw hn => hrelay v hv i o t (by linarith) ha w hw hn)
    v w hv hw c hc

/-- A frozen PC at HEAD was live at the exact preceding freeze input. -/
theorem headState_frozenPC_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) (c : PC p.n)
    (hc : frozenPCAt (headState p rho (r + 1) reader) r = some c) :
    (Run.stateBeforeTime (sapc p) rho (freezeTime p r) reader).bestPC = some c := by
  have hrow : (r, some c) ∈ (headState p rho (r + 1) reader).frozenPC := by
    unfold frozenPCAt at hc
    cases he : (headState p rho (r + 1) reader).frozenPC.find? (fun row => row.1 == r) with
    | none => simp [he] at hc
    | some row =>
      have hmem := List.mem_of_find?_eq_some he
      have hlabel : row.1 = r := by simpa using List.find?_some he
      simp only [he, Option.map_some, Option.getD_some] at hc
      simpa only [← hlabel, ← hc] using hmem
  have hclock := clock_frozenPC_origin p
    (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) reader)
    (voteTime p (r + 1)) r (some c) hrow
  have hne : voteTime p (r + 1) ≠ freezeTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≠
      4 * p.Δ * (r : Time) + 3 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hold := hclock.resolve_right (fun h => hne h.1)
  rw [time_input_eq_event_prefix p E rho hs] at hold
  obtain ⟨j, _, tick, eq⟩ := frozenPC_origin_before p rho _ reader r (some c) hold
  rw [stateBefore_tick_eq_stateBeforeTime hs tick] at eq
  exact eq.symm

/-- Relay and archive completeness bound each frozen PC by the honest
proposer's live rank, without a fault cap or a clean-path assumption. -/
theorem frozenPC_rank_at_proposer {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (hrelay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)))
    (reader : V) (hr : reader ∈ rho.honest)
    (hp : rho.proposerOf (r + 1) ∈ rho.honest) (c : PC p.n)
    (hc : frozenPCAt (headState p rho (r + 1) reader) r = some c) :
    ∃ d, (proposalState p rho (r + 1)).bestPC = some d ∧ c.slot ≤ d.slot := by
  set_option backward.isDefEq.respectTransparency false in
  have frozen := headState_frozenPC_origin p E rho hs r reader c hc
  have valid := installedPC_valid_beforeTime p rho reader (freezeTime p r) c frozen
  have ht : freezeTime p r ≤ proposalTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have relayed := strict_pc_relay p E rho hs _ _ ht hrelay reader _ hr hp c valid
  simpa only [proposalState, clock_bestPC] using!
    PCComplete_at_fold p _ (rho.proposerOf (r + 1)) c relayed

private theorem preferPC_idempotent {n : Nat} (old : Option (PC n)) (c : PC n) :
    preferPC (preferPC old c) c = preferPC old c := by
  cases old with
  | none => simp [preferPC]
  | some d => by_cases h : d.slot < c.slot <;> simp [preferPC, h]

/-- If the current-slot envelopes all carry one PC option, selection
compares just that option with the freeze. Equal rank retains the freeze. -/
theorem selectedPC_of_unique_carried (p : Params) {n : Nat} (st : State n)
    (r : Slot) (carried : Option (PC n))
    (unique : ∀ o ∈ st.proposals, ∀ b raw support c,
      o.payload = .proposal b raw support c → b.slot = r → c = carried)
    (present : ∀ c, carried = some c → pcValid p st c = true ∧
      ∃ o ∈ st.proposals, ∃ b raw support,
        o.payload = .proposal b raw support (some c) ∧ b.slot = r) :
    selectedPC p st r = carried.elim (frozenPCAt st (r - 1))
      (preferPC (frozenPCAt st (r - 1))) := by
  let step := fun (best : Option (PC n)) (o : Wire n) =>
    match o.payload with
    | .proposal b _ _ (some c) =>
        if b.slot == r && pcValid p st c then preferPC best c else best
    | _ => best
  change st.proposals.foldl step _ = _
  cases carried with
  | none =>
    have fixed (o : Wire n) (ho : o ∈ st.proposals) (best : Option (PC n)) :
        step best o = best := by
      dsimp only [step]
      split
      · rename_i b raw support c hp
        split
        · rename_i h
          have eq := unique o ho b raw support (some c) hp
            (by simpa using (Bool.and_eq_true_iff.mp h).1)
          contradiction
        · rfl
      · rfl
    have unchanged (xs : List (Wire n)) (hxs : xs ⊆ st.proposals)
        (best : Option (PC n)) : xs.foldl step best = best := by
      induction xs generalizing best with
      | nil => rfl
      | cons o xs ih =>
        rw [List.foldl_cons, fixed o (hxs (by simp))]
        exact ih (fun x hx => hxs (List.mem_cons_of_mem _ hx)) best
    exact unchanged st.proposals (List.Subset.refl _) _
  | some c =>
    obtain ⟨valid, o, ho, b, raw, support, hp, hslot⟩ := present c rfl
    have forms (key : Wire n) (hk : key ∈ st.proposals) (best : Option (PC n)) :
        step best key = best ∨ step best key = preferPC best c := by
      dsimp only [step]
      split
      · rename_i target raw support d hpay
        split
        · rename_i h
          have eq := unique key hk target raw support (some d) hpay
            (by simpa using (Bool.and_eq_true_iff.mp h).1)
          cases Option.some.inj eq
          exact Or.inr rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    have hit (best : Option (PC n)) : step best o = preferPC best c := by
      simp [step, hp, hslot, valid]
    have foldForms (xs : List (Wire n)) (hxs : xs ⊆ st.proposals) (best : Option (PC n)) :
        xs.foldl step best = best ∨ xs.foldl step best = preferPC best c := by
      induction xs generalizing best with
      | nil => exact Or.inl rfl
      | cons key xs ih =>
        have rest := ih (fun x hx => hxs (List.mem_cons_of_mem _ hx)) (step best key)
        rcases forms key (hxs (by simp)) best with he | he
        · simpa only [List.foldl_cons, he] using rest
        · rcases rest with rest | rest
          · exact Or.inr (rest.trans he)
          · exact Or.inr (rest.trans (by rw [he, preferPC_idempotent]))
    obtain ⟨left, right, eq, _⟩ := List.eq_append_cons_of_mem ho
    rw [eq, List.foldl_append, List.foldl_cons, hit]
    have rightSub : right ⊆ st.proposals := by
      rw [eq]
      intro key hk
      simp only [List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr hk)
    have leftSub : left ⊆ st.proposals := by
      rw [eq]
      exact List.subset_append_left _ _
    rcases foldForms right rightSub (preferPC (left.foldl step (frozenPCAt st (r - 1))) c)
      with he | he
    all_goals rw [he]
    all_goals try rw [preferPC_idempotent]
    all_goals rcases foldForms left leftSub (frozenPCAt st (r - 1)) with hl | hl
    all_goals simp only [hl, preferPC_idempotent, Option.elim]

/-- The carried live PC is valid before the HEAD choice by accepted
relay, including its paths. Later live PCs are irrelevant to selection. -/
theorem honest_proposal_PC_at_head {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (hp : rho.proposerOf s ∈ rho.honest) (reader : V) (hr : reader ∈ rho.honest)
    (c : PC p.n) (hc : (proposalState p rho s).bestPC = some c) :
    pcValid p (headState p rho s reader) c = true := by
  set_option backward.isDefEq.respectTransparency false in
  have he : max (proposalTime p s) E.t_GST + E.Δ = voteTime p s := by
    rw [max_eq_left hsync, hΔ]
    rfl
  have valid := installedPC_valid_beforeTime p rho _ _ c
    (by simpa only [proposalState, clock_bestPC] using! hc)
  have relay := strict_pc_relay p E rho hs (proposalTime p s) (voteTime p s)
    (by change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * (s : Time) + p.Δ
        linarith [p.deltaPos])
    (he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hh))
    _ reader hp hr c valid
  exact pcValid_mono p _ _ (by simp only [headState, clock_blocks]; exact List.Subset.refl _)
    (by simp only [headState, clock_archive]; exact List.Subset.refl _) c relay

/-- Exact frozen/carried comparison for an honest proposal. This is an
encoding-level statement and does not identify equal-rank targets. -/
theorem honest_proposal_selectedPC {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    selectedPC p (headState p rho s reader) s =
      (proposalState p rho s).bestPC.elim
        (frozenPCAt (headState p rho s reader) (s - 1))
        (preferPC (frozenPCAt (headState p rho s reader) (s - 1))) := by
  apply selectedPC_of_unique_carried
  · intro o ho target raw support c hp ht
    exact (headState_honest_proposal_unique p E rho hx s b hb reader o target
      raw support c ho hp ht).2
  · intro c hc
    refine ⟨honest_proposal_PC_at_head p E rho hx.toScheduleWellFormed hΔ hrelay s
      hsync hh hb.1 reader hr c hc, ?_⟩
    have stored := (honest_proposal_stored_at_head p E rho hx hΔ hnet s b hb
      hsync hh reader hr).1
    rw [hc] at stored
    exact ⟨_, stored, b, _, _, rfl,
      (honest_proposal_slot p E rho hx.toScheduleWellFormed s b hb).2.2⟩

/-- The selected PC and the honest proposer's PC have the same rank.
The result also states that either both options are empty or neither is. -/
theorem honest_proposal_selectedPC_rank {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    (selectedPC p (headState p rho (r + 1) reader) (r + 1)).map PC.slot =
      (proposalState p rho (r + 1)).bestPC.map PC.slot := by
  have hfp : freezeTime p r ≤ proposalTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hph : proposalTime p (r + 1) ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    linarith [p.deltaPos]
  have he : max (freezeTime p r) E.t_GST + E.Δ = proposalTime p (r + 1) := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    ring
  have relay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)) :=
    he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hph.trans hh)
  have bound := frozenPC_rank_at_proposer p E rho hx.toScheduleWellFormed r relay
    reader hr hb.1
  rw [honest_proposal_selectedPC p E rho hx hΔ hnet hrelay (r + 1) b hb
    (hsync.trans hfp) hh reader hr, Nat.add_sub_cancel]
  cases source : (proposalState p rho (r + 1)).bestPC with
  | none =>
    cases frozen : frozenPCAt (headState p rho (r + 1) reader) r with
    | none => rfl
    | some c => obtain ⟨d, hd, _⟩ := bound c frozen; simp [source] at hd
  | some c =>
    cases frozen : frozenPCAt (headState p rho (r + 1) reader) r with
    | none => rfl
    | some d =>
      obtain ⟨e, he, hle⟩ := bound d frozen
      have eq : e = c := Option.some.inj (he.symm.trans source)
      subst e
      simp only [Option.elim, preferPC]
      split
      · rfl
      · rename_i hn
        simp only [Option.map_some]
        exact congrArg some (Nat.le_antisymm hle (Nat.le_of_not_gt hn))

end AvailableChain.SAPC
end

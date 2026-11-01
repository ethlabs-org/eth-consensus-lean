module
public import AvailableChainGridCO.Proofs.MergedViews
public import AvailableChainGridCO.Proofs.ProposalAdoption

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem vote_proposals (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (admitVote p st o).proposals = st.proposals := by
  unfold admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

private theorem fold_proposalData (p : Params) {n : Nat} (st : State n)
    (raw : List (HeadWire n)) :
    let post := raw.foldl (fun acc row => admitVote p acc (fromHead row)) st
    post.blocks = st.blocks ∧ post.proposals = st.proposals := by
  induction raw generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons row raw ih =>
      simpa only [List.foldl_cons, admitVote_blocks, vote_proposals] using
        ih (admitVote p st (fromHead row))

/-- Proposal storage grows under processing, including the raw HEAD loop. -/
theorem process_proposals_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.proposals ⊆ (process p st o).proposals := by
  unfold process
  split
  · rw [vote_proposals]
  · unfold admitProposal
    dsimp only
    split <;> split
    all_goals first
      | exact List.Subset.refl _
      | rw [(fold_proposalData p _ _).2]
        exact List.subset_append_left _ _
  · exact List.Subset.refl _

/-- Stored proposal envelopes persist at later event prefixes. -/
theorem stateBefore_proposals_subset {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) {i j : Nat} (hij : i ≤ j) (reader : V) :
    (Run.stateBefore (gridCO p) rho i reader).proposals ⊆
      (Run.stateBefore (gridCO p) rho j reader).proposals := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with he | hlt
      · subst i; exact List.Subset.refl _
      · apply List.Subset.trans (ih (by omega))
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick v t =>
                by_cases hv : reader = v
                · subst v; simp [World.step, gridCO, clock_proposals]
                · simp [World.step, hv]
            | deliver v o t =>
                by_cases hv : reader = v
                · subst v
                  simpa [World.step] using! process_proposals_subset p
                    (Run.stateBefore (gridCO p) rho j reader) o
                · simp [World.step, hv]

/-- Between proposal and HEAD, the receiver's clock names the proposal's
slot. The required public tick also runs at a sleeping reader. -/
theorem proposal_delivery_current_label {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    {index : Nat} {reader : V} {o : Wire p.n} {s : Slot} {t : Time}
    (hi : rho.events[index]? = some (.deliver reader o t))
    (hlo : proposalTime p s ≤ t) (hhi : t < voteTime p s) :
    ((Run.stateBefore (gridCO p) rho index reader).now / (4 * p.Δ)).toNat = s := by
  have hpub : PublicTime E (proposalTime p s) := by
    refine ⟨4 * s, ?_⟩
    simp only [proposalTime, hΔ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hn : 0 ≤ proposalTime p s := by
    unfold proposalTime
    exact mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg s)
  have hl := delivery_now_ge_public p E rho hs hi hpub hn hlo
  have hh := (stateBefore_now_le_event p E rho hs hi reader).trans_lt hhi
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hdiv : (Run.stateBefore (gridCO p) rho index reader).now / (4 * p.Δ) = (s : Int) := by
    apply (Int.ediv_eq_iff_of_pos hd).mpr
    constructor
    · dsimp [proposalTime] at hl; nlinarith
    · dsimp [voteTime, proposalTime] at hh; nlinarith [p.deltaPos]
  rw [hdiv]
  simp

/-- An in-window proposal delivery stores both block and envelope. The
execution supplies every admission guard except the time window. -/
theorem delivered_proposal_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (index : Nat) (reader : V) (s : Slot) (B : Block) (raw support : List (HeadWire p.n))
    (t : Time) (hlo : proposalTime p s ≤ t) (hhi : t < voteTime p s)
    (hi : rho.events[index]? = some (.deliver reader ⟨.proposer s, .proposal B raw support⟩ t)) :
    B ∈ (Run.stateBefore (gridCO p) rho (index + 1) reader).blocks ∧
      (⟨.proposer s, .proposal B raw support⟩ : Wire p.n) ∈
        (Run.stateBefore (gridCO p) rho (index + 1) reader).proposals := by
  have hw := hx.wire index reader _ t hi
  have hd := hx.deps index reader _ t hi
  have hf := hx.fresh index reader _ t hi
  change wellFormed (⟨.proposer s, .proposal B raw support⟩ : Wire p.n) = true at hw
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  have hslot : B.slot = s := hw.1.1.1.1.symm
  have hparent : B.parent.slot < B.slot := by simpa [hslot] using hw.1.1.2
  change blockKnown (Run.stateBefore (gridCO p) rho index reader) B.parent = true at hd
  change blockKnown (Run.stateBefore (gridCO p) rho index reader) B = false at hf
  have hcurrent := proposal_delivery_current_label p E rho hx.toScheduleWellFormed hΔ hi hlo hhi
  rw [stateBefore_succ_event hi]
  simp only [World.step, Function.update_self]
  change B ∈ (process p _ _).blocks ∧ _ ∈ (process p _ _).proposals
  have hf' : B ∉ (Run.stateBefore (gridCO p) rho index reader).blocks := by
    simpa [blockKnown] using hf
  have hd' : B.parent ∈ (Run.stateBefore (gridCO p) rho index reader).blocks := by
    simpa [blockKnown] using hd
  have hparent' : B.parent.slot < s := by simpa [hslot] using hparent
  simp only [process, admitProposal, hslot, hcurrent, gt_iff_lt, lt_self_iff_false,
    decide_false, blockKnown, hd', decide_true, Bool.not_true, hf', hparent',
    beq_self_eq_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [(fold_proposalData p _ _).1, (fold_proposalData p _ _).2]
  constructor <;> exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- Broadcast delivers an honest proposal before HEAD, including its own
copy. Carried HEAD handling cannot substitute for the proposal envelope. -/
theorem synchronous_proposal_delivered {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (s : Slot) (hsync : EarlyDelivery p E rho s)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (B : Block) (raw support : List (HeadWire p.n))
    (hp : o.payload = .proposal B raw support)
    (hem : Run.emits (gridCO p) E rho source o (proposalTime p s))
    (hx : ∀ u, u ≤ voteTime p s →
        (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u reader) o = false) :
    ∃ (index : Nat) (t : Time), proposalTime p s ≤ t ∧ t < voteTime p s ∧
      rho.events[index]? = some (Event.deliver reader o t) := by
  have hdeadline : proposalTime p s + E.Δ = voteTime p s := by rw [hΔ]; rfl
  have hv : voteTime p s ≤ earlyTime p s := by
    dsimp [voteTime, earlyTime]; linarith [p.deltaPos]
  have hh : ∃ t, proposalTime p s ≤ t ∧ t < voteTime p s ∧
      ∃ index, Run.handlesAt (gridCO p) rho index reader o t := by
    rcases hsync.delivery with ⟨hgst, hnet⟩ | ⟨cut, hcut, hnet⟩
    · have hmax : max (proposalTime p s) E.t_GST = proposalTime p s := max_eq_left hgst
      obtain ⟨t, ht, hd, index, hh⟩ := hnet.broadcast source hs o _ hem reader hr
        (by rw [hmax, hdeadline]; exact hv.trans hsync.horizon)
        (hx _ (by rw [hmax, hdeadline]))
      exact ⟨t, ht, by simpa [hmax, hdeadline] using hd, index, hh⟩
    · obtain ⟨t, ht, hd, index, hh⟩ := hnet.broadcast source hs o _ hem reader hr
        (by rw [hdeadline]; exact hv.trans hcut) (hx _ hdeadline.le)
      exact ⟨t, ht, by simpa [hdeadline] using hd, index, hh⟩
  obtain ⟨t, hlo, hhi, index, outer, hi, hh⟩ := hh
  have he := handles_proposal_direct p _ outer o B raw support hp hh
  subst outer
  exact ⟨index, t, hlo, hhi, hi⟩

/-- The actual honest proposal and both declared views are stored at every
reader's next HEAD state. This theorem assumes no common-root invariant. -/
theorem honest_proposal_stored_at_head {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (reader : V) (hr : reader ∈ rho.honest) :
    let source := proposalState p rho (r + 1)
    let o : Wire p.n := ⟨.proposer (r + 1), .proposal B
      ((proposerView source (r + 1)).filterMap toHead?)
      ((proposerSupportView source (r + 1)).filterMap toHead?)⟩
    B ∈ (nextHeadState p rho r reader).blocks ∧
      o ∈ (nextHeadState p rho r reader).proposals := by
  dsimp only
  let source := proposalState p rho (r + 1)
  let raw := (proposerView source (r + 1)).filterMap toHead?
  let support := (proposerSupportView source (r + 1)).filterMap toHead?
  let o : Wire p.n := ⟨.proposer (r + 1), .proposal B raw support⟩
  have hs := hsync.execution.toScheduleWellFormed
  obtain ⟨_, _, hem⟩ := honest_proposal_views p E rho hs (r + 1) B hB
  obtain ⟨index, t, hlo, hhi, hi⟩ := synchronous_proposal_delivered p E rho hΔ (r + 1)
    hsync (rho.proposerOf (r + 1)) reader hB.1 hr o B raw support rfl hem
    (fun u _ => proposal_not_excluded p rho reader o B raw support rfl u)
  have hstored := delivered_proposal_stored p E rho hsync.execution hΔ index reader
    (r + 1) B raw support t hlo hhi hi
  rw [← release_eq_next_vote] at hhi
  have hblock := (delivery_prefix_before_cut p E rho hs hi hhi).blocks.subset hstored.1
  have hprop : o ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) reader).proposals := by
    rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_proposals_subset p rho ?_ reader hstored.2
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (releaseTime p r - 1) hi).mpr
      (Int.le_sub_one_iff.mpr hhi))
  have hb := congrArg Prod.fst (clock_receiptData p (releaseInput p rho r reader) (releaseTime p r))
  change (nextHeadState p rho r reader).blocks = (releaseInput p rho r reader).blocks at hb
  constructor
  · rw [hb]; exact hblock
  · change o ∈ (clock p _ _).proposals
    rw [clock_proposals]
    exact hprop

/-- Honest proposer authentication fixes one payload at a slot. It also
fixes the raw and resolved metadata, not only the proposed block. -/
theorem honest_proposal_payload_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (B : Block) (hB : HonestProposalAt E (gridInterface p) rho s B)
    (msg : Msg p.n) (t : Time)
    (hem : Run.emits (gridCO p) E rho (rho.proposerOf s) ⟨.proposer s, msg⟩ t) :
    msg = .proposal B ((proposerView (proposalState p rho s) s).filterMap toHead?)
      ((proposerSupportView (proposalState p rho s) s).filterMap toHead?) := by
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨ht, _, hp⟩ := emitted_proposal_action p E rho i _ t s msg ho
  subst t
  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hp
  obtain ⟨_, _, j, hj, hjmem⟩ := honest_proposal_views p E rho hs s B hB
  have hq := (emitted_proposal_action p E rho j _ _ s _ hjmem).2.2
  rw [stateBefore_tick_eq_stateBeforeTime hs hj] at hq
  exact Option.some.inj (hp.symm.trans hq)

/-- Every stored current-slot envelope is the one emitted by the honest
proposer. Faulty envelopes cannot add current-slot children or metadata. -/
theorem stored_honest_proposal_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (s : Slot) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho s B)
    (index : Nat) (reader : V) (o : Wire p.n)
    (ho : o ∈ proposalsAt (Run.stateBefore (gridCO p) rho index reader) s) :
    o = ⟨.proposer s, .proposal B
      ((proposerView (proposalState p rho s) s).filterMap toHead?)
      ((proposerSupportView (proposalState p rho s) s).filterMap toHead?)⟩ := by
  obtain ⟨hm, hslot⟩ := List.mem_filter.mp ho
  obtain ⟨j, _, t, C, raw, support, hi, hp, _⟩ :=
    stored_proposal_admission p rho index reader o hm
  have hw := hx.wire j reader o t hi
  change wellFormed o = true at hw
  have hCs : C.slot = s := by simpa [hp] using hslot
  have ha : o.auth = .proposer s := by
    cases he : o.auth <;> simp only [wellFormed, he, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq] at hw
        rw [hw.1.1.1.1, hCs]
  obtain ⟨t', _, hem⟩ := hx.unforgeable reader o t ⟨j, hi⟩ (rho.proposerOf s) hB.1
    (by simp [Run.holder, ha])
  have he : o = ⟨.proposer s, o.payload⟩ := by cases o; simp_all
  rw [he] at hem
  have hmsg := honest_proposal_payload_unique p E rho hx.toScheduleWellFormed s B hB
    o.payload t' hem
  rw [he, hmsg]

/-- The same authentication fact at the state after the release tick. -/
theorem nextHeadState_honest_proposal_unique {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (reader : V) (o : Wire p.n)
    (ho : o ∈ proposalsAt (nextHeadState p rho r reader) (r + 1)) :
    o = ⟨.proposer (r + 1), .proposal B
      ((proposerView (proposalState p rho (r + 1)) (r + 1)).filterMap toHead?)
      ((proposerSupportView (proposalState p rho (r + 1)) (r + 1)).filterMap toHead?)⟩ := by
  set_option backward.isDefEq.respectTransparency false in
  unfold proposalsAt nextHeadState releaseInput at ho
  rw [clock_proposals, time_input_eq_event_prefix p E rho hx.toScheduleWellFormed] at ho
  exact stored_honest_proposal_unique p E rho hx (r + 1) B hB _ reader o ho

end AvailableChain.GridCO
end

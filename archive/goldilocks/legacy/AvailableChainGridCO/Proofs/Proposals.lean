module
public import AvailableChainGridCO.Proofs.RecordSlots

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An emitted proposer object comes from the proposer action at its slot's
time. This includes the clock evaluation that precedes emission. -/
theorem emitted_proposal_action {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (i : Nat) (v : V) (t : Time)
    (s : Slot) (msg : Msg p.n)
    (ho : (⟨.proposer s, msg⟩ : Wire p.n) ∈
      Run.emittedAt (gridCO p) E rho i v t) :
    t = proposalTime p s ∧ rho.proposerOf s = v ∧
      propose p (clock p (Run.stateBefore (gridCO p) rho i v) t) s = some msg := by
  unfold Run.emittedAt at ho
  split at ho
  · change (⟨.proposer s, msg⟩ : Wire p.n) ∈
      (duties p t).filterMap (fun label =>
        (act p (clock p (Run.stateBefore (gridCO p) rho i v) t) label).map
          (fun payload => ⟨.seat label ((rho.seatOf label).symm v), payload⟩)) ++
      (slotsAt p t).filterMap (fun slot => if rho.proposerOf slot = v then
        (propose p (clock p (Run.stateBefore (gridCO p) rho i v) t) slot).map
          (fun payload => ⟨.proposer slot, payload⟩) else none) ++ [] at ho
    simp only [List.append_nil, List.mem_append] at ho
    rcases ho with ha | hp
    · obtain ⟨label, _, ha⟩ := List.mem_filterMap.mp ha
      cases hact : act p (clock p (Run.stateBefore (gridCO p) rho i v) t) label <;>
        simp [hact] at ha
    · obtain ⟨slot, hslot, hp⟩ := List.mem_filterMap.mp hp
      split at hp
      · rename_i hproposer
        cases hprop : propose p (clock p (Run.stateBefore (gridCO p) rho i v) t) slot with
        | none => simp [hprop] at hp
        | some payload =>
            have heq : (⟨.proposer slot, payload⟩ : Wire p.n) = ⟨.proposer s, msg⟩ := by
              simpa [hprop] using hp
            cases heq
            exact ⟨((slotsAt_spec p s t).mp hslot).symm, hproposer, hprop⟩
      · contradiction
  · contradiction

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The source state used by the actual proposer, including its clock tick. -/
def proposalState {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (s : Slot) : State p.n :=
  clock p (Run.stateBeforeTime (gridCO p) rho (proposalTime p s) (rho.proposerOf s))
    (proposalTime p s)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Honest proposal emission fixes the complete raw view and support view
carried on the wire. No cross-reader agreement is assumed here. -/
theorem honest_proposal_views {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (B : Block)
    (h : HonestProposalAt E (gridInterface p) rho s B) :
    let st := proposalState p rho s
    let parent := forkChoice st st.blocks (proposerView st s) (proposerSupportView st s) s
    0 < s ∧ B = .node parent s (nodeRoot parent.root s 0) 0 ∧
      Run.emits (gridCO p) E rho (rho.proposerOf s)
        ⟨.proposer s, .proposal B ((proposerView st s).filterMap toHead?)
          ((proposerSupportView st s).filterMap toHead?)⟩ (proposalTime p s) := by
  obtain ⟨_, msg, hb, i, hi, ho⟩ := h
  have hp := (emitted_proposal_action p E rho i _ _ s msg ho).2.2
  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hp
  change propose p (proposalState p rho s) s = some msg at hp
  cases msg with
  | head target => simp [gridInterface, block] at hb
  | proposal target raw support =>
      have heq : target = B := by simpa [gridInterface, block] using hb
      subst target
      simp only [propose] at hp
      split at hp
      · simp at hp
      · rename_i hpos
        have hn : 0 < s := by simpa using Nat.pos_of_ne_zero (by simpa using hpos)
        have hm := Option.some.inj hp
        cases hm
        exact ⟨hn, rfl, i, hi, ho⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An honest proposal contains its own live root. Extending this fact to
every reader requires a separate common-root argument. -/
theorem honest_proposal_contains_source_root {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (s : Slot) (B : Block)
    (h : HonestProposalAt E (gridInterface p) rho s B) :
    B.slot = s ∧
      Block.Preceq (liveRoot (proposalState p rho s)) B.parent := by
  obtain ⟨_, hb, _⟩ := honest_proposal_views p E rho hs s B h
  rw [hb]
  exact ⟨rfl, forkChoice_extends_liveRoot _ _ _ _ _⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A receipt before the previous freeze causes a handler call before the
proposal when its relay interval is available. This applies to both HEADs
and their separately admitted block paths. -/
theorem handled_before_proposal_of_ready {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (s : Slot)
    (hready : ProposalRelayReady p E rho s)
    (hh : proposalTime p s ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (i : Nat) (o : Wire p.n) (t : Time)
    (ha : Run.acceptsAt (gridCO p) rho i source o t)
    (hm : processed (Run.stateBefore (gridCO p) rho (i + 1) reader) o = false)
    (hdeadline : t + E.Δ ≤ proposalTime p s)
    (hx : ∀ u, u ≤ proposalTime p s →
        (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u reader) o = false) :
    ∃ j t', Run.handlesAt (gridCO p) rho j reader o t' ∧
      t ≤ t' ∧ t' < proposalTime p s := by
  rcases hready with ⟨hstart, hrelay⟩ | ⟨cut, hcut, hrelay⟩
  · have hd : max t E.t_GST + E.Δ ≤ proposalTime p s := by
      rw [← max_add_add_right]
      exact max_le hdeadline hstart
    obtain ⟨t', ht, hd', j, hj⟩ := hrelay.relay source hs i o t ha reader hr hm (hd.trans hh)
      (hx _ hd)
    exact ⟨j, t', hj, ht, hd'.trans_le hd⟩
  · obtain ⟨t', ht, hd, j, hj⟩ := hrelay.relay source hs i o t ha reader hr hm
      (hdeadline.trans hcut) (hx _ hdeadline)
    exact ⟨j, t', hj, ht, hd.trans_le hdeadline⟩

private theorem head_conversion {n : Nat} (o : Wire n) (r : Slot)
    (h : headLabel? o = some r) :
    ∃ wire, toHead? o = some wire ∧ fromHead wire = o := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> simp_all [headLabel?, toHead?, fromHead]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A stored current-slot proposal puts every stored prefix of its block
in the voter tree, even when that prefix was absent from the freeze. -/
theorem proposal_prefix_mem_voterTree (p : Params) {n : Nat} (st : State n)
    (s : Slot) (o : Wire n) (B K : Block) (raw support : List (HeadWire n))
    (ho : o ∈ st.proposals) (hp : o.payload = .proposal B raw support)
    (hslot : B.slot = s) (hk : K ∈ st.blocks) (hprefix : Block.Preceq K B) :
    K ∈ voterTree p st s := by
  apply List.mem_filter.mpr
  refine ⟨hk, Bool.or_eq_true_iff.mpr (Or.inr ?_)⟩
  apply List.any_eq_true.mpr
  refine ⟨B, ?_, hprefix⟩
  apply List.mem_filterMap.mpr
  exact ⟨o, List.mem_filter.mpr ⟨ho, by simp [hp, hslot]⟩, by simp [hp]⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Reachable prefix closure supplies the path membership needed by the
proposal-tree merge. The relay proof must still deliver the proposal. -/
theorem proposal_path_mem_voterTree (p : Params) {n : Nat} (st : State n)
    (s : Slot) (o : Wire n) (B K : Block) (raw support : List (HeadWire n))
    (ho : o ∈ st.proposals) (hp : o.payload = .proposal B raw support)
    (hslot : B.slot = s) (hclosed : StoredPrefixClosed st)
    (hb : B ∈ st.blocks) (hk : K ≠ .genesis) (hprefix : Block.Preceq K B) :
    K ∈ voterTree p st s := by
  exact proposal_prefix_mem_voterTree p st s o B K raw support ho hp hslot
    (hclosed B hb K hk hprefix) hprefix

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The raw proposer view is merged into each reader's voter view once
that proposal is stored. This does not require equal proposal-time walks. -/
theorem proposal_raw_mem_voterView (p : Params) {n : Nat} (source reader : State n)
    (s : Slot) (o : Wire n) (B : Block) (support : List (HeadWire n))
    (ho : o ∈ reader.proposals)
    (hp : o.payload = .proposal B ((proposerView source s).filterMap toHead?) support)
    (hslot : B.slot = s) (vote : Wire n) (hv : vote ∈ proposerView source s) :
    vote ∈ voterView p reader s := by
  have hl : headLabel? vote = some (s - 1) := by
    simpa using (List.mem_filter.mp hv).2
  obtain ⟨wire, hc, he⟩ := head_conversion vote (s - 1) hl
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [hl]⟩
  apply List.mem_flatMap.mpr
  refine ⟨o, List.mem_filter.mpr ⟨ho, by simp [hp, hslot]⟩, ?_⟩
  simp only [hp]
  exact List.mem_map.mpr ⟨wire, List.mem_filterMap.mpr ⟨vote, hv, hc⟩, he⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The declared support is merged after its target path is known locally.
Raw HEAD receipt alone is not enough for this step. -/
theorem proposal_support_mem_voterSupportView (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (o : Wire n) (B : Block)
    (raw : List (HeadWire n)) (ho : o ∈ reader.proposals)
    (hp : o.payload = .proposal B raw ((proposerSupportView source s).filterMap toHead?))
    (hslot : B.slot = s) (vote : Wire n) (target : Block)
    (hv : vote ∈ proposerSupportView source s)
    (ht : headTarget? vote = some target) (hknown : target ∈ reader.blocks) :
    vote ∈ voterSupportView p reader s := by
  obtain ⟨hraw, hresolved⟩ := List.mem_filter.mp hv
  have hl : headLabel? vote = some (s - 1) := by
    simpa using (List.mem_filter.mp hraw).2
  have hbound : target.slot ≤ s - 1 := by
    by_cases hm : target ∈ source.blocks
    · simpa [resolvedHead?, ht, resolveTarget, resolutionTree, hm] using hresolved
    · simp [resolvedHead?, ht, resolveTarget, resolutionTree, hm] at hresolved
  obtain ⟨wire, hc, he⟩ := head_conversion vote (s - 1) hl
  apply List.mem_eraseDups.mpr
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [hl, ht, resolvedHead?, resolveTarget, resolutionTree, hknown, hbound]⟩
  apply List.mem_flatMap.mpr
  refine ⟨o, List.mem_filter.mpr ⟨ho, by simp [hp, hslot]⟩, ?_⟩
  simp only [hp]
  exact List.mem_map.mpr ⟨wire, List.mem_filterMap.mpr ⟨vote, hv, hc⟩, he⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An awake honest proposer at a positive slot emits a proposal. -/
theorem honest_proposal_exists {V : Type} [DecidableEq V]
    {p : Params} {E : Env V} {rho : Run V (gridCO p)}
    (hexec : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (s : Slot) (hs : 0 < s)
    (hawake : HonestAwakeProposer E rho s)
    (hh : proposalTime p s ≤ rho.horizon) :
    ∃ B, HonestProposalAt E (gridInterface p) rho s B := by
  have hpub : PublicTime E (proposalTime p s) := by
    refine ⟨4 * s, ?_⟩
    simp only [proposalTime, hΔ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have ht : 0 ≤ proposalTime p s :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt p.deltaPos)) (Int.natCast_nonneg s)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
    (hexec.tick_total _ hawake.1 _ hpub ht hh)
  let st := clock p (Run.stateBefore (gridCO p) rho i (rho.proposerOf s)) (proposalTime p s)
  let parent := forkChoice st st.blocks (proposerView st s) (proposerSupportView st s) s
  let B := Block.node parent s (nodeRoot parent.root s 0) 0
  let msg := Msg.proposal B ((proposerView st s).filterMap toHead?)
    ((proposerSupportView st s).filterMap toHead?)
  have hp : propose p st s = some msg := by simp [propose, Nat.ne_of_gt hs, msg, B, parent]
  refine ⟨B, hawake.1, msg, rfl, i, hi, ?_⟩
  change _ ∈ Run.emittedAt (gridCO p) E rho i (rho.proposerOf s) (proposalTime p s)
  simp only [Run.emittedAt, show E.awake (rho.proposerOf s) (proposalTime p s) = true from hawake.2,
    ↓reduceIte, List.mem_append]
  apply Or.inl
  apply Or.inr
  apply List.mem_filterMap.mpr
  refine ⟨s, (slotsAt_spec p s _).mpr rfl, ?_⟩
  simp only [↓reduceIte]
  change (propose p st s).map _ = _
  rw [hp]
  rfl

end AvailableChain.GridCO
end

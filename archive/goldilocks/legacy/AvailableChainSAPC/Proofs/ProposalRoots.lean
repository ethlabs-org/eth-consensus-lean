module
public import AvailableChainSAPC.Proofs.ProposerTransfer
public import AvailableChainSAPC.Proofs.RunClean
public import AvailableChainSAPC.Proofs.ProposalAuthority
public import AvailableChainGridCO.Proofs.CleanInclusion

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A proposal-state lease has an older raw gate source. This statement
does not use an S write or any relation between a lease and S. -/
theorem proposalState_target_genuine_origin {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (a : Block) (g : Nat) (d : Time)
    (hm : (a, g, d) ∈ (proposalState p rho (r + 1)).base.obligations) :
    ∃ s c, s < r ∧ SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p s) (rho.proposerOf (r + 1))).base s =
        some c ∧ Block.Preceq a c := by
  have before : proposalTime p (r + 1) < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) < 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have older (s : Slot) (ht : gateTime p s ≤ proposalTime p (r + 1)) : s < r := by
    by_contra hn
    have ge := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
    exact (not_lt_of_ge ge) (ht.trans_lt before)
  have input := base_receiptStamped_at_fold p
    (rho.events.filter (fun e => decide (e.time < proposalTime p (r + 1))))
    (rho.proposerOf (r + 1))
  rcases clock_target_genuine_origin p _ (proposalTime p (r + 1)) input a g d hm with
    hold | ⟨s, c, ht, hc, hp⟩
  · change (a, g, d) ∈ (Run.stateBeforeTime (sapc p) rho
      (proposalTime p (r + 1)) (rho.proposerOf (r + 1))).base.obligations at hold
    rw [time_input_eq_event_prefix p E rho hs] at hold
    obtain ⟨j, hj, s, c, tick, hc, hp⟩ := run_target_genuine_origin p rho _ _ a g d hold
    have time := Int.le_sub_one_iff.mp
      ((index_lt_read_length_iff hs (proposalTime p (r + 1) - 1) tick).mp hj)
    rw [stateBefore_tick_eq_stateBeforeTime hs tick] at hc
    exact ⟨s, c, older s time.le, hc, hp⟩
  · exact ⟨s, c, older s ht.ge, by simpa only [ht] using! hc, hp⟩

/-- The proved run invariant supplies raw history at the next label.
The ordinary proposal transfer then covers every older genuine result. -/
theorem clean_history_at_ordinary_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (s : Slot) (hsr : s < r) (reader : V) (hr : reader ∈ rho.honest) (a : Block)
    (ha : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p s) reader).base s = some a) :
    Block.Preceq a (GridCO.ordinaryProposalHead (proposalState p rho (r + 1)).base (r + 1)) := by
  have history := clean_genuine_history_of_head_invariants p E rho hΔ t₀ hs r hh
    (fun _ _ i _ _ tick => clean_run_invariant p E rho hΔ t₀ hs i
      (List.getElem?_eq_some_iff.mp tick).1.le)
  obtain ⟨c, hc, hp⟩ := history.1 s hsr reader hr a ha reader hr
  have sync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have horizon : voteTime p (r + 1) ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  exact genuine_prefix_at_ordinary_proposal p E rho hs.execution hΔ hs.partialSynchrony
    hs.acceptedRelay r sync horizon b hb reader hr a c hc hp

/-- Both finite roots lie on the ordinary proposer walk: the source
root before proposal and every reader root after release. Expiry and
release need no assumption that finite targets are below S. -/
theorem clean_roots_at_ordinary_proposal {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b) :
    Block.Preceq (GridCO.liveRoot (proposalState p rho (r + 1)).base)
      (GridCO.ordinaryProposalHead (proposalState p rho (r + 1)).base (r + 1)) ∧
      ∀ reader ∈ rho.honest, Block.Preceq
        (GridCO.liveRoot (headState p rho (r + 1) reader).base)
        (GridCO.ordinaryProposalHead (proposalState p rho (r + 1)).base (r + 1)) := by
  constructor
  · apply GridCO.liveRoot_below_of_rows
    intro a g d hm
    obtain ⟨s, c, hsr, hc, hp⟩ := proposalState_target_genuine_origin p E rho
      hs.execution.toScheduleWellFormed r a g d hm
    exact GridCO.prefix_trans a c _ hp (clean_history_at_ordinary_proposal p E rho hΔ
      t₀ hs r hh b hb s hsr _ hb.1 c hc)
  · intro reader hr
    apply GridCO.liveRoot_below_of_rows
    intro a g d hm
    obtain ⟨s, c, hsr, hc, hp⟩ := nextHead_target_genuine_origin p E rho
      hs.execution.toScheduleWellFormed r reader a g d hm
    exact GridCO.prefix_trans a c _ hp (clean_history_at_ordinary_proposal p E rho hΔ
      t₀ hs r hh b hb s hsr reader hr c hc)

/-- A PC used by an active clean proposer has already transferred to
the preceding honest HEADs. Its target is on the ordinary proposer walk. -/
theorem clean_proposal_PC_at_ordinary_walk {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (active : capBroken p (proposalState p rho (r + 1)) = false)
    (cert : PC p.n) (selected : (proposalState p rho (r + 1)).bestPC = some cert) :
    Block.Preceq cert.target
      (GridCO.ordinaryProposalHead (proposalState p rho (r + 1)).base (r + 1)) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨_, _, i, tick, _⟩ := honest_proposal_views p E rho hs.execution.toScheduleWellFormed
    (r + 1) b hb
  have h := clean_run_invariant p E rho hΔ t₀ hs i
    (List.getElem?_eq_some_iff.mp tick).1.le
  have pc : (Run.stateBefore (sapc p) rho i (rho.proposerOf (r + 1))).bestPC = some cert := by
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick]
    simpa only [proposalState, clock_bestPC] using! selected
  have mode : capBroken p (Run.stateBefore (sapc p) rho i (rho.proposerOf (r + 1))) = false := by
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick]
    simpa only [proposalState, capBroken_clock] using! active
  have valid := installedPC_valid_before p rho _ i cert pc
  have source := (h.facts.certificates i (le_refl _) _ hb.1 cert valid).1
  have gate := validPC_gate_le_tick p E rho hΔ hs.execution
    (sleepy_quorum_above_faults p E rho t₀ hs) i _ _ tick cert valid
  have older : cert.slot < r := by
    by_contra hn
    have cast : (r : Time) ≤ cert.slot := by exact_mod_cast Nat.le_of_not_gt hn
    change 4 * p.Δ * (cert.slot : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) at gate
    push_cast at gate
    nlinarith [p.deltaPos]
  have before : voteTime p r < proposalTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have heads := timely_continues_before_active_input p E rho hΔ t₀ hs i _ tick h
    _ hb.1 mode r cert.slot cert.target source gate older before
  have early : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨c, raw, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r early cert.target
    heads _ hb.1
  have sync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  exact genuine_prefix_at_ordinary_proposal p E rho hs.execution hΔ hs.partialSynchrony
    hs.acceptedRelay r sync hh b hb _ hb.1 cert.target c raw hp

/-- A clean honest proposal has the ordinary SA parent in either mode.
The PC, F4, and finite roots are all on that walk, so the shared GHOST
reanchoring theorem applies without changing the executable choice. -/
theorem clean_proposal_parent_ordinary {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b) :
    b.parent = GridCO.ordinaryProposalHead (proposalState p rho (r + 1)).base (r + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  let st := proposalState p rho (r + 1)
  let raw := GridCO.proposerView st.base (r + 1)
  let support := GridCO.proposerSupportView st.base (r + 1)
  let ordinary := GridCO.ordinaryProposalHead st.base (r + 1)
  have roots := (clean_roots_at_ordinary_proposal p E rho hΔ t₀ hs r hh b hb).1
  have closed := (proposalState_paths p rho (r + 1)).1
  have stored : ordinary ∈ st.base.blocks := by
    rcases GridCO.ghostWalk_mem st.base.blocks.eraseDups
      (GridCO.goldfishScore st.base.blocks raw support)
      (GridCO.goldfishEligible st.base.blocks raw support (r + 1))
      st.base.blocks.eraseDups.length .genesis with eq | mem
    · change ordinary = .genesis at eq
      rw [eq]
      exact (proposalState_paths p rho (r + 1)).2
    · exact List.mem_eraseDups.mp mem
  have rootInjective : GridCO.RootInjectiveBelow st.base.blocks := by
    simpa only [st, proposalState, clock_blocks] using!
      time_input_rootInjectiveBelow p E rho hs.execution.toScheduleWellFormed hs.rootInjective
        (proposalTime p (r + 1)) (rho.proposerOf (r + 1))
  have reanchor (root : Block) (hp : Block.Preceq root ordinary) :
      GridCO.ghost root st.base.blocks (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support (r + 1)) = ordinary :=
    GridCO.ghost_reanchor _ _ _ .genesis root ordinary rootInjective closed rfl
      ⟨GridCO.genesis_prefix root, hp⟩ (fun a hn ha => closed ordinary stored a hn ha)
  have parent : b.parent = choice p st st.base.blocks raw support (r + 1) st.bestPC := by
    obtain ⟨_, shape, _⟩ := honest_proposal_views p E rho hs.execution.toScheduleWellFormed
      (r + 1) b hb
    rw [shape]
    rfl
  rw [parent]
  unfold choice
  split
  · exact reanchor _ roots
  · rename_i mode
    have active : capBroken p st = false := Bool.eq_false_iff.mpr mode
    have floorBelow : Block.Preceq (floor p st st.base.blocks raw support (r + 1)) ordinary := by
      by_cases hg : floor p st st.base.blocks raw support (r + 1) = .genesis
      · rw [hg]; exact GridCO.genesis_prefix ordinary
      · exact (floor_properties p st st.base.blocks raw support (r + 1) hg).2.1
    have anchorBelow : Block.Preceq
        (preliminaryAnchor (floor p st st.base.blocks raw support (r + 1)) st.bestPC) ordinary := by
      cases selected : st.bestPC with
      | none => exact floorBelow
      | some cert =>
        have headBound : voteTime p (r + 1) ≤ rho.horizon := by
          apply le_trans _ hh
          change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
            4 * p.Δ * (r : Time) + 6 * p.Δ
          push_cast
          linarith [p.deltaPos]
        have pcBelow := clean_proposal_PC_at_ordinary_walk p E rho hΔ t₀ hs r headBound
          b hb active cert selected
        simp only [preliminaryAnchor]
        split <;> assumption
    apply reanchor
    unfold mandatoryRoot
    split <;> assumption

end AvailableChain.SAPC
end

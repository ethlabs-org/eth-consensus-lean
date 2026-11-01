module
public import AvailableChainSAPC.Proofs.ProposalCertificates
public import AvailableChainSAPC.Proofs.ProposalFloors
public import AvailableChainSAPC.Proofs.RunClean

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A disabled honest proposer makes every HEAD reader disabled by
its duty. Therefore an active reader has an active proposer source. -/
theorem honest_proposal_active_source {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (hp : rho.proposerOf s ∈ rho.honest) (reader : V) (hr : reader ∈ rho.honest)
    (active : capBroken p (headState p rho s reader) = false) :
    capBroken p (proposalState p rho s) = false := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [headState, capBroken_clock] at active
  simp only [proposalState, capBroken_clock]
  cases mode : capBroken p (Run.stateBeforeTime (sapc p) rho
      (proposalTime p s) (rho.proposerOf s)) with
  | false => rfl
  | true =>
    have eq : Run.stateBeforeTime (sapc p) rho (proposalTime p s) =
        Run.readAt (sapc p) rho (proposalTime p s - 1) := by
      simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
    rw [eq] at mode
    have deadline : max (proposalTime p s) E.t_GST + E.Δ = voteTime p s := by
      rw [max_eq_left hsync, hΔ]
      rfl
    have relay : RelayBy p rho (proposalTime p s) (voteTime p s) :=
      deadline ▸ synchronous_relayBy p E rho _ hrelay (deadline.symm ▸ hh)
    have ht : proposalTime p s - 1 < voteTime p s := by
      change 4 * p.Δ * (s : Time) - 1 < 4 * p.Δ * (s : Time) + p.Δ
      linarith [p.deltaPos]
    have heads := read_head_relay p E rho hs _ _ ht
      (fun v hv i o t ht ha w hw hn => relay v hv i o t (by linarith) ha w hw hn)
      _ reader hp hr
    have broken := capBroken_mono p _ _ heads mode
    simp [active] at broken

private theorem path_slotOrdered {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (index : Nat) (b : Block)
    (hb : cleanRunPath p rho index b) : GridCO.SlotOrdered b := by
  rcases cleanRunPath_accessible p rho index b hb with rfl | ⟨v, _, i, _, known⟩
  · trivial
  · exact (paths_at_fold p _ v).2.2 b (pathKnown_mem _ b known)

private theorem pc_target_slot (p : Params) {n : Nat} (st : State n) (c : PC n)
    (hc : pcValid p st c = true) : c.target.slot = c.slot := by
  simp only [pcValid, pcWellFormed, Bool.and_eq_true, beq_iff_eq] at hc
  exact hc.1.1.1.1.1.2

/-- Active proposal and HEAD authorities have the same target under
plain Sleepy. Clean source order resolves an equal-rank frozen tie even
above the fault cap; certificate encodings need not be equal. -/
theorem clean_honest_proposal_selectedPC_target {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest)
    (active : capBroken p (headState p rho (r + 1) reader) = false) :
    (selectedPC p (headState p rho (r + 1) reader) (r + 1)).map PC.target =
      (proposalState p rho (r + 1)).bestPC.map PC.target := by
  have sync : E.t_GST ≤ freezeTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have syncP : E.t_GST ≤ proposalTime p (r + 1) := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  have ranks := honest_proposal_selectedPC_rank p E rho hs.execution hΔ
    hs.partialSynchrony hs.acceptedRelay r sync hh b hb reader hr
  cases source : (proposalState p rho (r + 1)).bestPC with
  | none =>
    cases selected : selectedPC p (headState p rho (r + 1) reader) (r + 1) with
    | none => rfl
    | some c => simp [source, selected] at ranks
  | some d =>
    cases selected : selectedPC p (headState p rho (r + 1) reader) (r + 1) with
    | none => simp [source, selected] at ranks
    | some c =>
      have rank : c.slot = d.slot := by simpa only [source, selected, Option.map_some,
        Option.some.injEq] using ranks
      have facts := (clean_run_invariant p E rho hΔ t₀ hs rho.events.length (le_refl _)).facts
      have sourceActive := honest_proposal_active_source p E rho hs.execution.toScheduleWellFormed
        hΔ hs.acceptedRelay (r + 1) syncP hh hb.1 reader hr active
      obtain ⟨_, _, i, tick, _⟩ := honest_proposal_views p E rho hs.execution.toScheduleWellFormed
        (r + 1) b hb
      have sourcePath := facts.proposalAuthorities i (List.getElem?_eq_some_iff.mp tick).1
        _ hb.1 (r + 1) d tick
        (by rwa [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick])
        (by rwa [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick])
      have pub : PublicTime E (voteTime p (r + 1)) := by
        refine ⟨4 * (r + 1) + 1, ?_⟩
        change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = _
        rw [hΔ]
        push_cast
        ring
      have nonneg : 0 ≤ voteTime p (r + 1) := by
        change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
        nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
      obtain ⟨j, head⟩ := List.mem_iff_getElem?.mp
        (hs.execution.tick_total reader hr _ pub nonneg hh)
      have targetPath := facts.headAuthorities j (List.getElem?_eq_some_iff.mp head).1
        reader hr (r + 1) c head
        (by rwa [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed head])
        (by rwa [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed head])
      have dvalid := clock_valid p _ _ (installedPC_valid_at_fold p _ _) d source
      have certificates := certificates_valid_at_fold p
        (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader
      have cvalid := selectedPC_valid p _
        (clock_frozenPC_valid p _ _ certificates.2 certificates.1) (r + 1) c selected
      have slots : c.target.slot = d.target.slot :=
        (pc_target_slot p _ c cvalid).trans (rank.trans (pc_target_slot p _ d dvalid).symm)
      have compatible := facts.chain.comparable c.target d.target targetPath sourcePath
      have eq : c.target = d.target := by
        rcases Bool.or_eq_true_iff.mp compatible with hcd | hdc
        · exact GridCO.prefix_eq_of_slot_ge _ _ (path_slotOrdered p rho _ _ sourcePath) hcd slots.ge
        · exact (GridCO.prefix_eq_of_slot_ge _ _
            (path_slotOrdered p rho _ _ targetPath) hdc slots.le).symm
      simp only [Option.map_some, eq]

/-- The common F4 floor and selected target give the same preliminary
anchor. The remaining choice proof must still account for finite roots. -/
theorem clean_honest_proposal_anchor_eq {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest)
    (active : capBroken p (headState p rho (r + 1) reader) = false) :
    let source := proposalState p rho (r + 1)
    let target := headState p rho (r + 1) reader
    let cert := selectedPC p target (r + 1)
    preliminaryAnchor (floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
        (GridCO.proposerSupportView source.base (r + 1)) (r + 1)) source.bestPC =
      preliminaryAnchor (floor p target (activeVoterTree p target (r + 1) cert)
        (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert := by
  dsimp only
  have sync : E.t_GST ≤ freezeTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  rw [honest_proposal_floor_eq p E rho hs.execution hΔ hs.rootInjective hs.partialSynchrony
    hs.acceptedRelay r sync hh b hb reader hr active
    (selectedPC p (headState p rho (r + 1) reader) (r + 1))]
  have targets := clean_honest_proposal_selectedPC_target p E rho hΔ t₀ hs r hh b hb
    reader hr active
  cases source : (proposalState p rho (r + 1)).bestPC <;>
    cases selected : selectedPC p (headState p rho (r + 1) reader) (r + 1) <;>
    simp only [source, selected, Option.map_some, Option.map_none, Option.some.injEq] at targets
  all_goals first | contradiction | rfl | simp only [preliminaryAnchor, targets]

end AvailableChain.SAPC
end

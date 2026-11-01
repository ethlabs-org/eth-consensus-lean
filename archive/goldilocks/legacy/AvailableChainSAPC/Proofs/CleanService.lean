module
public import AvailableChainSAPC.Proofs.Preservation
public import AvailableChainSAPC.Proofs.RunCleanTicks

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A successful N extends every prefix covered by the actual honest
HEADs at its label. The witness is an emitted signature, not a stored
proposal that happens to be accessible. No cap is needed. -/
theorem timely_prefix_of_head_coverage {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (index : Nat) (reader : V) (r : Slot) (b c : Block)
    (saved : savedTimely (Run.stateBefore (sapc p) rho index reader) r = some (some c))
    (coverage : ∀ v ∈ rho.honest, Block.Preceq b (headData p rho r v).target) :
    Block.Preceq b c := by
  obtain ⟨i, data, honest, target, j, hj, emitted⟩ :=
    savedTimely_honest_preparation p E rho hx.toUnforgeableSignatures ha index reader r c saved
  have action := (emittedAt_seat_action (sapc p) E rho j _ (voteTime p r)
    r i (.head data) emitted).2
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hj] at action
  change some (Msg.head (headData p rho r (rho.seatOf r i))) = some (.head data) at action
  have he := congrArg HeadData.target (Msg.head.inj (Option.some.inj action))
  exact (he.trans target) ▸ coverage _ honest

/-- The honest preparation behind any valid PC gives the same prefix
fact. Receipt of a PC cannot invent a target off that actual HEAD path. -/
theorem pc_prefix_of_head_coverage {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (index : Nat) (reader : V) (b : Block) (c : PC p.n)
    (valid : pcValid p (Run.stateBefore (sapc p) rho index reader) c = true)
    (coverage : ∀ v ∈ rho.honest, Block.Preceq b (headData p rho c.slot v).target) :
    Block.Preceq b c.target := by
  obtain ⟨v, _, j, _, _, saved⟩ := validPC_prior_timely p E rho hx ha index reader c valid
  exact timely_prefix_of_head_coverage p E rho hx ha (j + 1) v c.slot b c.target saved coverage

/-- The shared slot-order proof turns covering batch preservation into
an exact current-slot raw result. No PC or finite-root premise is used. -/
theorem raw_result_eq_of_exact_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : earlyTime p r ≤ rho.horizon) (b : Block) (hslot : b.slot = r)
    (heads : ∀ v ∈ rho.honest, (headData p rho r v).target = b)
    (reader : V) (hr : reader ∈ rho.honest) :
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) reader).base r =
      some b := by
  obtain ⟨c, hc, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r hh b
    (fun v hv => by rw [heads v hv]; exact GridCO.block_preceq_self b) reader hr
  have ordered := (paths_at_fold p
    (rho.events.filter (fun e => decide (e.time < gateTime p r))) reader).2.2
  have hcOrdered : GridCO.SlotOrdered c := by
    rcases @GridCO.confirmation_mem GridCO.slowLeasePolicy p.engine p.n _ r c hc with hg | hm
    · subst c; trivial
    · exact ordered c hm
  have bound := @GridCO.confirmation_slot_le GridCO.slowLeasePolicy p.engine p.n _ r c ordered hc
  have he := GridCO.prefix_eq_of_slot_ge b c hcOrdered hp (bound.trans_eq hslot.symm)
  simpa only [he] using hc

/-- Both 6Δ fields reduce to common exact HEAD choices for honest
proposals and the corrected run invariant. Raw service, both guards,
and preservation after the gate are all proved here. -/
theorem clean_inclusion_of_run_invariant_and_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (h : JointCleanInvariant p E rho rho.events.length)
    (proposals : ∀ r, t₀ < proposalTime p r → HonestAwakeProposer E rho r →
      gateTime p r ≤ rho.horizon → ∃ b,
        HonestProposalAt E (sapcInterface p).toInterface rho r b ∧
        ∀ v ∈ rho.honest, (headData p rho r v).target = b) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
      t₀ (6 * p.Δ) ∧
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).confirmed
      t₀ (6 * p.Δ) := by
  apply clean_inclusion_of_joint_and_service p E rho hΔ hs.execution.toScheduleWellFormed h.facts t₀
  intro r ht hp hh
  obtain ⟨b, hb, heads⟩ := proposals r ht hp hh
  have hslot := (honest_proposal_slot p E rho hs.execution.toScheduleWellFormed r b hb).2.2
  have hearly : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  exact ⟨b, hb, raw_result_eq_of_exact_heads p E rho hΔ t₀ hs r hearly b hslot heads⟩

end AvailableChain.SAPC
end

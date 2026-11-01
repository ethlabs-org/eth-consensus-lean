module
public import AvailableChainSAPC.Proofs.Outage
public import AvailableChainSAPC.Proofs.Clean
public import AvailableChainSAPC.Proofs.CertificateService

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Under capped Sleepy, valid PCs are ordered by their preparation
labels. This is a prefix statement, not merely monotonic certificate rank. -/
theorem clean_pc_target_prefix_of_slot_lt {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i j : Nat) (u v : V) (c d : PC p.n)
    (hc : pcValid p (Run.stateBefore (sapc p) rho i u) c = true)
    (hd : pcValid p (Run.stateBefore (sapc p) rho j v) d = true)
    (slots : c.slot < d.slot) : Block.Preceq c.target d.target := by
  have ha := capped_quorum_above_faults p rho cap
  obtain ⟨a, honestA, k, _, earlyC, saveC⟩ := validPC_prior_timely p E rho hs.execution ha i u c hc
  obtain ⟨b, honestB, m, _, earlyD, saveD⟩ := validPC_prior_timely p E rho hs.execution ha j v d hd
  have earlier : earlyTime p c.slot < earlyTime p d.slot := by
    have cast : (c.slot : Time) < d.slot := by exact_mod_cast slots
    change 4 * p.Δ * (c.slot : Time) + 2 * p.Δ < 4 * p.Δ * (d.slot : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have hkm := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed earlyC earlyD earlier
  have bound : m ≤ rho.events.length := (List.getElem?_eq_some_iff.mp earlyD).1.le
  have invariant := clean_run_invariant p E rho hΔ t₀ hs m bound
  have gateBound : gateTime p c.slot ≤ earlyTime p d.slot := by
    have cast : (c.slot : Time) + 1 ≤ d.slot := by exact_mod_cast slots
    change 4 * p.Δ * (c.slot : Time) + 6 * p.Δ ≤ 4 * p.Δ * (d.slot : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have voteBound : voteTime p d.slot < earlyTime p d.slot := by
    change 4 * p.Δ * (d.slot : Time) + p.Δ < 4 * p.Δ * (d.slot : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  apply timely_prefix_of_head_coverage p E rho hs.execution ha (m + 1) b d.slot
    c.target d.target saveD
  exact timely_continues_before_active_input p E rho hΔ t₀ hs m _ earlyD invariant b honestB
    (capBroken_false_before p E rho hs.execution cap b m) d.slot c.slot c.target
    ⟨a, honestA, k, hkm, earlyC, saveC⟩ gateBound slots voteBound

/-- The additive strong output is safe under Sleepy and the explicit cap.
Agreement uses canonical sources; monotonicity additionally uses PC rank
and the chronological prefix theorem above. -/
theorem strong_safe_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) :
    SafeFrom (sapc p) rho (sapcInterface p).strong t₀ := by
  have invariant := clean_run_invariant p E rho hΔ t₀ hs rho.events.length (le_refl _)
  have path (v : V) (hv : v ∈ rho.honest) (t : Time) :
      cleanRunPath p rho rho.events.length (strong (Run.readAt (sapc p) rho t v)) := by
    rw [readAt_eq_stateBefore hs.execution.toScheduleWellFormed]
    cases selected : (Run.stateBefore (sapc p) rho
      (rho.events.filter (fun e => decide (e.time ≤ t))).length v).bestPC with
    | none => simpa only [strong, selected, Option.map_none, Option.getD_none]
        using invariant.facts.chain.genesis
    | some c =>
      have member := (invariant.facts.certificates _ (List.length_filter_le _ _) v hv c
        (installedPC_valid_before p rho v _ c selected)).2 cap
      simpa only [strong, selected, Option.map_some, Option.getD_some] using member
  constructor
  · intro u hu v hv t t' _ _ _ _
    exact invariant.facts.chain.comparable _ _ (path u hu t) (path v hv t')
  · intro v _ t t' _ le _
    change Block.Preceq (strong (Run.readAt (sapc p) rho t v))
      (strong (Run.readAt (sapc p) rho t' v))
    cases selected : (Run.readAt (sapc p) rho t v).bestPC with
    | none => simpa only [strong, selected, Option.map_none, Option.getD_none]
        using GridCO.genesis_prefix (strong (Run.readAt (sapc p) rho t' v))
    | some c =>
      obtain ⟨d, next, rank⟩ :=
        read_rank p E rho hs.execution.toScheduleWellFormed v t t' le c selected
      simp only [strong, selected, next, Option.map_some, Option.getD_some]
      rcases rank with rfl | slots
      · exact GridCO.block_preceq_self _
      · rw [readAt_eq_stateBefore hs.execution.toScheduleWellFormed] at selected next
        exact clean_pc_target_prefix_of_slot_lt p E rho hΔ t₀ hs cap _ _ v v c d
          (installedPC_valid_before p rho v _ c selected)
          (installedPC_valid_before p rho v _ d next) slots

/-- Awake quorum participation under the cap supplies a PC for the common honest
proposal before its 6Δ gate. The selected PC has that exact label and
target; the honest ack deadline excludes a later label. -/
theorem strong_included_quorum_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (quorum : ∀ t, t₀ ≤ t → t ≤ rho.horizon →
      pcQuorum p ≤ (awakeAt E rho.honest t).card) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).strong
      t₀ (6 * p.Δ) := by
  intro s start proposer horizon
  change gateTime p s ≤ rho.horizon at horizon
  obtain ⟨B, proposal, choices⟩ := clean_proposal_choices_from_engine p E rho hΔ t₀ hs
    s start proposer horizon
  refine ⟨B, proposal, ?_⟩
  have earlyH : earlyTime p s ≤ rho.horizon := by
    apply le_trans _ horizon
    change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have slot := (honest_proposal_slot p E rho hs.execution.toScheduleWellFormed s B proposal).2.2
  have raw := raw_result_eq_of_exact_heads p E rho hΔ t₀ hs s earlyH B slot choices
    (rho.proposerOf s) proposal.1
  have earlyEq : earlyTime p (s + 1) = gateTime p s := GridCO.early_next_eq_gate p.engine s
  have invariant := clean_run_invariant p E rho hΔ t₀ hs
    (rho.events.filter (fun e => decide (e.time ≤ earlyTime p (s + 1)))).length
    (List.length_filter_le _ _)
  have ack := genuine_heads_of_early_invariant p E rho hΔ hs.execution.toScheduleWellFormed
    (s + 1) (earlyEq.symm ▸ horizon) invariant s (Nat.lt_succ_self s)
    (rho.proposerOf s) proposal.1 B raw
  have times : t₀ ≤ voteTime p s ∧ t₀ ≤ voteTime p (s + 1) ∧
      voteTime p s ≤ rho.horizon ∧ voteTime p (s + 1) ≤ rho.horizon := by
    have delta := p.deltaPos
    have snonneg : (0 : Time) ≤ s := Int.natCast_nonneg s
    rw [hs.start_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + p.Δ ∧
      0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ∧
      4 * p.Δ * (s : Time) + p.Δ ≤ rho.horizon ∧
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ≤ rho.horizon
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ rho.horizon at horizon
    push_cast
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> linarith
  have sync : E.t_GST ≤ proposalTime p s := by
    rw [hs.gst_zero]
    rw [hs.start_zero] at start
    exact start.le
  intro v hv
  obtain ⟨⟨c, cs, cb, valid⟩, d, selected, rank⟩ := quorum_preparation_ack_service p E rho
    hs.execution hΔ cap hs.partialSynchrony hs.acceptedRelay s B proposal sync horizon
    (quorum _ times.1 times.2.2.1)
    (quorum _ times.2.1 times.2.2.2) choices ack v hv
  have bound := installedPC_slot_le_at_gate p E rho hs.execution
    (capped_quorum_above_faults p rho cap) v s d selected
  have ds : d.slot = s := Nat.le_antisymm bound rank
  have input : Run.stateBeforeTime (sapc p) rho (gateTime p s) =
      Run.readAt (sapc p) rho (gateTime p s - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at selected valid
  have target := pc_same_slot_unique p E rho hs.execution.toScheduleWellFormed cap _ _
    (archive_authenticated_at_read p E rho hs.execution.toUnforgeableSignatures _ v)
    (archive_authenticated_at_read p E rho hs.execution.toUnforgeableSignatures _ v)
    c d valid (installedPC_valid_at_read p rho v _ d selected) (cs.trans ds.symm)
  have value : strong (Run.readAt (sapc p) rho (gateTime p s - 1) v) = B := by
    simp only [strong, selected, Option.map_some, Option.getD_some]
    exact target.symm.trans cb
  have nonneg : t₀ ≤ gateTime p s - 1 := by
    rw [hs.start_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ - 1
    have deltaOne : 1 ≤ p.Δ := Int.add_one_le_iff.mpr p.deltaPos
    nlinarith [Int.natCast_nonneg s]
  have monotone := (strong_safe_from_engine p E rho hΔ t₀ hs cap).monotone v hv
    (gateTime p s - 1) (gateTime p s) nonneg (Int.sub_le_self _ (by norm_num)) horizon
  change Block.Preceq (strong (Run.readAt (sapc p) rho (gateTime p s - 1) v))
    (strong (Run.readAt (sapc p) rho (gateTime p s) v)) at monotone
  rw [value] at monotone
  exact monotone

/-- The original full-participation inclusion claim follows directly. -/
theorem strong_included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (full : FullParticipation E rho t₀) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).strong
      t₀ (6 * p.Δ) := by
  apply strong_included_quorum_from_engine p E rho hΔ t₀ hs cap
  intro t lo hi
  have awake : awakeAt E rho.honest t = rho.honest := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact full v hv t lo hi
  rw [awake]
  simpa [honestSeats] using honestSeats_quorum p rho cap 0

end AvailableChain.SAPC
end

module
public import AvailableChainSAPC.Proofs.StrongHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- An extending selected PC, compatible finite sources, and the prior
honest HEADs suffice for the next HEAD. F4 cannot supply a first conflict. -/
theorem head_covers_of_pc_and_previous {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (r : Slot) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (c : PC p.n)
    (selected : selectedPC p (headState p rho (r + 1) v) (r + 1) = some c)
    (belowPC : Block.Preceq B c.target)
    (heads : ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target)
    (finite : ∀ b g d, (b, g, d) ∈ (headState p rho (r + 1) v).base.obligations →
      Block.Compatible b B) : Block.Preceq B (headData p rho (r + 1) v).target := by
  have pub : PublicTime E (voteTime p (r + 1)) := by
    refine ⟨4 * (r + 1) + 1, ?_⟩
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ voteTime p (r + 1) := by
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hx.tick_total v hv _ pub nonneg horizon)
  have eq := headState_at_tick p E rho hx.toScheduleWellFormed (r + 1) v i tick
  have active : capBroken p (headState p rho (r + 1) v) = false :=
    eq ▸ capBroken_false_before p E rho hx cap v (i + 1)
  have root : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) v).base) B := by
    rcases (GridCO.liveRoot_is_deepest (headState p rho (r + 1) v).base).1 with gen | member
    · rw [gen]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix B))
    · obtain ⟨⟨b, g, d⟩, row, value⟩ := List.mem_filterMap.mp member
      dsimp only at value
      split at value
      · rw [← Option.some.inj value]
        exact finite b g d row
      · contradiction
  have auth := archive_authenticated_before p E rho hx.toUnforgeableSignatures (i + 1) v
  have archived := voterView_archived p _ (baseArchived_at_fold p (rho.events.take (i + 1)) v)
    (frozenViewsStored_at_fold p _ v) (proposalViewsArchived_at_fold p _ v) (r + 1)
  have labels := voterView_label p _ (frozenViewsStored_at_fold p (rho.events.take (i + 1)) v)
    (r + 1)
  have subset := voterSupport_subset_before p E rho hx (i + 1) v (r + 1)
  change ArchiveAuthenticated p E rho (Run.stateBefore (sapc p) rho (i + 1) v) at auth
  change ∀ o ∈ GridCO.voterView p.engine
      (Run.stateBefore (sapc p) rho (i + 1) v).base (r + 1),
      ∃ h ∈ (Run.stateBefore (sapc p) rho (i + 1) v).receivedHeads, baseWire h = o at archived
  change ∀ o ∈ GridCO.voterView p.engine
      (Run.stateBefore (sapc p) rho (i + 1) v).base (r + 1),
      GridCO.headLabel? o = some ((r + 1) - 1) at labels
  rw [eq] at auth archived labels subset
  simp only [Nat.add_sub_cancel] at labels
  have floorComp := floor_compatible_of_heads p E rho hx.toScheduleWellFormed cap _ auth
    (activeVoterTree p (headState p rho (r + 1) v) (r + 1) (some c)) r (r + 1) _ _
    subset archived labels B heads
  simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, active, selected] using!
    choice_covers_of_pc p (headState p rho (r + 1) v) _ _ _ (r + 1) c B active
      belowPC floorComp root

/-- There is no first honest HEAD departure after sound strong arming.
Induction is on the preparation label, with no duration or lease budget. -/
theorem strongArmed_no_head_departure {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (later : c.slot < r) (horizon : voteTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq c.target (headData p rho r v).target := by
  set_option backward.isDefEq.respectTransparency false in
  induction r using Nat.strong_induction_on generalizing v with
  | h r ih =>
    by_cases healthy : earlyTime p r ≤ b₀
    · exact strongArmed_healthy_heads p E rho hΔ T b₀ h u c selected r later healthy
        (healthy.trans h.interval.2.2) v hv
    · have positive : r ≠ 0 := Nat.ne_of_gt ((Nat.zero_le c.slot).trans_lt later)
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive
      have older : c.slot < s := by
        have ack := installedPC_time_le_read p E rho h.execution.toUnforgeableSignatures
          (capped_quorum_above_faults p rho h.faultBound) u T c selected
        by_contra no
        have same : c.slot = s :=
          Nat.le_antisymm (Nat.le_of_lt_succ later) (Nat.le_of_not_gt no)
        rw [same] at ack
        have armed := h.armed
        rw [hΔ] at armed
        apply healthy
        change 4 * p.Δ * ((s + 1 : Nat) : Time) + 2 * p.Δ ≤ b₀
        change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ≤ T at ack
        linarith
      by_cases frozen : freezeTime p s ≤ b₀
      · have early : earlyTime p s ≤ b₀ := by
          apply le_trans _ frozen
          change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (s : Time) + 3 * p.Δ
          linarith [p.deltaPos]
        exact strongArmed_pending_head p E rho hΔ T b₀ h u c selected s older early horizon v hv
      · have heads (k : Slot) (lo : c.slot < k) (hi : k < s + 1) :
            ∀ w ∈ rho.honest, Block.Preceq c.target (headData p rho k w).target := by
          intro w hw
          have time : voteTime p k ≤ voteTime p (s + 1) := by
            have cast : (k : Time) ≤ (s + 1 : Nat) := by exact_mod_cast hi.le
            change 4 * p.Δ * (k : Time) + p.Δ ≤
              4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
            nlinarith [p.deltaPos]
          exact ih k hi lo (time.trans horizon) w hw
        have after : b₀ ≤ voteTime p (s + 1) := by
          have lt := lt_of_not_ge frozen
          change b₀ < 4 * p.Δ * (s : Time) + 3 * p.Δ at lt
          change b₀ ≤ 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
          push_cast; linarith [p.deltaPos]
        obtain ⟨d, chosen, rank⟩ := strongArmed_selected_rank p E rho hΔ T b₀ h u hu c selected
          s (le_of_not_ge frozen) horizon v hv
        have certificates := certificates_valid_at_fold p
          (rho.events.filter (fun e => decide (e.time < voteTime p (s + 1)))) v
        have valid := selectedPC_valid p _ (clock_frozenPC_valid p _ _
          certificates.2 certificates.1) (s + 1) d chosen
        rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at valid
        have below := strongArmed_pc_prefix_of_earlier_heads p E rho T b₀ h u c selected
          (s + 1) heads _ (le_refl _) v d valid rank
        exact head_covers_of_pc_and_previous p E rho hΔ h.execution h.faultBound s horizon
          v hv c.target d chosen below (heads s older (Nat.lt_succ_self s))
          (strongArmed_finite_of_earlier_heads p E rho hΔ T b₀ h u hu c selected
            (s + 1) heads after v hv)

/-- A PC first disclosed after arming cannot introduce a conflicting
same-or-higher target. Authentication supplies its historical preparation;
late assembly cannot create a missing honest HEAD or change that label. -/
theorem strongArmed_late_pc_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (st : State p.n) (auth : ArchiveAuthenticated p E rho st) (d : PC p.n)
    (valid : pcValid p st d = true) (rank : c.slot ≤ d.slot) :
    Block.Preceq c.target d.target := by
  rcases lt_or_eq_of_le rank with later | same
  · obtain ⟨seat, data, honest, target, i, tick, emitted⟩ := pc_honest_preparation p E rho
      h.execution.toUnforgeableSignatures st auth d valid
      (capped_quorum_above_faults p rho h.faultBound)
    have horizon := (h.execution.in_horizon _ (List.mem_of_getElem? tick)).2
    have coverage := strongArmed_no_head_departure p E rho hΔ T b₀ h u hu c selected
      d.slot later horizon (rho.seatOf d.slot seat) honest
    have act := (emittedAt_seat_action (sapc p) E rho i _ (voteTime p d.slot)
      d.slot seat (.head data) emitted).2
    rw [stateBefore_tick_eq_stateBeforeTime h.execution.toScheduleWellFormed tick] at act
    change some (Msg.head (headData p rho d.slot (rho.seatOf d.slot seat))) = some (.head data)
      at act
    have eq := (congrArg HeadData.target (Msg.head.inj (Option.some.inj act))).trans target
    exact eq ▸ coverage
  · have eq := pc_same_slot_unique p E rho h.execution.toScheduleWellFormed h.faultBound
      _ st (archive_authenticated_at_read p E rho h.execution.toUnforgeableSignatures T u)
      auth c d (installedPC_valid_at_read p rho u T c selected) valid same
    rw [eq]
    exact GridCO.block_preceq_self _

/-- Soundly armed strong output persists at every later honest read.
This is the exact additive companion field, with no duration budget and
no delivery or participation premise at or after the outage boundary. -/
theorem strong_resilient_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀) :
    PersistsFrom (sapc p) rho (sapcInterface p).strong T b₀ := by
  intro u hu B below t after _ v hv
  change Block.Preceq B (strong (Run.readAt (sapc p) rho T u)) at below
  change Block.Preceq B (strong (Run.readAt (sapc p) rho t v))
  cases selected : (Run.readAt (sapc p) rho T u).bestPC with
  | none =>
    have gen : B = .genesis := by
      simpa only [strong, selected, Option.map_none, Option.getD_none,
        Block.Preceq, Block.preceq, decide_eq_true_eq] using below
    subst B
    exact GridCO.genesis_prefix _
  | some c =>
    obtain ⟨d, common, rank, _⟩ := strongArmed_common_pc p E rho hΔ T b₀ h u hu c selected v hv
    have input : Run.stateBeforeTime (sapc p) rho b₀ =
        Run.readAt (sapc p) rho (b₀ - 1) := by
      simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
    rw [input] at common
    obtain ⟨e, live, next⟩ := strong_certificate_retained p E rho h.execution.toScheduleWellFormed
      v (b₀ - 1) t (by linarith) d common
    have contains := strongArmed_late_pc_prefix p E rho hΔ T b₀ h u hu c selected _
      (archive_authenticated_at_read p E rho h.execution.toUnforgeableSignatures t v) e
      (installedPC_valid_at_read p rho v t e live) (rank.trans next)
    simp only [strong, selected, Option.map_some, Option.getD_some] at below
    simpa only [strong, live, Option.map_some, Option.getD_some] using
      GridCO.prefix_trans B c.target e.target below contains

end AvailableChain.SAPC
end

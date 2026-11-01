module
public import AvailableChainSAPC.Proofs.StrongSelection

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A PC at a strict input before a HEAD has an older preparation label.
The honest ack bound applies to late archive assembly as well. -/
theorem validPC_slot_lt_before_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (t : Time) (r : Slot) (before : t ≤ voteTime p r) (v : V) (c : PC p.n)
    (valid : pcValid p (Run.stateBeforeTime (sapc p) rho t v) c = true) : c.slot < r := by
  obtain ⟨seat, data, honest, member, _, _⟩ := pc_honest_witness p rho _ c valid
    (capped_quorum_above_faults p rho cap)
  have input : Run.stateBeforeTime (sapc p) rho t = Run.readAt (sapc p) rho (t - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at member
  have time := archived_honest_head_time_le_read p E rho hx.toUnforgeableSignatures v
    (t - 1) (c.slot + 1) seat data member honest
  by_contra hn
  have cast : (r : Time) ≤ c.slot := by exact_mod_cast Nat.le_of_not_gt hn
  change 4 * p.Δ * ((c.slot + 1 : Nat) : Time) + p.Δ ≤ t - 1 at time
  change t ≤ 4 * p.Δ * (r : Time) + p.Δ at before
  push_cast at time
  nlinarith [p.deltaPos]

/-- The chronological HEAD induction excludes every higher conflicting
PC at the current input. Equal labels use capped quorum uniqueness. -/
theorem strongArmed_pc_prefix_of_earlier_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (heads : ∀ s, c.slot < s → s < r → ∀ v ∈ rho.honest,
      Block.Preceq c.target (headData p rho s v).target)
    (t : Time) (before : t ≤ voteTime p r) (v : V) (d : PC p.n)
    (valid : pcValid p (Run.stateBeforeTime (sapc p) rho t v) d = true)
    (rank : c.slot ≤ d.slot) : Block.Preceq c.target d.target := by
  rcases lt_or_eq_of_le rank with later | same
  · have bound := validPC_slot_lt_before_head p E rho h.execution h.faultBound t r before v d valid
    rw [time_input_eq_event_prefix p E rho h.execution.toScheduleWellFormed] at valid
    exact pc_prefix_of_head_coverage p E rho h.execution
      (capped_quorum_above_faults p rho h.faultBound) _ v c.target d valid
      (heads d.slot later bound)
  · have eq := pc_same_slot_unique p E rho h.execution.toScheduleWellFormed h.faultBound
      _ _ (archive_authenticated_at_read p E rho h.execution.toUnforgeableSignatures T u)
      (archive_authenticated_beforeTime p E rho h.execution.toUnforgeableSignatures t v)
      c d (installedPC_valid_at_read p rho u T c selected) valid same
    rw [eq]
    exact GridCO.block_preceq_self _

/-- Every live PC from arming to the current HEAD contains the target,
provided all earlier preparation HEADs do. No duration bound is used. -/
theorem strongArmed_live_pc_of_earlier_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (heads : ∀ s, c.slot < s → s < r → ∀ v ∈ rho.honest,
      Block.Preceq c.target (headData p rho s v).target)
    (t : Time) (after : b₀ ≤ t) (before : t ≤ voteTime p r) (v : V) (hv : v ∈ rho.honest) :
    ∃ d, (Run.stateBeforeTime (sapc p) rho t v).bestPC = some d ∧
      Block.Preceq c.target d.target := by
  obtain ⟨d, live, rank⟩ := strongArmed_rank_beforeTime p E rho hΔ T b₀ h u hu c selected
    t after v hv
  exact ⟨d, live, strongArmed_pc_prefix_of_earlier_heads p E rho T b₀ h u c selected r heads
    t before v d (installedPC_valid_beforeTime p rho v t d live) rank⟩

/-- The finite map cannot be the first departure. Between arming and the
current HEAD every gate uses an extending live PC, so each new prefix
passes its own guard. Release and expiry need no support or time budget. -/
theorem strongArmed_finite_of_earlier_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (T b₀ : Time)
    (h : StrongArmedRegime (sapc p) E (sapcInterface p) (pcFaultCap p) rho T b₀)
    (u : V) (hu : u ∈ rho.honest) (c : PC p.n)
    (selected : (Run.readAt (sapc p) rho T u).bestPC = some c)
    (r : Slot) (heads : ∀ s, c.slot < s → s < r → ∀ v ∈ rho.honest,
      Block.Preceq c.target (headData p rho s v).target)
    (after : b₀ ≤ voteTime p r) (v : V) (hv : v ∈ rho.honest) :
    ∀ b g d, (b, g, d) ∈ (headState p rho r v).base.obligations →
      Block.Compatible b c.target := by
  set_option backward.isDefEq.respectTransparency false in
  have hs := h.execution.toScheduleWellFormed
  let start := (rho.events.filter (fun e => decide (e.time ≤ b₀ - 1))).length
  let finish := (rho.events.filter (fun e => decide (e.time ≤ voteTime p r - 1))).length
  have bound : start ≤ finish := read_length_mono _ _ (by linarith)
  have base := strongArmed_finite_compatible p E rho hΔ T b₀ h u hu c selected
  have input : ∀ w ∈ rho.honest, ∀ b g d,
      (b, g, d) ∈ (Run.stateBefore (sapc p) rho finish w).base.obligations →
      Block.Compatible b c.target := by
    apply state_interval_induction (sapc p) rho
      (fun _ st => ∀ b g d, (b, g, d) ∈ st.base.obligations → Block.Compatible b c.target)
      start finish bound
    · intro w hw
      simpa only [time_input_eq_event_prefix p E rho hs] using base w hw
    · intro w hw st o old
      simpa only [sapc, process_obligations] using! old
    · intro i w t lo hi tick hw old _
      have before : t < voteTime p r := Int.le_sub_one_iff.mp
        ((index_lt_read_length_iff hs (voteTime p r - 1) tick).mp hi)
      have afterT : b₀ ≤ t := by
        by_contra no
        have lt := (index_lt_read_length_iff hs (b₀ - 1) tick).mpr
          (Int.le_sub_one_iff.mpr (lt_of_not_ge no))
        exact (Nat.not_lt_of_ge lo lt).elim
      obtain ⟨d, live, below⟩ := strongArmed_live_pc_of_earlier_heads p E rho hΔ T b₀ h
        u hu c selected r heads t afterT before.le w hw
      rw [← stateBefore_tick_eq_stateBeforeTime hs tick] at live
      exact clock_finite_compatible p _ t d c.target
        (capBroken_false_before p E rho h.execution h.faultBound w i) live below old
  obtain ⟨d, live, below⟩ := strongArmed_live_pc_of_earlier_heads p E rho hΔ T b₀ h
    u hu c selected r heads (voteTime p r) after (le_refl _) v hv
  apply clock_finite_compatible p _ (voteTime p r) d c.target
    (capBroken_false_beforeTime p E rho h.execution h.faultBound v _) live below
  simpa only [time_input_eq_event_prefix p E rho hs] using input v hv

end AvailableChain.SAPC
end

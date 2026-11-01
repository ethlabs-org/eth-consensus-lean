module
public import AvailableChainSAPC.Proofs.GenuineHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The base-cache projection of an honest early HEAD survives the late
filter. Authentication includes direct and proposal-carried signatures. -/
theorem base_honest_early_clean {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (cut : Time) (v : V) (r : Slot) (i : Fin p.n) (b : Block)
    (hh : rho.seatOf r i ∈ rho.honest)
    (ho : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈
      GridCO.earlyVotes p.engine (Run.stateBeforeTime (sapc p) rho cut v).base r) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈
      GridCO.cleanSupport p.engine (Run.stateBeforeTime (sapc p) rho cut v).base r := by
  apply List.mem_filter.mpr
  refine ⟨ho, ?_⟩
  simp only [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro hbad
  obtain ⟨q, hq, htest⟩ := List.any_eq_true.mp hbad
  obtain ⟨hsame, hne⟩ := Bool.and_eq_true_iff.mp htest
  have horaw := (List.mem_filter.mp ho).1
  have hqraw := (List.mem_filter.mp hq).1
  have hql : GridCO.headLabel? q = some r := by simpa using (List.mem_filter.mp hqraw).2
  have hqi : GridCO.headSeat? q = some i := by
    rcases q with ⟨auth, payload⟩
    cases auth <;> cases payload <;>
      simp_all [GridCO.sameSeat, GridCO.headSeat?, GridCO.headLabel?]
  have he := base_honest_heads_equal p E rho hx.toScheduleWellFormed _
    (baseArchived_at_fold p _ v)
    (archive_authenticated_beforeTime p E rho hx.toUnforgeableSignatures cut v)
    q _ r i (List.mem_filter.mp hqraw).1 (List.mem_filter.mp horaw).1
    hql rfl hqi rfl hh
  simp [he] at hne

/-- The SA-PC raw denominator has the same awake-plus-faulty bound as SA.
The only new bridge is from an internal key to its archived signature. -/
theorem base_late_count_le_awake_add_faulty {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (cut : Time) (v : V) (r : Slot) :
    GridCO.voterCount (GridCO.lateVotes p.engine
      (Run.stateBeforeTime (sapc p) rho cut v).base r) ≤
      (awakeAt E rho.honest (voteTime p r)).card + (faulty rho).card := by
  set_option backward.isDefEq.respectTransparency false in
  rw [← GridCO.lateSeats_card]
  apply le_trans (b := (awakeAt E rho.honest (voteTime p r) ∪ faulty rho).card)
  · apply Finset.card_le_card_of_injOn (rho.seatOf r)
    · intro i hi
      obtain ⟨o, ho, hseat⟩ := List.mem_filterMap.mp
        (List.mem_dedup.mp (List.mem_toFinset.mp hi))
      have hraw := (List.mem_filter.mp ho).1
      have hlabel : GridCO.headLabel? o = some r := by
        simpa using (List.mem_filter.mp hraw).2
      have hstored := (List.mem_filter.mp hraw).1
      by_cases hh : rho.seatOf r i ∈ rho.honest
      · apply Finset.mem_union_left
        obtain ⟨b, rfl⟩ := GridCO.head_wire_shape o r i hlabel hseat
        obtain ⟨data, hd, _⟩ := baseArchived_head _ (baseArchived_at_fold p _ v) r i b hstored
        obtain ⟨j, _, hem⟩ := archive_authenticated_beforeTime p E rho
          hx.toUnforgeableSignatures cut v r i data hd hh
        have hawake : E.awake (rho.seatOf r i) (voteTime p r) = true := by
          by_contra hn
          simp [Run.emittedAt, hn] at hem
        exact Finset.mem_filter.mpr ⟨hh, hawake⟩
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩)
    · intro i _ j _ he; exact (rho.seatOf r).injective he
  · exact Finset.card_union_le _ _

/-- A delivered honest HEAD and its relayed path enter the early base
view. The receipt deadlines, not the later gate time, are the premises. -/
theorem head_in_earlyVotes_of_delivery {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (r : Slot)
    (u v : V) (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    (relay : RelayBy p rho (voteTime p r) (earlyTime p r))
    (delivery : ∃ t, voteTime p r ≤ t ∧ t < earlyTime p r ∧ ∃ j,
      Run.handlesAt (sapc p) rho j v
        (fromHead ⟨.seat r ((rho.seatOf r).symm u), headData p rho r u⟩) t) :
    (⟨.seat r ((rho.seatOf r).symm u), .head (headData p rho r u).target⟩ : GridCO.Wire p.n) ∈
      GridCO.earlyVotes p.engine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r := by
  set_option backward.isDefEq.respectTransparency false in
  have hve : voteTime p r ≤ earlyTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have heg : earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨t, hlo, hhi, j, handle⟩ := delivery
  obtain ⟨key, stamp⟩ := early_honest_base_head_at_cut p E rho hx hΔ j v r
    ((rho.seatOf r).symm u) (headData p rho r u) (by simpa using hu)
    t (gateTime p r) hlo hhi heg handle
  have target := strict_block_relay p E rho hx.toScheduleWellFormed
    (voteTime p r) (earlyTime p r) hve relay u v hu hv _
    (headData_target_stored p rho r u)
  have receipts := time_input_base_receiptPrefix p E rho hx.toScheduleWellFormed
    (earlyTime p r) (gateTime p r) heg v
  have bound := (time_input_stamps_lt p E rho hx.toScheduleWellFormed (earlyTime p r)
    (by change 0 < 4 * p.Δ * (r : Time) + 2 * p.Δ
        nlinarith [p.deltaPos, Int.natCast_nonneg r]) v).2 (headData p rho r u).target
  have blockstamp : GridCO.stampBlock
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base
      (headData p rho r u).target < earlyTime p r := by
    rw [receipts.stampBlock (base_receiptStamped_at_fold p _ v) _ target]
    exact bound
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨key, by simp [GridCO.headLabel?]⟩, ?_⟩
  simpa only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
    Option.getD_some, GridCO.blockKnown, Bool.and_eq_true, decide_eq_true_eq] using!
    And.intro (And.intro (And.intro (receipts.blocks.subset target)
      (headData_target_slot p E rho hx.toScheduleWellFormed r u)) stamp) blockstamp

/-- Synchronous honest HEADs and their paths are early resolved base
receipts at the actual gate. No equality of raw archives is assumed. -/
theorem synchronous_head_in_earlyVotes {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (hsync : E.t_GST ≤ voteTime p r) (hhorizon : earlyTime p r ≤ rho.horizon)
    (u v : V) (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    (ha : E.awake u (voteTime p r) = true) :
    (⟨.seat r ((rho.seatOf r).symm u), .head (headData p rho r u).target⟩ : GridCO.Wire p.n) ∈
      GridCO.earlyVotes p.engine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r := by
  have hve : voteTime p r ≤ earlyTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have htime : max (voteTime p r) E.t_GST + E.Δ = earlyTime p r := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + p.Δ + p.Δ = 4 * p.Δ * (r : Time) + 2 * p.Δ
    ring
  have hem := honest_head_emitted p E rho hx.toScheduleWellFormed hΔ r
    ((rho.seatOf r).symm u) (by simpa using hu) (by simpa using ha) (hve.trans hhorizon)
  simp only [Equiv.apply_symm_apply] at hem
  obtain ⟨t, hlo, hhi, j, handle⟩ := hnet.broadcast u hu _ _ hem v hv
    (by rwa [htime]) rfl
  have hhi : t < earlyTime p r := by rwa [htime] at hhi
  apply head_in_earlyVotes_of_delivery p E rho hx hΔ r u v hu hv
  · rw [← htime]
    exact synchronous_relayBy p E rho _ hrelay (by rwa [htime])
  · exact ⟨t, hlo, hhi, j, handle⟩

/-- The complete honest early batch supplies its full prefix count.
Faulty support and ack variants do not enter this lower bound. -/
theorem prefixSupport_ge_honest_batch {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (r : Slot) (b : Block)
    (cover : ∀ u ∈ rho.honest, Block.Preceq b (headData p rho r u).target)
    (v : V) (batch : ∀ u ∈ rho.honest, E.awake u (voteTime p r) = true →
      (⟨.seat r ((rho.seatOf r).symm u), .head (headData p rho r u).target⟩ : GridCO.Wire p.n) ∈
        GridCO.earlyVotes p.engine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    (awakeAt E rho.honest (voteTime p r)).card ≤ GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r b := by
  rw [GridCO.prefixSupport_eq_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf r).symm
  · intro u hu
    obtain ⟨honest, awake⟩ := Finset.mem_filter.mp hu
    have early := batch u honest awake
    have clean := base_honest_early_clean p E rho hx (gateTime p r) v r
      ((rho.seatOf r).symm u) (headData p rho r u).target (by simpa using honest) early
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr (List.mem_dedup.mpr
      (List.mem_filterMap.mpr ⟨_, clean, rfl⟩)), List.any_eq_true.mpr ⟨_,
      List.mem_filter.mpr ⟨clean, by simp [GridCO.headSeat?]⟩, ?_⟩⟩
    have resolved := (List.mem_filter.mp early).2
    simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
      Option.getD_some, Bool.and_eq_true, decide_eq_true_eq, GridCO.blockKnown] at resolved
    simpa only [GridCO.headTarget?, GridCO.headLabel?, Option.getD_some, Bool.and_eq_true,
      decide_eq_true_eq] using! And.intro (And.intro resolved.1.1.1 resolved.1.1.2)
        (cover u honest)
  · intro u _ w _ he; exact (rho.seatOf r).symm.injective he

/-- SA raw confirmation consumes an early batch without any gate-time
network premise. Thus the gate itself may occur inside an outage. -/
theorem preserve_of_early_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (r : Slot)
    (majority : AwakeMajority E rho (voteTime p r)) (b : Block)
    (cover : ∀ u ∈ rho.honest, Block.Preceq b (headData p rho r u).target)
    (v : V) (batch : ∀ u ∈ rho.honest, E.awake u (voteTime p r) = true →
      (⟨.seat r ((rho.seatOf r).symm u), .head (headData p rho r u).target⟩ : GridCO.Wire p.n) ∈
        GridCO.earlyVotes p.engine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    ∃ c,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c ∧
        Block.Preceq b c := by
  let st := (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base
  have support := prefixSupport_ge_honest_batch p E rho hx r b cover v batch
  change (awakeAt E rho.honest (voteTime p r)).card ≤
    GridCO.prefixSupport p.engine st r b at support
  have late := base_late_count_le_awake_add_faulty p E rho hx (gateTime p r) v r
  change GridCO.voterCount (GridCO.lateVotes p.engine st r) ≤ _ at late
  have hm : GridCO.voterCount (GridCO.lateVotes p.engine st r) <
      2 * GridCO.prefixSupport p.engine st r b := by
    change (faulty rho).card < (awakeAt E rho.honest (voteTime p r)).card at majority
    omega
  obtain ⟨target, ht, _, hp⟩ := GridCO.prefixSupport_target p.engine st r b (by omega)
  exact @GridCO.confirmation_covers_majority GridCO.slowLeasePolicy p.engine p.n st r b
    (fun a hn ha => (paths_at_fold p _ v).1 target ht a hn
      (GridCO.prefix_trans a b target ha hp)) hm

/-- The unchanged SA confirmation theorem consumes the complete honest
batch. This is an actual raw gate result, before either guard. -/
theorem preserve_from_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (hsync : E.t_GST ≤ voteTime p r) (hhorizon : earlyTime p r ≤ rho.horizon)
    (majority : AwakeMajority E rho (voteTime p r)) (b : Block)
    (cover : ∀ u ∈ rho.honest, Block.Preceq b (headData p rho r u).target)
    (v : V) (hv : v ∈ rho.honest) : ∃ c,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c ∧
        Block.Preceq b c := by
  exact preserve_of_early_heads p E rho hx r majority b cover v
    (fun u hu ha => synchronous_head_in_earlyVotes p E rho hx hΔ hnet hrelay r
      hsync hhorizon u v hu hv ha)

/-- Plain Sleepy supplies all batch-preservation premises. Only the
actual HEAD coverage is an induction input; no cap is needed. -/
theorem sleepy_preserve_from_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : earlyTime p r ≤ rho.horizon) (b : Block)
    (cover : ∀ u ∈ rho.honest, Block.Preceq b (headData p rho r u).target)
    (v : V) (hv : v ∈ rho.honest) : ∃ c,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c ∧
        Block.Preceq b c := by
  have hn : 0 ≤ voteTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hve : voteTime p r ≤ earlyTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  exact preserve_from_heads p E rho hs.execution hΔ hs.partialSynchrony hs.acceptedRelay r
    (by rwa [hs.gst_zero]) hh
    (hs.participation _ (by rwa [hs.start_zero]) (hve.trans hh)) b cover v hv

/-- Batch preservation is discharged from Sleepy. The shared clean
induction now has only the PC-specific active transfer condition left.
In disabled mode its transfer step uses the plain SA walk directly. -/
theorem clean_genuine_history_of_pc {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (pc : ∀ s, s ≤ r →
      GridCO.GenuineExtends (fun v => v ∈ rho.honest)
        (fun s v => SA.confirmation p
          (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) s →
      ∀ source ∈ rho.honest, ∀ b,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) source).base s =
          some b → ∀ reader ∈ rho.honest, ∀ cert,
        capBroken p (headState p rho (s + 1) reader) = false →
        selectedPC p (headState p rho (s + 1) reader) (s + 1) = some cert →
          Block.Compatible cert.target b) :
    GridCO.GenuineExtends (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r ∧
    GridCO.GenuineContinues (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
      (fun s v => (headData p rho (s + 1) v).target) r := by
  apply clean_genuine_history_of_steps p E rho hΔ t₀ hs r hh _ pc
  intro s hsr continuation source hsource b hb reader hr
  have hgate : gateTime p (s + 1) ≤ rho.horizon :=
    ((GridCO.gateTime_le_iff p.engine (s + 1) r).mpr (Nat.succ_le_of_lt hsr)).trans hh
  have hearly : earlyTime p (s + 1) ≤ rho.horizon := by
    apply le_trans _ hgate
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  exact sleepy_preserve_from_heads p E rho hΔ t₀ hs (s + 1) hearly b
    (continuation source hsource b hb) reader hr

end AvailableChain.SAPC
end

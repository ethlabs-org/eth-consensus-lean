module
public import AvailableChainSAPC.Proofs.EarlyReceipts
public import AvailableChainSAPC.Proofs.MergedReceipts

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Early resolved support identifies both receipts at the strict early
input, even when read from the later gate input. -/
theorem early_head_at_early {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (o : GridCO.Wire p.n) (b : Block)
    (ht : GridCO.headTarget? o = some b)
    (ho : o ∈ GridCO.earlyVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    o ∈ (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v).base.votes ∧
    b ∈ (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v).base.blocks := by
  have hpub : PublicTime E (earlyTime p r) := by
    refine ⟨4 * r + 2, ?_⟩
    change 4 * p.Δ * (r : Time) + 2 * p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have hz : 0 ≤ earlyTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  obtain ⟨hm, hres⟩ := List.mem_filter.mp ho
  have hv := (List.mem_filter.mp hm).1
  simp only [GridCO.resolvedBefore_block, ht, Bool.and_eq_true_iff,
    decide_eq_true_eq, GridCO.blockKnown] at hres
  rw [time_input_eq_event_prefix p E rho hs] at hv hres
  have h := base_early_receipts_at_input p E rho hs _ hpub hz
    (rho.events.filter (fun e => decide (e.time ≤ gateTime p r - 1))).length v
  exact ⟨h.2 o hv hres.1.2, h.1 b hres.1.1.1 hres.2⟩

/-- Every early resolved HEAD supplies its exact frozen support key or
retained equivocation evidence. Its target path relays independently. -/
theorem early_head_at_freeze {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hrelay : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (i : Fin p.n) (b : Block)
    (ho : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈ GridCO.earlyVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    let st := (Run.stateBeforeTime (sapc p) rho (freezeTime p r) w).base
    b ∈ st.blocks ∧
      ((⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈ (GridCO.freezeView p.engine st r).2.1 ∨
        GridCO.equivocates (GridCO.freezeView p.engine st r).1 i = true) := by
  obtain ⟨hm, hb⟩ := early_head_at_early p E rho hs hΔ r v _ b rfl ho
  obtain ⟨data, hm, ht⟩ := baseArchived_head _ (baseArchived_at_fold p _ v) r i b hm
  have hef : earlyTime p r ≤ freezeTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have hz : 0 < freezeTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hcut : freezeTime p r ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hb' := strict_block_relay p E rho hs _ _ hef hrelay v w hv hw b hb
  refine ⟨hb', ?_⟩
  have he : Run.stateBeforeTime (sapc p) rho (earlyTime p r) =
      Run.readAt (sapc p) rho (earlyTime p r - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  change (⟨.seat r i, data⟩ : HeadWire p.n) ∈
    (Run.stateBeforeTime (sapc p) rho (earlyTime p r) v).receivedHeads at hm
  rw [he] at hm
  have hrec := read_head_base_relay p E rho hs (earlyTime p r - 1) (freezeTime p r)
    (by linarith) hz r hcut
    (fun u hu j obj t htime ha reader hr hn => hrelay u hu j obj t
      (le_of_lt (Int.le_sub_one_iff.mp htime)) ha reader hr hn) v w hv hw i data hm
  rcases hrec with hk | heq
  · left
    have hkey : baseWire ⟨.seat r i, data⟩ =
        (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) := by
      simp [baseWire, baseHead, GridCO.fromHead, ht]
    rw [hkey] at hk
    have hres := (List.mem_filter.mp ho).2
    simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
      Option.getD_some, Bool.and_eq_true_iff, decide_eq_true_eq] at hres
    apply List.mem_filter.mpr
    refine ⟨hk, ?_⟩
    have stamps := time_input_stamps_lt p E rho hs _ hz w
    simp only [GridCO.resolvedBefore_block, GridCO.headTarget?, GridCO.headLabel?,
      Option.getD_some, Bool.and_eq_true_iff, decide_eq_true_eq, GridCO.blockKnown]
    exact ⟨⟨⟨hb', hres.1.1.2⟩, stamps.1 _⟩, stamps.2 _⟩
  · right
    rwa [(base_freezeView_at_input p E rho hs r w).1]

/-- A surviving genuine supporter cannot be an equivocator in the
source late pool. No honesty assumption about that seat is needed. -/
theorem cleanSupport_not_equivocating (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (o : GridCO.Wire n) (i : Fin n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.cleanSupport p.engine st r) :
    GridCO.equivocates (GridCO.lateVotes p.engine st r) i = false := by
  apply GridCO.equivocates_false_of_unique
  intro a ha b hb
  obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbi⟩ := List.mem_filter.mp hb
  exact (GridCO.cleanSupport_eq_of_late_same_seat p.engine st r i o a ho ha hi
    (by simpa using hai)).symm.trans
    (GridCO.cleanSupport_eq_of_late_same_seat p.engine st r i o b ho hb hi
      (by simpa using hbi))

/-- Reverse relay excludes all conflicting copies of a genuine
supporter from the full merged HEAD view. -/
theorem cleanSupport_voter_unique_of_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p))
    (r : Slot) (v w : V)
    (hrelay : BackReceipts p rho r v w)
    (o : GridCO.Wire p.n) (i : Fin p.n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    ∀ key ∈ GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1),
      GridCO.headSeat? key = some i → key = o := by
  intro key hm hseat
  rcases hrelay key i hseat hm with hk | he
  · exact (GridCO.cleanSupport_eq_of_late_same_seat p.engine _ r i o key ho hk hi hseat).symm
  · rw [cleanSupport_not_equivocating p _ r o i hi ho] at he
    contradiction

theorem cleanSupport_voter_unique {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hrelay : RelayBy p rho (voteTime p (r + 1)) (gateTime p r))
    (o : GridCO.Wire p.n) (i : Fin p.n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    ∀ key ∈ GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1),
      GridCO.headSeat? key = some i → key = o :=
  cleanSupport_voter_unique_of_back_receipts p rho r v w
    (voter_raw_at_gate p E rho hs r v w hv hw hrelay) o i hi ho

/-- Every genuine supporter occurs in the actual next support view.
The cache's equivocation alternative is excluded by reverse relay. -/
theorem cleanSupport_in_voterSupport_of_frozen_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (forward : ∀ i b,
      (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈ GridCO.earlyVotes p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r →
      let st := (Run.stateBeforeTime (sapc p) rho (freezeTime p r) w).base
      b ∈ st.blocks ∧
        ((⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈ (GridCO.freezeView p.engine st r).2.1 ∨
          GridCO.equivocates (GridCO.freezeView p.engine st r).1 i = true))
    (hback : BackReceipts p rho r v w)
    (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    o ∈ GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1) ∧
      ∃ target, GridCO.headTarget? o = some target ∧
        target ∈ (headState p rho (r + 1) w).base.blocks := by
  set_option backward.isDefEq.respectTransparency false in
  have hearly := (List.mem_filter.mp ho).1
  have hl : GridCO.headLabel? o = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp hearly).1).2
  have hshape : ∃ i b, o = (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) := by
    rcases o with ⟨auth, payload⟩
    cases auth <;> cases payload <;> simp_all [GridCO.headLabel?]
  obtain ⟨i, b, rfl⟩ := hshape
  obtain ⟨hb, hrec⟩ := forward i b hearly
  have hf := headState_base_frozenAt p E rho hs hΔ r w hw hh
  have hraw : (GridCO.freezeView p.engine
      (Run.stateBeforeTime (sapc p) rho (freezeTime p r) w).base r).1 ⊆
      GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1) := by
    intro key hk
    simp only [GridCO.voterView, Nat.add_sub_cancel, hf]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ hk)
  have hsupport : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∈
      (GridCO.freezeView p.engine
        (Run.stateBeforeTime (sapc p) rho (freezeTime p r) w).base r).2.1 := by
    rcases hrec with hk | he
    · exact hk
    · have hn : GridCO.equivocates
          (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1)) i = false := by
        apply GridCO.equivocates_false_of_unique
        intro a ha b hb
        obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
        obtain ⟨hb, hbi⟩ := List.mem_filter.mp hb
        have hu := cleanSupport_voter_unique_of_back_receipts p rho r v w
          hback _ i rfl ho
        exact (hu a ha (by simpa using hai)).trans (hu b hb (by simpa using hbi)).symm
      have he' := GridCO.equivocates_mono _ _ i hraw he
      rw [hn] at he'
      contradiction
  refine ⟨?_, b, rfl, ?_⟩
  · simp only [GridCO.voterSupportView, Nat.add_sub_cancel, hf]
    exact List.mem_eraseDups.mpr (List.mem_append_left _ hsupport)
  · simp only [headState, clock_blocks]
    apply (time_input_base_receiptPrefix p E rho hs _ _ ?_ w).blocks.subset hb
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]

/-- Every genuine supporter occurs in the actual next support view.
The cache's equivocation alternative is excluded by reverse relay. -/
theorem cleanSupport_in_voterSupport_of_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : BackReceipts p rho r v w)
    (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    o ∈ GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1) ∧
      ∃ target, GridCO.headTarget? o = some target ∧
        target ∈ (headState p rho (r + 1) w).base.blocks :=
  cleanSupport_in_voterSupport_of_frozen_receipts p E rho hs hΔ r v w hw hh
    (early_head_at_freeze p E rho hs hΔ r v w hv hw hforward) hback o ho

theorem cleanSupport_in_voterSupport {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : RelayBy p rho (voteTime p (r + 1)) (gateTime p r))
    (o : GridCO.Wire p.n)
    (ho : o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) :
    o ∈ GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1) ∧
      ∃ target, GridCO.headTarget? o = some target ∧
        target ∈ (headState p rho (r + 1) w).base.blocks :=
  cleanSupport_in_voterSupport_of_back_receipts p E rho hs hΔ r v w hv hw hh hforward
    (voter_raw_at_gate p E rho hs r v w hv hw hback) o ho

/-- The common SA transfer object needs support reflection and reverse
receipts. These inputs can come from relay or from one reader's history. -/
theorem genuine_transfer_receipts_of_support {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (r : Slot) (v w : V) (b : Block)
    (forward : ∀ o, o ∈ GridCO.cleanSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r →
      o ∈ GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1) ∧
        ∃ target, GridCO.headTarget? o = some target ∧
          target ∈ (headState p rho (r + 1) w).base.blocks)
    (back : BackReceipts p rho r v w) :
    GridCO.TransferReceipts p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r
      (headState p rho (r + 1) w).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1)) b := by
  set_option backward.isDefEq.respectTransparency false in
  refine ⟨fun o ho _ => forward o ho, fun o ho i hi => back o i hi ho, ?_⟩
  apply voterSupport_subset_raw
  · have h := frozenViewsStored_at_fold p
      ((rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) ++
        [.tick w (voteTime p (r + 1))]) w
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
      World.step, Function.update_self] using! h
  · simpa only [headState, DeclaredSupport, clock_base_proposals] using!
      declaredSupport_beforeTime p E rho hx (voteTime p (r + 1)) w

/-- The SA support-transfer interface holds for actual SA-PC gate and
HEAD states, in either mode and without an actual fault cap. -/
theorem genuine_transfer_receipts_of_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : BackReceipts p rho r v w) (b : Block) :
    GridCO.TransferReceipts p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r
      (headState p rho (r + 1) w).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1)) b :=
  genuine_transfer_receipts_of_support p E rho hx r v w b
    (cleanSupport_in_voterSupport_of_back_receipts p E rho hx.toScheduleWellFormed hΔ
      r v w hv hw hh hforward hback) hback

theorem genuine_transfer_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : RelayBy p rho (voteTime p (r + 1)) (gateTime p r)) (b : Block) :
    GridCO.TransferReceipts p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r
      (headState p rho (r + 1) w).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1)) b :=
  genuine_transfer_receipts_of_back_receipts p E rho hx hΔ r v w hv hw hh hforward
    (voter_raw_at_gate p E rho hx.toScheduleWellFormed r v w hv hw hback) b

/-- A target stored at the freeze supplies its non-genesis ancestor path
in the ordinary next-duty domain. No network premise is required. -/
theorem path_in_voterTree_of_frozen_target {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (w : V) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon) (target b : Block)
    (htarget : target ∈ (Run.stateBeforeTime (sapc p) rho (freezeTime p r) w).base.blocks)
    (hn : b ≠ .genesis) (hp : Block.Preceq b target) :
    b ∈ GridCO.voterTree p.engine (headState p rho (r + 1) w).base (r + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  have hb := (paths_at_fold p _ w).1 target htarget b hn hp
  apply List.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · simp only [headState, clock_blocks]
    apply (time_input_base_receiptPrefix p E rho hs _ _ ?_ w).blocks.subset hb
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  · apply Bool.or_eq_true_iff.mpr
    left
    simp only [Nat.add_sub_cancel, headState_base_frozenAt p E rho hs hΔ r w hw hh]
    rw [(base_freezeView_at_input p E rho hs r w).2]
    exact decide_eq_true hb

/-- The ordinary frozen domain contains every non-genesis ancestor of
an early resolved target, including at sleeping readers. -/
theorem early_path_in_voterTree {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hrelay : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (o : GridCO.Wire p.n) (target b : Block) (ht : GridCO.headTarget? o = some target)
    (ho : o ∈ GridCO.earlyVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r)
    (hn : b ≠ .genesis) (hp : Block.Preceq b target) :
    b ∈ GridCO.voterTree p.engine (headState p rho (r + 1) w).base (r + 1) := by
  have hef : earlyTime p r ≤ freezeTime p r := by
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have htarget := strict_block_relay p E rho hs _ _ hef hrelay v w hv hw target
    (early_head_at_early p E rho hs hΔ r v o target ht ho).2
  exact path_in_voterTree_of_frozen_target p E rho hs hΔ r w hw hh target b htarget hn hp

/-- A genuine result has positive surviving support. One such receipt
supplies its whole next-duty path through the ordinary frozen domain. -/
theorem genuine_path_in_voterTree {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hrelay : RelayBy p rho (earlyTime p r) (freezeTime p r)) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c) (hn : b ≠ .genesis) :
    b ∈ GridCO.voterTree p.engine (headState p rho (r + 1) w).base (r + 1) := by
  have hmajor := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r c hc
  have hmono := GridCO.prefixSupport_mono p.engine
    (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r b c hp
  have hpos : 0 < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r b := by omega
  rw [GridCO.prefixSupport_eq_card] at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨o, ho, _, target, ht, hp⟩ := GridCO.prefixSupportSeats_witness p.engine _ r b i hi
  exact early_path_in_voterTree p E rho hs hΔ r v w hv hw hh hrelay o target b ht
    (List.mem_filter.mp ho).1 hn hp

/-- The shared SA walk theorem transfers any genuine prefix from a
compatible finite root. PCs have not yet been applied in this result. -/
theorem genuine_ordinary_head_covers_of_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : BackReceipts p rho r v w) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (GridCO.forkChoice (headState p rho (r + 1) w).base
      (GridCO.voterTree p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1)) (r + 1)) := by
  exact @GridCO.forkChoice_covers_of_transfer GridCO.slowLeasePolicy p.n p.engine _ _ r
    (r + 1) _ _ _ b c hc hp
    (genuine_transfer_receipts_of_back_receipts p E rho hx hΔ r v w hv hw hh hforward hback b) hr
    (fun a hn ha => genuine_path_in_voterTree p E rho hx.toScheduleWellFormed hΔ
      r v w hv hw hh hforward a c hc (GridCO.prefix_trans a b c ha hp) hn)

theorem genuine_ordinary_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : RelayBy p rho (voteTime p (r + 1)) (gateTime p r)) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (GridCO.forkChoice (headState p rho (r + 1) w).base
      (GridCO.voterTree p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterView p.engine (headState p rho (r + 1) w).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) w).base (r + 1)) (r + 1)) :=
  genuine_ordinary_head_covers_of_back_receipts p E rho hx hΔ r v w hv hw hh hforward
    (voter_raw_at_gate p E rho hx.toScheduleWellFormed r v w hv hw hback) b c hc hp hr

/-- With compatible finite and selected-PC roots, the shared genuine
majority controls both choices. This statement does not require an F4
score or a fault cap. -/
theorem choice_covers_of_genuine_transfer (p : Params) {n : Nat}
    (source : GridCO.State n) (st : State n) (r current : Slot)
    (tree : List Block) (raw support : List (GridCO.Wire n)) (b c : Block)
    (cert : Option (PC n)) (hc : SA.confirmation p source r = some c)
    (hp : Block.Preceq b c)
    (ht : GridCO.TransferReceipts p.engine source r st.base.blocks raw support b)
    (hpath : ∀ a, a ≠ .genesis → Block.Preceq a b → a ∈ tree)
    (hr : Block.Compatible (GridCO.liveRoot st.base) b)
    (hcert : ∀ pc, cert = some pc → Block.Compatible pc.target b) :
    Block.Preceq b (choice p st tree raw support current cert) := by
  have hm : GridCO.voterCount (GridCO.lateVotes p.engine source r) <
      2 * GridCO.prefixSupport p.engine source r b := by
    have hmajor := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine n source r c hc
    have hmono := GridCO.prefixSupport_mono p.engine source r b c hp
    omega
  obtain ⟨helig, hdom⟩ := ht.majority hm
  have walk (root : Block) (hroot : Block.Compatible root b) :
      Block.Preceq b (GridCO.ghost root tree (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support current)) := by
    apply GridCO.ghost_covers_of_path_dominance tree _ _ root b hroot hpath
    · intro a _ hab
      have hmono := GridCO.goldfishScore_prefix_mono st.base.blocks raw support a b hab
      exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (by omega)))
    · intro a _ hab d _ hparent _ hne
      have hconf := GridCO.conflict_mono_descendant a b d hab
        (GridCO.siblings_incompatible d a hparent hne)
      have hconf' : Block.compatible b d = false := by
        simpa [Block.compatible, Bool.or_comm] using hconf
      exact (hdom d hconf').trans_le
        (GridCO.goldfishScore_prefix_mono st.base.blocks raw support a b hab)
  have hf : Block.Compatible (floor p st tree raw support current) b := by
    by_cases hz : floor p st tree raw support current = .genesis
    · rw [hz]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))
    · exact GridCO.ancestors_compatible _ _ _
        (floor_properties p st tree raw support current hz).2.1
        (walk .genesis (Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))))
  have ha : Block.Compatible
      (preliminaryAnchor (floor p st tree raw support current) cert) b := by
    cases cert with
    | none => exact hf
    | some pc =>
        simp only [preliminaryAnchor]
        split
        · exact hcert pc rfl
        · exact hf
  unfold choice
  split
  · exact walk _ hr
  · apply walk
    unfold mandatoryRoot
    split <;> assumption

/-- PC compatibility is needed only in active mode. Disabled transfer
uses the shared SA proof on the retained base state. -/
theorem genuine_activePC_head_covers_of_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : BackReceipts p rho r v w) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    (hcert : capBroken p (headState p rho (r + 1) w) = false →
      ∀ pc, selectedPC p (headState p rho (r + 1) w) (r + 1) = some pc →
      Block.Compatible pc.target b) :
    Block.Preceq b (headData p rho (r + 1) w).target := by
  cases ha : capBroken p (headState p rho (r + 1) w) with
  | true =>
      simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, decide_false, Bool.false_eq_true, ↓reduceIte, ha, choice] using!
        genuine_ordinary_head_covers_of_back_receipts p E rho hx hΔ r v w hv hw
          hh hforward hback b c hc hp hr
  | false =>
      have h := choice_covers_of_genuine_transfer p
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base
        (headState p rho (r + 1) w) r (r + 1)
        (activeVoterTree p (headState p rho (r + 1) w) (r + 1)
          (selectedPC p (headState p rho (r + 1) w) (r + 1))) _ _ b c
        (selectedPC p (headState p rho (r + 1) w) (r + 1)) hc hp
        (genuine_transfer_receipts_of_back_receipts p E rho hx hΔ r v w hv hw hh hforward hback b)
        (fun a hn hab => activeVoterTree_contains_plain p _ _ _
          (genuine_path_in_voterTree p E rho hx.toScheduleWellFormed hΔ r v w hv hw hh
            hforward a c hc (GridCO.prefix_trans a b c hab hp) hn)) hr (hcert ha)
      simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, decide_false, Bool.false_eq_true, ↓reduceIte, ha] using! h

/-- Low genuine support also transfers to the actual HEAD when the
joint invariant supplies compatibility of the selected PC and finite root. -/
theorem genuine_compatiblePC_head_covers_of_back_receipts {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : BackReceipts p rho r v w) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    (hcert : ∀ pc, selectedPC p (headState p rho (r + 1) w) (r + 1) = some pc →
      Block.Compatible pc.target b) :
    Block.Preceq b (headData p rho (r + 1) w).target :=
  genuine_activePC_head_covers_of_back_receipts p E rho hx hΔ r v w hv hw hh hforward
    hback b c hc hp hr (fun _ => hcert)

theorem genuine_compatiblePC_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : RelayBy p rho (voteTime p (r + 1)) (gateTime p r)) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b)
    (hcert : ∀ pc, selectedPC p (headState p rho (r + 1) w) (r + 1) = some pc →
      Block.Compatible pc.target b) :
    Block.Preceq b (headData p rho (r + 1) w).target :=
  genuine_compatiblePC_head_covers_of_back_receipts p E rho hx hΔ r v w hv hw hh hforward
    (voter_raw_at_gate p E rho hx.toScheduleWellFormed r v w hv hw hback) b c hc hp hr hcert

/-- Genuine support above f drives F4 through its prefix for any
selected PC. In disabled mode the same result follows from plain SA.
Finite-root compatibility remains a source-support obligation. -/
theorem genuine_highSupport_head_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : RelayBy p rho (voteTime p (r + 1)) (gateTime p r)) (b c : Block)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some c)
    (hp : Block.Preceq b c)
    (hsupport : pcFaultCap p < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r b)
    (hr : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) b) :
    Block.Preceq b (headData p rho (r + 1) w).target := by
  cases ha : capBroken p (headState p rho (r + 1) w) with
  | true =>
      simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, decide_false, Bool.false_eq_true, ↓reduceIte, ha, choice] using!
        genuine_ordinary_head_covers p E rho hx hΔ r v w hv hw hh hforward hback b c hc hp hr
  | false =>
      by_cases hg : b = .genesis
      · rw [hg]; exact GridCO.genesis_prefix _
      let st := headState p rho (r + 1) w
      let cert := selectedPC p st (r + 1)
      have hpath : ∀ a, a ≠ .genesis → Block.Preceq a b →
          a ∈ activeVoterTree p st (r + 1) cert := by
        intro a hn hab
        exact activeVoterTree_contains_plain p st (r + 1) cert
          (genuine_path_in_voterTree p E rho hx.toScheduleWellFormed hΔ r v w hv hw hh
            hforward a c hc (GridCO.prefix_trans a b c hab hp) hn)
      have ht := genuine_transfer_receipts p E rho hx hΔ r v w hv hw hh hforward hback b
      have hscore : pcFaultCap p < GridCO.goldfishScore st.base.blocks
          (GridCO.voterView p.engine st.base (r + 1))
          (GridCO.voterSupportView p.engine st.base (r + 1)) b := by
        apply hsupport.trans_le
        rw [GridCO.prefixSupport_eq_card, GridCO.goldfishScore_eq_card]
        exact Finset.card_le_card ht.supporters_subset
      have hwalk := @GridCO.forkChoice_covers_of_transfer GridCO.slowLeasePolicy p.n p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base
        { st.base with obligations := [] } r (r + 1) (activeVoterTree p st (r + 1) cert)
        (GridCO.voterView p.engine st.base (r + 1))
        (GridCO.voterSupportView p.engine st.base (r + 1)) b c hc hp ht
        (Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))) hpath
      have hchoice := choice_covers_of_ordinary_floor p st _ _ _ (r + 1) cert b ha
        (activeVoterTree_subset p st _ cert (hpath b hg (GridCO.block_preceq_self b))) hg
        hwalk hscore hr
      simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, decide_false, Bool.false_eq_true, ↓reduceIte, ha] using! hchoice

/-- Raw genuine results at one healthy label are compatible, before
either gate guard and in any mix of active and disabled readers. -/
theorem sameLabel_from_engine {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon)
    (hforward : RelayBy p rho (earlyTime p r) (freezeTime p r))
    (hback : RelayBy p rho (voteTime p (r + 1)) (gateTime p r)) (b c : Block)
    (hb : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b)
    (hc : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) w).base r = some c) :
    Block.Compatible b c := by
  have tb := genuine_transfer_receipts p E rho hx hΔ r v w hv hw hh hforward hback b
  have tc := genuine_transfer_receipts p E rho hx hΔ r w w hw hw hh hforward hback c
  have mb := tb.majority
    (@GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r b hb)
  have mc := tc.majority
    (@GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r c hc)
  cases he : Block.compatible b c with
  | true => exact he
  | false =>
      have he' : Block.compatible c b = false := by
        simpa [Block.compatible, Bool.or_comm] using he
      have := mb.2 c he
      have := mc.2 b he'
      omega

end AvailableChain.SAPC
end

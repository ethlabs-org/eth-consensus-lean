module
public import AvailableChainSAPC.Proofs.Assembly
public import AvailableChainSAPC.Proofs.Paths
public import AvailableChainSAPC.Proofs.ReceiptRelay

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- An accepted-object relay bound for evidence present by one source
read. Both fixed contract relay premises imply this proof interface. -/
def RelayBy {V : Type} [DecidableEq V] (p : Params) (rho : Run V (sapc p))
    (source deadline : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ i o t, t ≤ source → Run.acceptsAt (sapc p) rho i v o t →
    ∀ w ∈ rho.honest,
      (sapc p).processed (Run.stateBefore (sapc p) rho (i + 1) w) o = false →
      ∃ t' < deadline, ∃ j, Run.acceptsAt (sapc p) rho j w o t'

theorem healthy_relayBy {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (cut source : Time)
    (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut) (hcut : source + E.Δ ≤ cut) :
    RelayBy p rho source (source + E.Δ) := by
  intro v hv i o t ht ha w hw hn
  obtain ⟨t', _, htime, j, hj⟩ := hrelay v hv i o t ha w hw hn
    ((Int.add_le_add_right ht E.Δ).trans hcut)
  exact ⟨t', htime.trans_le (Int.add_le_add_right ht E.Δ), j, hj⟩

theorem synchronous_relayBy {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (source : Time) (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (horizon : max source E.t_GST + E.Δ ≤ rho.horizon) :
    RelayBy p rho source (max source E.t_GST + E.Δ) := by
  intro v hv i o t ht ha w hw hn
  have hmax := max_le_max_right E.t_GST ht
  obtain ⟨t', _, htime, j, hj⟩ := hrelay v hv i o t ha w hw hn
    ((Int.add_le_add_right hmax E.Δ).trans horizon)
  exact ⟨t', htime.trans_le (Int.add_le_add_right hmax E.Δ), j, hj⟩

/-- Relayed evidence includes signatures carried by accepted proposals
or envelopes. The proof uses the first actual accepted call. -/
theorem read_head_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source deadline : Time)
    (ht : source < deadline) (hrelay : RelayBy p rho source deadline)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (o : HeadWire p.n)
    (ho : o ∈ (Run.readAt (sapc p) rho source v).receivedHeads) :
    o ∈ (Run.stateBeforeTime (sapc p) rho deadline w).receivedHeads := by
  rw [readAt_eq_stateBefore hs] at ho
  obtain ⟨i, hi, t, ha⟩ := stored_head_accepted p rho _ v o ho
  obtain ⟨parent, he, _⟩ := ha.1
  have htime : t ≤ source := (index_lt_read_length_iff hs source he).mp hi
  by_cases hm : o ∈ (Run.stateBefore (sapc p) rho (i + 1) w).receivedHeads
  · rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_archive_mono p rho (v := w) _ hm
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (deadline - 1) he).mpr
      (Int.le_sub_one_iff.mpr (htime.trans_lt ht)))
  · obtain ⟨t', ht', j, hj⟩ := hrelay v hv i (fromHead o) t htime ha w hw
      (by simpa [sapc, processed, fromHead] using hm)
    exact accepted_head_before_cut p E rho hs j w o t' deadline hj ht'

theorem read_block_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source deadline : Time)
    (ht : source < deadline) (hrelay : RelayBy p rho source deadline)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (b : Block)
    (hb : b ∈ (Run.readAt (sapc p) rho source v).base.blocks) :
    b ∈ (Run.stateBeforeTime (sapc p) rho deadline w).base.blocks := by
  by_cases hg : b = .genesis
  · subst b
    exact (paths_at_fold p _ w).2.1
  rw [readAt_eq_stateBefore hs] at hb
  obtain ⟨i, hi, t, o, raw, support, c, he, hp, ha⟩ := stored_block_accepted p rho _ v b hg hb
  have htime : t ≤ source := (index_lt_read_length_iff hs source he).mp hi
  by_cases hm : b ∈ (Run.stateBefore (sapc p) rho (i + 1) w).base.blocks
  · rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_blocks_mono p rho (v := w) _ hm
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (deadline - 1) he).mpr
      (Int.le_sub_one_iff.mpr (htime.trans_lt ht)))
  · obtain ⟨t', ht', j, hj⟩ := hrelay v hv i o t htime ha w hw
      (by simpa [sapc, processed, hp, GridCO.blockKnown] using hm)
    exact accepted_block_before_cut p E rho hs j w o b raw support c hp t' deadline hj ht'

/-- Healthy relay makes a detected cap breach common before the next
Δ deadline, including evidence from old labels and unresolved targets. -/
theorem capBroken_healthy_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (cut source : Time)
    (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut) (hcut : source + E.Δ ≤ cut)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hbroken : capBroken p (Run.readAt (sapc p) rho source v) = true) :
    capBroken p (Run.stateBeforeTime (sapc p) rho (source + E.Δ) w) = true := by
  apply capBroken_mono p _ _ _ hbroken
  exact read_head_relay p E rho hs source (source + E.Δ) (by linarith [E.Δ_pos])
    (healthy_relayBy p E rho cut source hrelay hcut) v w hv hw

theorem capBroken_synchronous_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source : Time)
    (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (horizon : max source E.t_GST + E.Δ ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hbroken : capBroken p (Run.readAt (sapc p) rho source v) = true) :
    capBroken p (Run.stateBeforeTime (sapc p) rho (max source E.t_GST + E.Δ) w) = true := by
  have ht : source < max source E.t_GST + E.Δ := by
    have := le_max_left source E.t_GST
    linarith [E.Δ_pos]
  apply capBroken_mono p _ _ _ hbroken
  exact read_head_relay p E rho hs source _ ht
    (synchronous_relayBy p E rho source hrelay horizon) v w hv hw

theorem pathKnown_mem {n : Nat} (st : State n) (b : Block) (hb : pathKnown st b = true) :
    b ∈ st.base.blocks := by
  cases b with
  | genesis => exact of_decide_eq_true hb
  | node parent s r_s root => exact of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1

/-- The accepted-object premise transfers the full PC, including every
admitted path. Gossip timing and the reader's awake status are not needed. -/
theorem read_pc_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source deadline : Time)
    (ht : source < deadline) (hrelay : RelayBy p rho source deadline)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (c : PC p.n)
    (hc : pcValid p (Run.readAt (sapc p) rho source v) c = true) :
    pcValid p (Run.stateBeforeTime (sapc p) rho deadline w) c = true := by
  have hwell := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  have hpaths := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  have hheads := (Bool.and_eq_true_iff.mp hc).2
  have path (b : Block) (hb : pathKnown (Run.readAt (sapc p) rho source v) b = true) :
      pathKnown (Run.stateBeforeTime (sapc p) rho deadline w) b = true :=
    stored_pathKnown_at_fold p _ w b
      (read_block_relay p E rho hs source deadline ht hrelay v w hv hw b (pathKnown_mem _ b hb))
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hwell, ?_⟩, ?_⟩
  · exact Bool.and_eq_true_iff.mpr ⟨path c.target (Bool.and_eq_true_iff.mp hpaths).1,
      List.all_eq_true.mpr (fun o ho => path o.payload.target
        (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hpaths).2 o ho))⟩
  · exact List.all_eq_true.mpr (fun o ho => by
      simpa using read_head_relay p E rho hs source deadline ht hrelay v w hv hw o
        (of_decide_eq_true (List.all_eq_true.mp hheads o ho)))

/-- Before the healthy relay deadline, every honest reader has the PC
evidence and a stored certificate of at least its rank. This alone does
not prove compatible targets or sound strong arming. -/
theorem installedPC_healthy_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (cut source : Time)
    (hrelay : HealthyAcceptedObjectRelay (sapc p) E rho cut) (hcut : source + E.Δ ≤ cut)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (c : PC p.n)
    (hc : (Run.readAt (sapc p) rho source v).bestPC = some c) :
    pcValid p (Run.stateBeforeTime (sapc p) rho (source + E.Δ) w) c = true ∧
      ∃ d, (Run.stateBeforeTime (sapc p) rho (source + E.Δ) w).bestPC = some d ∧
        c.slot ≤ d.slot := by
  have hvalid := read_pc_relay p E rho hs source (source + E.Δ) (by linarith [E.Δ_pos])
    (healthy_relayBy p E rho cut source hrelay hcut) v w hv hw c
    (installedPC_valid_at_read p rho v source c hc)
  exact ⟨hvalid, PCComplete_at_fold p _ w c hvalid⟩

theorem installedPC_synchronous_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source : Time)
    (hrelay : AcceptedObjectRelay (sapc p) E rho)
    (horizon : max source E.t_GST + E.Δ ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (c : PC p.n)
    (hc : (Run.readAt (sapc p) rho source v).bestPC = some c) :
    pcValid p (Run.stateBeforeTime (sapc p) rho (max source E.t_GST + E.Δ) w) c = true ∧
      ∃ d, (Run.stateBeforeTime (sapc p) rho (max source E.t_GST + E.Δ) w).bestPC = some d ∧
        c.slot ≤ d.slot := by
  have ht : source < max source E.t_GST + E.Δ := by
    have := le_max_left source E.t_GST
    linarith [E.Δ_pos]
  have hvalid := read_pc_relay p E rho hs source _ ht
    (synchronous_relayBy p E rho source hrelay horizon) v w hv hw c
    (installedPC_valid_at_read p rho v source c hc)
  exact ⟨hvalid, PCComplete_at_fold p _ w c hvalid⟩

end AvailableChain.SAPC
end

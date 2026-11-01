module
public import AvailableChainSAPC.Proofs.RecoveryService

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Supported source rows cannot veto a synchronous raw result after
the boundary. This checks the actual pre-gate clock, including expiry. -/
theorem recovery_gate_finite_guard_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (s : Slot) (start : voteTime p boundary ≤ gateTime p s)
    (sync : E.t_GST ≤ voteTime p s) (horizon : gateTime p s ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some C) :
    (clockPreGate p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v)
      (gateTime p s)).base.obligations.any (fun (K, _, _) => !Block.compatible K C) = false := by
  apply List.any_eq_false.mpr
  rintro ⟨K, g, d⟩ row
  obtain ⟨r, before, support⟩ := recovery_preGate_row_support p E rho h.execution
    boundary sources (gateTime p s) start v hv K g d row
  have lt : r < s := by
    by_contra hn
    exact (not_lt.mpr ((GridCO.gateTime_le_iff p.engine s r).mpr
      (Nat.le_of_not_gt hn))) before
  have eq : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.zero_le r |>.trans_lt lt)
  have cover := support (s - 1) (Nat.le_sub_one_of_lt lt)
    (((GridCO.gateTime_le_iff p.engine (s - 1) s).mpr (Nat.sub_le s 1)).trans horizon)
  simp only [RecoveryHeadCovers, eq] at cover
  have early : voteTime p s ≤ earlyTime p s ∧ earlyTime p s ≤ gateTime p s := by
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ ∧
      4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  obtain ⟨D, rawD, below⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay s sync (early.2.trans horizon)
    (recovery_awake_majority_quorum p E rho G h _ sync (early.1.trans (early.2.trans horizon)))
    K cover v hv
  have eq : D = C := Option.some.inj (rawD.symm.trans raw)
  subst D
  have compatible : Block.compatible K C = true := Bool.or_eq_true_iff.mpr (Or.inl below)
  simp [compatible]

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_gate_finite_guard {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (s : Slot) (start : voteTime p boundary ≤ gateTime p s)
    (sync : E.t_GST ≤ voteTime p s) (horizon : gateTime p s ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some C) :
    (clockPreGate p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v)
      (gateTime p s)).base.obligations.any (fun (K, _, _) => !Block.compatible K C) = false := by
  apply List.any_eq_false.mpr
  rintro ⟨K, g, d⟩ row
  obtain ⟨r, before, support⟩ := recovery_preGate_row_support p E rho h.execution
    boundary sources (gateTime p s) start v hv K g d row
  have lt : r < s := by
    by_contra hn
    exact (not_lt.mpr ((GridCO.gateTime_le_iff p.engine s r).mpr
      (Nat.le_of_not_gt hn))) before
  have eq : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.zero_le r |>.trans_lt lt)
  have cover := support (s - 1) (Nat.le_sub_one_of_lt lt)
    (((GridCO.gateTime_le_iff p.engine (s - 1) s).mpr (Nat.sub_le s 1)).trans horizon)
  simp only [RecoveryHeadCovers, eq] at cover
  have early : voteTime p s ≤ earlyTime p s ∧ earlyTime p s ≤ gateTime p s := by
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ ∧
      4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  obtain ⟨D, rawD, below⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay s sync (early.2.trans horizon)
    (recovery_awake_majority p E rho G h _ sync (early.1.trans (early.2.trans horizon)))
    K cover v hv
  have eq : D = C := Option.some.inj (rawD.symm.trans raw)
  subst D
  have compatible : Block.compatible K C = true := Bool.or_eq_true_iff.mpr (Or.inl below)
  simp [compatible]

/-- With both guards open, the stable record is the ordinary SA advance.
The additional PC lease filter cannot change that record. -/
theorem gateWithPC_stable_advance (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (cert : Option (PC n)) (B : Block)
    (raw : SA.confirmation p st r = some B)
    (finite : st.obligations.any (fun (K, _, _) => !Block.compatible K B) = false)
    (pc : pcOK cert B = true) :
    (gateWithPC p st r cert).stableRecord = GridCO.advance st.stableRecord B := by
  have fold (base : GridCO.State n) (prefixes : List Block) (levels : Block → List Nat) :
      (prefixes.foldl (fun acc b => (levels b).foldl (fun acc g =>
        GridCO.writeObligation acc b g (gateTime p r + lifetime p)) acc) base).stableRecord =
          base.stableRecord :=
    fold_field GridCO.State.stableRecord _
      (fun _ _ => fold_field GridCO.State.stableRecord _ (by intros; rfl) _ _) _ _
  cases cert <;> simp only [gateWithPC, SA.gate, GridCO.gate, raw, finite,
    Bool.false_eq_true, ↓reduceIte]
  · exact fold _ _ _
  · rw [fold]
    simp only [pc, ↓reduceIte]

/-- A current-slot block cannot be below a record from an earlier gate. -/
theorem fresh_proposal_not_below_gate_record {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (positive : 0 < s) (B : Block) (slot : B.slot = s) (v : V) :
    Block.preceq B (stable (Run.stateBeforeTime (sapc p) rho (gateTime p s) v)) = false := by
  apply Bool.eq_false_iff.mpr
  intro below
  rw [time_input_eq_event_prefix p E rho hs] at below
  rcases run_stable_origin p rho _ v with gen | ⟨i, hi, r, tick, raw⟩
  · rw [gen] at below
    have bound := GridCO.slot_le_of_prefix B .genesis (by trivial) below
    rw [slot] at bound
    change s ≤ 0 at bound
    exact (Nat.not_le_of_lt positive) bound
  · have before : gateTime p r < gateTime p s :=
      Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (gateTime p s - 1) tick).mp hi)
    have lt : r < s := by
      by_contra hn
      exact (not_lt.mpr ((GridCO.gateTime_le_iff p.engine s r).mpr
        (Nat.le_of_not_gt hn))) before
    have ordered := (paths_at_fold p (rho.events.take i) v).2.2
    have resultOrdered : GridCO.SlotOrdered (stable (Run.stateBefore (sapc p) rho
        (rho.events.filter (fun e => decide (e.time ≤ gateTime p s - 1))).length v)) := by
      rcases @GridCO.confirmation_mem GridCO.slowLeasePolicy p.engine p.n _ r _ raw with
        gen | stored
      · rw [gen]; trivial
      · exact ordered _ stored
    have bound := @GridCO.confirmation_slot_le GridCO.slowLeasePolicy p.engine p.n _ r _ ordered raw
    have le := GridCO.slot_le_of_prefix _ _ resultOrdered below
    rw [slot] at le
    exact (Nat.not_le_of_lt lt) (le.trans bound)

/-- Fresh common raw service and a matching PC repair S at the actual
public gate. Equal-time deliveries cannot undo the stable write. -/
theorem recovery_gate_repairs_record_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (s : Slot) (positive : 0 < s) (start : voteTime p boundary ≤ gateTime p s)
    (sync : E.t_GST ≤ voteTime p s) (horizon : gateTime p s ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (slot : B.slot = s)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B)
    (c : PC p.n) (selected : (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).bestPC = some c)
    (target : c.target = B) : stable (Run.readAt (sapc p) rho (gateTime p s) v) = B := by
  set_option backward.isDefEq.respectTransparency false in
  let st := Run.stateBeforeTime (sapc p) rho (gateTime p s) v
  let pre := clockPreGate p st (gateTime p s)
  have pub : PublicTime E (gateTime p s) := by
    refine ⟨4 * s + 6, ?_⟩
    change 4 * p.Δ * (s : Time) + 6 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ gateTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have tick := h.execution.tick_total v hv _ pub nonneg horizon
  rw [read_stable_eq_clock p E rho h.execution.toScheduleWellFormed v _ tick, clock_at_gate]
  have rawPre : SA.confirmation p pre.base s = some B := by
    rw [clockPreGate_base]
    exact (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
      _ st.base (GridCO.clockPreGate_receiptData p.engine st.base _)
      (base_receiptStamped_at_fold p _ v)
      s).trans raw
  have pc : pcOK (if capBroken p pre then none else pre.bestPC) B = true := by
    have selectedPre : pre.bestPC = some c := (clockPreGate_pcData p st _).1.trans selected
    split
    · rfl
    · simp only [pcOK, selectedPre, target]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.block_preceq_self B))
  have value := gateWithPC_stable_advance p pre.base s _ B rawPre
    (recovery_gate_finite_guard_quorum p E rho hΔ G h boundary sources s start sync horizon v hv B
      raw) pc
  change (gateWithPC p pre.base s _).stableRecord = B
  rw [value, GridCO.advance]
  have fresh := fresh_proposal_not_below_gate_record p E rho h.execution.toScheduleWellFormed
    s positive B slot v
  have preRecord : pre.base.stableRecord = stable st := by
    rw [clockPreGate_base, GridCO.clockPreGate_stable]
    rfl
  rw [preRecord, fresh]
  rfl

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_gate_repairs_record {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (s : Slot) (positive : 0 < s) (start : voteTime p boundary ≤ gateTime p s)
    (sync : E.t_GST ≤ voteTime p s) (horizon : gateTime p s ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (slot : B.slot = s)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B)
    (c : PC p.n) (selected : (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).bestPC = some c)
    (target : c.target = B) : stable (Run.readAt (sapc p) rho (gateTime p s) v) = B := by
  set_option backward.isDefEq.respectTransparency false in
  let st := Run.stateBeforeTime (sapc p) rho (gateTime p s) v
  let pre := clockPreGate p st (gateTime p s)
  have pub : PublicTime E (gateTime p s) := by
    refine ⟨4 * s + 6, ?_⟩
    change 4 * p.Δ * (s : Time) + 6 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ gateTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have tick := h.execution.tick_total v hv _ pub nonneg horizon
  rw [read_stable_eq_clock p E rho h.execution.toScheduleWellFormed v _ tick, clock_at_gate]
  have rawPre : SA.confirmation p pre.base s = some B := by
    rw [clockPreGate_base]
    exact (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
      _ st.base (GridCO.clockPreGate_receiptData p.engine st.base _)
      (base_receiptStamped_at_fold p _ v)
      s).trans raw
  have pc : pcOK (if capBroken p pre then none else pre.bestPC) B = true := by
    have selectedPre : pre.bestPC = some c := (clockPreGate_pcData p st _).1.trans selected
    split
    · rfl
    · simp only [pcOK, selectedPre, target]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.block_preceq_self B))
  have value := gateWithPC_stable_advance p pre.base s _ B rawPre
    (recovery_gate_finite_guard p E rho hΔ G h boundary sources s start sync horizon v hv B raw) pc
  change (gateWithPC p pre.base s _).stableRecord = B
  rw [value, GridCO.advance]
  have fresh := fresh_proposal_not_below_gate_record p E rho h.execution.toScheduleWellFormed
    s positive B slot v
  have preRecord : pre.base.stableRecord = stable st := by
    rw [clockPreGate_base, GridCO.clockPreGate_stable]
    rfl
  rw [preRecord, fresh]
  rfl

end AvailableChain.SAPC
end

module
public import AvailableChainSAPC.Proofs.RecoveryRepair
public import AvailableChainGridCO.Proofs.RepairedHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A gate either retains the preceding gate record or has the current
raw result as its record. No clean-prefix or PC premise is required. -/
theorem recovery_record_step {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hs : ScheduleWellFormed E rho) (s : Slot) (pos : 0 < s)
    (horizon : gateTime p s ≤ rho.horizon) (v : V) (hv : v ∈ rho.honest) :
    stable (Run.readAt (sapc p) rho (gateTime p s) v) =
        stable (Run.readAt (sapc p) rho (gateTime p (s - 1)) v) ∨
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s =
        some (stable (Run.readAt (sapc p) rho (gateTime p s) v)) := by
  have pub : PublicTime E (gateTime p s) := by
    refine ⟨4 * s + 6, ?_⟩
    change 4 * p.Δ * (s : Time) + 6 * p.Δ = _
    rw [hΔ]; push_cast; ring
  have nonneg : 0 ≤ gateTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have tick := hs.tick_total v hv _ pub nonneg horizon
  rw [read_stable_eq_clock p E rho hs v _ tick]
  rcases clock_stable_cases p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v) _
    (base_receiptStamped_at_fold p _ v) with old | ⟨r, time, raw⟩
  · left
    rw [old]
    have input : Run.stateBeforeTime (sapc p) rho (gateTime p s) =
        Run.readAt (sapc p) rho (gateTime p s - 1) := by
      simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
    rw [input]
    have eq : s - 1 + 1 = s := Nat.sub_add_cancel pos
    apply read_stable_eq_latest_gate p E rho hs (s - 1) (gateTime p s - 1) _ _ v
    · have cast : ((s - 1 : Nat) : Time) + 1 = s := by exact_mod_cast eq
      change 4 * p.Δ * ((s - 1 : Nat) : Time) + 6 * p.Δ ≤
        4 * p.Δ * (s : Time) + 6 * p.Δ - 1
      have one : 1 ≤ p.Δ := Int.add_one_le_iff.mpr p.deltaPos
      nlinarith
    · rw [eq]; exact sub_lt_self _ (by norm_num)
  · have eq : r = s := Nat.le_antisymm
      ((GridCO.gateTime_le_iff p.engine r s).mp time.ge)
      ((GridCO.gateTime_le_iff p.engine s r).mp time.le)
    subst r
    exact Or.inr raw

/-- SA's repaired-record induction applies to SA-PC's retained or raw
record steps. Ordered raw history supplies safety at all later reads. -/
theorem recovery_safe_from_repaired_gate_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sync : E.t_GST ≤ proposalTime p boundary)
    (sources : RecoverySourcesSupported p rho boundary)
    (repair : Slot) (start : boundary ≤ repair) (B : Block)
    (records : ∀ v ∈ rho.honest,
      stable (Run.readAt (sapc p) rho (gateTime p repair) v) = B)
    (raw : ∀ v ∈ rho.honest,
      SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p repair) v).base repair = some B) :
    SafeFrom (sapc p) rho (sapcInterface p).stable (gateTime p repair) := by
  let result := fun s v =>
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s
  let record := fun s v => stable (Run.readAt (sapc p) rho (gateTime p s) v)
  let valid := fun s => gateTime p s ≤ rho.horizon
  have down (r s : Slot) (le : r ≤ s) (bound : valid s) : valid r :=
    ((GridCO.gateTime_le_iff p.engine r s).mpr le).trans bound
  have syncVote (s : Slot) (lo : boundary ≤ s) : E.t_GST ≤ voteTime p s := by
    have time := (GridCO.proposalTime_le_iff p.engine boundary s).mpr lo
    apply sync.trans
    change 4 * p.Δ * (boundary : Time) ≤ 4 * p.Δ * (s : Time) + p.Δ
    change 4 * p.Δ * (boundary : Time) ≤ 4 * p.Δ * (s : Time) at time
    linarith [p.deltaPos]
  have step (v : V) (hv : v ∈ rho.honest) (s : Slot) (lo : repair < s) (bound : valid s) :
      record s v = record (s - 1) v ∨ result s v = some (record s v) :=
    recovery_record_step p E rho hΔ h.execution.toScheduleWellFormed s
      (Nat.zero_le repair |>.trans_lt lo) bound v hv
  have initial (v : V) (hv : v ∈ rho.honest) : result repair v = some (record repair v) := by
    dsimp only [result, record]
    rw [records v hv]
    exact raw v hv
  have origin (s : Slot) (lo : repair ≤ s) (bound : valid s) (v : V) (hv : v ∈ rho.honest) :
      ∃ r, repair ≤ r ∧ r ≤ s ∧ result r v = some (record s v) :=
    GridCO.repaired_record_source (fun s => result s v) (fun s => record s v) valid down
      repair (initial v hv) (step v hv) s lo bound
  have ordered (r s : Slot) (lo : repair ≤ r) (lt : r < s) (bound : valid s)
      (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (C D : Block)
      (rawC : result r v = some C) (rawD : result s w = some D) : Block.Preceq C D :=
    recovery_genuine_prefix_quorum p E rho hΔ G hG h boundary sources r s (start.trans lo) lt
      (syncVote r (start.trans lo)) bound v w hv hw C D rawC rawD
  have monotone (r s : Slot) (lo : repair ≤ r) (le : r ≤ s) (bound : valid s)
      (v : V) (hv : v ∈ rho.honest) : Block.Preceq (record r v) (record s v) :=
    GridCO.repaired_record_prefix (fun s => result s v) (fun s => record s v) valid down
      repair (initial v hv) (step v hv)
      (fun a b hlo hlt hh C D hc hd => ordered a b hlo hlt hh v v hv hv C D hc hd)
      r s lo le bound
  have compatible (r s : Slot) (loR : repair ≤ r) (loS : repair ≤ s)
      (hr : valid r) (hs : valid s) (u v : V) (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
      Block.Compatible (record r u) (record s v) := by
    obtain ⟨a, loA, hiA, rawA⟩ := origin r loR hr u hu
    obtain ⟨b, loB, hiB, rawB⟩ := origin s loS hs v hv
    rcases lt_trichotomy a b with lt | eq | lt
    · exact Bool.or_eq_true_iff.mpr (Or.inl
        (ordered a b loA lt (down b s hiB hs) u v hu hv _ _ rawA rawB))
    · subst b
      have early : E.t_GST ≤ earlyTime p a := by
        apply (syncVote a (start.trans loA)).trans
        change 4 * p.Δ * (a : Time) + p.Δ ≤ 4 * p.Δ * (a : Time) + 2 * p.Δ
        linarith [p.deltaPos]
      exact synchronous_sameLabel p E rho h.execution hΔ h.acceptedRelay a early
        (down a r hiA hr) u v hu hv _ _ rawA rawB
    · exact Bool.or_eq_true_iff.mpr (Or.inr
        (ordered b a loB lt (down a r hiA hr) v u hv hu _ _ rawB rawA))
  have latest (t : Time) (lo : gateTime p repair ≤ t) :
      ∃ r, repair ≤ r ∧ gateTime p r ≤ t ∧ t < gateTime p (r + 1) := by
    obtain ⟨r, lower, upper⟩ := GridCO.exists_latest_gate p.engine t
      (((GridCO.gateTime_le_iff p.engine 0 repair).mpr (Nat.zero_le _)).trans lo)
    refine ⟨r, ?_, lower, upper⟩
    by_contra hn
    have le := (GridCO.gateTime_le_iff p.engine (r + 1) repair).mpr
      (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
    exact (not_lt.mpr (le.trans lo)) upper
  constructor
  · intro u hu v hv t t' lo bound lo' bound'
    obtain ⟨r, startR, lowerR, upperR⟩ := latest t lo
    obtain ⟨s, startS, lowerS, upperS⟩ := latest t' lo'
    change Block.Compatible (stable (Run.readAt (sapc p) rho t u))
      (stable (Run.readAt (sapc p) rho t' v))
    rw [read_stable_eq_latest_gate p E rho h.execution.toScheduleWellFormed r t lowerR upperR u,
      read_stable_eq_latest_gate p E rho h.execution.toScheduleWellFormed s t' lowerS upperS v]
    exact compatible r s startR startS (lowerR.trans bound) (lowerS.trans bound') u v hu hv
  · intro v hv t t' lo le bound
    obtain ⟨r, startR, lowerR, upperR⟩ := latest t lo
    obtain ⟨s, _, lowerS, upperS⟩ := latest t' (lo.trans le)
    change Block.Preceq (stable (Run.readAt (sapc p) rho t v))
      (stable (Run.readAt (sapc p) rho t' v))
    rw [read_stable_eq_latest_gate p E rho h.execution.toScheduleWellFormed r t lowerR upperR v,
      read_stable_eq_latest_gate p E rho h.execution.toScheduleWellFormed s t' lowerS upperS v]
    have slots : r ≤ s := by
      by_contra hn
      have time := (GridCO.gateTime_le_iff p.engine (s + 1) r).mpr
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
      exact (not_lt.mpr (time.trans (lowerR.trans le))) upperS
    exact monotone r s startR slots (lowerS.trans bound) v hv

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_safe_from_repaired_gate {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sync : E.t_GST ≤ proposalTime p boundary)
    (sources : RecoverySourcesSupported p rho boundary)
    (repair : Slot) (start : boundary ≤ repair) (B : Block)
    (records : ∀ v ∈ rho.honest,
      stable (Run.readAt (sapc p) rho (gateTime p repair) v) = B)
    (raw : ∀ v ∈ rho.honest,
      SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p repair) v).base repair = some B) :
    SafeFrom (sapc p) rho (sapcInterface p).stable (gateTime p repair) :=
  recovery_safe_from_repaired_gate_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)
    boundary sync sources repair start B records raw

/-- The Draft 4.3 recovery conclusion under awake quorum participation,
with the same 2L+G+8Δ bound. -/
theorem sapc_recovered_quorum_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho) :
    RecoveredAt (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho
      (E.t_GST + (sapcConstants p G).recoveryBound) := by
  obtain ⟨boundary, repair, B, _, sync, sources, later, deadline, _, records, raw⟩ :=
    recovery_common_repair_quorum p E rho hΔ G hG h
  have safe := recovery_safe_from_repaired_gate_quorum p E rho hΔ G hG h boundary sync.le sources
    repair later.le B (fun v hv => (records v hv).1) raw
  have safeFrom : SafeFrom (sapc p) rho (sapcInterface p).stable
      (E.t_GST + (sapcConstants p G).recoveryBound) := by
    constructor
    · intro u hu v hv t t' lo hi lo' hi'
      exact safe.agree u hu v hv t t' (deadline.trans lo) hi (deadline.trans lo') hi'
    · intro v hv t t' lo le hi
      exact safe.monotone v hv t t' (deadline.trans lo) le hi
  have included := recovery_included_from_engine_quorum p E rho hΔ G hG h
  exact ⟨safeFrom, safeFrom, included.2.1, included.1⟩

/-- The original Draft 4.3 interface is retained. -/
theorem recovered_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    RecoveredAt (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho
      (E.t_GST + (sapcConstants p G).recoveryBound) :=
  sapc_recovered_quorum_from_engine p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)

end AvailableChain.SAPC
end

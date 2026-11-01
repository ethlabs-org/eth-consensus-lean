module
public import AvailableChainSAPC.Proofs.RecoveryRelease
public import AvailableChainSA.Proofs.RecoverySupport

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Support concerns the actual next HEAD, regardless of PC selection. -/
def RecoveryHeadCovers {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (B : Block) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq B (headData p rho (r + 1) v).target

def RecoveryRowsCompatible {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (B : Block) : Prop :=
  ∀ v ∈ rho.honest, ∀ K g d,
    (K, g, d) ∈ (headState p rho (r + 1) v).base.obligations → Block.Compatible K B

/-- The live root is one of the surviving rows, or genesis. -/
theorem liveRoot_compatible_of_rows {n : Nat} (st : GridCO.State n) (B : Block)
    (rows : ∀ K g d, (K, g, d) ∈ st.obligations → Block.Compatible K B) :
    Block.Compatible (GridCO.liveRoot st) B := by
  rcases (GridCO.liveRoot_is_deepest st).1 with genesis | member
  · rw [genesis]
    exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix B))
  · obtain ⟨⟨K, g, d⟩, row, eq⟩ := List.mem_filterMap.mp member
    dsimp only at eq
    split at eq
    · have eq' : K = GridCO.liveRoot st := Option.some.inj eq
      exact eq' ▸ rows K g d row
    · contradiction

/-- Recovery's threshold implies the ordinary honest majority at each
synchronous HEAD. No clean-prefix premise is introduced. -/
theorem recovery_awake_majority_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (G : Time)
    (h : QuorumRecoveryRegime p G E rho)
    (t : Time) (sync : E.t_GST ≤ t) (horizon : t ≤ rho.horizon) : AwakeMajority E rho t := by
  have count := h.participation t sync horizon
  change (2 / 3 : ℚ) * ((awakeAt E rho.honest t).card + (faulty rho).card) <
    ((awakeAt E rho.honest t).card : ℚ) at count
  have nonneg : (0 : ℚ) ≤ (faulty rho).card := Nat.cast_nonneg _
  have bound : ((faulty rho).card : ℚ) < (awakeAt E rho.honest t).card := by linarith
  exact_mod_cast bound

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_awake_majority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (G : Time)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (t : Time) (sync : E.t_GST ≤ t) (horizon : t ≤ rho.horizon) : AwakeMajority E rho t := by
  have count := h.participation t sync horizon
  change (2 / 3 : ℚ) * ((awakeAt E rho.honest t).card + (faulty rho).card) <
    ((awakeAt E rho.honest t).card : ℚ) at count
  have nonneg : (0 : ℚ) ≤ (faulty rho).card := Nat.cast_nonneg _
  have bound : ((faulty rho).card : ℚ) < (awakeAt E rho.honest t).card := by linarith
  exact_mod_cast bound

/-- F4 removes PC compatibility from the shared source-support induction.
Lease deletion cannot remove the support already carried by honest HEADs. -/
theorem recovery_permanent_support_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) (rows : RecoveryRowsCompatible p rho r B) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B ∧
      (r < t → ∀ v ∈ rho.honest, ∃ D,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p t) v).base t = some D ∧
          Block.Preceq B D) := by
  have syncLater (s : Slot) (le : r ≤ s) : E.t_GST ≤ voteTime p s := by
    have cast : (r : Time) ≤ s := by exact_mod_cast le
    apply sync.trans
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + p.Δ
    nlinarith [p.deltaPos]
  have earlyAfter (s : Slot) : voteTime p s ≤ earlyTime p s := by
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have earlyGate (s : Slot) : earlyTime p s ≤ gateTime p s := by
    change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have transfer (s : Slot) (le : r ≤ s) (hh : gateTime p s ≤ rho.horizon) (D : Block)
      (rawD : SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) source).base s = some D)
      (belowD : Block.Preceq B D) (compatible : RecoveryRowsCompatible p rho s B) :
      RecoveryHeadCovers p rho s B := by
    intro v hv
    exact recovery_genuine_head_covers_quorum p E rho hΔ G hG h s (syncLater s le) hh
      source v hs hv B D rawD belowD (liveRoot_compatible_of_rows _ B (compatible v hv))
  apply GridCO.source_support_induction (fun v => v ∈ rho.honest)
    (fun s v => SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
    (fun s v => (headData p rho (s + 1) v).target)
    (fun s v => (headState p rho (s + 1) v).base.obligations)
    (fun s => gateTime p s ≤ rho.horizon)
    (fun s t le hh => ((GridCO.gateTime_le_iff p.engine s t).mpr le).trans hh)
    r source hs B C below rows (transfer r (le_refl _) horizon C raw below rows)
  · intro t before _ v hv K g d row
    apply head_row_source_since p E rho h.execution.toScheduleWellFormed hΔ
      r t before _ v hv K g d row
    apply le_trans _ horizon
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast; linarith [p.deltaPos]
  · intro v hv D rawD
    exact synchronous_sameLabel p E rho h.execution hΔ h.acceptedRelay r
      (sync.trans (earlyAfter r)) horizon v source hv hs D C rawD raw
  · intro t le hh heads v hv
    have syncNext := syncLater (t + 1) (le.trans (Nat.le_succ t))
    exact preserve_from_heads p E rho h.execution hΔ h.partialSynchrony h.acceptedRelay
      (t + 1) syncNext ((earlyGate _).trans hh)
      (recovery_awake_majority_quorum p E rho G h _ syncNext
        ((earlyAfter _).trans ((earlyGate _).trans hh))) B heads v hv
  · exact transfer

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_permanent_support {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) (rows : RecoveryRowsCompatible p rho r B) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B ∧
      (r < t → ∀ v ∈ rho.honest, ∃ D,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p t) v).base t = some D ∧
          Block.Preceq B D) :=
  recovery_permanent_support_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) r sync
    horizon source hs B C raw below rows

/-- A synchronous fast source has permanent support. Its own lease is
not an induction premise, and the raw tip need not enter S. -/
theorem recovery_fast_source_supported_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) (fast : SA.releaseThreshold p ≤ GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B := by
  have early : E.t_GST ≤ earlyTime p r := by
    apply sync.trans
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have rows : RecoveryRowsCompatible p rho r B := by
    intro v hv K g d row
    exact fast_source_rows_compatible p E rho h.execution hΔ h.acceptedRelay r early horizon
      source v hs hv B fast K g d row
  intro t le hh
  have supported := recovery_permanent_support_quorum p E rho hΔ G hG h r sync horizon
    source hs B C raw below rows t le hh
  exact ⟨supported.1, supported.2.1⟩

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_fast_source_supported {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) (fast : SA.releaseThreshold p ≤ GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B :=
  recovery_fast_source_supported_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) r sync
    horizon source hs B C raw below fast

/-- A slow source with a fully synchronous window has the same permanent
support as a fast source. Only the source exclusion argument differs. -/
theorem recovery_slow_source_supported_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) (slow : SA.slowEligible p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B = true)
    (window : ∀ s, s < r → r + 1 ≤ s + p.k → E.t_GST ≤ earlyTime p s) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B := by
  have rows : RecoveryRowsCompatible p rho r B := by
    intro v hv K g d row
    exact slow_window_rows_compatible p E rho h.execution hΔ h.acceptedRelay r source hs B
      slow window horizon v hv K g d row
  intro t le hh
  have supported := recovery_permanent_support_quorum p E rho hΔ G hG h r sync horizon
    source hs B C raw below rows t le hh
  exact ⟨supported.1, supported.2.1⟩

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_slow_source_supported {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) (slow : SA.slowEligible p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B = true)
    (window : ∀ s, s < r → r + 1 ≤ s + p.k → E.t_GST ≤ earlyTime p s) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B :=
  recovery_slow_source_supported_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) r sync
    horizon source hs B C raw below slow window

/-- SA's admitted-source interface on the actual SA-PC run. -/
def RecoverySourcesSupported {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (boundary : Slot) : Prop :=
  ∀ s, gateTime p s ≤ rho.horizon → ∀ source ∈ rho.honest, ∀ B C g,
    voteTime p boundary < gateTime p s + lifetime p →
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) source).base s = some C →
    Block.Preceq B C → g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
      (Run.stateBeforeTime (sapc p) rho (gateTime p s) source).base s B →
    ∀ t, s ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B

/-- All sources that can outlive SA's two-lease boundary have permanent
support. The timing lemma and admission split are reused from SA. -/
theorem recovery_sources_after_two_leases_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (b : Slot) (sync : E.t_GST ≤ voteTime p b) :
    RecoverySourcesSupported p rho (SA.recoveryBoundary p b) := by
  intro s hh source hs B C g deadline raw below admission
  have window := SA.live_source_after_window p b s deadline
  have start : b ≤ s := by have := p.kLarge; simp only [Slot] at *; omega
  have syncLater (t : Slot) (le : b ≤ t) : E.t_GST ≤ voteTime p t := by
    have cast : (b : Time) ≤ t := by exact_mod_cast le
    apply sync.trans
    change 4 * p.Δ * (b : Time) + p.Δ ≤ 4 * p.Δ * (t : Time) + p.Δ
    nlinarith [p.deltaPos]
  rcases (SA.admissionLevels_iff p _ s B g).mp admission |>.2 with fast | slow
  · exact recovery_fast_source_supported_quorum p E rho hΔ G hG h s (syncLater s start) hh
      source hs B C raw below fast
  · apply recovery_slow_source_supported_quorum p E rho hΔ G hG h s (syncLater s start) hh
      source hs B C raw below slow
    intro t before inWindow
    have lo : b ≤ t := by simp only [Slot] at *; omega
    apply (syncLater t lo).trans
    change 4 * p.Δ * (t : Time) + p.Δ ≤ 4 * p.Δ * (t : Time) + 2 * p.Δ
    linarith [p.deltaPos]

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_sources_after_two_leases {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (b : Slot) (sync : E.t_GST ≤ voteTime p b) :
    RecoverySourcesSupported p rho (SA.recoveryBoundary p b) :=
  recovery_sources_after_two_leases_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) b
    sync

end AvailableChain.SAPC
end

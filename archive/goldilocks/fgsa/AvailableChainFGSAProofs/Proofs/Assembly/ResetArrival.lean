module
public import AvailableChainFGSAProofs.Proofs.Healing.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (lane boundary)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum

public section

/-! Blueprint 21 H.11:1572–1595; S5 J8 R2. Assembly of the frozen reset-arrival
statement: the Healing reset witness (R1) with the Foundations source producer.
DC: INTENTIONAL row-delay bound; H0Reset and SA clocks unchanged. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Blueprint 21 H.11:1757–1759; S5 J8 R1/R2 INLINE discharge.
DC: SAME the frozen F1.5 source-discipline package (sourceDiscipline_base),
with heights already read through heightView; no old derive read. -/
theorem healing_reset_emittedName (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : BaseSet p c E rho)
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    (ha : HonestRowAt p c E rho j x r a) (he : namedEntry a.payload.height_pair = some e) :
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = ((heightView p C).h, (heightView p C).T_h.root) ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
  have hsd : SourceDisciplineBaseAt p c E rho :=
    sourceDiscipline_base p c E rho (pt := ()) ⟨hb⟩
  delta SourceDisciplineBaseAt at hsd
  obtain ⟨e', C, G, he', hC, hh, _, hG, hCG, hf⟩ := hsd.2.2 j x r a ha
  obtain rfl : e = e' := Option.some.inj (he.symm.trans he')
  exact ⟨C, G, hC, hh, hG, hCG, hf⟩

/-- P-H1 supplies permanence for this sleep healing run. Foundations supply all run channels.
Healing.Export exposes the proved RecoveryPerm producer. -/
theorem assembly_healing_tPerm_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) : TPerm p c E rho := by
  exact healing_tPerm_recovery E rho hset (fgsa_rMonoAll p c E rho)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)

/-- Blueprint 21 H.11:1572–1595; S5 J8 R2. Frozen ResetArrivalStatement.
DC: INTENTIONAL row-delay bound; H0Reset and SA clocks unchanged.
Named HG.5 input `hsearch` (all runs): exact P-H2 search obligation;
reset_row and reset_first come from it. -/
theorem healing_resetArrival (p : Params) (G ΔF : Time)
    (hsearch : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      FrontierSearchStatement p c E rho G ΔF) :
    ResetArrivalStatement p G ΔF := by
  intro hδ V _ _ In c E rho hset hbound hhor
  exact healing_resetWitness p c E rho
    (healing_reset_emittedName p c E rho hset.base)
    hset hδ hbound (hsearch c E rho hset hbound) hhor

/-- Blueprint 21 HG.5. Recovery supplies the selected scopes. Foundations supply
all run inputs. The rise and row horizon guards stay in the returned statement. -/
theorem healing_frontierSearch_of_set (p : Params) {V : Type} [DecidableEq V] [Fintype V]
    {In : Type} (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hset : HealingSet p c E rho G ΔF) :
    FrontierSearchStatement p c E rho G ΔF := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  exact healing_frontierSearch_recovery E rho hset (fgsa_rMonoAll p c E rho)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
      (fgsa_rStore p c E rho))
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho hset.base hset.fault)
    (fgsa_tRows_recovery p c E rho hset.toRecovery₂).receipt
    (fgsa_batchCoverage p ΔF .progress c E rho) (fgsa_foldTrichotomy_progress p)
    faultQ (kmid_honest_quorum p c rho hset.base.linked hset.fault)

/-- Blueprint 21 H.11:1572–1595. The named HG.5 producer supplies reset arrival. -/
theorem healing_resetArrivalStatement (p : Params) (G ΔF : Time) :
    ResetArrivalStatement p G ΔF :=
  healing_resetArrival p G ΔF fun c E rho hset _hbound =>
    healing_frontierSearch_of_set p c E rho hset

/-- Blueprint 21 H.11:1572–1595. The reset-only claim retains its finite horizon. -/
theorem healing_resetArrivalClaim (p : Params) : ResetArrivalClaim p := by
  intro G ΔF hδ V _ _ In c E rho _ h
  exact healing_resetArrivalStatement p G ΔF hδ c E rho h.set h.bound h.hhor

/-- The named recovery producer supplies the invariant at every event cut. -/
theorem assembly_healing_inv_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (hreset : H0Reset p c E rho w) : ∀ i, PostResetInv p c E rho w i := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  exact healing_postReset_inv_recovery p c E rho hset
    (fgsa_rMonoAll p c E rho)
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
      (fgsa_rStore p c E rho))
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
      hset.base.valid.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
    (cap_finality_head p c E rho) (rowPermission_covered E rho) hreset

/-- The named recovery producer changes only u and QStar in the reset witness. -/
theorem assembly_healing_extension_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) :
    p.δt = 2 * p.R → ∀ w, H0Reset p c E rho w →
      p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∃ u Q, H0 p c E rho { w with u := u, QStar := Q } := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  exact healing_h0_extension_recovery p c E rho hset
    (fgsa_rMonoAll p c E rho)
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
      (fgsa_rStore p c E rho))
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
      hset.base.valid.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
    (cap_finality_head p c E rho) (rowPermission_covered E rho)

/-- The local input uses the selected witness and its own finite horizon. -/
theorem assembly_healing_localInput_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) :
    p.δt = 2 * p.R → ∀ w, H0 p c E rho w →
      tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  exact healing_localInput_recovery p c E rho hset
    (fgsa_rMonoAll p c E rho)
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
      (fgsa_rStore p c E rho))
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
      hset.base.valid.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
    (cap_finality_head p c E rho) (rowPermission_covered E rho)
    (fgsa_tRows_recovery p c E rho hset.toRecovery₂)

/-- The full input keeps the complete recoveryStart horizon and the selected witness. -/
theorem assembly_healing_fullInput_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) (hbound : LivenessBoundW p ΔF) :
    p.δt = 2 * p.R →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → HealingInput p c E rho w ΔF ∧
        tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  exact healing_fullInput_recovery p c E rho
    (fgsa_rMonoAll p c E rho)
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
      (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
      (fgsa_rStore p c E rho))
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
      hset.base.valid.toScheduleWellFormed)
    (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
    (cap_finality_head p c E rho) (rowPermission_covered E rho) hset hbound
    (fgsa_tRows_recovery p c E rho hset.toRecovery₂)
    (healing_reset_emittedName p c E rho hset.base)
    (fgsa_batchCoverage p ΔF .progress c E rho) (fgsa_foldTrichotomy_progress p)
    faultQ (kmid_honest_quorum p c rho hset.base.linked hset.fault)

/-- ROOT-DIGEST W2b. Blueprint 21 H.17:2958–3012; plan S5 CONE-2 K2.
DC: SAME cone step at every event cut. HealingSet supplies each run port. -/
theorem healing_postReset_coneStep_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) : ∀ i, PostResetConeStep p c E rho w i := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMonoAll p c E rho
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
  exact healing_postReset_coneStep p c E rho hset mono
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
    crossing origin h0r cap
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho)

/-- The selected healing gate catches up each honest suffix reader. The proof
uses actual cuts, applied wakes, and the recovery epoch through the finite horizon. -/
theorem assembly_healing_suffix_reader (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : HealingSet p c E rho G ΔF) {w : HealingWitness} (h0 : H0 p c E rho w)
    (hhor : tstar p w ≤ rho.horizon) {i : Nat} {x : V}
    (hi : HealSuffix p c rho (tstar p w) i) (hx : x ∈ rho.honest) :
    confirmedReaderIdx p c E rho x i := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hcut : E.t_GST ≤ slotStartZ p (w.u : Int) :=
    healing_reset_slot_cutoff h0.toH0Reset |>.trans (by
      have hu : (w.sStar : Int) ≤ w.u := by
        exact_mod_cast (Nat.le_add_right w.sStar 2 |>.trans h0.proposal_lower)
      change 4 * p.Δ * (w.sStar : Int) ≤ 4 * p.Δ * (w.u : Int)
      nlinarith [p.deltaPos])
  have hgate : healStart p c rho (tstar p w) = afterTicksIdx rho (tstar p w) := by
    have hg : isGateTime p (tstar p w) = true := (isGateTime_iff p _).mpr ⟨w.u, rfl⟩
    rw [healStart_def, hg]
    rfl
  have htime : ((4 * w.u + 6 : Nat) : Time) * p.Δ = tstar p w := by
    rw [tstar_def]
    change ((4 * w.u + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx (4 * w.u + 6)
    (htime ▸ hhor) (htime ▸ hrec.awake x hx _ h0.after_gst hhor)
  rw [htime] at hj
  have hji : j < i := by
    have hlt : j < afterTicksIdx rho (tstar p w) := by
      by_contra hn
      have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred (P := fgsa p c) _)
        (fun _ _ hk hf => decide_eq_true (hk.trans (of_decide_eq_true hf)))
        (Nat.le_of_not_gt hn) hj
      have ht : cutPred (P := fgsa p c) (tstar p w)
          (.tick x (tstar p w) : V2.Event V (Obj p)) = true := by
        change decide (toLex (_, 1) ≤ toLex (_, 1)) = true
        exact decide_eq_true le_rfl
      exact Bool.noConfusion (ht.symm.trans hf)
    exact hlt.trans_le (hgate ▸ hi.1)
  have hile : i ≤ rho.events.length := hi.2
  have hl : i - 1 < rho.events.length := by omega
  have he : (rho.events.take i).getLast? = some rho.events[i - 1] := by
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, min_eq_left hi.2]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hl]
  have hp : prefixTime rho i = rho.events[i - 1].time := by
    change ((rho.events.take i).getLast?.map (fun e => e.time)).getD 0 = _
    rw [he]
    rfl
  have hlow : tstar p w ≤ prefixTime rho i := by
    rw [hp]
    rcases (show j ≤ i - 1 by omega).lt_or_eq with hjl | rfl
    · obtain ⟨hjl', hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hm := List.pairwise_iff_getElem.mp hs.sorted j (i - 1) hjl' hl hjl
      rw [hje] at hm
      exact V2.D.Engine.time_le_of_key_le _ _ hm
    · have heq := Option.some.inj ((List.getElem?_eq_getElem hl).symm.trans hj)
      rw [heq]
      exact le_rfl
  have hhigh : prefixTime rho i ≤ rho.horizon := by
    rw [hp]
    exact (hs.in_horizon _ (List.getElem_mem hl)).2
  have hb (k : Nat) : ∀ t, (storeAt p c E rho k x).restartTime = some t →
      t ≤ slotStartZ p (w.u : Int) := by
    apply fgsa_restartTime_bound E rho k x _
    intro q t _ ht
    exact (healing_scope_restart_bound hrec hx
      (hs.in_horizon _ (List.mem_of_getElem? ht)).2 le_rfl
      (List.mem_of_getElem? ht)).trans hcut
  have hg : enabledGateAt p c E rho j x w.u := by
    refine ⟨hj, ?_⟩
    cases hr : (storeAt p c E rho j x).restartTime with
    | none => trivial
    | some t => exact hb j t hr
  refine ⟨⟨hx, hrec.awake x hx _ (h0.after_gst.trans hlow) hhigh, ?_⟩, ?_⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some t =>
      refine ⟨w.u, j, hb i t hr, hlow, hji, hg, ?_, ?_⟩
      · intro u _ hu hup
        exact hrec.awake x hx u (hcut.trans hu) (hup.trans hhigh)
      · intro u hu hup hm
        exact (not_lt.mpr ((healing_scope_restart_bound hrec hx hhigh hup hm).trans hcut)) hu
  · intro u hu0 hup hW
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
      (hrec.base.valid.wake_restart x hx u hu0 (hup.trans hhigh) hW)
    have hub := healing_scope_restart_bound hrec hx hhigh hup (List.mem_of_getElem? hk)
    have hut : u < tstar p w := by
      have hgt : slotStartZ p (w.u : Int) < tstar p w := by
        change 4 * p.Δ * (w.u : Int) < 4 * p.Δ * (w.u : Int) + 6 * p.Δ
        linarith [p.deltaPos]
      exact (hub.trans hcut).trans_lt hgt
    have hkj := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk (tstar p w)).mpr hut
    exact ⟨k, hkj.trans_le ((preIdx_le_afterTicksIdx E rho hs (tstar p w)).1.trans
      (hgate ▸ hi.1)), hk⟩

/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W2/W4.
DC: SAME all-cut invariant. HealingSet supplies each standing run port.
The cone is used only in the adjacent J6-3 step producers below. -/
private theorem healing_postReset_inv_of_open (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w)
    (_stepRL : ∀ i, PostResetResetLeaseStep p c E rho w i)
    (_stepLease : ∀ i, PostResetLeaseStep p c E rho w i)
    (_stepRaw : ∀ i, PostResetRawStep p c E rho w i)
    (_hcone : PostResetRetainedCone p c E rho w) :
    ∀ i, PostResetInv p c E rho w i := by
  exact assembly_healing_inv_of_set p c E rho hset h0r

section HTime
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (hcone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      PostResetRetainedCone p c E rho w)

include stepRL stepLease stepRaw hcone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W2.
DC: SAME strict reset arrival. J7 changes only u and QStar for full H0.
The four inputs have the exact joint-step and retained-cone types. -/
theorem healing_resetArrivalFull_of_open (G ΔF : Time) :
    ResetArrivalFullStatement p G ΔF := by
  intro hClock V _ _ In c E rho hset hbound hhor
  have hΓ := (fgsa_gamma_bounds p G).1
  have hG := hset.gapPos
  have hd := p.deltaPos
  obtain ⟨w, h0r, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
    hset hbound (by linarith)
  have inv := healing_postReset_inv_of_open p c E rho hset h0r
    (stepRL c E rho hset h0r) (stepLease c E rho hset h0r)
    (stepRaw c E rho hset h0r) (hcone c E rho hset h0r)
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have carrier := postReset_tCarrier_reset p c E rho hset.toRecovery₂
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho) h0r inv
  obtain ⟨u, Q, h0, _⟩ := healing_h0_of p c E rho hset carrier h0r (by linarith)
  exact ⟨{ w with u := u, QStar := Q }, h0, harrival⟩

omit stepRL stepLease stepRaw hcone in
/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W3.
DC: SAME statement under HealingTimePrem. The package supplies HealingSet,
LivenessBoundW, and the healing horizon at the original G and ΔF. -/
theorem healing_hTimeClaim_of_statement
    (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact hTime G ΔF hClock c E rho h.set h.bound h.hhor

/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HTIME-WIRE W4.
DC: SAME HTimeClaim. The only open inputs are J5-A reset lease and raw steps,
J4A2-2 lease steps, and G-H17 retained cone, under HealingSet and H0Reset. -/
theorem healing_hTimeClaim_of_open : HTimeClaim p := by
  apply healing_hTimeClaim_of_statement p
  intro G ΔF
  have timeBound := healing_timeBound_of_resetArrival p G ΔF
    (healing_resetArrivalStatement p G ΔF)
  have hInput : HealingInputOfH0Statement p G ΔF := by
    apply healing_healingInputOfH0 p G ΔF
    case timeBound => exact timeBound
    case sourcePrefix =>
      intro _ V _ _ In c E rho _ _ _ w h0
      exact h0.source_prefix
    case rows =>
      intro _ V _ _ In c E rho hset _ _
      exact fgsa_tRows_recovery p c E rho hset.toRecovery₂
    all_goals intro hClock V _ _ In c E rho hset hbound hhor w h0
    all_goals
      have inv := healing_postReset_inv_of_open p c E rho hset h0.toH0Reset
        (stepRL c E rho hset h0.toH0Reset) (stepLease c E rho hset h0.toH0Reset)
        (stepRaw c E rho hset h0.toH0Reset) (hcone c E rho hset h0.toH0Reset)
      have faultQ := fgsa_faultQ_of_count p hset.fault
      have mono := fgsa_rMonoAll p c E rho
      have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
        (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
      have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
        (fgsa_rStore p c E rho)
      have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
      have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
      have source := sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed
      have high := postReset_tHigh_reset p c E rho hset mono
        (sourceDiscipline_emittedNonempty p c E rho)
        (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
        crossing origin h0.toH0Reset cap source (rowPermission_covered E rho) inv
      have carrier := postReset_tCarrier_reset p c E rho hset.toRecovery₂ cap source
        (rowPermission_covered E rho) h0.toH0Reset inv
      have h2a := postReset_h2A_reset p c E rho hset.toRecovery₂ cap source
        (rowPermission_covered E rho) h0.toH0Reset inv
      have h2p := postReset_h2Prime_reset p c E rho hset mono cap source
        (rowPermission_covered E rho) h0.toH0Reset crossing origin inv
      have h3 := healing_postReset_exactService E rho w rho.events.length le_rfl
        (inv rho.events.length).service
      have h5 := postReset_h5RawTransfer_body p c E rho h0.toH0Reset
        (fun i => (inv i).raw_transfer)
      have h6 := healing_postReset_h6GateService E rho hset mono w rho.events.length le_rfl
        (inv rho.events.length).raw_transfer writes
      first
      | exact high
      | exact carrier
      | exact h2a
      | exact h2p
      | exact h3
      | exact h5
      | exact h6
      | have ht := timeBound hClock c E rho hset hbound hhor w h0
        have hΓ := (fgsa_gamma_bounds p G).1
        have hG := hset.gapPos
        have hd := p.deltaPos
        obtain ⟨w₀, h0r, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
          hset hbound (by linarith)
        have hr := healing_reset_rStar_unique p c E rho h0.toH0Reset h0r
        rw [hr] at ht
        have start := healing_postResetStart_of_h0 p c E rho h0
        have h4 := healing_h4 p c E rho hset start h2a h3 h5 inv (by linarith)
          (fun _ _ hi hx => assembly_healing_suffix_reader p c E rho hset h0
            (by linarith) hi hx)
        first
        | exact h4
        | exact healing_healed p c E rho hset start h4 h3
  exact healing_hTime_of p G ΔF
    (healing_resetArrivalFull_of_open p stepRL stepLease stepRaw hcone G ΔF) hInput

end HTime

/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 W2/W4.
DC: SAME all-cut invariant and run cone, from joint₂ and the four open steps.
HealingSet supplies each run port. RE-BIND supplies the two cut step producers. -/
private theorem healing_postReset_inv_cone_of_open₂ (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w)
    (stepRL : ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ i, PostResetRawStep p c E rho w i)
    (stepCone : ∀ i, PostResetConeStep p c E rho w i) :
    (∀ i, PostResetInv p c E rho w i) ∧ PostResetRetainedCone p c E rho w := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMonoAll p c E rho
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
  have steps := fun i => And.intro
    (healing_postReset_openingDomainStep₂ E rho hset w h0r cap
      (rowPermission_covered E rho) mono crossing origin i)
    (healing_postReset_serviceStep₂ E rho hset w h0r cap
      (rowPermission_covered E rho) mono writes i)
  -- Both projections use postReset_joint₂_all with the same run ports and steps.
  exact ⟨postReset_inv_all₂ p c E rho hset mono
      (sourceDiscipline_emittedNonempty p c E rho)
      (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
      crossing origin cap
      (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
      (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
        hset.base.valid.toScheduleWellFormed)
      (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
      (cap_finality_head p c E rho) h0r stepRL stepLease stepRaw stepCone
      (fun i => (steps i).1) (fun i => (steps i).2),
    postReset_retainedCone_run p c E rho hset mono
      (sourceDiscipline_emittedNonempty p c E rho)
      (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
      crossing origin cap
      (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
      (held_chain_row_origin_before p c E rho hset.base.valid.toUnforgeableSignatures
        hset.base.valid.toScheduleWellFormed)
      (fgsa_finalityCap p c E rho hset.base.linked hset.base.valid faultQ)
      (cap_finality_head p c E rho) h0r stepRL stepLease stepRaw stepCone
      (fun i => (steps i).1) (fun i => (steps i).2)⟩

section HTime₂
variable (p : Params)
    (stepRL : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetResetLeaseStep p c E rho w i)
    (stepLease : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetLeaseStep p c E rho w i)
    (stepRaw : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetRawStep p c E rho w i)
    (stepCone : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      HealingSet p c E rho G ΔF → ∀ {w : HealingWitness}, H0Reset p c E rho w →
      ∀ i, PostResetConeStep p c E rho w i)

include stepRL stepLease stepRaw stepCone

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 W2.
DC: SAME strict reset arrival. J7 changes only u and QStar for full H0.
The four inputs are reset lease, lease safety, raw transfer, and cone steps. -/
theorem healing_resetArrivalFull_of_open₂ (G ΔF : Time) :
    ResetArrivalFullStatement p G ΔF := by
  intro hClock V _ _ In c E rho hset hbound hhor
  have hΓ := (fgsa_gamma_bounds p G).1
  have hG := hset.gapPos
  have hd := p.deltaPos
  obtain ⟨w, h0r, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
    hset hbound (by linarith)
  have inv := (healing_postReset_inv_cone_of_open₂ p c E rho hset h0r
    (stepRL c E rho hset h0r) (stepLease c E rho hset h0r)
    (stepRaw c E rho hset h0r) (stepCone c E rho hset h0r)).1
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have carrier := postReset_tCarrier_reset p c E rho hset.toRecovery₂
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (rowPermission_covered E rho) h0r inv
  obtain ⟨u, Q, h0, _⟩ := healing_h0_of p c E rho hset carrier h0r (by linarith)
  exact ⟨{ w with u := u, QStar := Q }, h0, harrival⟩


/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HTW-3 W4.
DC: SAME HTimeClaim, from joint₂ with the three old steps and the cone step.
The invariant and run cone are projections of joint₂ with RE-BIND cut steps. -/
theorem healing_hTimeClaim_of_open₂ : HTimeClaim p := by
  apply healing_hTimeClaim_of_statement p
  intro G ΔF
  have timeBound := healing_timeBound_of_resetArrival p G ΔF
    (healing_resetArrivalStatement p G ΔF)
  have hInput : HealingInputOfH0Statement p G ΔF := by
    apply healing_healingInputOfH0 p G ΔF
    case timeBound => exact timeBound
    case sourcePrefix =>
      intro _ V _ _ In c E rho _ _ _ w h0
      exact h0.source_prefix
    case rows =>
      intro _ V _ _ In c E rho hset _ _
      exact fgsa_tRows_recovery p c E rho hset.toRecovery₂
    all_goals intro hClock V _ _ In c E rho hset hbound hhor w h0
    all_goals
      have inv := (healing_postReset_inv_cone_of_open₂ p c E rho hset h0.toH0Reset
        (stepRL c E rho hset h0.toH0Reset) (stepLease c E rho hset h0.toH0Reset)
        (stepRaw c E rho hset h0.toH0Reset) (stepCone c E rho hset h0.toH0Reset)).1
      have faultQ := fgsa_faultQ_of_count p hset.fault
      have mono := fgsa_rMonoAll p c E rho
      have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
        (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
      have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
        (fgsa_rStore p c E rho)
      have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
      have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
      have source := sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed
      have high := postReset_tHigh_reset p c E rho hset mono
        (sourceDiscipline_emittedNonempty p c E rho)
        (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
        crossing origin h0.toH0Reset cap source (rowPermission_covered E rho) inv
      have carrier := postReset_tCarrier_reset p c E rho hset.toRecovery₂ cap source
        (rowPermission_covered E rho) h0.toH0Reset inv
      have h2a := postReset_h2A_reset p c E rho hset.toRecovery₂ cap source
        (rowPermission_covered E rho) h0.toH0Reset inv
      have h2p := postReset_h2Prime_reset p c E rho hset mono cap source
        (rowPermission_covered E rho) h0.toH0Reset crossing origin inv
      have h3 := healing_postReset_exactService E rho w rho.events.length le_rfl
        (inv rho.events.length).service
      have h5 := postReset_h5RawTransfer_body p c E rho h0.toH0Reset
        (fun i => (inv i).raw_transfer)
      have h6 := healing_postReset_h6GateService E rho hset mono w rho.events.length le_rfl
        (inv rho.events.length).raw_transfer writes
      first
      | exact high
      | exact carrier
      | exact h2a
      | exact h2p
      | exact h3
      | exact h5
      | exact h6
      | have ht := timeBound hClock c E rho hset hbound hhor w h0
        have hΓ := (fgsa_gamma_bounds p G).1
        have hG := hset.gapPos
        have hd := p.deltaPos
        obtain ⟨w₀, h0r, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
          hset hbound (by linarith)
        have hr := healing_reset_rStar_unique p c E rho h0.toH0Reset h0r
        rw [hr] at ht
        have start := healing_postResetStart_of_h0 p c E rho h0
        have h4 := healing_h4 p c E rho hset start h2a h3 h5 inv (by linarith)
          (fun _ _ hi hx => assembly_healing_suffix_reader p c E rho hset h0
            (by linarith) hi hx)
        first
        | exact h4
        | exact healing_healed p c E rho hset start h4 h3
  exact healing_hTime_of p G ΔF
    (healing_resetArrivalFull_of_open₂ p stepRL stepLease stepRaw stepCone G ΔF) hInput


omit stepCone in
/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 CONE-3 R3.
DC: SAME HTimeClaim with the cone step supplied by HealingSet.
The three inputs keep the exact types from healing_hTimeClaim_of_open₂. -/
theorem healing_hTimeClaim_of_steps : HTimeClaim p :=
  healing_hTimeClaim_of_open₂ p stepRL stepLease stepRaw
    (healing_postReset_coneStep_of_set p)

end HTime₂

/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE H1 reset lease.
DC: SAME reset lease step at every cut. HealingSet supplies each run port. -/
theorem healing_postReset_resetLeaseStep_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) : ∀ i, PostResetResetLeaseStep p c E rho w i := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  exact postReset_resetLease_succ' p c E rho hset
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed)
    (fgsa_rMonoAll p c E rho) crossing h0r
    (fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ)
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)

/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE H1 lease safety.
DC: SAME lease safety step at every cut. HealingSet supplies each run port. -/
theorem healing_postReset_leaseStep_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) : ∀ i, PostResetLeaseStep p c E rho w i := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMonoAll p c E rho
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  exact postReset_leaseSafe_succ p c E rho hset mono
    (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
    crossing origin h0r

/-- ROOT-DIGEST W2b. Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE H1 raw transfer.
DC: SAME raw transfer step at every cut. HealingSet supplies each run port. -/
theorem healing_postReset_rawStep_of_set (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0r : H0Reset p c E rho w) : ∀ i, PostResetRawStep p c E rho w i := by
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMonoAll p c E rho
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  exact postReset_rawTransfer_succ p c E rho hset
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
    mono (sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed)
    crossing origin h0r

section SelectedResults
variable (p : Params) {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
include hset hbound

/-- The recovery producer supplies extension for this run.
Only u and QStar change in the reset witness. -/
theorem assembly_resetArrivalFull_at
    (hClock : p.δt = 2 * p.R)
    (hhor : recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon) :
    ∃ w, H0 p c E rho w ∧ p.actionTime w.rStar <
      recoveryStart p E + B'_resetF p ΔF G := by
  have hΓ := (fgsa_gamma_bounds p G).1
  have hd := p.deltaPos
  have hG := hset.gapPos
  obtain ⟨w, hreset, harrival⟩ := healing_resetArrivalStatement p G ΔF hClock c E rho
    hset hbound (by linarith)
  obtain ⟨u, Q, h0⟩ := assembly_healing_extension_of_set p c E rho hset
    hClock w hreset (by linarith)
  exact ⟨{ w with u := u, QStar := Q }, h0, harrival⟩

omit hbound in
/-- The local input producer keeps the selected witness's own finite horizon. -/
theorem assembly_healingInput_at
    (hClock : p.δt = 2 * p.R) (w : HealingWitness) (h0 : H0 p c E rho w)
    (hhor : tstar p w ≤ rho.horizon) : HealingInput p c E rho w ΔF :=
  assembly_healing_localInput_of_set p c E rho hset hClock w h0 hhor

/-- The recovery producers supply extension and full input in this finite run. The selected witness
and the complete Jst horizon are used in both time bounds. -/
theorem assembly_hTime_at
    (hClock : p.δt = 2 * p.R)
    (hhor : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon) :
    HTimeConcl p c E rho G ΔF := by
  have hfull := healing_resetFull_horizon p G ΔF (recoveryStart p E) rho.horizon hhor
  obtain ⟨w, h0, harrival⟩ := assembly_resetArrivalFull_at p c E rho hset hbound
    hClock hfull
  obtain ⟨hinput, ht⟩ := assembly_healing_fullInput_of_set p c E rho hset hbound
    hClock hfull w h0
  exact ⟨w, hinput, ht, healing_time_strict_of_reset p G ΔF (recoveryStart p E)
    (p.actionTime w.rStar) harrival⟩

end SelectedResults

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE H2.
DC: SAME HTimeClaim. The named recovery producers supply search, extension and full input. -/
theorem healing_hTimeClaim (p : Params) : HTimeClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact assembly_hTime_at p c E rho h.set h.bound hClock h.hhor

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE H2 all parameters.
DC: SAME HTimeClaim for each Params value, with the named HG.5 producer. -/
theorem healing_hTimeClaim_all : ∀ p, HTimeClaim p := healing_hTimeClaim

/-- Blueprint 21 H.18–H.22:3049–3176; plan S5 HCLOSE H3.
DC: SAME full reset arrival. HealingSet supplies the named extension producer. -/
theorem healing_resetArrivalFull (p : Params) (G ΔF : Time) :
    ResetArrivalFullStatement p G ΔF := by
  intro hClock V _ _ In c E rho hset hbound hhor
  exact assembly_resetArrivalFull_at p c E rho hset hbound hClock hhor

/-- P-H2 owns the joint invariant for this selected witness. Every other input
has a named producer. The local horizon is the public HealingInput horizon. -/
theorem assembly_healingInput_of_inv (p : Params) {V : Type}
    [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hset : HealingSet p c E rho G ΔF) {w : HealingWitness}
    (h0 : H0 p c E rho w) (hhor : tstar p w ≤ rho.horizon) : HealingInput p c E rho w ΔF := by
  have inv := assembly_healing_inv_of_set p c E rho hset h0.toH0Reset
  have faultQ := fgsa_faultQ_of_count p hset.fault
  have mono := fgsa_rMonoAll p c E rho
  have crossing := fgsa_rXing (hroots := hset.base.idealization) p c E rho hset.base.linked
    (fgsa_faultX_count_rec p hset.fault) hset.base.valid.toUnforgeableSignatures
  have origin := sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hset.base, faultQ⟩
    (fgsa_rStore p c E rho)
  have writes := fgsa_leaseOrigins_lastWrite p c E rho hset.base.valid.toScheduleWellFormed
  have cap := fgsa_rCap_channel p c E rho hset.base.linked hset.base.valid faultQ
  have source := sourceDiscipline_tSrc p c E rho hset.base.valid.toScheduleWellFormed
  have high := postReset_tHigh_reset p c E rho hset mono
    (sourceDiscipline_emittedNonempty p c E rho)
    (emittedName_window p c E rho hset.base.valid.toScheduleWellFormed) writes
    crossing origin h0.toH0Reset cap source (rowPermission_covered E rho) inv
  have carrier := postReset_tCarrier_reset p c E rho hset.toRecovery₂ cap source
    (rowPermission_covered E rho) h0.toH0Reset inv
  have h2a := postReset_h2A_reset p c E rho hset.toRecovery₂ cap source
    (rowPermission_covered E rho) h0.toH0Reset inv
  have h2p := postReset_h2Prime_reset p c E rho hset mono cap source
    (rowPermission_covered E rho) h0.toH0Reset crossing origin inv
  have h3 := healing_postReset_exactService E rho w rho.events.length le_rfl
    (inv rho.events.length).service
  have h5 := postReset_h5RawTransfer_body p c E rho h0.toH0Reset
    (fun i => (inv i).raw_transfer)
  have h6 := healing_postReset_h6GateService E rho hset mono w rho.events.length le_rfl
    (inv rho.events.length).raw_transfer writes
  have start := healing_postResetStart_of_h0 p c E rho h0
  have h4 := healing_h4 p c E rho hset start h2a h3 h5 inv hhor
    (fun _ _ hi hx => assembly_healing_suffix_reader p c E rho hset h0 hhor hi hx)
  exact healing_healingInput_of p c E rho (healing_healed p c E rho hset start h4 h3)
    start h0.source_prefix
    (healing_healT_of p c E rho high carrier
      (fgsa_tRows_recovery p c E rho hset.toRecovery₂))
    (healing_healAC_of p c E rho h2a h2p h3 h4 h5 h6)

/-- Blueprint 21 H.18–H.22. The claim uses the selected all-cut producer.
The local horizon remains independent of the full reset budget. -/
theorem healing_healingInputClaim (p : Params) : HealingInputClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact assembly_healing_localInput_of_set p c E rho h.set hClock pt.w h.h0 h.hhor

/-- Blueprint 21 H.18. P-H2 owns the full-H0 extension at this selected reset witness.
It changes only u and QStar. The strict arrival bound therefore stays at Jst. -/
theorem assembly_resetArrivalFull_of_extension (p : Params) (G ΔF : Time)
    (hreset : ResetArrivalStatement p G ΔF)
    (hextend : p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      ∀ w, H0Reset p c E rho w →
      p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∃ u Q, H0 p c E rho { w with u := u, QStar := Q }) :
    ResetArrivalFullStatement p G ΔF := by
  intro hClock V _ _ In c E rho hset hbound hhor
  have hΓ := (fgsa_gamma_bounds p G).1
  have hG := hset.gapPos
  have hd := p.deltaPos
  obtain ⟨w, h0r, harrival⟩ := hreset hClock c E rho hset hbound (by linarith)
  obtain ⟨u, Q, h0⟩ := hextend hClock c E rho hset hbound w h0r (by linarith)
  exact ⟨{ w with u := u, QStar := Q }, h0, harrival⟩

/-- The statement adapter uses the unchanged HealingTimePrem and its Jst horizon. -/
theorem assembly_hTimeClaim_of_statement (p : Params)
    (hTime : ∀ G ΔF, HTimeStatement p G ΔF) : HTimeClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact hTime G ΔF hClock c E rho h.set h.bound h.hhor

/-- Blueprint 21 H.18–H.22. P-H2 owns full reset and the selected full-H0 input.
The generic time composition uses the same witness and the same joined start. -/
theorem assembly_hTimeClaim_of_reset_input (p : Params)
    (hReset : ∀ G ΔF, ResetArrivalFullStatement p G ΔF)
    (hInput : ∀ G ΔF, HealingInputOfH0Statement p G ΔF) : HTimeClaim p :=
  assembly_hTimeClaim_of_statement p fun G ΔF =>
    healing_hTime_of p G ΔF (hReset G ΔF) (hInput G ΔF)

/-- P-H2 supplies the selected full-H0 input at its local public horizon.
The input needs no whole-run NoRestart or full reset budget. -/
theorem assembly_healingInputClaim_of_input (p : Params)
    (hInput : ∀ G ΔF, p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF → ∀ w,
      H0 p c E rho w → tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF) :
    HealingInputClaim p := by
  intro G ΔF hClock V _ _ In c E rho pt h
  exact hInput G ΔF hClock c E rho h.set h.bound pt.w h.h0 h.hhor

end AvailableChain.FGSA.Run
end

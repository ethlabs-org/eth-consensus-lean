module
public import AvailableChainGridCO.Proofs.Coverage

@[expose] public section

namespace AvailableChain.GridCO

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The last early healthy batch retains every earlier clean genuine
result. Its late pool and its gate may be inside the outage. -/
theorem pending_genuine_extends_history [LeasePolicy] {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (hd : EarlyDelivery p E rho (r + 1))
    (hm : AwakeMajority E rho (voteTime p (r + 1)))
    (s : Slot) (hsr : s ≤ r) (source reader : V)
    (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest) (B C : Block)
    (hB : confirmation p (gateInput p rho s source) s = some B)
    (hC : confirmation p (gateInput p rho (r + 1) reader) (r + 1) = some C) :
    Block.Preceq B C := by
  obtain ⟨hhist, htransfer⟩ := clean_genuine_history p E rho hΔ r hclean
  have hheads : ∀ v ∈ rho.honest,
      Block.Preceq B (nextHead p (nextHeadState p rho r v) r) := by
    rcases eq_or_lt_of_le hsr with he | hlt
    · subst s; exact htransfer source hs B hB
    · obtain ⟨D, hD, hBD⟩ := hhist s hlt source hs B hB source hs
      intro v hv
      exact prefix_trans B D _ hBD (htransfer source hs D hD v hv)
  obtain ⟨D, hD, hBD, _⟩ := preserve_of_early_delivery p E rho hΔ r hd hm B hheads reader hr
  have he : D = C := Option.some.inj (hD.symm.trans hC)
  exact he ▸ hBD

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
No earlier map target can veto the pending healthy gate. All targets
come from earlier clean genuine results, covered by its honest batch. -/
theorem pending_gate_guard [LeasePolicy] {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (hd : EarlyDelivery p E rho (r + 1))
    (hm : AwakeMajority E rho (voteTime p (r + 1)))
    (reader : V) (hr : reader ∈ rho.honest) (C : Block)
    (hc : confirmation p (gateInput p rho (r + 1) reader) (r + 1) = some C) :
    (gateInput p rho (r + 1) reader).obligations.any
      (fun (target, _, _) => !Block.compatible target C) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨⟨B, g, d⟩, hb, hbad⟩ := List.any_eq_true.mp h
  obtain ⟨s, D, ht, hD, hBD⟩ := time_input_target_genuine_origin p E rho
    hd.execution.toScheduleWellFormed (gateTime p (r + 1)) reader B g d hb
  have hsr : s ≤ r := by
    by_contra hn
    have hle := (gateTime_le_iff p (r + 1) s).mpr (Nat.succ_le_of_lt (lt_of_not_ge hn))
    exact (not_lt.mpr hle) ht
  have hp := pending_genuine_extends_history p E rho hΔ r hclean hd hm
    s hsr reader reader hr hr D C hD hc
  have hgood : Block.compatible B C = true :=
    Bool.or_eq_true_iff.mpr (Or.inl (prefix_trans B D C hBD hp))
  simp [hgood] at hbad

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The pending healthy gate renews a covered prefix at its actual
rounded support, with a deadline measured from that gate. -/
theorem pending_coverage {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (hd : EarlyDelivery p E rho (r + 1))
    (hm : AwakeMajority E rho (voteTime p (r + 1)))
    (hh : gateTime p (r + 1) ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B : Block) (hn : B ≠ .genesis)
    (hp : Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source))) :
    ∀ reader ∈ rho.honest,
      Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)) ∧
      ∃ g, (awakeAt E rho.honest (voteTime p (r + 1))).card ≤
          prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B ∧
        g = roundedLevel p (prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B) ∧
        (B, g, gateTime p (r + 1) + lifetime p) ∈
          (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader).obligations := by
  have hheads := clean_stable_heads_cover p E rho hΔ r hclean source hs B hp
  intro reader hr
  obtain ⟨C, hc, hBC, hB⟩ := preserve_of_early_delivery p E rho hΔ r hd hm B hheads reader hr
  have hsupp := prefixSupport_ge_early_honest_batch p E rho hd.execution _ reader (r + 1) B
    (synchronous_next_head_batch p E rho hΔ r hd B hheads reader hr)
  let count := prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B
  have hpos : 1 ≤ count :=
    (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hm)).trans hsupp
  obtain ⟨hrecord, hrow⟩ := read_gate_writes_supported_prefix p E rho hΔ
    hd.execution.toScheduleWellFormed (r + 1) hh reader hr B C (roundedLevel p count)
    hc hBC hn hB (roundedLevel_mem p count hpos) (roundedLevel_le p count)
    (pending_gate_guard p E rho hΔ r hclean hd hm reader hr C hc)
  exact ⟨hrecord, roundedLevel p count, hsupp, rfl, hrow⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Exactly one HEAD label is in flight at a gate. -/
theorem in_flight_label_at_gate (p : Params) (r k : Slot)
    (hvote : voteTime p k ≤ gateTime p r)
    (hrelease : gateTime p r < releaseTime p k) : k = r + 1 := by
  have hd := p.deltaPos
  dsimp [voteTime, gateTime, releaseTime, proposalTime] at hvote hrelease
  have hlo : r < k := by
    by_contra h
    have hk : (k : Time) ≤ r := by exact_mod_cast (le_of_not_gt h)
    nlinarith
  have hhi : k ≤ r + 1 := by
    by_contra h
    have hk : (r : Time) + 2 ≤ k := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h) : r + 2 ≤ k)
    nlinarith
  exact le_antisymm hhi (Nat.succ_le_of_lt hlo)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Clean transfer supplies the in-flight HEAD premise at a completed gate. -/
theorem armingHeadsCompatible_of_heads [LeasePolicy] {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (r : Slot) (B : Block)
    (hheads : ∀ reader ∈ rho.honest,
      Block.Preceq B (nextHead p (nextHeadState p rho r reader) r)) :
    ArmingHeadsCompatible p E rho (gateTime p r) B := by
  intro k u hu o t ht hq hem hl target htarget
  obtain ⟨i, hi, ho⟩ := hem
  obtain ⟨he, ha⟩ := emitted_head_action p E rho i u t o k target ho hl htarget
  have hk := in_flight_label_at_gate p r k (he ▸ ht) hq
  subst k
  subst t
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hi,
    ← release_eq_next_vote] at ha
  have hh : nextHead p (nextHeadState p rho r u) r = target := by
    simpa [act, targetOfBlock, nextHead, nextHeadState, releaseInput] using ha
  rw [← hh]
  exact Bool.or_eq_true_iff.mpr (Or.inr
    (hheads u hu))

theorem armingHeadsCompatible_of_clean [LeasePolicy] {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hclean : CleanThroughLabel p E rho r)
    (source : V) (hs : source ∈ rho.honest) (B : Block)
    (hp : Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source))) :
    ArmingHeadsCompatible p E rho (gateTime p r) B :=
  armingHeadsCompatible_of_heads p E rho (hclean r (le_refl _)).1 r B
    (clean_stable_heads_cover p E rho hΔ r hclean source hs B hp)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Protection carries the in-flight HEAD condition to a later arming read.
This includes HEADs emitted during the outage before the pending safe write. -/
theorem armingHeadsCompatible_of_protection [LeasePolicy] {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hexec : ExecutionValid (gridCO p) E rho) (B : Block) (g : V → Nat)
    (U d W : Time) (hUW : U ≤ W) (hWd : W < d)
    (hstrong : ∀ v ∈ rho.honest, (faulty rho).card < g v)
    (hbase : ∀ v ∈ rho.honest,
      ProtectsUntil (Run.readAt (gridCO p) rho U v) B (g v) d ∧
      Block.Preceq B (stable (Run.readAt (gridCO p) rho U v)))
    (hseed : ArmingHeadsCompatible p E rho U B) :
    ArmingHeadsCompatible p E rho W B := by
  intro r u hu o t ht hrelease hem hl target htarget
  by_cases htu : t ≤ U
  · exact hseed r u hu o t htu (lt_of_le_of_lt hUW hrelease) hem hl target htarget
  · have htd : t < d := ht.trans_lt hWd
    obtain ⟨hp, _⟩ := protection_from_armed_read p E rho hexec B g U d hstrong hbase hseed
      t (le_of_not_ge htu) htd u hu
    obtain ⟨i, hi, ho⟩ := hem
    have hpost : ProtectsUntil (Run.stateBefore (gridCO p) rho (i + 1) u) B (g u) d := by
      obtain ⟨deadline, hd, hrow⟩ := hp
      rw [read_obligations_eq_clock p E rho hexec.toScheduleWellFormed u t
        (List.mem_iff_getElem?.mpr ⟨i, hi⟩)] at hrow
      refine ⟨deadline, hd, ?_⟩
      rw [stateBefore_succ_event hi]
      simp only [World.step, Function.update_self]
      rw [stateBefore_tick_eq_stateBeforeTime hexec.toScheduleWellFormed hi]
      exact hrow
    exact emitted_head_compatible_of_protection p E rho hexec.toScheduleWellFormed
      i u t hi B (g u) d hpost htd o r target ho hl htarget

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The minimum lease is longer than the gap to the pending gate. -/
theorem lifetime_gt_four_delta (p : Params) : 4 * p.Δ < lifetime p := by
  have hm : (2 : Time) ≤ p.m := by exact_mod_cast p.mLarge
  dsimp [lifetime]
  nlinarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A completed healthy covering gate gives a row stronger than all faults. -/
theorem outage_covering_protection {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho T b₀ b₁)
    (r : Slot) (hgate : gateTime p (r + 1) ≤ b₀)
    (source : V) (hs : source ∈ rho.honest) (B : Block) (hn : B ≠ .genesis)
    (hp : Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source))) :
    ∀ reader ∈ rho.honest,
      let g := roundedLevel p (prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B)
      (faulty rho).card < g ∧
        ProtectsUntil (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)
          B g (gateTime p (r + 1) + lifetime p) ∧
        Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)) := by
  have hclean := cleanThroughLabel_of_outage G T b₀ b₁ ho (r + 1) hgate
  have hsync := hclean (r + 1) (le_refl _)
  have hvote : voteTime p (r + 1) < b₀ := by
    dsimp [voteTime, gateTime] at *
    linarith [p.deltaPos]
  have hzero : 0 ≤ voteTime p (r + 1) := by
    dsimp [voteTime, proposalTime]
    have hd := p.deltaPos
    positivity
  have hstrong := roundedLevel_gt_faults_of_outage G T b₀ b₁ _ ho hzero hvote
  intro reader hr
  obtain ⟨hrecord, g, deadline, _, hlevel, hsupport, hdeadline, hrow⟩ :=
    coverage_from_engine p E rho hΔ r hclean source hs B hp hn hsync.2.1 reader hr
  rw [hlevel] at hrow
  exact ⟨hstrong.trans_le (roundedLevel_mono p hsupport), ⟨deadline, hdeadline, hrow⟩, hrecord⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The pending healthy gate gives the same strong-row guarantee, even
when delivery is arbitrary after its early cutoff. -/
theorem pending_outage_protection {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho T b₀ b₁)
    (r : Slot) (hgate : gateTime p r ≤ b₀) (hearly : earlyTime p (r + 1) ≤ b₀)
    (hh : gateTime p (r + 1) ≤ rho.horizon)
    (source : V) (hs : source ∈ rho.honest) (B : Block) (hn : B ≠ .genesis)
    (hp : Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source))) :
    ∀ reader ∈ rho.honest,
      let g := roundedLevel p (prefixSupport p (gateInput p rho (r + 1) reader) (r + 1) B)
      (faulty rho).card < g ∧
        ProtectsUntil (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)
          B g (gateTime p (r + 1) + lifetime p) ∧
        Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)) := by
  have hclean := cleanThroughLabel_of_outage G T b₀ b₁ ho r hgate
  have hvote : voteTime p (r + 1) < b₀ := by
    dsimp [voteTime, earlyTime] at *
    linarith [p.deltaPos]
  have hzero : 0 ≤ voteTime p (r + 1) := by
    dsimp [voteTime, proposalTime]
    have hd := p.deltaPos
    positivity
  have hm := ho.sleepyBefore _ hzero hvote
  have hstrong := roundedLevel_gt_faults_of_outage G T b₀ b₁ _ ho hzero hvote
  intro reader hr
  obtain ⟨hrecord, g, hsupport, hlevel, hrow⟩ := pending_coverage p E rho hΔ r hclean
    (.of_outage G T b₀ b₁ ho (r + 1) hearly) hm hh source hs B hn hp reader hr
  rw [hlevel] at hrow
  exact ⟨hstrong.trans_le (roundedLevel_mono p hsupport),
    ⟨gateTime p (r + 1) + lifetime p, le_refl _, hrow⟩, hrecord⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The next early cutoff is the current genuine gate. -/
theorem early_next_eq_gate (p : Params) (r : Slot) :
    earlyTime p (r + 1) = gateTime p r := by
  simp only [earlyTime, gateTime, proposalTime, Nat.cast_add, Nat.cast_one]
  ring

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Shared outage bridge from completed and pending covering leases.
The selected release level can vary by label, reader, and prefix. -/
theorem resilient_of_covering_protection [LeasePolicy] {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho T b₀ b₁)
    (strength : Slot → V → Block → Nat)
    (hcover : ∀ r, gateTime p (r + 1) ≤ b₀ → ∀ source ∈ rho.honest, ∀ B,
      B ≠ .genesis → Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source)) →
      ∀ reader ∈ rho.honest,
        (faulty rho).card < strength (r + 1) reader B ∧
        ProtectsUntil (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)
          B (strength (r + 1) reader B) (gateTime p (r + 1) + lifetime p) ∧
        Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)))
    (hpending : ∀ r, gateTime p r ≤ b₀ → earlyTime p (r + 1) ≤ b₀ →
      gateTime p (r + 1) ≤ rho.horizon → ∀ source ∈ rho.honest, ∀ B,
      B ≠ .genesis → Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source)) →
      ∀ reader ∈ rho.honest,
        (faulty rho).card < strength (r + 1) reader B ∧
        ProtectsUntil (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader)
          B (strength (r + 1) reader B) (gateTime p (r + 1) + lifetime p) ∧
        Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p (r + 1)) reader))) :
    PersistsThrough (gridCO p) rho (gridInterface p).stable T b₀ b₁ := by
  intro source hs B hB t ht0 ht1
  change Block.Preceq B (stable (Run.readAt (gridCO p) rho T source)) at hB
  by_cases hn : B = .genesis
  · subst B
    intro reader _
    exact genesis_prefix _
  have hT : gateTime p 0 ≤ T := by
    by_contra h
    rw [read_stable_before_first_gate p rho T (lt_of_not_ge h) source] at hB
    exact hn (by simpa [Block.Preceq, Block.preceq] using hB)
  obtain ⟨s, hslo, hshi⟩ := exists_latest_gate p T hT
  obtain ⟨k, hklo, hkhi⟩ := exists_latest_gate p b₀ (hT.trans ho.interval.2.1)
  have hnext : gateTime p (s + 1) ≤ b₀ := by
    rw [next_gate_four_delta]
    have ha : T + 4 * p.Δ ≤ b₀ := ho.armed
    linarith
  have hsk : s < k := by
    by_contra h
    have hle := (gateTime_le_iff p (k + 1) (s + 1)).mpr
      (Nat.succ_le_succ (le_of_not_gt h))
    linarith
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hsk)
  have hsr : s ≤ r := Nat.le_of_lt_succ hsk
  have hclean := cleanThroughLabel_of_outage G T b₀ b₁ ho (r + 1) hklo
  rw [read_stable_eq_latest_gate p E rho ho.execution.toScheduleWellFormed
    s T hslo hshi source] at hB
  have hprefix : Block.Preceq B (stable (Run.readAt (gridCO p) rho (gateTime p r) source)) :=
    prefix_trans _ _ _ hB (clean_gate_record_prefix p E rho hΔ s r hsr
      (fun q hq => hclean q (hq.trans (Nat.le_succ r))) source hs)
  let U := gateTime p (r + 1)
  let W := gateTime p (r + 1 + 1)
  let g := fun v => strength (r + 1) v B
  have hbase := hcover r hklo
    source hs B hn hprefix
  have hseed := armingHeadsCompatible_of_clean p E rho hΔ (r + 1) hclean source hs B
    (hbase source hs).2.2
  have hstrong : ∀ v ∈ rho.honest, (faulty rho).card < g v := fun v hv => (hbase v hv).1
  have hrows : ∀ v ∈ rho.honest,
      ProtectsUntil (Run.readAt (gridCO p) rho U v) B (g v) (U + lifetime p) ∧
      Block.Preceq B (stable (Run.readAt (gridCO p) rho U v)) := fun v hv => (hbase v hv).2
  have hUW : U ≤ W := (gateTime_le_iff p _ _).mpr (Nat.le_succ _)
  have hWd : W < U + lifetime p := by
    dsimp [W, U]
    rw [next_gate_four_delta]
    linarith [lifetime_gt_four_delta p]
  by_cases htw : t < W
  · intro reader hr
    exact (protection_from_armed_read p E rho ho.execution B g U (U + lifetime p)
      hstrong hrows hseed t (hklo.trans ht0) (htw.trans hWd) reader hr).2
  · have hwt : W ≤ t := le_of_not_gt htw
    have hwh : W ≤ rho.horizon := hwt.trans (ht1.le.trans ho.interval.2.2.2)
    have hearly : earlyTime p (r + 1 + 1) ≤ b₀ := by
      rw [early_next_eq_gate]
      exact hklo
    have hpending := hpending (r + 1) hklo
      hearly hwh source hs B hn (hbase source hs).2.2
    let g' := fun v => strength (r + 1 + 1) v B
    have hstrong' : ∀ v ∈ rho.honest, (faulty rho).card < g' v :=
      fun v hv => (hpending v hv).1
    have hrows' : ∀ v ∈ rho.honest,
        ProtectsUntil (Run.readAt (gridCO p) rho W v) B (g' v) (W + lifetime p) ∧
        Block.Preceq B (stable (Run.readAt (gridCO p) rho W v)) :=
      fun v hv => (hpending v hv).2
    have hseed' := armingHeadsCompatible_of_protection p E rho ho.execution B g U
      (U + lifetime p) W hUW hWd hstrong hrows hseed
    have hbudget : b₁ - b₀ ≤ lifetime p :=
      ho.withinBudget.trans (min_le_right p.η (lifetime p))
    have htd : t < W + lifetime p := by
      change b₀ < W at hkhi
      linarith
    intro reader hr
    exact (protection_from_armed_read p E rho ho.execution B g' W (W + lifetime p)
      hstrong' hrows' hseed' t hwt htd reader hr).2

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Full P1 from the frozen OutageRegime. The last completed healthy gate
protects the record until the pending healthy gate renews it beyond b₁.
No delivery or participation premise is used inside the outage. -/
theorem stable_resilient_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (G T b₀ b₁ : Time)
    (ho : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho T b₀ b₁) :
    PersistsThrough (gridCO p) rho (gridInterface p).stable T b₀ b₁ := by
  exact resilient_of_covering_protection p E rho hΔ G T b₀ b₁ ho
    (fun r v B => roundedLevel p (prefixSupport p (gateInput p rho r v) r B))
    (outage_covering_protection p E rho hΔ G T b₀ b₁ ho)
    (pending_outage_protection p E rho hΔ G T b₀ b₁ ho)

end AvailableChain.GridCO
end

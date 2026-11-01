module
public import AvailableChainFGSAProofs.Proofs.Clean.Chain
public import AvailableChainFGSAProofs.Proofs.Clean.StateEpoch
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSARun.Proofs.AC

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open AvailableChain.Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

private theorem clean_gate_label (s : Slot) :
    ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
  have he : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  rw [he, Int.mul_ediv_cancel_left _ (by have := p.deltaPos; positivity), Int.toNat_natCast]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An enabled event result is the raw result of its pre-gate store. -/
theorem clean_gate_raw {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho)
    (ht : enabledGateAt p c E rho j v s) :
    gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s) :=
  clean_gate_raw_enabled hsch ht

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Own-record processing after the clock leaves the gate store unchanged. -/
theorem clean_gate_store {j : Nat} {v : V} {s : Slot}
    (ht : IsGateTick p c rho j v s) :
    storeAt p c E rho (j + 1) v =
      gateStep p (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)) s := by
  change (V2.D.Run.stateBefore E rho (j + 1) v).st = _
  rw [V2.D.Run.stateBefore_succ E rho ht]
  simp only [V2.D.World.step, Function.update_self]
  rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho j v) v (SA.gateTime p.toParams s)]
  change (if isGateTime p (SA.gateTime p.toParams s) then
    gateStep p (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))
      ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat else _) = _
  rw [(isGateTime_iff p _).mpr ⟨s, rfl⟩, ite_eq_left rfl, clean_gate_label]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every old target is compatible with this completed gate result. -/
theorem clean_state_gate_guard {i j : Nat} {v : V} {s : Slot} {C : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C)) :
    ((actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))).obligations.any
      (fun row => !Block.compatible row.1 C)) = false := by
  apply List.any_eq_false.mpr
  intro row hr
  have hold : row ∈ (storeAt p c E rho j v).base.obligations :=
    (clockPre_obligations_sublist p _ _).subset hr
  obtain ⟨k, hk, r, B, hkt, _, hB, hrow⟩ := hs.leases v row hold
  have hcompat := cleanHist_belowLabel_compatible hh
    (belowLabel_of_gateResultAt hsch (Nat.lt_trans hk hji) hkt hB (Nat.le_refl r))
    (belowLabel_of_gateResultAt hsch hji ht hC (Nat.le_refl s))
  have hrowC := block_compatible_of_preceq_compatible hrow hcompat
  simpa only [Block.Compatible, Bool.not_eq_true', Bool.not_eq_false] using hrowC

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A scheduled gate under the fixed history passes the whole-result guard. -/
theorem clean_gate_passed {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : enabledGateAt p c E rho j v s) : gatePassedAt p c E rho j := by
  obtain ⟨C, hC, _⟩ := hh.nonempty j v s hji ht
  refine ⟨v, s, ht, ?_, C, ?_,
    clean_state_gate_guard hsch hji hh hs ht.1 hC⟩
  · change ((clockPre p (storeAt p c E rho j v) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht.1
  · exact (clean_gate_nonempty_raw hsch ht.1 hC).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A fresh gate saves its event result and appends the exact fast-write row. -/
theorem clean_gate_writes {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s) :
    GridCO.savedGenuine (storeAt p c E rho (j + 1) v).base s = gateResultAt p c E rho j ∧
    (∀ r, r ≠ s → GridCO.savedGenuine (storeAt p c E rho (j + 1) v).base r =
      GridCO.savedGenuine (storeAt p c E rho j v).base r) ∧
    (storeAt p c E rho (j + 1) v).fastWrite = (storeAt p c E rho j v).fastWrite ++
      [(s, if joinedAtTime p (storeAt p c E rho j v).restartTime
        (SA.gateTime p.toParams s) then
        fastSet p (eraseFG (storeAt p c E rho j v).fg.F)
          (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s
        else [])] := by
  have hf : GridCO.savedGenuine
      (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)).base s = none := by
    change ((clockPre p (storeAt p c E rho j v) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht
  have hw := gateStep_fresh_cases p _ s hf
  rw [clockPre_joined, clockPre_fg] at hw
  refine ⟨?_, ?_, ?_⟩
  · rw [clean_gate_store ht, hw.1, clean_gate_executed hsch ht]
    cases joinedAtTime p (storeAt p c E rho j v).restartTime (SA.gateTime p.toParams s) <;>
      rfl
  · intro r hr
    rw [clean_gate_store ht, gateStep_other p _ s r hr]
    change ((clockPre p (storeAt p c E rho j v) _).base.genuine.find? _).map _ = _
    rw [clockPre_genuine]
    rfl
  · rw [clean_gate_store ht, hw.2, clockPre_fastWrite]

/-- A suppressed gate keeps S and adds no lease or nonempty fast-write row. -/
theorem clean_gate_suppressed_fields {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hN : ¬ enabledGateAt p c E rho j v s) :
    S_at p c E rho (j + 1) v = S_at p c E rho j v ∧
    (storeAt p c E rho (j + 1) v).base.obligations.Sublist
      (storeAt p c E rho j v).base.obligations ∧
    (storeAt p c E rho (j + 1) v).fastWrite =
      (storeAt p c E rho j v).fastWrite ++ [(s, [])] := by
  let pre := clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)
  have hf : GridCO.savedGenuine pre.base s = none := by
    change ((clockPre p (storeAt p c E rho j v) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht
  have hj : joinedNow p pre = false := by
    rw [clockPre_joined]
    exact Bool.eq_false_iff.mpr (fun h => hN ((clean_gate_join_test_iff ht).mp h))
  have hn : NestOK pre := by
    change Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j v) _).fg.F)
      (clockPre p (storeAt p c E rho j v) _).base.stableRecord
    rw [clockPre_fg, clockPre_stable]
    exact nestOK_stateBefore E rho j v
  have hg := gateStep_unjoined p pre s hf hj
  have hk := hg.2.2 hn
  refine ⟨?_, ?_, ?_⟩
  · rw [S_at_def, S_at_def, clean_gate_store ht, hk.2.2, clockPre_stable]
  · rw [clean_gate_store ht, hk.2.1]
    exact clockPre_obligations_sublist p _ _
  · rw [clean_gate_store ht, hg.2.1, clockPre_fastWrite]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A new lease target is old or is a prefix of this gate's result. -/
theorem clean_gate_lease_targets {j : Nat} {v : V} {s : Slot} {C : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C))
    (row : Block × Nat × Time)
    (hr : row ∈ (storeAt p c E rho (j + 1) v).base.obligations) :
    (∃ g d, (row.1, g, d) ∈ (storeAt p c E rho j v).base.obligations) ∨
      Block.Preceq row.1 C := by
  let pre := clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)
  have hf : GridCO.savedGenuine pre.base s = none := by
    change ((clockPre p (storeAt p c E rho j v) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht
  rw [clean_gate_store ht] at hr
  change row ∈ (gateStep p pre s).base.obligations at hr
  have he : (gateStep p pre s).base.obligations =
      (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s).obligations := by
    have hj := fgsa_gate_joined_of_enabled E rho (clean_gate_enabled_of_result hsch ht hC)
    have hjpre : joinedNow p pre = true := by rwa [clockPre_joined]
    unfold gateStep
    rw [normalizeS_fields]
    simp only [hf, Option.isSome_none, Bool.false_eq_true, ite_false, hjpre]
    rfl
  rw [he] at hr
  rcases gateFrom_target_origin_slow p.toParams.engine (eraseFG pre.fg.F)
      (actView pre) s row.1 row.2.1 row.2.2 hr with hold | ⟨B, hB, hrow⟩
  · obtain ⟨g, d, hm⟩ := hold
    exact Or.inl ⟨g, d, (clockPre_obligations_sublist p _ _).subset hm⟩
  · have hc : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = some C :=
      (clean_gate_nonempty_raw hsch ht hC).2
    have hBC : B = C := Option.some.inj (hB.symm.trans hc)
    exact Or.inr (hBC ▸ hrow)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every member of the newly appended fast-write row is below the event result. -/
theorem clean_gate_fast_prefix {j : Nat} {v : V} {s : Slot} {C X : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C))
    (hX : X ∈ fastSet p (eraseFG (storeAt p c E rho j v).fg.F)
      (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s) :
    Block.Preceq X C := by
  obtain ⟨B, hB, hXB, _⟩ := fastSet_prefix p _ _ s hX
  have hc := (clean_gate_nonempty_raw hsch ht hC).2
  rw [clockPre_fg] at hc
  have hBC := Option.some.inj (hB.symm.trans hc)
  exact hBC ▸ hXB

private theorem clean_F_mono {j k : Nat} (hjk : j ≤ k) (v : V) :
    Block.Preceq (F_at p c E rho j v) (F_at p c E rho k v) := by
  apply eraseFG_preceq
  apply V2.D.Engine.stateBefore_stable_restore (P := fgsa p c)
    (fun nd => FGBlock.Preceq (storeAt p c E rho j v).fg.F nd.st.fg.F)
    ?_ ?_ (fun _ _ h => h) E rho hjk v ?_ (KitFG.preceq_refl _)
  · intro nd t h
    change FGBlock.Preceq _ (clock p nd.st t).fg.F
    rw [clock_fg]
    exact h
  · intro nd o h
    exact KitFG.preceq_trans h (process_F_mono p nd.st (toWire p o))
  · intro nd t h
    change FGBlock.Preceq _ (acRestart p nd.st t).fg.F
    rwa [acRestart_fg]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The old output is compatible with the current result under the fixed history. -/
theorem clean_gate_output_compatible {i j : Nat} {v : V} {s : Slot} {C : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C)) :
    Block.Compatible (S_at p c E rho j v) C := by
  have hc := belowLabel_of_gateResultAt hsch hji ht hC (Nat.le_refl s)
  rcases hs.sOrigin v with hg | ⟨k, hk, r, hkt, hB⟩ | ⟨k, hk, hSF⟩
  · rw [hg]
    exact block_compatible_of_common (block_genesis_preceq C) (block_preceq_refl C)
  · exact cleanHist_belowLabel_compatible hh
      (belowLabel_of_gateResultAt hsch (Nat.lt_trans hk hji) hkt hB (Nat.le_refl r)) hc
  · rw [hSF]
    exact cleanHist_belowLabel_compatible hh
      (belowLabel_of_preceq (clean_F_mono hk v)
        (belowLabel_mono_index (Nat.le_of_lt hji) (hs.fOrigin v).1)) hc

private theorem clean_gate_output_step {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    Block.Preceq (S_at p c E rho j v) (S_at p c E rho (j + 1) v) ∧
      (S_at p c E rho (j + 1) v = S_at p c E rho j v ∨
        gateResultAt p c E rho j = some (some (S_at p c E rho (j + 1) v))) := by
  by_cases hE : enabledGateAt p c E rho j v s
  · obtain ⟨C, hC, _⟩ := hh.nonempty j v s hji hE
    have hc := (clean_gate_nonempty_raw hsch ht hC).2
    rw [clockPre_fg] at hc
    have hview := fgsa_clockPre_gateView p (storeAt p c E rho j v) s
    have hraw : (fgsaAC E rho).raw j s v = some C := by
      have hb := congrArg (fun w => SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho j v).fg.F) w s) hview
      exact hb.symm.trans hc
    have hguard : ∀ lease ∈ ((fgsaAC E rho).gateView j v s).obligations,
        Block.Compatible (Gen.AC.Lease.target lease) C := by
      intro lease hm
      have he : (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)).base.obligations =
          ((fgsaAC E rho).gateView j v s).obligations := by
        have he' := congrArg GridCO.State.obligations hview
        exact he'
      rw [← he] at hm
      have hg := List.any_eq_false.mp (clean_state_gate_guard hsch hji hh hs ht hC) lease hm
      simpa only [Gen.AC.Lease.target, Block.Compatible, Bool.not_eq_true',
        Bool.not_eq_false] using hg
    have hcompat := clean_gate_output_compatible hsch hji hh hs ht hC
    have hadv : Block.Preceq (S_at p c E rho j v)
        (GridCO.advance (S_at p c E rho j v) C) := by
      unfold GridCO.advance
      split
      · exact block_preceq_refl _
      · next hn =>
        rcases Bool.or_eq_true_iff.mp hcompat with hSC | hCS
        · exact hSC
        · exact (hn hCS).elim
    have hjpre : joinedNow p (clockPre p (storeAt p c E rho j v)
        (SA.gateTime p.toParams s)) = true := by
      rw [clockPre_joined]
      exact fgsa_gate_joined_of_enabled E rho (clean_gate_enabled_of_result hsch ht hC)
    rcases (fgsaAC_gate_write E rho j s v hjpre ht).effects with hskip | hrun
    · have he : S_at p c E rho (j + 1) v = S_at p c E rho j v := hskip.2.1
      rw [he]
      exact ⟨block_preceq_refl _, Or.inl rfl⟩
    · have hw := (hrun.accept C hraw hguard).1
      change (storeAt p c E rho (j + 1) v).base.stableRecord =
        Gen.AC.normalizeOutput (F_at p c E rho j v)
          (GridCO.advance (storeAt p c E rho j v).base.stableRecord C) at hw
      rw [← S_at_def p c E rho (j + 1) v, ← S_at_def p c E rho j v] at hw
      rw [hw, Gen.AC.normalizeOutput_def]
      have hnest : Block.Preceq (F_at p c E rho j v) (S_at p c E rho j v) :=
        nestOK_stateBefore E rho j v
      rw [ite_eq_left (show Block.preceq (F_at p c E rho j v)
        (GridCO.advance (S_at p c E rho j v) C) = true from block_preceq_trans hnest hadv)]
      refine ⟨hadv, ?_⟩
      unfold GridCO.advance
      split
      · exact Or.inl rfl
      · exact Or.inr hC
  · have he := (clean_gate_suppressed_fields hsch ht hE).1
    rw [he]
    exact ⟨block_preceq_refl _, Or.inl rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The gate advances S under the fixed completed history; normalization is inert. -/
theorem clean_gate_sExtends {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    Block.Preceq (S_at p c E rho j v) (S_at p c E rho (j + 1) v) :=
  (clean_gate_output_step hsch hji hh hs ht).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The gate keeps the old output origin or supplies this gate's exact event value. -/
theorem clean_gate_sOrigin {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    S_at p c E rho (j + 1) v = .genesis ∨
      (∃ k < j + 1, ∃ r, IsGateTick p c rho k v r ∧
        gateResultAt p c E rho k = some (some (S_at p c E rho (j + 1) v))) ∨
      (∃ k ≤ j + 1, S_at p c E rho (j + 1) v = F_at p c E rho k v) := by
  rcases (clean_gate_output_step hsch hji hh hs ht).2 with he | hresult
  · rw [he]
    rcases hs.sOrigin v with hg | ⟨k, hk, r, hkt, hC⟩ | ⟨k, hk, hF⟩
    · exact Or.inl hg
    · exact Or.inr (Or.inl ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, hkt, hC⟩)
    · exact Or.inr (Or.inr ⟨k, Nat.le_trans hk (Nat.le_succ j), hF⟩)
  · exact Or.inr (Or.inl ⟨j, Nat.lt_succ_self j, s, ht, hresult⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
All lease rows after the gate retain a passed event origin, including due rows. -/
theorem clean_gate_leases {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    ∀ row ∈ (storeAt p c E rho (j + 1) v).base.obligations,
      ∃ k < j + 1, ∃ r C, IsGateTick p c rho k v r ∧ gatePassedAt p c E rho k ∧
        gateResultAt p c E rho k = some (some C) ∧ Block.Preceq row.1 C := by
  by_cases hE : enabledGateAt p c E rho j v s
  · obtain ⟨C, hC, _⟩ := hh.nonempty j v s hji hE
    intro row hr
    rcases clean_gate_lease_targets hsch ht hC row hr with ⟨g, d, hm⟩ | hrow
    · obtain ⟨k, hk, r, B, hkt, hp, hB, htarget⟩ := hs.leases v (row.1, g, d) hm
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, B, hkt, hp, hB, htarget⟩
    · exact ⟨j, Nat.lt_succ_self j, s, C, ht, clean_gate_passed hsch hji hh hs hE, hC, hrow⟩
  · intro row hr
    obtain ⟨k, hk, r, C, hkt, hp, hC, hpre⟩ := hs.leases v row
      ((clean_gate_suppressed_fields hsch ht hE).2.1.subset hr)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, C, hkt, hp, hC, hpre⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A gate keeps older saved values in the receiver epoch. -/
theorem clean_gate_saved {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    ∀ k r C, k < j + 1 → enabledGateAt p c E rho k v r →
      V2.D.restartFree rho v k (j + 1) →
      activeCompatible (storeAt p c E rho (j + 1) v) C = true →
      gateResultAt p c E rho k = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho (j + 1) v).base r = some (some C) := by
  intro k r C hk hkt hRF hActive hC
  by_cases hrs : r = s
  · subst r
    have hkj := fgsa_tick_unique E rho hsch hkt.1 ht
    subst k
    exact (clean_gate_writes hsch ht).1.trans hC
  · have hkj : k < j := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
      · exact h
      · have htime := (V2.Event.tick.inj (Option.some.inj (hkt.1.symm.trans ht))).2
        have hlabel : r = s := by
          have hr := clean_gate_label (p := p) r
          rw [htime] at hr
          exact hr.symm.trans (clean_gate_label s)
        exact (hrs hlabel).elim
    rw [(clean_gate_writes hsch ht).2.1 r hrs]
    have hA : activeCompatible (storeAt p c E rho j v) C = true := by
      change Block.compatible C (eraseFG (storeAt p c E rho (j + 1) v).fg.F) = true at hActive
      rw [clean_gate_fg_eq ht] at hActive
      exact hActive
    exact hs.saved v k r C hkj hkt (hRF.mono le_rfl (Nat.le_succ j)) hA hC

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Every nonempty saved value after a gate has its exact event origin. -/
theorem clean_gate_savedOnly {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    ∀ r C, GridCO.savedGenuine (storeAt p c E rho (j + 1) v).base r = some (some C) →
      ∃ k < j + 1, V2.D.restartFree rho v k (j + 1) ∧
        enabledGateAt p c E rho k v r ∧ gateResultAt p c E rho k = some (some C) := by
  intro r C hC
  by_cases hrs : r = s
  · subst r
    have hR := (clean_gate_writes hsch ht).1.symm.trans hC
    exact ⟨j, Nat.lt_succ_self j, clean_gate_restartFree ht,
      clean_gate_enabled_of_result hsch ht hR, hR⟩
  · rw [(clean_gate_writes hsch ht).2.1 r hrs] at hC
    obtain ⟨k, hk, hRF, hkt, hresult⟩ := hs.savedOnly v r C hC
    have hRF' := clean_restartFree_succ hRF (by intro t hn; rw [ht] at hn; cases hn)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hresult⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A member of the new fast-write row satisfies the event's fast test. -/
theorem clean_gate_fastAt {j : Nat} {v : V} {s : Slot} {X : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hX : X ∈ fastSet p (eraseFG (storeAt p c E rho j v).fg.F)
      (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s) :
    fastAt p c E rho v s X := by
  let pre := clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)
  refine ⟨pre, ?_, ?_⟩
  · have hidx : V2.D.Run.tickIdx? rho v (SA.gateTime p.toParams s) = some j := by
      have hj := (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? rho v (SA.gateTime p.toParams s) = some k := by
        rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
        refine ⟨rho.events[j], List.getElem_mem hj, ?_⟩
        rw [(List.getElem?_eq_some_iff.mp ht).2]
        simp
      exact (fgsa_tick_unique E rho hsch (V2.D.Run.tickIdx?_spec hk) ht) ▸ hk
    rw [gateIn_def, preTick_def, hidx]
    rfl
  · change X ∈ (match SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho j v).fg.F) (actView pre) s with
      | none => []
      | some C => if (actView pre).obligations.any (fun row => !Block.compatible row.1 C)
          then [] else (actView pre).blocks.filter (fun (B : Block) =>
            B != Block.genesis && Block.preceq B C &&
              decide (SA.releaseThreshold p.toParams ≤
                SA.Root.prefixSupport p.toParams (actView pre) s B))) at hX
    cases hc : SA.Root.confirmationFrom p.toParams
        (eraseFG (storeAt p c E rho j v).fg.F) (actView pre) s with
    | none =>
      rw [hc] at hX
      exact (List.not_mem_nil hX).elim
    | some C =>
      rw [hc] at hX
      change X ∈ (if (actView pre).obligations.any (fun row => !Block.compatible row.1 C)
        then [] else (actView pre).blocks.filter (fun B =>
          B != Block.genesis && Block.preceq B C &&
            decide (SA.releaseThreshold p.toParams ≤
              SA.Root.prefixSupport p.toParams (actView pre) s B))) at hX
      by_cases hg : (actView pre).obligations.any (fun row => !Block.compatible row.1 C) = true
      · rw [ite_eq_left hg] at hX
        exact (List.not_mem_nil hX).elim
      · rw [ite_eq_right hg] at hX
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp hX).2).2

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A fast-write lookup after the gate has its exact passed event origin. -/
theorem clean_gate_fastWrite {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    ∀ r X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho (j + 1) v) r).getD [] →
      ∃ k < j + 1, V2.D.restartFree rho v k (j + 1) ∧
        enabledGateAt p c E rho k v r ∧ gatePassedAt p c E rho k ∧
        ∃ C, gateResultAt p c E rho k = some (some C) ∧
          Block.Preceq X C ∧ fastAt p c E rho v r X := by
  intro r X hX
  change X ∈ (((storeAt p c E rho (j + 1) v).fastWrite.find?
    (fun row => row.1 == r)).map Prod.snd).getD [] at hX
  rw [(clean_gate_writes hsch ht).2.2, List.find?_append] at hX
  cases ho : (storeAt p c E rho j v).fastWrite.find? (fun row => row.1 == r) with
  | some row =>
    rw [ho] at hX
    have hold : X ∈ (FGSA.fastWriteAt (storeAt p c E rho j v) r).getD [] := by
      change X ∈ (((storeAt p c E rho j v).fastWrite.find? _).map Prod.snd).getD []
      rw [ho]
      exact hX
    obtain ⟨k, hk, hRF, hkt, hp, C, hC, hXC, hf⟩ := hs.fastWrite v r X hold
    have hRF' := clean_restartFree_succ hRF (by intro t hn; rw [ht] at hn; cases hn)
    exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hp, C, hC, hXC, hf⟩
  | none =>
    rw [ho] at hX
    by_cases hsr : s = r
    · subst r
      simp only [Option.none_or, List.find?_cons, beq_self_eq_true,
        Option.map_some, Option.getD_some] at hX
      by_cases hE : enabledGateAt p c E rho j v s
      · obtain ⟨C, hC, _⟩ := hh.nonempty j v s hji hE
        have hj : joinedAtTime p (storeAt p c E rho j v).restartTime
            (SA.gateTime p.toParams s) = true :=
          fgsa_gate_joined_of_enabled E rho (hE)
        simp only [hj, ite_true] at hX
        exact ⟨j, Nat.lt_succ_self j, clean_gate_restartFree ht, hE,
            clean_gate_passed hsch hji hh hs hE,
          C, hC, clean_gate_fast_prefix hsch ht hC hX, clean_gate_fastAt hsch ht hX⟩
      · have hj : joinedAtTime p (storeAt p c E rho j v).restartTime
            (SA.gateTime p.toParams s) = false :=
          Bool.eq_false_iff.mpr (fun h => hE ((clean_gate_join_test_iff ht).mp h))
        simp only [hj, Bool.false_eq_true, ite_false] at hX
        exact (List.not_mem_nil hX).elim
    · simp only [Option.none_or, List.find?_cons,
        show (s == r) = false from beq_eq_false_iff_ne.mpr hsr,
        List.find?_nil, Option.map_none, Option.getD_none] at hX
      exact (List.not_mem_nil hX).elim

private theorem clean_gate_other_store {j : Nat} {v w : V} {s : Slot}
    (ht : IsGateTick p c rho j v s) (hw : w ≠ v) :
    storeAt p c E rho (j + 1) w = storeAt p c E rho j w := by
  change (V2.D.Run.stateBefore E rho (j + 1) w).st = _
  rw [V2.D.Run.stateBefore_succ E rho ht]
  simp only [V2.D.World.step, Function.update_of_ne hw]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
bp02 §5.5: the gate preserves the SA fields at every node.
DC MonotoneFrom restricts to honest reads; here other nodes keep their state
because the event updates one node. The FG source and frame fields are separate. -/
theorem clean_gate_fields_all {i j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (hji : j < i)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho j)
    (ht : IsGateTick p c rho j v s) :
    (∀ w row, row ∈ (storeAt p c E rho (j + 1) w).base.obligations →
      ∃ k < j + 1, ∃ r C, IsGateTick p c rho k w r ∧ gatePassedAt p c E rho k ∧
        gateResultAt p c E rho k = some (some C) ∧ Block.Preceq row.1 C) ∧
    (∀ w k r C, k < j + 1 → enabledGateAt p c E rho k w r →
      V2.D.restartFree rho w k (j + 1) →
      activeCompatible (storeAt p c E rho (j + 1) w) C = true →
      gateResultAt p c E rho k = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho (j + 1) w).base r = some (some C)) ∧
    (∀ w r C, GridCO.savedGenuine (storeAt p c E rho (j + 1) w).base r = some (some C) →
      ∃ k < j + 1, V2.D.restartFree rho w k (j + 1) ∧
        enabledGateAt p c E rho k w r ∧ gateResultAt p c E rho k = some (some C)) ∧
    (∀ w r X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho (j + 1) w) r).getD [] →
      ∃ k < j + 1, V2.D.restartFree rho w k (j + 1) ∧
        enabledGateAt p c E rho k w r ∧ gatePassedAt p c E rho k ∧
        ∃ C, gateResultAt p c E rho k = some (some C) ∧
          Block.Preceq X C ∧ fastAt p c E rho w r X) ∧
    (∀ w, S_at p c E rho (j + 1) w = .genesis ∨
      (∃ k < j + 1, ∃ r, IsGateTick p c rho k w r ∧
        gateResultAt p c E rho k = some (some (S_at p c E rho (j + 1) w))) ∨
      (∃ k ≤ j + 1, S_at p c E rho (j + 1) w = F_at p c E rho k w)) ∧
    (∀ w k l, k ≤ l → l ≤ j + 1 →
      Block.Preceq (S_at p c E rho k w) (S_at p c E rho l w)) := by
  have other (w : V) (hw : w ≠ v) := clean_gate_other_store (E := E) ht hw
  have hout (w : V) (hw : w ≠ v) : S_at p c E rho (j + 1) w = S_at p c E rho j w :=
    congrArg (fun st => st.base.stableRecord) (other w hw)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w row hr
    by_cases hw : w = v
    · subst w; exact clean_gate_leases hsch hji hh hs ht row hr
    · rw [other w hw] at hr
      obtain ⟨k, hk, r, C, hkt, hp, hC, hpre⟩ := hs.leases w row hr
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, C, hkt, hp, hC, hpre⟩
  · intro w k r C hk hkt hRF hActive hC
    by_cases hw : w = v
    · subst w; exact clean_gate_saved hsch hs ht k r C hk hkt hRF hActive hC
    · rw [other w hw]
      have hkj : k < j := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
        · exact hk
        · exact (hw (V2.Event.tick.inj (Option.some.inj (hkt.1.symm.trans ht))).1).elim
      rw [other w hw] at hActive
      exact hs.saved w k r C hkj hkt (hRF.mono le_rfl (Nat.le_succ j)) hActive hC
  · intro w r C hC
    by_cases hw : w = v
    · subst w; exact clean_gate_savedOnly hsch hs ht r C hC
    · rw [other w hw] at hC
      obtain ⟨k, hk, hRF, hkt, hresult⟩ := hs.savedOnly w r C hC
      have hRF' := clean_restartFree_succ hRF (by intro t hn; rw [ht] at hn; cases hn)
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hresult⟩
  · intro w r X hX
    by_cases hw : w = v
    · subst w; exact clean_gate_fastWrite hsch hji hh hs ht r X hX
    · rw [other w hw] at hX
      obtain ⟨k, hk, hRF, hkt, hp, C, hC, hpre, hfast⟩ := hs.fastWrite w r X hX
      have hRF' := clean_restartFree_succ hRF (by intro t hn; rw [ht] at hn; cases hn)
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), hRF', hkt, hp, C, hC, hpre, hfast⟩
  · intro w
    by_cases hw : w = v
    · subst w; exact clean_gate_sOrigin hsch hji hh hs ht
    · rw [hout w hw]
      rcases hs.sOrigin w with hg | ⟨k, hk, r, hkt, hC⟩ | ⟨k, hk, hF⟩
      · exact Or.inl hg
      · exact Or.inr (Or.inl ⟨k, Nat.lt_trans hk (Nat.lt_succ_self j), r, hkt, hC⟩)
      · exact Or.inr (Or.inr ⟨k, Nat.le_trans hk (Nat.le_succ j), hF⟩)
  · have hstep (w : V) : Block.Preceq (S_at p c E rho j w) (S_at p c E rho (j + 1) w) := by
      by_cases hw : w = v
      · subst w; exact clean_gate_sExtends hsch hji hh hs ht
      · rw [hout w hw]; exact block_preceq_refl _
    intro w k l hkl hlj
    rcases Nat.lt_or_eq_of_le hlj with hl | rfl
    · exact hs.sExtends w k l hkl (Nat.le_of_lt_succ hl)
    · rcases Nat.lt_or_eq_of_le hkl with hk | rfl
      · exact block_preceq_trans
          (hs.sExtends w k j (Nat.le_of_lt_succ hk) (Nat.le_refl j)) (hstep w)
      · exact block_preceq_refl _

end AvailableChain.FGSA.Run
end

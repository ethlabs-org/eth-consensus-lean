module
public import AvailableChainFGSAProofs.Proofs.Outage.Arming
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingBatch
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPrefix
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPending
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel
public import AvailableChainFGSARun.Proofs.AncestorDeadlinesStore

public section

/-! Plan O-ARM §5 `pending_gate_lease_or_F`, §6.5. The state of every honest
node after all ticks at the pending gate d(l + 1) and before the deliveries at
that time. The gate has no saved result, its raw result covers `D`, and every
lease target is below `D`, so the gate accepts. It advances S and writes a
lease for B at the release level with deadline at least d(l + 1) + L. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; the clock at a gate time is
the gate step of the pre-gate clock. -/
theorem arming_clock_gate (p : Params) (st : State p.n) (s : Slot) :
    clock p st (SA.gateTime p.toParams s) =
      gateStep p (clockPre p st (SA.gateTime p.toParams s)) s := by
  have hd : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * s + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hi : ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
    rw [hd, Int.mul_ediv_cancel_left _ (by have := p.deltaPos; positivity)]
    exact Int.toNat_natCast s
  change (if _ then _ else _) = _
  rw [hi]
  have hn : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by
    rw [hd]; have := p.deltaPos; positivity
  simp only [hn, decide_true, BEq.rfl, Bool.and_self, ite_true]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; the release level is
admitted by the fast test or by the slow test. -/
theorem arming_admission (p : Params) {n : Nat} (v : GridCO.State n .root) (r : Slot) (B : Block)
    (h : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v r B ∨
      GridCO.slowEligible p.toParams.engine v r B = true) :
    SA.releaseThreshold p.toParams ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine n .root v r B := by
  have hpolicy : @GridCO.LeasePolicy.slowArming GridCO.slowLeasePolicy = true := rfl
  simp only [GridCO.admissionLevels, hpolicy, ite_true]
  have hb : (decide (SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams v r B) ||
      GridCO.slowEligible p.toParams.engine v r B) = true := by
    rcases h with h | h
    · simp only [h, decide_true, Bool.true_or]
    · simp only [h, Bool.or_true]
  split
  · exact List.mem_singleton_self _
  · next h => exact absurd hb h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; an unsaved gate whose raw
result passes the lease guard keeps F and the blocks, advances S to a block
above B, and writes a release-level lease for every admitted non-genesis
prefix of the result, with deadline at least d + L. -/
theorem arming_gate_write (p : Params) (P : State p.n) (j : Slot) {Cj B : Block}
    (hJoined : joinedNow p P = true)
    (hsv : GridCO.savedGenuine P.base j = none)
    (hraw : SA.Root.confirmationFrom p.toParams (eraseFG P.fg.F) (actView P) j = some Cj)
    (hguard : ∀ row ∈ (actView P).obligations, Block.Compatible row.1 Cj)
    (hFC : Block.Preceq (eraseFG P.fg.F) Cj)
    (hB : B ∈ (actView P).blocks) (hne : B ≠ .genesis) (hBC : Block.Preceq B Cj)
    (hlev : SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams (actView P) j B ∨
      GridCO.slowEligible p.toParams.engine (actView P) j B = true) :
    (gateStep p P j).fg = P.fg ∧ (gateStep p P j).base.blocks = P.base.blocks ∧
    Block.Preceq B (gateStep p P j).base.stableRecord ∧
    ∃ d, (B, SA.releaseThreshold p.toParams, d) ∈ (gateStep p P j).base.obligations ∧
      SA.gateTime p.toParams j + L p ≤ d := by
  have hgs : gateStep p P j = normalizeS
      { onView (fun v => SA.Root.gateFrom p.toParams (eraseFG P.fg.F) v j) P with
        fastWrite := P.fastWrite ++ [(j, fastSet p (eraseFG P.fg.F) (actView P) j)] } := by
    change normalizeS (if _ then _ else _) = _
    rw [hsv]
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false, hJoined,
      Bool.not_true]
  have hany : (actView P).obligations.any (fun row => !Block.compatible row.1 Cj) = false := by
    apply List.any_eq_false.mpr
    intro row hr
    have h := hguard row hr
    change Block.compatible row.1 Cj = true at h
    simp only [h, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  have hw := gateFrom_eq_writeKeys_fgsa p.toParams (eraseFG P.fg.F) (actView P) j Cj hraw hany
  have hS : (SA.Root.gateFrom p.toParams (eraseFG P.fg.F) (actView P) j).stableRecord =
      GridCO.advance (actView P).stableRecord Cj := by
    rw [hw, arming_writeKeys_stable]
  have hadv : ∀ X, Block.Preceq X Cj →
      Block.Preceq X (GridCO.advance (actView P).stableRecord Cj) := by
    intro X hX
    change Block.Preceq X (if Block.preceq Cj (actView P).stableRecord then
      (actView P).stableRecord else Cj)
    split
    · next h => exact block_preceq_trans hX h
    · exact hX
  rw [hgs, normalizeS_fields]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Block.Preceq B (if Block.preceq (eraseFG P.fg.F)
      (SA.Root.gateFrom p.toParams (eraseFG P.fg.F) (actView P) j).stableRecord then
      (SA.Root.gateFrom p.toParams (eraseFG P.fg.F) (actView P) j).stableRecord
      else eraseFG P.fg.F)
    rw [hS]
    split
    · exact hadv B hBC
    · next h => exact absurd (hadv _ hFC) h
  · change ∃ d, (B, SA.releaseThreshold p.toParams, d) ∈
      (SA.Root.gateFrom p.toParams (eraseFG P.fg.F) (actView P) j).obligations ∧ _
    rw [hw]
    apply arming_writeKeys_row
    rw [@GridCO.gateWriteKeys_def GridCO.slowLeasePolicy]
    exact List.mem_flatMap.mpr ⟨B, List.mem_filter.mpr ⟨hB,
      Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr hne, hBC⟩⟩,
      List.mem_map.mpr ⟨_, arming_admission p _ j B hlev, rfl⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; with unique lease targets
the lease read of a stored target is its row deadline. -/
theorem arming_leaseOf (p : Params) (st : State p.n) (h : CStoreInv p st) {B : Block}
    {g : Nat} {d : Time} (hm : (B, g, d) ∈ st.base.obligations) :
    leaseOf st B = some d := by
  change (st.base.obligations.find? (fun row => row.1 == B)).map (fun row => row.2.2) = some d
  cases hf : st.base.obligations.find? (fun row => row.1 == B) with
  | none => exact absurd (beq_self_eq_true B) (List.find?_eq_none.mp hf _ hm)
  | some r₀ =>
    have hr₀ := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have heq : r₀ = (B, g, d) :=
      List.inj_on_of_nodup_map h.leaseKeys.1 hr₀ hm (beq_iff_eq.mp hp)
    subst heq
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §6.5. Class (iii). DC: INTENTIONAL; every named entry of an honest
row before the post-tick read is on a chain with B. An action before d(l + 1)
reads a gate of label at most `l`, below `D`; an action at d(l + 1) reads the
pending gate, whose result covers `D` (field 9). -/
theorem arming_rows_compat {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hroots : NamedRootCollisionFree p c E rho)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    {fast : Bool} {T b₀ b₁ : Time} {B : Block} {l : Slot} {u : V} {s : Slot} {C : Block}
    {iₛ : Nat} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    {Bh : FGBlock (Fin p.n)} (hBh : eraseFG Bh = B) :
    ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) →
      FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e := by
  intro y r a e ⟨k, hk, hrow⟩ hent heScope
  obtain ⟨e', C', G, hent', hSource, hee, hTC, hG, hCG, _⟩ := hnamed k y r a hrow
  have h1 : ((heightView p e).h, e.root) =
      ((heightView p C').h, (heightView p C').T_h.root) := by
    rw [← hee]
    exact Option.some.inj (hent.symm.trans hent')
  have he : e = (heightView p C').T_h := rootScope_eq hroots heScope
    (rootScope_entry (rootScope_source hrow.1 hSource)) (Prod.mk.inj h1).2
  have heG : Block.Preceq (eraseFG e) G :=
    block_preceq_trans (eraseFG_preceq (he ▸ hTC)) hCG
  have hkt : k < timeIdx rho (SA.gateTime p.toParams (l + 1)) :=
    lt_of_lt_of_le hk (preIdx_le_afterTicksIdx E rho hs _).2
  have htick : IsGateTick p c rho k y (r * p.R) := hrow.2.1
  have hrj : r * p.R ≤ l + 1 :=
    (arming_gate_le_iff p _ _).mp ((arming_lt_timeIdx_iff hs _ htick).mp hkt)
  obtain ⟨W, heW, hBW⟩ : ∃ W, Block.Preceq (eraseFG e) W ∧ Block.Preceq B W := by
    rcases Nat.lt_or_eq_of_le hrj with hlt | heq
    · have hrl : r * p.R ≤ l := Nat.lt_succ_iff.mp hlt
      have hgb : SA.gateTime p.toParams (r * p.R) ≤ b₀ :=
        ((arming_gate_le_iff p _ _).mpr hrl).trans hc.gate_le_cut
      have hGD := hc.max_le _ G (arming_clean_of_tick hs (arming_enabled_of_result hs htick
        ((gateResultAt_eq_gateResult p c E rho hs htick).trans hG)) hgb hG).2 hrl
      exact ⟨D, block_preceq_trans heG hGD, hc.max_read⟩
    · rw [heq] at htick hG
      obtain ⟨_, ⟨Cj, hCj, hDCj⟩, _⟩ := hc.pending_input k y htick hrow.1
      have hGr : gateResult p c E rho y (l + 1) = some (some Cj) :=
        (arming_gateResult_tick hs (arming_enabled_of_result hs htick
        ((gateResultAt_eq_gateResult p c E rho hs htick).trans hG))).trans (congrArg some hCj)
      rw [hGr] at hG
      have hGC : Cj = G := Option.some.inj (Option.some.inj hG)
      exact ⟨G, heG, block_preceq_trans hc.max_read (hGC ▸ hDCj)⟩
  rcases block_preceq_total_of_common heW hBW with h | h
  · exact Or.inl (arming_lift (hBh ▸ h))
  · exact Or.inr (arming_lift (hBh ▸ h))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan O-ARM §5 `pending_gate_lease_or_F`, §6.5. Class (iii). DC: INTENTIONAL;
the certificate form at its label `l`. The read index is I⁺, after all ticks
at d(l + 1) and before the deliveries at d(l + 1). -/
theorem arming_gate_core {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∀ y ∈ rho.honest, E.awake y (SA.gateTime p.toParams (l + 1)) = true →
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  have _hcanonicalFrame := hframe
  intro y hy hAw I st
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨i, hi⟩ := arming_tick_exists hs hdelta hy (4 * (l + 1) + 6)
    (arming_gate_nat p (l + 1)) hgate hAw
  obtain ⟨h9a, ⟨Cj, hCj, hDCj⟩, h9c, h9d, h9e, h9f, h9g⟩ := hc.pending_input i y hi hy
  let P := FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
  have hEnabled := fgsa_enabledGate_noRestart E rho hnr hi
  have hJoined : joinedNow p
      (FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))) = true := by
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho hEnabled
  have hst := arming_tick_store hs hnr hi
  have hFD : Block.Preceq (F_at p c E rho i y) D := by
    have h := (hc.prefix_state _ y le_rfl (arming_idxBefore_le_length rho _) hy).1
    change Block.Preceq (eraseFG (storeAt p c E rho i y).fg.F) D
    rw [hst]
    exact h
  have hPF : eraseFG P.fg.F = F_at p c E rho i y := by
    change eraseFG (clockPre p (storeAt p c E rho i y) _).fg.F =
      eraseFG (storeAt p c E rho i y).fg.F
    rw [clockPre_fg]
  have hlev : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams (actView P) (l + 1) B ∨
      GridCO.slowEligible p.toParams.engine (actView P) (l + 1) B = true := by
    cases fast with
    | true => exact Or.inl (h9f rfl)
    | false =>
      right
      obtain ⟨hk2, hwin⟩ := h9g rfl
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true hk2, List.all_eq_true.mpr ?_⟩
      intro a ha
      obtain ⟨Ca, hsv, hBCa⟩ := hwin a (List.mem_range.mp ha)
      rw [show GridCO.savedGenuine (actView P) (l + 1 - (a + 1)) = some (some Ca) from hsv]
      exact hBCa
  have hBC : Block.Preceq B Cj := block_preceq_trans hc.max_read hDCj
  obtain ⟨hfg, hblocks, hS, d, hrow, hd⟩ := arming_gate_write p P (l + 1) hJoined h9a hCj
    (fun row hrow => block_compatible_of_common (block_preceq_trans (h9c row hrow) hDCj)
      (block_preceq_refl Cj))
    (hPF ▸ block_preceq_trans hFD hDCj) h9d hne hBC hlev
  -- The post-tick store of y is the gate step of its pre-gate clock.
  have hI : storeAt p c E rho I y = gateStep p P (l + 1) := by
    change (V2.D.Run.stateBefore E rho I y).st = _
    rw [← afterTicks_eq_stateBefore E rho hs, afterTicks_node E rho hs hi]
    exact (tick_st (c := c) E rho _ y _).trans (arming_clock_gate p _ (l + 1))
  have hFI : F_at p c E rho I y = F_at p c E rho i y := by
    change eraseFG (storeAt p c E rho I y).fg.F = eraseFG (storeAt p c E rho i y).fg.F
    rw [hI, hfg]
    exact hPF
  refine ⟨?_, ?_⟩
  · change Block.Preceq B (storeAt p c E rho I y).base.stableRecord
    rw [hI]
    exact hS
  by_cases hBF : Block.Preceq B (F_at p c E rho I y)
  · exact Or.inl hBF
  right
  have hFB : Block.Preceq (F_at p c E rho I y) B := by
    rw [hFI]
    rcases Bool.or_eq_true_iff.mp h9e with h | h
    · exact h
    · exact absurd (hFI ▸ h) hBF
  refine ⟨hFB, fun heq => hBF (heq ▸ block_preceq_refl _), d, ?_, ?_, hd, ?_⟩
  · have hm : (B, SA.releaseThreshold p.toParams, d) ∈ st.base.obligations := by
      change _ ∈ (storeAt p c E rho I y).base.obligations
      rw [hI]
      exact hrow
    exact arming_leaseOf p st (cstoreInv_stateBefore E rho I y) hm
  · exact lt_of_lt_of_le (lt_add_of_pos_right _ (arming_L_pos p)) hd
  · have hinv : CStoreInv p st := cstoreInv_stateBefore E rho I y
    have hBm : B ∈ st.base.blocks := by
      change B ∈ (storeAt p c E rho I y).base.blocks
      rw [hI, hblocks]
      exact ((actView_blocks P B).mp h9d).1
    obtain ⟨Bh, hBh, hBe⟩ := (hinv.baseTree B).1 hBm
    have hFBh : FGBlock.Preceq st.fg.F Bh := arming_lift (hBe ▸ hFB)
    have hcp := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat
    obtain ⟨_, _, hdom, _⟩ := (hcp I y Bh hy (arming_rows_compat (hroots := hroots) hs hnamed hc
        hBe)).2
    rcases hdom hBh hFBh with hZ | hD
    · right
      rw [← hBe]
      exact eraseFG_preceq hZ
    · left
      refine ⟨Bh, ?_, hBe⟩
      rw [fgsa_fullTree_eq_filtered, ← fgsa_domainR_eq_filtered]
      exact hD

/-- Pending lease closure uses the consuming receiver's enabled gate and epoch. -/
theorem arming_gate_core_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hLabel : coverLabel p b₀ = l + 1)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  have _hcanonicalFrame := hframe
  intro y hyG I st
  have hs := hvalid.toScheduleWellFormed
  have hQ : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hLabel]
    cases fast with
    | true => exact rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk := p.kLarge
      constructor
      · have hk' : (1 : Int) ≤ (p.k : Int) := by exact_mod_cast (show 1 ≤ p.k by omega)
        omega
      · exact le_rfl
  obtain ⟨hy, _, hR⟩ := arming_receiver_window hyG hQ
  have hAw := (arming_receiver_times hyG hQ).2
  obtain ⟨i, hi⟩ := arming_tick_exists hs hdelta hy (4 * (l + 1) + 6)
    (arming_gate_nat p (l + 1)) hgate hAw
  obtain ⟨h9a, ⟨Cj, hCj, hDCj⟩, h9c, h9d, h9e, h9f, h9g⟩ := hc.pending_input i y hi hy
  let P := FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
  have hEnabled := arming_receiver_enabled hs hyG hQ hi
  have hTickEpoch : V2.D.restartFree rho y
      (rho.idxBefore (SA.gateTime p.toParams (l + 1))) i := by
    intro k w hstart hki he
    have hw : SA.gateTime p.toParams (l + 1) ≤ w := by
      by_contra hn
      have hk := (Gen.V2.Duty.index_lt_idxBefore_iff hs he _).mpr (lt_of_not_ge hn)
      omega
    have hwg : w ≤ SA.gateTime p.toParams (l + 1) := by
      by_contra hn
      have hik := V2.D.Engine.eventIndex_lt_of_time_lt hs hi he (lt_of_not_ge hn)
      omega
    have hsg : slotStartZ p ((l + 1 : Nat) : Int) < SA.gateTime p.toParams (l + 1) := by
      change 4 * p.Δ * ((l + 1 : Nat) : Int) <
        4 * p.Δ * ((l + 1 : Nat) : Int) + 6 * p.Δ
      linarith [p.deltaPos]
    exact hR w (hsg.trans_le hw) (hwg.trans_eq (congrArg (SA.gateTime p.toParams)
      hLabel.symm)) (List.mem_of_getElem? he)
  have hJoined : joinedNow p
      (FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))) = true := by
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho hEnabled
  have hst := arming_tick_store_on hs hi hTickEpoch
  have hFD : Block.Preceq (F_at p c E rho i y) D := by
    have h := (hc.prefix_state _ y le_rfl (arming_idxBefore_le_length rho _) hy).1
    change Block.Preceq (eraseFG (storeAt p c E rho i y).fg.F) D
    rw [hst]
    exact h
  have hPF : eraseFG P.fg.F = F_at p c E rho i y := by
    change eraseFG (clockPre p (storeAt p c E rho i y) _).fg.F =
      eraseFG (storeAt p c E rho i y).fg.F
    rw [clockPre_fg]
  have hlev : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams (actView P) (l + 1) B ∨
      GridCO.slowEligible p.toParams.engine (actView P) (l + 1) B = true := by
    cases fast with
    | true => exact Or.inl (h9f rfl)
    | false =>
      right
      obtain ⟨hk2, hwin⟩ := h9g rfl
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true hk2, List.all_eq_true.mpr ?_⟩
      intro a ha
      obtain ⟨Ca, hsv, hBCa⟩ := hwin a (List.mem_range.mp ha)
      rw [show GridCO.savedGenuine (actView P) (l + 1 - (a + 1)) = some (some Ca) from hsv]
      exact hBCa
  have hBC : Block.Preceq B Cj := block_preceq_trans hc.max_read hDCj
  obtain ⟨hfg, hblocks, hS, d, hrow, hd⟩ := arming_gate_write p P (l + 1) hJoined h9a hCj
    (fun row hrow => block_compatible_of_common (block_preceq_trans (h9c row hrow) hDCj)
      (block_preceq_refl Cj))
    (hPF ▸ block_preceq_trans hFD hDCj) h9d hne hBC hlev
  -- The post-tick store of y is the gate step of its pre-gate clock.
  have hI : storeAt p c E rho I y = gateStep p P (l + 1) := by
    change (V2.D.Run.stateBefore E rho I y).st = _
    rw [← afterTicks_eq_stateBefore E rho hs, afterTicks_node E rho hs hi]
    exact (tick_st (c := c) E rho _ y _).trans (arming_clock_gate p _ (l + 1))
  have hFI : F_at p c E rho I y = F_at p c E rho i y := by
    change eraseFG (storeAt p c E rho I y).fg.F = eraseFG (storeAt p c E rho i y).fg.F
    rw [hI, hfg]
    exact hPF
  refine ⟨?_, ?_⟩
  · change Block.Preceq B (storeAt p c E rho I y).base.stableRecord
    rw [hI]
    exact hS
  by_cases hBF : Block.Preceq B (F_at p c E rho I y)
  · exact Or.inl hBF
  right
  have hFB : Block.Preceq (F_at p c E rho I y) B := by
    rw [hFI]
    rcases Bool.or_eq_true_iff.mp h9e with h | h
    · exact h
    · exact absurd (hFI ▸ h) hBF
  refine ⟨hFB, fun heq => hBF (heq ▸ block_preceq_refl _), d, ?_, ?_, hd, ?_⟩
  · have hm : (B, SA.releaseThreshold p.toParams, d) ∈ st.base.obligations := by
      change _ ∈ (storeAt p c E rho I y).base.obligations
      rw [hI]
      exact hrow
    exact arming_leaseOf p st (cstoreInv_stateBefore E rho I y) hm
  · exact lt_of_lt_of_le (lt_add_of_pos_right _ (arming_L_pos p)) hd
  · have hinv : CStoreInv p st := cstoreInv_stateBefore E rho I y
    have hBm : B ∈ st.base.blocks := by
      change B ∈ (storeAt p c E rho I y).base.blocks
      rw [hI, hblocks]
      exact ((actView_blocks P B).mp h9d).1
    obtain ⟨Bh, hBh, hBe⟩ := (hinv.baseTree B).1 hBm
    have hFBh : FGBlock.Preceq st.fg.F Bh := arming_lift (hBe ▸ hFB)
    have hcp := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat
    obtain ⟨_, _, hdom, _⟩ := (hcp I y Bh hy (arming_rows_compat (hroots := hroots) hs hnamed hc
        hBe)).2
    rcases hdom hBh hFBh with hZ | hD
    · right
      rw [← hBe]
      exact eraseFG_preceq hZ
    · left
      refine ⟨Bh, ?_, hBe⟩
      rw [fgsa_fullTree_eq_filtered, ← fgsa_domainR_eq_filtered]
      exact hD

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §§7–8; plan O-ARM §5 `pending_gate_lease_or_F`. Class (iii).
DC: INTENTIONAL; at the read I⁺ after all ticks at the pending gate d(j),
j = l + 1, and before the deliveries at d(j), every honest S covers B, and B
is below F or has a lease to at least d(j) + L with B in the full domain or
below the frame root. -/
theorem pending_gate_lease_or_F {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (T b₀ b₁ : Time)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    (B : Block) (hne : B ≠ .genesis)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (fast : Bool) (harm : ArmingData p c E rho fast T b₀ b₁ B)
    (hgate : SA.gateTime p.toParams (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) ≤
      rho.horizon)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∀ y ∈ rho.honest,
      E.awake y (SA.gateTime p.toParams (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1)) = true →
      let j := ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1
      let I := afterTicksIdx rho (SA.gateTime p.toParams j)
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams j < dl ∧
            SA.gateTime p.toParams j + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  rw [ArmingData_def] at harm
  obtain ⟨u, s, C, iₛ, D, Dh, hc⟩ := harm
  exact arming_gate_core (hroots := hroots) (hstrat := hstrat)  hvalid hnr
    hdelta hstore hframe
    hsrc hnamed hne hc hgate

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationGate
public import AvailableChainFGSAProofs.Proofs.Outage.LaterHeads
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDeadlines
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedInduction

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The continuation event induction keeps global source names and durable F
compatibility. Stable inclusion is required only at covered receivers.
The result history is restricted to actual enabled gates in this event prefix. -/
theorem outage_continuation_event_induction
    (hBase : Base₂ p c E rho) (hf : FGFoundation p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {fast : Bool} {b₀ : Time} {B : Block} {β : FGBlock (Fin p.n)} {r : Slot}
    {I i : Nat} (hβ : eraseFG β = B)
    (hStart : afterTicksIdx rho (SA.gateTime p.toParams r) ≤ I)
    (hSeed : OutageSourceHistory p c E rho B I)
    (hCover : ∀ y ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho I y))
    (hResults : ∀ k x s C, I ≤ k → k < i → x ∈ rho.honest → r < s →
      enabledGateAt p c E rho k x s → gateResultAt p c E rho k = some (some C) →
      Block.Compatible C B)
    (hI : I ≤ i) (hi : i ≤ rho.events.length) :
    OutageSourceHistory p c E rho B i ∧ OutageNamedHistory p c E rho β i ∧
      (∀ y ∈ rho.honest, Block.Compatible (F_at p c E rho i y) B) ∧
      ∀ y ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho i y) := by
  classical
  have hs := hBase.valid.toScheduleWellFormed
  have names (k : Nat) (h : OutageSourceHistory p c E rho B k) :=
    outage_named_of_source_history hBase.idealization hβ h hnamed
  have frame (k : Nat) (h : OutageSourceHistory p c E rho B k) :=
    fun y hy => outage_source_frame_compatible hf hβ (names k h) (x := y) hy
  induction i, hI using Nat.le_induction with
  | base => exact ⟨hSeed, names I hSeed, frame I hSeed, hCover⟩
  | succ k hIk ih =>
    have hk : k < rho.events.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hi
    have hResult : ∀ a x s C, I ≤ a → a < k → x ∈ rho.honest → r < s →
        enabledGateAt p c E rho a x s → gateResultAt p c E rho a = some (some C) →
        Block.Compatible C B :=
      fun a x s C hIa hak => hResults a x s C hIa (hak.trans (Nat.lt_succ_self k))
    obtain ⟨hSource, _, hF, hS⟩ := ih hResult (Nat.le_of_lt hk)
    have after {x : V} {s : Slot} (ht : IsGateTick p c rho k x s) : r < s := by
      have htime := outage_tick_after_cut hs ht (hStart.trans hIk)
      exact (arming_gate_lt_iff p r s).mp htime
    have result {x : V} {s : Slot} {C : Block} (hx : x ∈ rho.honest)
        (ht : IsGateTick p c rho k x s) (hC : gateResultAt p c E rho k = some (some C)) :=
      hResults k x s C hIk (Nat.lt_succ_self k) hx (after ht)
        (arming_enabled_of_result hs ht hC) hC
    have hSource' : OutageSourceHistory p c E rho B (k + 1) := by
      constructor
      intro a x q C ha hx ht hC
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha) with hak | hak
      · exact hSource.history a x q C hak hx ht hC
      subst a
      have hgate : IsGateTick p c rho k x (q * p.R) := by
        change rho.events[k]? = some (.tick x (SA.gateTime p.toParams (q * p.R)))
        rwa [← fgsa_action_gate_time]
      obtain ⟨X, G, _, hCX, hG, hCG, _⟩ := htsrc x q C hx hC
      have hGr : gateResultAt p c E rho k = some (some G) := by
        rwa [gateResultAt_eq_gateResult p c E rho hs hgate]
      exact block_compatible_of_preceq_compatible (hCG C hCX) (result hx hgate hGr)
    refine ⟨hSource', names (k + 1) hSource', frame (k + 1) hSource', ?_⟩
    intro x hxG
    have hx := (Finset.mem_filter.mp hxG).1
    rcases fgsaAC_output_step E rho k x with he | ⟨s, ht⟩ |
        ⟨o, t, b, _, _, _, hn⟩ | ⟨t, hr, _⟩
    · change S_at p c E rho (k + 1) x = S_at p c E rho k x at he
      rw [he]
      exact hS x hxG
    · have hpost : storeAt p c E rho (k + 1) x =
          clock p (storeAt p c E rho k x) (SA.gateTime p.toParams s) := by
        change (rho.stateBefore E (k + 1) x).st = _
        rw [(rho.step_tick_eq E ht).1]
        exact tick_st (c := c) E rho _ x _
      change Block.Preceq B (storeAt p c E rho (k + 1) x).base.stableRecord
      rw [hpost, arming_clock_gate]
      let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s)
      have hBS : Block.Preceq B pre.base.stableRecord := by
        rw [clockPre_stable]
        exact hS x hxG
      have hFB : Block.Compatible (eraseFG pre.fg.F) B := by
        rw [clockPre_fg]
        exact hF x hx
      by_cases hJ : joinedNow p pre = true
      · apply outageV_gateStep_covers p pre (cstoreInv_clockPre p _
          (cstoreInv_stateBefore E rho k x) _) s B hBS hFB
        intro C hC
        have hres : gateResultAt p c E rho k = some (some C) := by
          have hguard : joinedAtTime p (storeAt p c E rho k x).restartTime
              (SA.gateTime p.toParams s) = true := by
            simpa only [pre, clockPre_joined] using hJ
          have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
            (fgsa_postClock_slot (c := c) (rho.stateBefore E k x) _).2.symm.trans
              (fgsa_gate_slot (c := c) (rho.stateBefore E k x) s)
          have hG : enabledGateAt p c E rho k x s := by
            refine ⟨ht, ?_⟩
            cases hr : (storeAt p c E rho k x).restartTime with
            | none => trivial
            | some w =>
              simp only [joinedAtTime, hr, hslot, Nat.cast_add, Nat.cast_one,
                add_sub_cancel_right, decide_eq_true_eq] at hguard
              exact hguard
          have hraw := inclusion_gate_raw_at_tick E rho hs hG
          exact hraw.trans (congrArg some hC)
        exact result hx ht hres
      · have hN : joinedNow p pre = false := Bool.eq_false_iff.mpr hJ
        unfold gateStep
        rw [hN]
        simp only [Bool.not_false, ite_true]
        split <;> rw [normalizeS_fields] <;> exact outage_normalize_covers hBS hFB
    · change S_at p c E rho (k + 1) x =
          Gen.AC.normalizeOutput (F_at p c E rho (k + 1) x) (S_at p c E rho k x) at hn
      rw [hn]
      exact outage_normalize_covers (hS x hxG) (frame (k + 1) hSource' x hx)
    · have hpost : storeAt p c E rho (k + 1) x =
          acRestart p (storeAt p c E rho k x) t := by
        change (rho.stateBefore E (k + 1) x).st = _
        rw [V2.D.Engine.state_after_restart hr]
        rfl
      change Block.Preceq B (storeAt p c E rho (k + 1) x).base.stableRecord
      rw [hpost, acRestart_stableRecord]
      exact hS x hxG

/-- Every live row at a later HEAD has passed expiry at handover.
Earlier result compatibility is required only at its actual write event. -/
theorem outage_head_rows_after_handover
    (hs : V2.D.ScheduleWellFormed E rho) {r s : Slot} {i : Nat} {x : V} {B : Block}
    (hEnd : OutageEnd p r ≤ SA.voteTime p.toParams s)
    (hResults : ∀ j q C, j < i → r < q → enabledGateAt p c E rho j x q →
      gateResultAt p c E rho j = some (some C) → Block.Compatible C B) :
    ∀ row ∈ (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.obligations,
      Block.Compatible row.1 B := by
  rw [inclusion_clock_offGate p _ _ (fun q => arming_gate_ne_vote p q s)]
  intro row hr
  by_contra hConflict
  have hm := (clockPre_obligations_sublist p _ _).subset hr
  have hd := outage_conflicting_row_deadline hs r B i x hResults row hm hConflict
  have hl : SA.voteTime p.toParams s < row.2.2 :=
    of_decide_eq_true (List.mem_filter.mp (outage_clockPre_expired_rows _ _ hr)).2
  exact (not_lt_of_ge (hd.trans hEnd)) hl

/-- An actual joined HEAD after handover uses only the earlier event invariant.
The marker's old receipt deadline is not used at this later reader. -/
theorem outage_marker_head_at_read [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) {B P : FGBlock (Fin p.n)}
    {k i : Nat} {y x : V} {m s : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x s (SA.voteTime p.toParams s))
    (hrm : restoredLabel p b₁ ≤ m) (hms : m < s)
    (hLate : restoredLabel p b₁ + p.k + 1 ≤ s)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBJ : FGBlock.Preceq B (heightView p P).J) (hnz : (heightView p P).h_j ≠ 0)
    (hNames : OutageNamedHistory p c E rho B i)
    (hResults : ∀ j q C, j < i → restoredLabel p b₁ < q →
      enabledGateAt p c E rho j x q → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C (eraseFG B)) :
    Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  have hEnd : OutageEnd p (restoredLabel p b₁) ≤ SA.voteTime p.toParams s := by
    rw [(outage_handover_time p _).1, arming_vote_eq, arming_vote_eq]
    have hcast := Int.ofNat_le.mpr hLate
    nlinarith [p.deltaPos]
  have hlocks := outage_head_rows_after_handover h.pre.base.valid.toScheduleWellFormed
    hEnd hResults
  have heq : s - 1 + 1 = s := Nat.sub_add_cancel (by dsimp only [Slot] at hms ⊢; omega)
  have hHead := outage_later_marker_head h.pre.base h.sync hf hk
    (by simpa only [heq] using hi) hy hx (by simpa only [heq] using hJ)
    (show m ≤ s - 1 by dsimp only [Slot] at hms ⊢; omega)
    (h.gst.trans (outage_restored_vote_cut p b₁ hrm)) hP hBJ hnz hNames
    (by simpa only [heq] using fun row hr _ => hlocks row hr)
  simpa only [heq] using hHead

/-- Once an actual marker and the finite prefix are established, the healthy
suffix produces its HEAD and gate compatibility together with source names.
The prefix ends after gate max(m,r+k), so a marker before r+k is allowed.
There is no future HEAD, result, receipt, or all-honest stable seed input. -/
theorem outage_marker_continuation_induction [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {B P : FGBlock (Fin p.n)} {k I i : Nat} {y : V} {m : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hy : y ∈ rho.honest) (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBJ : FGBlock.Preceq B (heightView p P).J) (hnz : (heightView p P).h_j ≠ 0)
    (hm : restoredLabel p b₁ ≤ m)
    (hStart : afterTicksIdx rho
      (SA.gateTime p.toParams (max m (restoredLabel p b₁ + p.k))) ≤ I)
    (hSeed : OutageSourceHistory p c E rho (eraseFG B) I)
    (hCover : ∀ x ∈ coveredNodes p E rho fast b₀,
      Block.Preceq (eraseFG B) (S_at p c E rho I x))
    (hPrefix : ∀ j x s C, j < I → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C (eraseFG B))
    (hI : I ≤ i) (hi : i ≤ rho.events.length) :
    (∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C (eraseFG B)) ∧
    OutageSourceHistory p c E rho (eraseFG B) i ∧ OutageNamedHistory p c E rho B i ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho i x) (eraseFG B)) ∧
      (∀ x ∈ coveredNodes p E rho fast b₀,
        Block.Preceq (eraseFG B) (S_at p c E rho i x)) ∧
      ∀ x ∈ rho.honest, ∀ row ∈ (storeAt p c E rho i x).base.obligations,
        ¬ Block.Compatible row.1 (eraseFG B) →
        row.2.2 ≤ OutageEnd p (restoredLabel p b₁) := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hrm : restoredLabel p b₁ ≤ m := hm
  have hStartR : afterTicksIdx rho (SA.gateTime p.toParams (restoredLabel p b₁)) ≤ I :=
    (afterTicksIdx_mono rho ((arming_gate_le_iff p _ _).mpr
      (hrm.trans (le_max_left _ _)))).trans hStart
  induction i, hI using Nat.le_induction with
  | base =>
    have hNames := outage_named_of_source_history h.pre.base.idealization rfl hSeed hnamed
    refine ⟨hPrefix, hSeed, hNames,
      fun x hx => outage_source_frame_compatible hf rfl hNames hx, hCover, ?_⟩
    intro x hx row hr hConflict
    exact outage_conflicting_row_deadline hs _ _ I x
      (fun j s C hj hrs hG hC => hPrefix j x s C hj hx hrs hG hC) row hr hConflict
  | succ n hIn ih =>
    have hn : n < rho.events.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hi
    obtain ⟨hResults, hSource, _, _, _⟩ := ih (Nat.le_of_lt hn)
    have hNew : ∀ j x s C, j < n + 1 → x ∈ rho.honest → restoredLabel p b₁ < s →
        enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
        Block.Compatible C (eraseFG B) := by
      intro j x s C hj hx hrs hG hC
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | hjn
      · exact hResults j x s C hjn hx hrs hG hC
      subst j
      have hCut : max m (restoredLabel p b₁ + p.k) < s :=
        (arming_gate_lt_iff p _ s).mp
          (outage_tick_after_cut hs hG.1 (hStart.trans hIn))
      have hms : m < s := (le_max_left _ _).trans_lt hCut
      have hLate : restoredLabel p b₁ + p.k < s :=
        (le_max_right _ _).trans_lt hCut
      apply outage_continuation_result_of_head_history h hx hrs hG hC
      intro q K hReader hK
      have hKeep := hK
      obtain ⟨a, _, _, ha, hem, _, _⟩ := hK
      have han : a < n := V2.D.Engine.eventIndex_lt_of_time_lt hs ha hG.1
        (fgsa_vote_lt_gate p s)
      have hHist : OutageSourceHistory p c E rho (eraseFG B) a :=
        ⟨fun z v r D hza hv hz hD => hSource.history z v r D (hza.trans han) hv hz hD⟩
      have hNames := outage_named_of_source_history h.pre.base.idealization rfl hHist hnamed
      have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
        slotOf_offset p s p.Δ p.deltaPos.le
          (by have := p.deltaPos; dsimp [Time] at *; omega)
      have hJ : joinedAt p E rho (rho.seatOf (.base (.head s)) q) s
          (SA.voteTime p.toParams s) := by
        simpa only [hslot] using hReader.1.2
      have hHead := outage_marker_head_at_read h hf hk ha hy hReader.1.1 hJ hm hms
        (Nat.succ_le_of_lt hLate) hP hBJ hnz hNames
        (fun z r D hza hrr hZ hD =>
          hResults z _ r D (hza.trans han) hReader.1.1 hrr hZ hD)
      have hEq := headTargetAtEmission_at_tick E rho hs hKeep ha rfl
      exact hEq.symm ▸ hHead
    have hState := outage_continuation_event_induction h.pre.base hf htsrc hnamed rfl hStartR
      hSeed hCover (fun j x s C _ hj hx hrs hG hC => hNew j x s C hj hx hrs hG hC)
      (Nat.le_succ_of_le hIn) hi
    refine ⟨hNew, hState.1, hState.2.1, hState.2.2.1, hState.2.2.2, ?_⟩
    intro x hx row hr hConflict
    exact outage_conflicting_row_deadline hs _ _ (n + 1) x
      (fun j s C hj hrs hG hC => hNew j x s C hj hx hrs hG hC) row hr hConflict

/-- The public read includes same-time deliveries and horizon events.
This adapter consumes the current event invariant, without a future callback. -/
theorem outage_continuation_inclusive_read
    (hs : V2.D.ScheduleWellFormed E rho) {B : Block} {x : V} {t : Time}
    (hS : Block.Preceq B (S_at p c E rho (timeIdx rho t) x))
    (hF : Block.Compatible (F_at p c E rho (timeIdx rho t) x) B) :
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  have hread := arming_stable_read hs x t
  exact ⟨hread.symm ▸ hS, hread.symm ▸ hS, by
    change Block.compatible _ _ = true
    rw [block_compatible_comm]
    exact hF⟩

end AvailableChain.FGSA.Run
end

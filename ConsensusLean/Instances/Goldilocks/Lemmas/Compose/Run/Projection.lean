module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # Goldilocks runs: the projections onto the component traces (C0.5)

`ac_projection` and `fg_projection` are in `Run/ACProjection` and `Run/FGProjection`. -/

namespace Consensus.Goldilocks

/-- Source-window service with inclusive lower bound and recipient-deadline cutoff.
The relay is actual acceptance; network receipt alone does not supply it. -/
structure RunTrace.SyncWindowBefore {P : Params} {A : NodeAC P} (tr : RunTrace A)
    (H : Set (Fin P.n)) (ΔF a b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x ∈ H, ∀ i m, tr.SendOrAdmitAt x i m → a ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      tr.MsgDeliveredBy y j (tr.time i) (tr.time i) m
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B → a ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (tr.time i) B
  relay : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B → a ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j (tr.time i) B
  attestation : ∀ x ∈ H, ∀ i att, tr.SendOrAdmitAttAt x i att → a ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) ΔF ≤ b →
      tr.deadline y j (tr.time i) ΔF ≤ tr.time j →
      tr.AttDeliveredBy y j (tr.time i) (tr.time i) ΔF att

/-- At source lower bound zero the existing finite service contract is unchanged. -/
theorem syncWindowBefore_zero_iff {P : Params} {A : NodeAC P} {tr : RunTrace A}
    {H : Set (Fin P.n)} {ΔF b : Time} :
    tr.SyncWindowBefore H ΔF 0 b ↔ tr.SyncBefore H ΔF b :=
  ⟨fun h => ⟨h.deltaF, h.message, h.block, h.relay, h.attestation⟩,
    fun h => ⟨h.deltaF, h.message, h.block, h.relay, h.attestation⟩⟩

namespace Compose

open Node

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

/-- A restart of the AC projection is a restart of the run. -/
theorem projAC_restartAt {y : Fin P.n} {k : Nat} : tr.projAC.RestartAt y k ↔ tr.RestartAt y k :=
  ⟨fun ⟨ℓ, hc, hr⟩ => ⟨ℓ, projAC_callAt.1 hc, hr⟩, fun ⟨ℓ, hc, hr⟩ => ⟨ℓ, projAC_callAt.2 hc, hr⟩⟩

/-- The AC projection's latest wakes are the run's. -/
theorem projAC_lastWake (y : Fin P.n) : tr.projAC.lastWake y = tr.lastWake y := by
  funext k
  induction k with
  | zero =>
    simp only [ACTrace.lastWake, RunTrace.lastWake]
    by_cases hr : tr.RestartAt y 0
    · simp only [projAC_restartAt.2 hr, hr, ↓reduceIte]
      rfl
    · simp [hr, mt projAC_restartAt.1 hr]
  | succ k ih =>
    simp only [ACTrace.lastWake, RunTrace.lastWake, ih]
    by_cases hr : tr.RestartAt y (k + 1)
    · simp only [projAC_restartAt.2 hr, hr, ↓reduceIte]
      rfl
    · simp [hr, mt projAC_restartAt.1 hr]

/-- The AC projection's deadlines are the run's with `Δ`. -/
theorem projAC_deadline (y : Fin P.n) (k : Nat) (τ : Time) :
    tr.projAC.deadline y k τ = tr.deadline y k τ P.Δ := by
  simp only [ACTrace.deadline, RunTrace.deadline, projAC_lastWake]

/-- Projection preserves both the inclusive source bound and recipient-deadline cutoff. -/
theorem syncWindowBefore_projection {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {ΔF a b : Time}
    {sg : A.Msg → Fin P.n} (h : LocalRun proposer dg H sg tr)
    (hs : tr.SyncWindowBefore H ΔF a b) :
    SyncACWindowBefore H (tr.HonestBlocks H) a b tr.projAC := by
  refine ⟨fun x hx i m hsa hai y hy j ℓ hc hdb hdl => ?_,
    fun x hx i B hacc hai y hy j ℓ hc hdb hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, projAC_callAt.1 hc₀, by
      rw [projAC_state h hx] at hm
      exact hm⟩
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x hx i m hsa' hai y hy j
      ⟨_, projAC_callAt.1 hc⟩ (by rw [← projAC_deadline]; exact hdb)
      (by rw [← projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', projAC_callAt.2 hc', Or.inl hm'⟩, ⟨ℓ', projAC_callAt.2 hc', Or.inr hm'⟩]
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := projAC_callAt.1 hc
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev h hx (projAC_callAt.1 hc₀) hb
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.cutLaw y hy j _ hc).1]
      rfl
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x hx i' B hi' (hti ▸ hai) y hy j ⟨_, hc⟩
      (by rw [hti, ← projAC_deadline]; exact hdb)
      (by rw [hti, ← projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ℓ', hc', hb', htk⟩ := accept_next h hy hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', projAC_callAt.2 hc', hb'⟩, ?_⟩
    change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (tr.time (i' + 1))
    rw [projAC_deadline, htk, ← hti]
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

/-- Deadline-bounded service projects without assuming service after the finite horizon. -/
theorem syncBefore_projection {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {ΔF b : Time}
    {sg : A.Msg → Fin P.n} (h : LocalRun proposer dg H sg tr) (hs : tr.SyncBefore H ΔF b) :
    SyncACBefore H (tr.HonestBlocks H) b tr.projAC :=
  (syncACWindowBefore_zero_iff _ _ _ _).mp
    (syncWindowBefore_projection h (syncWindowBefore_zero_iff.mpr hs))

/-- **`Sync` projects**: a send or admission of the AC projection is the run's, and its
processing is the run's; an `ac_on_block(B)` follows the FG acceptance of `B` at its time, whose
relay is an acceptance of `B`, followed at once by the AC call of `B` (not a restart, so with the
same deadline). -/
theorem sync_projection : SyncProjection := by
  intro P A dg H sg tr proposer ΔF a b h hs
  refine ⟨fun x hx i m hsa hai hib y hy j ℓ hc hdl => ?_,
    fun x hx i B hacc hai hib y hy j ℓ hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, projAC_callAt.1 hc₀, by
      rw [projAC_state h hx] at hm
      exact hm⟩
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x hx i m hsa' ⟨hai, hib⟩ y hy j
      ⟨_, projAC_callAt.1 hc⟩ (by rw [← projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', projAC_callAt.2 hc', Or.inl hm'⟩, ⟨ℓ', projAC_callAt.2 hc', Or.inr hm'⟩]
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := projAC_callAt.1 hc
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev h hx (projAC_callAt.1 hc₀) hb
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.cutLaw y hy j _ hc).1]
      rfl
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x hx i' B hi' ⟨hti ▸ hai, hti ▸ hib⟩ y hy j ⟨_, hc⟩
      (by rw [hti, ← projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ℓ', hc', hb', htk⟩ := accept_next h hy hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', projAC_callAt.2 hc', hb'⟩, ?_⟩
    change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (tr.time (i' + 1))
    rw [projAC_deadline, htk, ← hti]
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

section

open SA

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

private theorem joined_iff {τ t : Time} (hτ : 0 ≤ τ) :
    (0 < sp.toParams.slotOf t ∧ τ ≤ sp.toParams.slotTime (sp.toParams.slotOf t - 1)) ↔
      τ ≤ sp.ts ((sp.slot t : Int) - 1) := by
  have hΔ := sp.toParams.hΔ
  rcases Nat.eq_zero_or_pos (sp.toParams.slotOf t) with h0 | hpos
  · simp only [SAParams.slot, h0, lt_irrefl, false_and, false_iff, not_le, SAParams.ts]
    push_cast
    nlinarith
  · rw [sp.slotTime_eq]
    simp only [hpos, true_and, SAParams.ts, SAParams.slot]
    push_cast [Nat.one_le_iff_ne_zero.2 hpos.ne']
    rfl

/-- The latest restart time before cut `i`. -/
private noncomputable def lastBefore (tr : GoldilocksTrace sp ro) (y : Fin sp.n) :
    Nat → WithBot Time
  | 0 => ⊥
  | i + 1 => tr.lastWake y i

open Classical in
private theorem lastBefore_succ (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat) :
    lastBefore tr y (i + 1) =
      if tr.RestartAt y i then (tr.time i : WithBot Time) else lastBefore tr y i := by
  cases i <;> rfl

private theorem lastBefore_le {dg} {H} {tr : GoldilocksTrace sp ro}
    (h : GoldilocksRun proposer dg H tr)
    (y : Fin sp.n) (x : Time) :
    ∀ i, lastBefore tr y i ≤ x ↔ ∀ k < i, tr.RestartAt y k → tr.time k ≤ x := by
  intro i
  induction i with
  | zero => simp [lastBefore]
  | succ i ih =>
    rw [lastBefore_succ]
    split_ifs with hr
    · refine ⟨fun hx k hk hk' => ?_, fun hall => WithBot.coe_le_coe.2 (hall i (by omega) hr)⟩
      exact (h.time_mono (show k ≤ i by omega)).trans (WithBot.coe_le_coe.1 hx)
    · rw [ih]
      refine ⟨fun hall k hk hk' => ?_, fun hall k hk => hall k (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      exacts [hall k hk hk', absurd hk' hr]

private theorem restartTime_eq {dg} {H} {tr : GoldilocksTrace sp ro}
    (h : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) : ∀ i, (tr.state y i).ac.restartTime = lastBefore tr y i := by
  intro i
  induction i with
  | zero => rw [Trace.state, h.init y hy]; rfl
  | succ i ih =>
    rw [lastBefore_succ, ← ih]
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := h.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        have hpost : (tr.post i).ac = ((goldilocksNode sp ro).step y (tr.state y i).ac ℓ.frame
            (tr.time i) ℓ.call).1 := (congrArg Prod.fst hlaw.2.1).symm
        rw [hpost]
        split_ifs with hR
        · obtain ⟨ℓ', hℓ', hr⟩ := hR
          cases Option.some.inj (hc.2.symm.trans hℓ'.2)
          rw [hr]
          have hΦ : FrameOK ℓ.frame := hlaw.1 ▸
            (Store.frame_realization _ _ _ _ (fg_reachable h.toLocalRun hy i)).1
          exact (restart_state sp _ ro y _ ℓ.frame (tr.time i) hΦ
            (h.time_nonneg i)).2.2.2.2.2.2.1
        · exact step_restartTime y _ _ _ _ fun hr => hR ⟨ℓ, hc, hr⟩
      | fg ℓ =>
        split_ifs with hR
        · obtain ⟨ℓ', hℓ', _⟩ := hR
          cases Option.some.inj (hc.2.symm.trans hℓ'.2)
        congr 1
        cases ℓ with
        | block B acc =>
          cases acc
          · rw [hlaw.2]
          · exact hlaw.2.2.1
        | attestation a => exact hlaw.2.1
        | attest C s =>
          cases s
          · rw [hlaw.2]
          · exact hlaw.2.2
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      split_ifs with hR
      · obtain ⟨ℓ, hℓ, _⟩ := hR
        exact absurd ⟨_, hℓ⟩ hc
      · rfl

/-- **Joining and participation project**: a restart of the run is a restart of the AC
projection, and the run's joined test (with `0 < slot(t)`) is the SA's on restart times `≥ 0`;
the AC state's `restart_time` at a call is the time of the latest restart before it (a restart
sets it, every other call keeps it), and the restarts at or before the time of a call other than
a restart are the ones before it (restarts come first at a time). -/
theorem joined_projection : JoinedProjection := by
  intro sp ro dg H tr proposer h y hy t
  have hpt : ∀ z, (tr.JoinedAt z t ↔ SA.JoinedAt tr.projAC z t) := fun z => by
    unfold RunTrace.JoinedAt SA.JoinedAt
    refine forall_congr' fun k => ?_
    rw [projAC_restartAt]
    exact imp_congr_right fun _ => imp_congr_right fun _ => joined_iff (h.time_nonneg k)
  refine ⟨hpt y, fun i hi hnr hit => ?_, ?_⟩
  · -- the restarts at or before `t` are the restarts before `i`
    have hset : ∀ k, tr.RestartAt y k → (tr.time k ≤ t ↔ k < i) := by
      intro k hk
      refine ⟨fun hkt => ?_, fun hki => hit ▸ h.time_mono hki.le⟩
      by_contra hik
      rcases Nat.lt_or_eq_of_le (not_lt.1 hik) with hik | rfl
      · obtain ⟨j, e, hj, hg, hp⟩ := group_not_restart h.toLocalRun hy hi hnr
        have htk : tr.time k = t := le_antisymm hkt (hit ▸ h.time_mono hik.le)
        have hgk := restartCall_group h.toLocalRun hy hk
        rw [htk] at hgk
        rw [hit] at hg
        have : e.phase ≤ 0 := h.phase_order y hy y hy j k t e .restart hg hgk (by omega)
        omega
      · exact hnr hk
    unfold RunTrace.JoinedAt SA.joined
    rw [restartTime_eq h hy, lastBefore_le h]
    exact ⟨fun hj k hki hk => (joined_iff (h.time_nonneg k)).1 (hj k hk ((hset k hk).2 hki)),
      fun hj k hk hkt => (joined_iff (h.time_nonneg k)).2 (hj k ((hset k hk).1 hkt) hk)⟩
  · unfold RunTrace.honestAwakeJoined SA.honestAwakeJoined
    congr 1
    ext z
    exact Iff.rfl.and (Iff.rfl.and (hpt z))

end

end Compose

end Consensus.Goldilocks

end

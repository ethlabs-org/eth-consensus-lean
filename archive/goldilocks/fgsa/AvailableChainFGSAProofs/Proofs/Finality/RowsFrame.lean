module
public import AvailableChainFGSAProofs.Proofs.Finality.Middle
public import AvailableChainFGSAProofs.Proofs.Finality.RecordInv

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

private theorem rowsPrem_rootIsJ_def {n : Nat} (R : Controls (Fin n)) :
    R.rootIsJ = (decide (R.H = R.j + 1) && !R.contest) := rfl

private theorem rowsPrem_Z_def {n : Nat} (R : Controls (Fin n)) :
    R.Z = (if R.rootIsJ then R.J else R.F) := rfl

private theorem rowsPrem_lo_def {n : Nat} (R : Controls (Fin n)) :
    R.lo = (if R.contest then R.H else R.H - 1) := rfl

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [Fintype V] in
private theorem rowsPrem_clock_read (x : V) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) :
    ∃ i, rho.events[i]? = some (.tick x t) ∧
      (fgsa p c).clock (V2.D.Run.stateBefore E rho i x) t = nd := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x t with
  | none => rw [hi] at hnd; cases hnd
  | some i =>
    rw [hi] at hnd
    exact ⟨i, V2.D.Run.tickIdx?_spec hi, Option.some.inj hnd⟩

omit [Fintype V] in
/-- Paper 22:1236–1242: the post-clock store equals the store after all action ticks.
DC: INTENTIONAL: the own record can change; the store cannot change in the remaining ticks. -/
theorem rowsPrem_postClock_store (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (nd : Node p) (hnd : postClock E rho x t = some nd) :
    storeAt p c E rho (afterTicksIdx rho t) x = nd.st := by
  obtain ⟨i, hi, hclock⟩ := rowsPrem_clock_read p c E rho x t nd hnd
  change (V2.D.Run.stateBefore E rho (afterTicksIdx rho t) x).st = nd.st
  rw [← afterTicks_eq_stateBefore E rho hs t, afterTicks_node E rho hs hi]
  exact (tick_st (p := p) (c := c) E rho (V2.D.Run.stateBefore E rho i x) x t).trans
    (congrArg Node.st hclock)

variable {G ΔF : Time} {pt : KernelPt} {A : Block}
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

omit [DecidableEq V] [Fintype V] in
private theorem rowsPrem_UD (U B D : FGBlock (Fin p.n))
    (hUB : FGBlock.Preceq U B) (hBD : FGBlock.Preceq B D.parent) :
    FGBlock.Preceq U D :=
  preceq_trans (preceq_trans hUB hBD) (kmid_parent_preceq p D)

omit [DecidableEq V] [Fintype V] in
private theorem rowsPrem_cut_le_length (t : Time) :
    afterTicksIdx rho t ≤ rho.events.length := List.length_filter_le _ _

omit [Fintype V] in
private theorem rowsPrem_U_held (i : Nat) (x : V) (U D : FGBlock (Fin p.n))
    (hx : x ∈ rho.honest) (hD : D ∈ (storeAt p c E rho i x).fg.TF)
    (hUD : FGBlock.Preceq U D) : HeldAt p c E rho i x U := by
  refine ⟨hx, ?_⟩
  exact ancestor_closed_of_parent_closed _ (cstoreInv_stateBefore E rho i x).fg.closed D hD U hUD

omit [Fintype V] in
private theorem rowsPrem_FU_prefix (hXing : RXing p c E rho)
    (U : FGBlock (Fin p.n)) (cut i : Nat) (x : V)
    (hx : x ∈ rho.honest) (hi : i ≤ cut)
    (hfin : ∀ W ∈ (storeAt p c E rho i x).fg.TF,
      (finalityView p W).h_F < (heightView p U).h)
    (hU : HeldAt p c E rho cut x U) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F U := by
  obtain ⟨K, hKmem, hKF⟩ := (cstoreInv_stateBefore E rho i x).fg.Fcar
  exact hXing i cut x x K U hx hi hKmem hKF hU (hfin K hKmem)

include hK in
/-- Paper 22:1239–1240,1702–1706: the gate input finality block is below D.
DC: INTENTIONAL: RXing uses the accepted carrier's certificate height and the held U. -/
theorem rowsPrem_F_below_D_at_gate (hXing : RXing p c E rho) :
    ∀ x st, x ∈ rho.honest → gateIn p c E rho x ((pt.r + 2) * p.R) = some st →
      Block.Preceq (eraseFG st.fg.F) (eraseFG m.X_D) := by
  intro x st hx hst
  rw [gateIn_def, preTick_def] at hst
  cases hi : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams ((pt.r + 2) * p.R)) with
  | none => rw [hi] at hst; cases hst
  | some i =>
    rw [hi] at hst
    have he := Option.some.inj hst
    have hcut := kmid_tick_lt_afterTicks p c E rho hK.set.base.valid.toScheduleWellFormed
      (V2.D.Run.tickIdx?_spec hi)
      (show SA.gateTime p.toParams ((pt.r + 2) * p.R) ≤ p.actionTime (pt.r + 2) from le_rfl)
    have hf := rowsPrem_FU_prefix p c E rho hXing m.U
      (afterTicksIdx rho (p.actionTime (pt.r + 2))) i x hx hcut.le (by
        intro W hW
        rw [m.freshEntry.1]
        exact m.finalityThroughFinalAction i x W
          (hcut.le.trans (rowsPrem_cut_le_length p c rho _)) hcut.le ⟨hx, hW⟩)
      (rowsPrem_U_held p c E rho _ x m.U m.X_D hx (m.heldDAtFinalAction x hx)
        (rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD))
    have hfg := congrArg (fun s : State p.n => s.fg) he
    rw [clockPre_fg] at hfg
    rw [← hfg]
    exact eraseFG_preceq (preceq_trans hf (rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD))

include hK in
/-- ROOT-DIGEST W2b. Paper 22:1236–1242,1687–1695: the full F6 control frame at the actual action
read.
DC: INTENTIONAL: F below U precedes the cached-J calculation and FF2 contest exclusion. -/
theorem rowsPrem_action_frame (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      let R := FGSA.controls p nd.st
      m.X_D ∈ nd.st.fg.TF ∧ FGBlock.Preceq nd.st.fg.F m.U ∧
      R.H = m.d + 2 ∧ R.j = m.d + 1 ∧ R.J = m.U ∧
      R.contest = false ∧ R.Z = m.U ∧ R.lo = m.d + 1 ∧
      FGBlock.Preceq R.F m.X_D ∧ FGBlock.Preceq R.Z m.X_D ∧
      R.lo ≤ (heightView p m.X_D).h := by
  intro x nd hx hnd
  let i := afterTicksIdx rho (p.actionTime (pt.r + 2))
  have hhigh := m.highA
  have hi : i ≤ rho.events.length := rowsPrem_cut_le_length p c rho _
  have hr := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
    x (p.actionTime (pt.r + 2)) nd hnd
  change storeAt p c E rho i x = nd.st at hr
  have hD : m.X_D ∈ nd.st.fg.TF := by
    have hm : m.X_D ∈ (storeAt p c E rho i x).fg.TF := m.heldDAtFinalAction x hx
    rwa [hr] at hm
  have hFU : FGBlock.Preceq nd.st.fg.F m.U := by
    have hf := rowsPrem_FU_prefix p c E rho hXing m.U i i x hx le_rfl (by
      intro W hW
      rw [m.freshEntry.1]
      exact m.finalityThroughFinalAction i x W hi le_rfl ⟨hx, hW⟩)
      (rowsPrem_U_held p c E rho i x m.U m.X_D hx (m.heldDAtFinalAction x hx)
        (rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD))
    simpa only [hr] using hf
  have hI := (storeBundle_stateBefore E rho i x).cstore.fg
  rw [show (V2.D.Run.stateBefore E rho i x).st = nd.st from hr] at hI
  have hcap : ∀ W ∈ nd.st.fg.TF, (heightView p W).h ≤ m.d + 2 := by
    intro W hW
    exact m.capThroughFinalAction i x W hi le_rfl ⟨hx, by rw [hr]; exact hW⟩
  have hH : nd.st.fg.h_max = m.d + 2 := by
    rw [hI.hmax]
    apply le_antisymm
    · exact max_le (Finset.sup_le hcap) (by change 1 ≤ m.d + 2; omega)
    · exact (m.heightD ▸ Finset.le_sup (f := fun W => (heightView p W).h) hD).trans
        (le_max_left _ _)
  obtain ⟨K, hKmem, _, hjK, hJK⟩ := hI.pair.1
  have hjup : nd.st.fg.h_j ≤ m.d + 1 := by
    have := (fgCertificateLaws p).height.justified_below_height K
    have := hcap K hKmem
    simp only [Height] at *
    omega
  have hjlow : m.d + 1 ≤ nd.st.fg.h_j := by
    have hl := hI.pair.2 m.X_D hD (by rw [m.justifiedD]; exact hFU)
    have hf := KitFG.fst_le_of_lexKey_le hl
    simpa only [m.justifiedHeightD] using hf
  have hj : nd.st.fg.h_j = m.d + 1 := le_antisymm hjup hjlow
  obtain ⟨entry, hsource, hidentity⟩ := ff2_high_qc_identity p c E rho pt.w hK.input.t.h1 hQC hNames
  have heB := hsource x (pt.r + 1) m.B hx (m.sourceB x hx)
    (by change pt.w.M + 1 ≤ (heightView p m.B).h; rw [m.heightB]; omega)
  rw [m.heightB, m.entryB] at heB
  have heK := ((hidentity i x K hx (by rw [hr]; exact hKmem)).2.1
    (by rw [← hjK, hj]; omega)).1
  have hJ : nd.st.fg.J = m.U := by
    have hst : CStoreInv p nd.st := hr ▸ cstoreInv_stateBefore E rho i x
    apply viewRootInj_TF p nd.st hst _ _
      ⟨nd.st.fg.J, J_mem p nd.st hst, KitFG.preceq_refl _⟩
      ⟨m.X_D, hD, rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD⟩
    rw [hJK, heK, ← hjK, hj, heB]
  have hc : (FGSA.controls p nd.st).contest = false := by
    cases hh : (FGSA.controls p nd.st).contest with
    | false => rfl
    | true =>
      have hbad := ff2_no_high_contest p c E rho pt.w hK.input.t.h1 hQC hNames i x hi hx
      rw [hr] at hbad
      have hl := hbad hh
      change nd.st.fg.h_max ≤ pt.w.M + 1 at hl
      rw [hH] at hl
      change m.d + 2 ≤ pt.w.M + 1 at hl
      omega
  have hRH : (FGSA.controls p nd.st).H = m.d + 2 := hH
  have hRj : (FGSA.controls p nd.st).j = m.d + 1 := hj
  have hRJ : (FGSA.controls p nd.st).J = m.U := hJ
  have hZ : (FGSA.controls p nd.st).Z = m.U := by
    simp only [rowsPrem_Z_def, rowsPrem_rootIsJ_def, hRH, hRj, hc, Bool.not_false,
      show m.d + 2 = m.d + 1 + 1 from rfl, decide_true, Bool.and_self, ↓reduceIte, hRJ]
  have hlo : (FGSA.controls p nd.st).lo = m.d + 1 := by
    simp only [rowsPrem_lo_def, hc, Bool.false_eq_true, ↓reduceIte, hRH]
    change m.d + 2 - 1 = m.d + 1
    omega
  exact ⟨hD, hFU, hRH, hRj, hRJ, hc, hZ, hlo,
    preceq_trans hFU (rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD),
    hZ ▸ rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD,
    by rw [hlo, m.heightD]; exact Nat.le_succ _⟩

include hK in
/-- Paper 22:1236–1242: P1 keeps the actual D in the full filtered domain.
DC: INTENTIONAL: D supplies its own descendant height witness in the frame filter. -/
theorem rowsPrem_full_domain (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      m.X_D ∈ FGSA.fullTree p nd.st := by
  intro x nd hx hnd
  have hf := rowsPrem_action_frame p c E rho hK m hQC hXing hNames x nd hx hnd
  exact (KitFG.mem_filteredFromView (heightView p) _ _ m.X_D).mpr
    ⟨hf.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1,
      m.X_D, hf.1, KitFG.preceq_refl _, hf.2.2.2.2.2.2.2.2.2.2⟩

include hK in
/-- Paper 22:1243–1250,1696–1699: P2 gives compatibility of the actual live root and D.
DC: INTENTIONAL: T-START puts each selected live lease below the compatible output. -/
theorem rowsPrem_liveRoot_compatible (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      Block.Compatible (FGSA.liveRoot p nd.st) (eraseFG m.X_D) := by
  intro x nd hx hnd
  have hr := rowsPrem_postClock_store p c E rho hK.set.base.valid.toScheduleWellFormed
    x (p.actionTime (pt.r + 2)) nd hnd
  have ht := hK.services.start.2 (afterTicksIdx rho (p.actionTime (pt.r + 2))) x hx
  rw [hr] at ht
  rcases ht with hz | ⟨row, _, _, he, _, hle⟩
  · have hf := rowsPrem_action_frame p c E rho hK m hQC hXing hNames x nd hx hnd
    rw [hz, hf.2.2.2.2.2.2.1]
    exact block_compatible_of_common
      (eraseFG_preceq (rowsPrem_UD p m.U m.B m.X_D m.pathUB m.parentBD))
      (block_preceq_refl _)
  · have hc : Block.Compatible
        (S_at p c E rho (afterTicksIdx rho (p.actionTime (pt.r + 2))) x)
        (eraseFG m.X_D) := by
      have htime : tstar p pt.w ≤ SA.gateTime p.toParams m.cD := by
        have hrD : pt.r * p.R ≤ m.cD := by
          have := m.earlySlot.1
          have := Nat.le_add_right (pt.r * p.R) p.R
          have he : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
          omega
        have ht := kmid_slot_scale_le p hrD
        have hs := hK.start
        rw [kmid_period_eq] at hs
        change SA.gateTime p.toParams pt.w.u ≤ SA.gateTime p.toParams m.cD
        change SA.gateTime p.toParams pt.w.u ≤ 4 * p.Δ * ((pt.r * p.R : Nat) : Time) at hs
        change _ ≤ 4 * p.Δ * (m.cD : Time) + 6 * p.Δ
        have := p.deltaPos
        linarith
      have hgate : isGateTime p (tstar p pt.w) = true :=
        (isGateTime_iff p _).mpr ⟨pt.w.u, rfl⟩
      have hsD : HealSuffix p c rho (tstar p pt.w)
          (afterTicksIdx rho (SA.gateTime p.toParams m.cD)) := by
        change (if isGateTime p (tstar p pt.w) then _ else _) ≤ _ ∧ _
        rw [hgate, ite_eq_left rfl]
        exact ⟨afterTicksIdx_mono rho htime, List.length_filter_le _ _⟩
      have hsQ : HealSuffix p c rho (tstar p pt.w)
          (afterTicksIdx rho (p.actionTime (pt.r + 2))) := by
        change (if isGateTime p (tstar p pt.w) then _ else _) ≤ _ ∧ _
        rw [hgate, ite_eq_left rfl]
        exact ⟨afterTicksIdx_mono rho (htime.trans (by
          rw [kmid_actionTime_eq]
          have := kmid_slot_scale_le p m.earlySlot.2
          change 4 * p.Δ * (m.cD : Time) + 6 * p.Δ ≤ _
          linarith)), List.length_filter_le _ _⟩
      have hex := (m.serviceD.2 (kmid_slot_horizon hK m.earlySlot.2).2.2 x hx
        (kmid_window_confirmed hK ((Nat.mul_le_mul_right p.R (Nat.le_succ pt.r)).trans
          ((Nat.le_add_right _ _).trans m.earlySlot.1))
          (kmid_slot_horizon hK m.earlySlot.2).2.2 hx)).2.2.2.1
      have hhorStart : tstar p pt.w ≤ rho.horizon := by
        have hh := (kmid_slot_horizon hK (s := (pt.r + 2) * p.R) le_rfl).1
        have ht := hK.start
        rw [kmid_period_eq] at ht
        exact ht.trans ((kmid_slot_scale_le p
          (Nat.mul_le_mul_right p.R (by omega : pt.r ≤ pt.r + 2))).trans hh)
      have hout := hK.input.ac.h4.2.1 _ _ x x hsQ hsD
        (kmid_suffix_confirmed hK hx hsQ hhorStart)
        (kmid_suffix_confirmed hK hx hsD hhorStart)
      have heD : S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams m.cD)) x =
          eraseFG m.X_D := by
        rw [afterTicks_eq_stateBefore E rho hK.set.base.valid.toScheduleWellFormed] at hex
        exact hex
      rwa [heD] at hout
    change Block.Compatible (outputS p (storeAt p c E rho _ x)) _ at hc
    rw [hr] at hc
    exact he ▸ block_compatible_of_preceq_compatible hle hc

end AvailableChain.FGSA.Run
end

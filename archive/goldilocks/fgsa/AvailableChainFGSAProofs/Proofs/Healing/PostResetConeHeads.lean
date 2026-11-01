module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint2 -- shake: keep J6
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetProject

public section

/-! Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C1–C2.
DC: SAME source and live lease HEAD transfer at one event cut. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section Sources
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (cap : RCap p c E rho)
    (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec cap source rowCovered h0r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C1.
DC: SAME selected source below each honest HEAD at the named cut.
The ports have producers sourceDiscipline_tSrc, fgsa_rCap_channel,
rowPermission_covered, and the Recovery₂ and H0Reset inputs. -/
theorem postReset_source_heads_at_cut (i : Nat)
    (hraw : PostResetRawTransfer p c E rho w i)
    {D : FGBlock (Fin p.n)} {r s : Slot}
    (hD : SelectedBefore p c E rho i D r) (hhD : high p w D)
    (hgap : r + 1 ≤ s) (hcut : timeIdx rho (SA.voteTime p.toParams s) ≤ i) :
    ∀ y ∈ rho.honest, ∀ H, headAtLabel p c E rho y s = some H →
      Block.Preceq (eraseFG D) H := by
  rw [SelectedBefore_def] at hD
  obtain ⟨j, x, a, hj, hx, ht, hsrc, rfl⟩ := hD
  obtain ⟨C, hC, hDC, hlower⟩ :=
    postReset_source_gate_result p c E rho hrec.toRecovery₂ cap source rowCovered h0r hx hsrc hhD
  have hgate : IsGateTick p c rho j x (a * p.R) := ht
  rw [PostResetRawTransfer_def] at hraw
  intro y hy H hH
  exact block_preceq_trans hDC
    ((hraw j hj x (a * p.R) C hx hlower hgate hC).2.1 y s H hy hgap hcut hH)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14–H.17:2958–3012; plan S5 CONE C2.
DC: SAME live lease targets below the preceding honest HEAD batch.
The last-write port has producer fgsa_leaseOrigins_lastWrite. -/
theorem postReset_liveLease_heads_at_cut (i : Nat)
    (hrl : PostResetResetLeaseCompatible p c E rho w i)
    (hlease : PostResetLeaseSafe p c E rho w i)
    (hraw : PostResetRawTransfer p c E rho w i)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {s : Slot} (hs : w.sStar + 2 ≤ s)
    (hcut : timeIdx rho (SA.voteTime p.toParams s) ≤ i) :
    ∀ j z t (row : Block × Nat × Time), z ∈ rho.honest →
      rho.events[j]? = some (.tick z t) → SA.proposalTime p.toParams s ≤ t →
      t ≤ SA.voteTime p.toParams s → row ∈ (storeAt p c E rho j z).base.obligations →
      t < row.2.2 → ∀ y ∈ rho.honest, ∀ H,
        headAtLabel p c E rho y (s - 1) = some H → Block.Preceq row.1 H := by
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨j0, z0, a0, C0, ha0, _, hsrc0, he0, hh0⟩ := h0r.fresh
  have ht0 : IsGateTick p c rho j0 z0 w.sStar := by
    rw [h0r.label]
    exact ha0.2.1
  have hresetTime : SA.gateTime p.toParams w.sStar ≤ SA.voteTime p.toParams s := by
    have hsi : (w.sStar : Int) + 2 ≤ (s : Int) := by exact_mod_cast hs
    change 4 * p.Δ * (w.sStar : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hj0 : j0 < i :=
    ((V2.D.Engine.index_lt_read_length_iff hS _ ht0).mpr hresetTime).trans_le hcut
  have hselected : SelectedBefore p c E rho i C0 w.sStar :=
    selectedBefore_of_sourceBefore p c E rho ⟨j0, z0, w.rStar, a0, hj0, ha0,
      hsrc0, h0r.label⟩
  have hhigh0 : high p w C0 := by rw [high_def, hh0]
  have hprev : timeIdx rho (SA.voteTime p.toParams (s - 1)) ≤ i := by
    apply le_trans _ hcut
    change (rho.events.filter (fun e => decide (e.time ≤
      SA.voteTime p.toParams (s - 1)))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ SA.voteTime p.toParams s))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    apply decide_eq_true
    apply (of_decide_eq_true he).trans
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    have hm : ((s - 1 : Nat) : Int) ≤ (s : Int) := by exact_mod_cast Nat.sub_le s 1
    nlinarith [p.deltaPos]
  have hCHeads := postReset_source_heads_at_cut p c E rho hrec cap source rowCovered h0r
    i hraw hselected hhigh0
      (s := s - 1) (by simp only [Slot] at *; omega) hprev
  rw [PostResetResetLeaseCompatible_def] at hrl
  intro j z t row hz ht hlo hhi hrow hlive y hy H hH
  have hji : j < i :=
    ((V2.D.Engine.index_lt_read_length_iff hS _ ht).mpr hhi).trans_le hcut
  have hrelease : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤ j := by
    have hqt : SA.releaseTime p.toParams w.sStar < t := by
      have hbound := postReset_release_before_proposal p w hs
      linarith [p.deltaPos]
    have hpre : afterTicksIdx rho (SA.releaseTime p.toParams w.sStar) ≤
        V2.D.Run.idxBefore rho t := by
      change (rho.events.filter (cutPred _)).length ≤
        (rho.events.filter (fun e => decide (e.time < t))).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ he
      have htime : e.time ≤ SA.releaseTime p.toParams w.sStar :=
        V2.D.Engine.time_le_of_key_le e
          (.tick z (SA.releaseTime p.toParams w.sStar)) (of_decide_eq_true he)
      exact decide_eq_true (htime.trans_lt hqt)
    exact hpre.trans (healing_support_idxBefore_le p c E rho hS ht le_rfl)
  have hnow : (storeAt p c E rho j z).base.now ≤ t := by
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS ht z
    rw [fgsa_clock_now p c (rho.stateBefore E j z)] at hn
    exact hn
  have hcompat := hrl j hji z hz hrelease row hrow (hnow.trans_lt hlive)
  rcases Bool.or_eq_true_iff.mp hcompat with hlow | hhigh
  · exact block_preceq_trans hlow (he0 ▸ hCHeads y hy H hH)
  · by_cases heq : row.1 = w.CStar
    · exact heq ▸ (he0 ▸ hCHeads y hy H hH)
    obtain ⟨k, hkj, u, C, _, htk, hp, hres, hCB, hne, hB, hgen, hBC, hg⟩ :=
      postReset_leaseSafe_antecedent_of_lastWrite p c E rho writes hrow hz hhigh heq
    have htime : SA.gateTime p.toParams u ≤ SA.voteTime p.toParams s := by
      exact (fgsa_tick_time_strict E rho hS htk ht hkj).le.trans hhi
    have hgap := healing_source_label_bound p htime
    rw [PostResetLeaseSafe_def] at hlease
    exact (hlease k (hkj.trans hji) z u row.1 row.2.1 C hz htk hp hres
      hCB hne hB hgen hBC hg).2.1 y (s - 1) H hy
      (by simp only [Slot] at *; omega) hprev hH

end Sources

end AvailableChain.FGSA.Run
end

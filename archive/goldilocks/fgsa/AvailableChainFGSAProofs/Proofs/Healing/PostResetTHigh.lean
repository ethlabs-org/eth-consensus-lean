module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetProject

public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryProducers

public section

/-! Blueprint 21 H.13:2677–2741, H.14:2826–2846, H.22 H1:3244–3250;
plan THIGH-C A–C; B1/B13/B17/B18.
DC: SAME actual-source compatibility and label bound.
The all-cut carrier is an input; this file does not prove its induction. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2718–2741; plan THIGH-C A; B1/B13/B17/B18.
DC: SAME actual honest supporting HEAD at the selected source's own label.
TSrc (sourceDiscipline_tSrc) supplies fast support; Recovery₂ supplies an
honest seat and its actual vote. No row or later reader guard is needed. -/
theorem postReset_selected_supporting_head [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (source : TSrc p c E rho)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ z H, z ∈ rho.honest ∧ headAtLabel p c E rho z (r * p.R) = some H ∧
      Block.Preceq (eraseFG C) H := by
  have he : actionSource p c E rho x r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = _
    rw [hsrc]
    rfl
  obtain ⟨X, -, -, hC, -, -, hfast, -⟩ := source x r (eraseFG C) hx he
  obtain ⟨st, hst, hτ⟩ := hfast _ hC
  rw [gateIn_def, preTick_def] at hst
  cases hi : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams (r * p.R)) with
  | none => rw [hi] at hst; cases hst
  | some i =>
    rw [hi] at hst
    have hst := Option.some.inj hst
    subst st
    obtain ⟨k, o, hh, ho, hk, hsup⟩ := healing_support_honest_seat rho
      hrec.base.cstar hrec.fault _ _ _ hτ
    obtain ⟨H, hH, hHm, -, -, hm, hl⟩ := healing_support_clean_target E rho o ho
    obtain ⟨j, hj, hhead⟩ := healing_support_honest_head E rho hrec.base.valid hm hl hk hh
    let z := rho.seatOf (RunLabel.base (Label.head (r * p.R))) k
    refine ⟨z, FGSA.headVote p
      ((fgsa p c).clock (V2.D.Run.stateBefore E rho j z)
        (SA.voteTime p.toParams (r * p.R))).st
      (r * p.R), hh, ?_, ?_⟩
    · change (postClock E rho z (SA.voteTime p.toParams (r * p.R))).map _ = _
      rw [postClock_def, preTick_def,
        fgsa_tickIdx_of_event p c E rho hrec.base.valid.toScheduleWellFormed hj]
      rfl
    · change Gen.AC.Root.voteSupports
        (GridCO.resolutionTree (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams (r * p.R))))) (eraseFG C) o = true at hsup
      rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hH] at hsup
      have heq := stored_eq_headVote E rho hrec.base.idealization i x hHm j z
        (SA.voteTime p.toParams (r * p.R)) (r * p.R)
        (Option.some.inj ((resolvedHead_root _ o hH).symm.trans hhead))
      exact heq ▸ (Bool.and_eq_true_iff.mp hsup).2

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

omit cap source rowCovered in
private theorem thigh_label_sync {x : V} {r : Nat} {C : FGBlock (Fin p.n)}
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hj : w.sStar ≤ r * p.R) :
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (r * p.R)) (SA.gateTime p.toParams (r * p.R)) := by
  have hGST : E.t_GST ≤ SA.voteTime p.toParams (r * p.R) := by
    apply h0r.synchronous.trans
    have hc : (w.sStar : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hj
    change 4 * p.Δ * (w.sStar : Int) + p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hhor : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon := by
    rw [actionSourceFG_def, postClock_def, preTick_def] at hsrc
    cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
    | none => simp only [hi, Option.map_none] at hsrc; contradiction
    | some i =>
      exact (hrec.base.valid.toScheduleWellFormed.in_horizon _
        (List.mem_of_getElem? (V2.D.Run.tickIdx?_spec hi))).2
  have hvd : SA.voteTime p.toParams (r * p.R) + E.Δ ≤
      SA.gateTime p.toParams (r * p.R) := by
    rw [hrec.base.delta]
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hGST hvd hhor

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2677–2687, 2718–2741; H.14:2826–2846;
plan THIGH-C B; B1/B13/B17/B18. DC: SAME pairwise high-source compatibility.
Different rounds use H2A clause 1 and the later source's actual supporting
HEAD. Equal rounds use IF.6 on both raw gate results, then prefix transfer.
Only inv.raw_transfer is used, at max (k + 1) (timeIdx rho (voteTime s)),
where k is the earlier source's actual gate tick. The named producers are
fgsa_rCap_channel, sourceDiscipline_tSrc and rowPermission_covered. -/
theorem postReset_tHigh_pairwise (inv : ∀ i, PostResetInv p c E rho w i) :
    ∀ x y r r' C C', x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG p c E rho x r = some (some C) →
      actionSourceFG p c E rho y r' = some (some C') → high p w C → high p w C' →
      Block.Compatible (eraseFG C) (eraseFG C') := by
  have later {x y : V} {r r' : Nat} {C C' : FGBlock (Fin p.n)}
      (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
      (hC : actionSourceFG p c E rho x r = some (some C))
      (hC' : actionSourceFG p c E rho y r' = some (some C'))
      (hh : high p w C) (hlt : r < r') :
      Block.Compatible (eraseFG C) (eraseFG C') := by
    obtain ⟨z, H, hz, hH, hC'H⟩ :=
      postReset_selected_supporting_head p c E rho hrec.toRecovery₂ source hy hC'
    have hlabel : r * p.R + 1 ≤ r' * p.R := by
      have hm := Nat.mul_le_mul_right p.R (Nat.succ_le_of_lt hlt)
      have hR := p.RLarge
      rw [Nat.succ_mul] at hm
      omega
    have hCut : E.t_GST ≤ slotStartZ p (((r' * p.R : Nat) : Int) - 1) := by
      have hlabel0 := postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap
        h0r hx hC hh
      have hbase := healing_ready_vote_cutoff E (healing_reset_source_ready h0r)
      have hI : (w.sStar : Int) ≤ (r' * p.R : Nat) := by
        have hle := Nat.mul_le_mul_right p.R (Nat.le_of_lt hlt)
        exact_mod_cast hlabel0.trans hle
      change E.t_GST ≤ 4 * p.Δ * ((w.sStar : Int) - 1) at hbase
      change E.t_GST ≤ 4 * p.Δ * (((r' * p.R : Nat) : Int) - 1)
      nlinarith [p.deltaPos]
    have hHhor : SA.voteTime p.toParams (r' * p.R) ≤ rho.horizon := by
      have h := hH
      unfold headAtLabel at h
      rw [postClock_def, preTick_def] at h
      cases hi : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams (r' * p.R)) with
      | none => simp only [hi, Option.map_none] at h; cases h
      | some k => exact (hrec.base.valid.toScheduleWellFormed.in_horizon _
          (List.mem_of_getElem? (V2.D.Run.tickIdx?_spec hi))).2
    have hSync : E.t_GST ≤ SA.voteTime p.toParams (r' * p.R) := by
      apply le_trans hCut
      change 4 * p.Δ * (((r' * p.R : Nat) : Int) - 1) ≤
        4 * p.Δ * ((r' * p.R : Nat) : Int) + p.Δ
      linarith [p.deltaPos]
    have hCH := (postReset_h2A_reset p c E rho hrec.toRecovery₂ cap source rowCovered h0r inv
      x r C hx hC hh).1 z (r' * p.R) H
      ⟨hz, healing_recovery_joined E rho hrec hz hCut hSync hHhor⟩ hlabel hH
    exact Gen.Pure.block_compatible_of_common hCH hC'H
  intro x y r r' C C' hx hy hC hC' hh hh'
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · exact later hx hy hC hC' hh hlt
  · subst r'
    obtain ⟨B, hB, hCB, hj⟩ :=
      postReset_source_gate_result p c E rho hrec.toRecovery₂ cap source rowCovered h0r hx hC hh
    obtain ⟨B', hB', hC'B', -⟩ :=
      postReset_source_gate_result p c E rho hrec.toRecovery₂ cap source rowCovered h0r hy hC' hh'
    have hSame := fgsa_sameLabel_serviceScope E rho hrec.base.valid
      hrec.base.restartsAtWakes hrec.base.delta (r * p.R)
      (thigh_label_sync p c E rho hrec h0r hC hj)
    have hc := fgsa_sameLabel_on p c E rho hrec.base.valid (r * p.R) hSame
      hrec.base.idealization x y B B' hx hy hB hB'
    change (Block.preceq B B' || Block.preceq B' B) = true at hc
    rcases Bool.or_eq_true_iff.mp hc with hc | hc
    · exact Gen.Pure.block_compatible_of_common
        (Gen.Pure.block_preceq_trans hCB hc) hC'B'
    · exact Gen.Pure.block_compatible_of_common hCB
        (Gen.Pure.block_preceq_trans hC'B' hc)
  · have hc := later hy hx hC' hC hh' hgt
    change (Block.preceq (eraseFG C') (eraseFG C) ||
      Block.preceq (eraseFG C) (eraseFG C')) = true at hc
    change (Block.preceq (eraseFG C) (eraseFG C') ||
      Block.preceq (eraseFG C') (eraseFG C)) = true
    simpa only [Bool.or_comm] using hc

end Sources

section Reset
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
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
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec mono emittedNonempty emittedName writes xing origin h0r

variable (cap : RCap p c E rho) (source : TSrc p c E rho)
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

include cap source rowCovered

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2826–2846, H.22 H1:3244–3250;
plan THIGH-C C; B1/B13/B17/B18. DC: SAME frozen THigh, verbatim.
B supplies the pairwise clause. THIGH B2 supplies compatibility with C*,
and THIGH A supplies the label bound, including actions that send no row.
Only inv.raw_transfer is used through B. Other named producers are fgsa_rMono,
sourceDiscipline_emittedNonempty, emittedName_window, fgsa_leaseOrigins_lastWrite,
fgsa_rXing, sourceDiscipline_qcOrigin, fgsa_rCap_channel, sourceDiscipline_tSrc
and rowPermission_covered, with each producer's exact input type. -/
theorem postReset_tHigh_reset (inv : ∀ i, PostResetInv p c E rho w i) :
    THigh p c E rho w := by
  have lossScopes := healing_loss_service_scope_recovery E rho hrec mono source
    emittedNonempty emittedName
  intro x y r r' C C' hx hy hC hC' hh hh'
  exact ⟨postReset_tHigh_pairwise p c E rho hrec cap source rowCovered h0r inv
      x y r r' C C' hx hy hC hC' hh hh',
    postReset_selected_reset_compatible p c E rho hrec lossScopes mono emittedNonempty
      emittedName writes xing origin h0r
      (fgsa_sameLabel_serviceScope E rho hrec.base.valid hrec.base.restartsAtWakes
        hrec.base.delta w.sStar (by
          have h := h0r.synchronous
          have hd : SA.voteTime p.toParams w.sStar + E.Δ ≤ SA.gateTime p.toParams w.sStar := by
            rw [hrec.base.delta]
            change 4 * p.Δ * (w.sStar : Int) + p.Δ + p.Δ ≤
              4 * p.Δ * (w.sStar : Int) + 6 * p.Δ
            linarith [p.deltaPos]
          exact Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
            hrec.sync (fgsaDelay_nonrow E.Δ _) h hd
            (by
              obtain ⟨j, y, a, C0, ha, _⟩ := h0r.fresh
              have hh := (hrec.base.valid.toScheduleWellFormed.in_horizon _
                (List.mem_of_getElem? ha.2.1)).2
              change SA.gateTime p.toParams (w.rStar * p.R) ≤ rho.horizon at hh
              simpa only [h0r.label] using hh))) cap source rowCovered hx hC hh,
    postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap h0r hx hC hh⟩

end Reset

end AvailableChain.FGSA.Run
end
